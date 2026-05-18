(** Drive certificate emission: run the symbolic interpreter over every
    function in a crate, collect the per-function event buffer, and write
    [<input>.cert.json].

    Conceptually mirrors [BorrowCheck.borrow_check_crate]: we don't synthesize
    a Pure AST, we just exercise the interpreter to populate the event
    buffer. The post-prepass crate is serialized into [cc_llbc_program]
    inside the cert itself (cert_fmt_version >= 3), so the Lean side
    reads exactly what the OCaml side checked from a single artifact. *)

open Interp
open InterpStatements
open LlbcAst
open Contexts
open TranslateCore

(* M9.5l: capitalize the first ASCII letter of [s]. Mirrors
   [StringUtils.capitalize_first_letter] in the standard backend, used
   when flattening Lean names like ["traits_basic"; "Numeric"] to
   ["Traits_basic"; "Numeric"] before the no-separator concat that
   produces ["Traits_basicNumeric"]. *)
let capitalize_first_letter (s : string) : string =
  if String.length s = 0 then s
  else
    let c = Char.uppercase_ascii s.[0] in
    String.make 1 c ^ String.sub s 1 (String.length s - 1)

(* [M9.7o-E5b] The [trait_clauses_of_generics] helper was deleted
   alongside the flat [cert_signature] record; trait-clause info now
   flows from the structured [LlbcProgram.fun_decls[k].signature
   .generics] which [LlbcJson] serializes directly. *)

(* M9.5l: extract a [cert_source_span] from a Charon [item_meta]. *)
let source_span_of_item_meta (im : Types.item_meta) : CertEvent.cert_source_span option =
  let sp = im.span.data in
  let file = match sp.file.name with Virtual s | Local s | NotReal s -> s in
  Some
    {
      CertEvent.ss_file = file;
      ss_beg_line = sp.beg_loc.line;
      ss_beg_col = sp.beg_loc.col;
      ss_end_line = sp.end_loc.line;
      ss_end_col = sp.end_loc.col;
    }

let log = Logging.main_log

(** Run the symbolic interpreter, then steal the event buffer from the
    eval_ctx before it is dropped.

    [evaluate_function_symbolic] does not return the final ctx, so for M3 we
    replicate its setup just enough to drive the interpreter and keep a
    reference to the ctx we built. *)
let collect_for_fun (trans_ctx : trans_ctx) (marked_ids : marked_ids)
    (fdef : fun_decl) : CertEvent.fun_cert option =
  match fdef.body with
  | StructuredBody _ -> begin
      try
        (* Reset the observer's per-function state before driving
           the interpreter on this fun_decl. -*)
        CertObserver.reset ();
        let ctx, _input_svs, _inst_sg =
          initialize_symbolic_context_for_fun trans_ctx marked_ids fdef
        in
        let config = mk_config SymbolicMode in
        let body =
          [%add_loc] LlbcAstUtils.body_as_body_exn fdef.body
        in
        let _ =
          try
            let ctx_resl, _cc = eval_function_body config body.body ctx in
            (* M9.5v: drive [pop_frame] on each Return branch so that the
               function-exit cleanup ([drop_outer_loans_at_lplace] inside
               [pop_frame]) emits EvEndBorrow events for outer loans that
               are dropped when the frame dies. Without this, fixtures
               like [paper::call_choose] leave loans live at EvReturn
               (the borrow check passes because the frame goes away, but
               the cert replay has no event to release them). Mirrors the
               [finish] path in [evaluate_function_symbolic]. *)
            List.iter
              (fun (ctx, res) ->
                match res with
                | Cps.Return ->
                    (try
                       let _, _, _ =
                         pop_frame config fdef.item_meta.span
                           ~pop_locals:true ~pop_return_value:true ctx
                       in
                       ()
                     with Errors.CFailure _ -> ())
                | _ -> ())
              ctx_resl
          with Errors.CFailure _ ->
            (* Match the behavior of evaluate_function_symbolic: tolerate
               failures during M3 so the cert covers as many functions as
               possible. *)
            ()
        in
        let events = CertObserver.flush () in
        let env = Print.Contexts.decls_ctx_to_fmt_env trans_ctx in
        let fn_name = Print.name_to_string env fdef.item_meta.name in
        (* [M9.7o-E5b] Cert v3 no longer carries a flat per-function
           [cert_signature] copy. The Lean checker reads the structured
           signature from [cc_llbc_program.fun_decls[k].signature]
           after matching by [fc_fn_id]. *)
        let source_span : CertEvent.cert_source_span option =
          let span_data = fdef.item_meta.span.data in
          let file =
            match span_data.file.name with
            | Virtual s | Local s | NotReal s -> s
          in
          Some
            {
              ss_file = file;
              ss_beg_line = span_data.beg_loc.line;
              ss_beg_col = span_data.beg_loc.col;
              ss_end_line = span_data.end_loc.line;
              ss_end_col = span_data.end_loc.col;
            }
        in
        (* M10.x.0 (cert v6): [fc_stmt_refs] is a parallel-to-events
           array carrying one [Option cert_stmt_ref] per event. At
           M10.x.0 we ship a length-matched array of [None]
           sentinels — the threading at the 23 emit sites is
           deferred to M10.x.0b (audit §"OCaml emit-site changes",
           blocker-policy fallback). The shape is in place so the
           Lean parser already accepts the field and the Phase-E2
           consumer ([replayFun_event_induct]) can land alongside
           the population work without a second schema bump. *)
        let stmt_refs : CertEvent.cert_stmt_ref option list =
          List.map (fun _ -> None) events
        in
        Some
          {
            CertEvent.fc_fn_id = fdef.def_id;
            fc_fn_name = fn_name;
            fc_source_span = source_span;
            fc_events = events;
            fc_final_state =
              { CertEvent.cs_env = []; cs_live_loans = [] };
            (* M6 will populate cs_env / cs_live_loans from the final ctx. *)
            (* M9.5l: pretty name is filled in by [generate_crate_cert]
               from the trait-impl table, after this record is built. *)
            fc_pretty_name = None;
            fc_stmt_refs = stmt_refs;
          }
      with _ -> None
    end
  | _ -> None

(** [M9.5l] Bare last-segment name of a Charon item. For a trait
    [traits_basic::Numeric] this returns [Numeric]; for a type
    [traits_basic::Tag] it returns [Tag]. *)
let bare_name_of (n : Types.name) : string =
  match List.rev n with
  | Types.PeIdent (s, _) :: _ -> s
  | _ -> "__Anon"

(** [M9.5l] First identifier in the name path. *)
let crate_segment_of (n : Types.name) : string =
  match n with
  | Types.PeIdent (s, _) :: _ -> s
  | _ -> "crate"

(** [M9.7o-E5a] Build a [fun_decl_id → pretty_name] table by walking
    the crate's [trait_impls] directly. Pre-M9.7o-E5a this routed
    through the now-deleted [cert_trait_impl] mirror; we now compute
    the same standard-backend impl-pretty-name shape inline.

    For each impl method, the pretty name is
    [<impl_pretty_name>.<method_name>] — e.g.
    [Tag.Insts.Traits_basicNumeric.value]. Used by
    [generate_crate_cert] to set [fc_pretty_name] for impl-method
    function bodies. The Lean side recomputes the same shape from the
    structured [LlbcTraitImpl] (see [traitImplOfLlbcTraitImpl] in
    [Translate/Driver.lean]); the two sides agree on the result. *)
let build_fn_pretty_name_table (crate : crate)
    : (int, string) Hashtbl.t =
  let h = Hashtbl.create 16 in
  let trait_name_of (id : Types.trait_decl_id) : string =
    match LlbcAst.TraitDeclId.Map.find_opt id crate.trait_decls with
    | Some td -> bare_name_of td.item_meta.name
    | None -> "__UnknownTrait"
  in
  let self_type_var_of (impl : trait_impl) : string option =
    match impl.impl_trait.generics.types with
    | Types.TVar _ :: _ -> Some "_"  (* presence is what we need *)
    | _ -> None
  in
  let lean_name_of_lit_ty (lty : Types.literal_type) : string =
    match lty with
    | TBool -> "Bool"
    | TChar -> "Char"
    | TUInt U8 -> "Std.U8" | TUInt U16 -> "Std.U16"
    | TUInt U32 -> "Std.U32" | TUInt U64 -> "Std.U64"
    | TUInt U128 -> "Std.U128" | TUInt Usize -> "Std.Usize"
    | TInt I8 -> "Std.I8" | TInt I16 -> "Std.I16"
    | TInt I32 -> "Std.I32" | TInt I64 -> "Std.I64"
    | TInt I128 -> "Std.I128" | TInt Isize -> "Std.Isize"
    | TFloat F16 -> "Std.F16" | TFloat F32 -> "Std.F32"
    | TFloat F64 -> "Std.F64" | TFloat F128 -> "Std.F128"
  in
  let self_name_of (impl : trait_impl) : string =
    match impl.impl_trait.generics.types with
    | Types.TAdt { id = Types.TAdtId tid; _ } :: _ -> (
        match Types.TypeDeclId.Map.find_opt tid crate.type_decls with
        | Some td -> bare_name_of td.item_meta.name
        | None -> "__UnknownSelf")
    | Types.TVar _ :: _ -> "Blanket"
    | Types.TLiteral lty :: _ -> lean_name_of_lit_ty lty
    | _ -> "__UnknownSelf"
  in
  LlbcAst.TraitImplId.Map.values crate.trait_impls
  |> List.iter (fun (impl : trait_impl) ->
       let trait_id = impl.impl_trait.id in
       let trait_bare = trait_name_of trait_id in
       let self_bare = self_name_of impl in
       let self_var = self_type_var_of impl in
       let trait_crate_seg = crate_segment_of (
         match LlbcAst.TraitDeclId.Map.find_opt trait_id crate.trait_decls with
         | Some td -> td.item_meta.name
         | None -> [])
       in
       let pretty_name =
         match self_var with
         | Some _ -> Printf.sprintf "%s.Blanket" trait_bare
         | None ->
             Printf.sprintf "%s.Insts.%s%s" self_bare
               (capitalize_first_letter trait_crate_seg)
               trait_bare
       in
       match LlbcAst.TraitDeclId.Map.find_opt trait_id crate.trait_decls with
       | Some td ->
           List.iter2
             (fun (_, (b : Types.fun_decl_ref Types.binder))
                  (_, (tb : trait_method Types.binder)) ->
               let fn_id = Types.FunDeclId.to_int b.binder_value.id in
               let mname = tb.binder_value.name in
               Hashtbl.replace h fn_id (pretty_name ^ "." ^ mname))
             (Types.TraitMethodId.Map.bindings impl.methods)
             (Types.TraitMethodId.Map.bindings td.methods)
       | None -> ());
  h

(** Run the interpreter on every function in the crate, capturing per-function
    event traces. *)
let generate_crate_cert (crate : crate) (marked_ids : marked_ids)
    (crate_hash : string) : CertEvent.crate_cert =
  let trans_ctx = compute_contexts crate in
  let pretty_table = build_fn_pretty_name_table crate in
  let fun_certs : CertEvent.fun_cert list =
    List.filter_map
      (fun fd ->
        match collect_for_fun trans_ctx marked_ids fd with
        | None -> None
        | Some fc ->
            let id_int = Types.FunDeclId.to_int fc.fc_fn_id in
            let pretty = Hashtbl.find_opt pretty_table id_int in
            Some { fc with fc_pretty_name = pretty })
      (FunDeclId.Map.values crate.fun_decls)
  in
  (* M9.7d: populate the cert-v3 [llbc_program] subtree from a
     minimal Aeneas-side LLBC -> JSON serializer. See
     [src/cert/LlbcJson.ml] for the why (Charon-ml ships only
     deserializers; no upstream [crate_to_json] binding exists) and
     for the per-type field set the Lean parser
     ([AeneasCheck.Json.Parser.parseLlbcProgram]) actually reads.
     M9.7o-E5a: with the flat ADT / trait decl mirrors removed, the
     structured subtree is now the sole source of type / trait decls
     on the Lean side. *)
  let llbc_program = LlbcJson.crate_to_json crate in
  {
    cc_fmt_version = CertEvent.cert_fmt_version;
    cc_crate_hash = crate_hash;
    cc_functions = fun_certs;
    cc_llbc_program = llbc_program;
  }

(** Write [crate.cert.json] alongside [crate.llbc]. *)
let write_cert (input_path : string) (cc : CertEvent.crate_cert) : string =
  let out_path =
    let base = Filename.remove_extension input_path in
    base ^ ".cert.json"
  in
  CertJson.write_to_file out_path cc;
  log#linfo (lazy ("Wrote certificate: " ^ out_path));
  out_path

(** Top-level entry point.

    The cert (cert_fmt_version >= 3) embeds the post-pre-pass LLBC
    program directly via [LlbcJson.crate_to_json]. The companion
    [.llbc.json] stub previously written via [-emit-llbc-json] was
    retired in M9.7e (commit B2). [cc_crate_hash] now hashes the
    input LLBC file (the Charon emission Aeneas consumed); the
    post-pre-pass content travels inside the cert itself. *)
let emit (input_path : string) (crate : crate) (marked_ids : marked_ids) : unit =
  if !Config.emit_cert then begin
    let crate_hash = CertJson.sha256_file input_path in
    let cc = generate_crate_cert crate marked_ids crate_hash in
    let _ = write_cert input_path cc in
    ()
  end

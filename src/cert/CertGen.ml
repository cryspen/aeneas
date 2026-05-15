(** Drive certificate emission: run the symbolic interpreter over every
    function in a crate, collect the per-function event buffer, and write
    [<input>.cert.json].

    Conceptually mirrors [BorrowCheck.borrow_check_crate]: we don't synthesize
    a Pure AST, we just exercise the interpreter to populate the event
    buffer. The post-prepass crate is also written to [<input>.llbc.json] so
    the Lean side reads exactly what the OCaml side checked. *)

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
        let ctx, _input_svs, _inst_sg =
          initialize_symbolic_context_for_fun trans_ctx marked_ids fdef
        in
        let buffer = ctx.cert_event_buffer in
        let config = mk_config SymbolicMode in
        let body =
          [%add_loc] LlbcAstUtils.body_as_body_exn fdef.body
        in
        let _ =
          try
            let _ctx_resl, _cc = eval_function_body config body.body ctx in
            ()
          with Errors.CFailure _ ->
            (* Match the behavior of evaluate_function_symbolic: tolerate
               failures during M3 so the cert covers as many functions as
               possible. *)
            ()
        in
        let events = List.rev !buffer in
        let fn_name =
          let env = Print.Contexts.decls_ctx_to_fmt_env trans_ctx in
          Print.name_to_string env fdef.item_meta.name
        in
        let signature : CertEvent.cert_signature =
          {
            csig_inputs = fdef.signature.inputs;
            csig_output = fdef.signature.output;
            (* M9.5i: the function's type-parameter names live on
               [fun_decl.generics], not [fun_sig] (Charon keeps the
               value-level signature separate from the generics
               binder; only [fun_decl] sees both). *)
            csig_type_params =
              List.map
                (fun (tp : Types.type_param) -> tp.name)
                fdef.generics.types;
          }
        in
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
        Some
          {
            CertEvent.fc_fn_id = fdef.def_id;
            fc_fn_name = fn_name;
            fc_signature = signature;
            fc_source_span = source_span;
            fc_events = events;
            fc_final_state =
              { CertEvent.cs_env = []; cs_live_loans = [] };
            (* M6 will populate cs_env / cs_live_loans from the final ctx. *)
            (* M9.5l: pretty name is filled in by [generate_crate_cert]
               from the trait-impl table, after this record is built. *)
            fc_pretty_name = None;
          }
      with _ -> None
    end
  | _ -> None

(** Collect the crate's transparent ADT type declarations into a flat list
    indexed by [TypeDeclId]. Struct decls carry their full field list
    (name + type); other kinds are downgraded to [Opaque] so the Lean
    parser can tolerate them. M9.5b only consumes [Struct]. *)
let collect_type_decls (crate : crate) : CertEvent.cert_type_decl list =
  Types.TypeDeclId.Map.values crate.type_decls
  |> List.map (fun (td : Types.type_decl) : CertEvent.cert_type_decl ->
         let env = Print.Contexts.decls_ctx_to_fmt_env (compute_contexts crate) in
         let full_name =
           Print.name_to_string env td.item_meta.name
         in
         let bare_name =
           match List.rev (String.split_on_char ':' full_name) with
           | [] -> full_name
           | last :: _ -> last
         in
         let kind : CertEvent.cert_type_decl_kind =
           match td.kind with
           | Types.Struct fields ->
               let cert_fields : CertEvent.cert_field list =
                 List.mapi
                   (fun i (f : Types.field) ->
                     CertEvent.{
                       cf_idx = i;
                       cf_name = f.field_name;
                       cf_ty = f.field_ty;
                     })
                   fields
               in
               CTDStruct cert_fields
           | Types.Enum variants ->
               let cert_variants : CertEvent.cert_variant list =
                 List.mapi
                   (fun i (v : Types.variant) ->
                     let cert_fields : CertEvent.cert_field list =
                       List.mapi
                         (fun j (f : Types.field) ->
                           CertEvent.{
                             cf_idx = j;
                             cf_name = f.field_name;
                             cf_ty = f.field_ty;
                           })
                         v.fields
                     in
                     CertEvent.{
                       cv_id = i;
                       cv_name = v.variant_name;
                       cv_fields = cert_fields;
                     })
                   variants
               in
               CTDEnum cert_variants
           | _ -> CTDOpaque
         in
         (* M9.5l: detect tuple-style structs (positional fields, OR a
            unit struct's empty field list). Lean side renders these
            as `@[reducible] def <Name> := Unit` when there are zero
            fields, mirroring the standard backend's handling. *)
         let is_tuple_struct = TypesAnalysis.type_decl_is_tuple_struct td in
         {
           ctd_id = Types.TypeDeclId.to_int td.def_id;
           ctd_name = bare_name;
           ctd_kind = kind;
           (* M9.5i: emit the ADT's type-parameter names so the Lean
              side can render `inductive Foo (T : Type) where ...`
              and resolve `TVar (Free K)` inside variant payload
              types to the K-th name. *)
           ctd_type_params =
             List.map
               (fun (tp : Types.type_param) -> tp.name)
               td.generics.types;
           ctd_is_tuple_struct = is_tuple_struct;
           ctd_source_span = source_span_of_item_meta td.item_meta;
         })

(** [M9.5l] Bare last-segment name of a Charon item. For a trait
    [traits_basic::Numeric] this returns [Numeric]; for a type
    [traits_basic::Tag] it returns [Tag]. Used when assembling
    standard-backend-style names for trait decls / impls. *)
let bare_name_of (n : Types.name) : string =
  match List.rev n with
  | Types.PeIdent (s, _) :: _ -> s
  | _ -> "__Anon"

(** [M9.5l] First identifier in the name path — used as the crate
    segment when computing flat impl names. *)
let crate_segment_of (n : Types.name) : string =
  match n with
  | Types.PeIdent (s, _) :: _ -> s
  | _ -> "crate"

(** [M9.5l] Collect trait declarations from the crate. The cert
    carries the bare trait name and the trait's methods (name +
    signature only — bodies, if any, live as standalone [fun_decl]s
    already in [cc_functions]). *)
let collect_trait_decls (crate : crate) : CertEvent.cert_trait_decl list =
  let env = Print.Contexts.decls_ctx_to_fmt_env (compute_contexts crate) in
  LlbcAst.TraitDeclId.Map.values crate.trait_decls
  |> List.map (fun (td : trait_decl) : CertEvent.cert_trait_decl ->
         let name = bare_name_of td.item_meta.name in
         let qualified = Print.name_to_string env td.item_meta.name in
         let methods : CertEvent.cert_trait_method list =
           List.map
             (fun (_, (b : trait_method Types.binder)) ->
               let m = b.binder_value in
               let sg : CertEvent.cert_signature =
                 {
                   csig_inputs = m.signature.inputs;
                   csig_output = m.signature.output;
                   (* The trait method's generics live on the binder
                      (Charon separates value-sig from generics). *)
                   csig_type_params =
                     List.map
                       (fun (tp : Types.type_param) -> tp.name)
                       b.binder_params.types;
                 }
               in
               { CertEvent.ctm_name = m.name; ctm_signature = sg })
             (Types.TraitMethodId.Map.bindings td.methods)
         in
         {
           ctrd_id = LlbcAst.TraitDeclId.to_int td.def_id;
           ctrd_name = name;
           ctrd_qualified_name = qualified;
           ctrd_methods = methods;
           ctrd_source_span = source_span_of_item_meta td.item_meta;
         })

(** [M9.5l] Collect trait impls. For each impl, we compute the
    standard-Aeneas Lean impl name [<SelfBare>.Insts.<CrateCap><TraitBare>]
    (the minimal-case formula — generic / blanket impls are out of
    scope for M9.5l). The Lean checker uses this name verbatim for
    both the [@[reducible] def …] header and the per-method body
    references inside [use_…] callers. *)
let collect_trait_impls (crate : crate) : CertEvent.cert_trait_impl list =
  let env = Print.Contexts.decls_ctx_to_fmt_env (compute_contexts crate) in
  let trait_name_of (id : Types.trait_decl_id) : string =
    match LlbcAst.TraitDeclId.Map.find_opt id crate.trait_decls with
    | Some td -> bare_name_of td.item_meta.name
    | None -> "__UnknownTrait"
  in
  let self_type_decl_id_of (impl : trait_impl) : int option =
    match impl.impl_trait.generics.types with
    | Types.TAdt { id = Types.TAdtId tid; _ } :: _ ->
        Some (Types.TypeDeclId.to_int tid)
    | _ -> None
  in
  let self_name_of (impl : trait_impl) : string =
    match impl.impl_trait.generics.types with
    | Types.TAdt { id = Types.TAdtId tid; _ } :: _ -> (
        match Types.TypeDeclId.Map.find_opt tid crate.type_decls with
        | Some td -> bare_name_of td.item_meta.name
        | None -> "__UnknownSelf")
    | _ -> "__UnknownSelf"
  in
  LlbcAst.TraitImplId.Map.values crate.trait_impls
  |> List.map (fun (impl : trait_impl) : CertEvent.cert_trait_impl ->
         let trait_id = impl.impl_trait.id in
         let trait_bare = trait_name_of trait_id in
         let self_bare = self_name_of impl in
         (* M9.5l: standard-backend name shape for a non-generic impl.
            See [ExtractBase.ctx_compute_trait_impl_name_raw] for the
            full machinery (which handles renames, blanket impls,
            non-ADT self types). The minimal-case formula is:
            [<SelfBare>.Insts.<CrateCap><TraitBare>] where
            [CrateCap] is the trait's crate segment with its first
            letter capitalised. *)
         let trait_crate_seg = crate_segment_of (
           match LlbcAst.TraitDeclId.Map.find_opt trait_id crate.trait_decls with
           | Some td -> td.item_meta.name
           | None -> [])
         in
         let pretty_name =
           Printf.sprintf "%s.Insts.%s%s" self_bare
             (capitalize_first_letter trait_crate_seg)
             trait_bare
         in
         (* Pair each impl-method entry with the trait method's name
            via the shared TraitMethodId key. *)
         let methods : CertEvent.cert_trait_impl_method list =
           match
             LlbcAst.TraitDeclId.Map.find_opt trait_id crate.trait_decls
           with
           | Some td ->
               List.map2
                 (fun (_, (b : Types.fun_decl_ref Types.binder))
                      (_, (tb : trait_method Types.binder)) ->
                   { CertEvent.ctim_name = tb.binder_value.name;
                     ctim_fn_id = Types.FunDeclId.to_int b.binder_value.id })
                 (Types.TraitMethodId.Map.bindings impl.methods)
                 (Types.TraitMethodId.Map.bindings td.methods)
           | None -> []
         in
         {
           ctri_id = LlbcAst.TraitImplId.to_int impl.def_id;
           ctri_pretty_name = pretty_name;
           ctri_qualified_name = Print.name_to_string env impl.item_meta.name;
           ctri_trait_decl_id = LlbcAst.TraitDeclId.to_int trait_id;
           ctri_self_type_decl_id = self_type_decl_id_of impl;
           ctri_methods = methods;
           ctri_source_span = source_span_of_item_meta impl.item_meta;
         })

(** [M9.5l] Build a [fun_decl_id → pretty_name] table from the trait
    impls. For each impl method, the pretty name is
    [<impl_pretty_name>.<method_name>] — e.g.
    [Tag.Insts.Traits_basicNumeric.value]. Used by [collect_for_fun]
    to set [fc_pretty_name] for impl-method functions. *)
let build_fn_pretty_name_table (impls : CertEvent.cert_trait_impl list)
    : (int, string) Hashtbl.t =
  let h = Hashtbl.create 16 in
  List.iter
    (fun (i : CertEvent.cert_trait_impl) ->
      List.iter
        (fun (m : CertEvent.cert_trait_impl_method) ->
          Hashtbl.replace h m.ctim_fn_id (i.ctri_pretty_name ^ "." ^ m.ctim_name))
        i.ctri_methods)
    impls;
  h

(** Run the interpreter on every function in the crate, capturing per-function
    event traces. *)
let generate_crate_cert (crate : crate) (marked_ids : marked_ids)
    (crate_hash : string) : CertEvent.crate_cert =
  let trans_ctx = compute_contexts crate in
  let trait_decls = collect_trait_decls crate in
  let trait_impls = collect_trait_impls crate in
  let pretty_table = build_fn_pretty_name_table trait_impls in
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
  let type_decls = collect_type_decls crate in
  {
    cc_fmt_version = CertEvent.cert_fmt_version;
    cc_crate_hash = crate_hash;
    cc_type_decls = type_decls;
    cc_trait_decls = trait_decls;
    cc_trait_impls = trait_impls;
    cc_functions = fun_certs;
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

(** Round-trip the post-prepass crate to JSON next to the cert.

    For M3 we emit a minimal envelope that records the crate name and the
    list of fun-decl ids covered by the cert. M4+ will replace this with a
    full crate dump when the Lean Raw parser needs more than that. *)
let write_llbc_json (input_path : string) (crate : crate) : string =
  let out_path =
    let base = Filename.remove_extension input_path in
    base ^ ".llbc.json"
  in
  let oc = open_out out_path in
  let payload : Yojson.Basic.t =
    `Assoc
      [
        "fmt_version", `Int CertEvent.cert_fmt_version;
        "crate_name", `String crate.name;
        ( "fun_decl_ids",
          `List
            (List.map
               (fun (d : fun_decl) -> `Int (FunDeclId.to_int d.def_id))
               (FunDeclId.Map.values crate.fun_decls)) );
      ]
  in
  Yojson.Basic.pretty_to_channel oc payload;
  output_char oc '\n';
  close_out oc;
  log#linfo (lazy ("Wrote llbc.json: " ^ out_path));
  out_path

(** Top-level entry point. *)
let emit (input_path : string) (crate : crate) (marked_ids : marked_ids) : unit =
  let llbc_path =
    if !Config.emit_llbc_json then Some (write_llbc_json input_path crate)
    else None
  in
  if !Config.emit_cert then begin
    let crate_hash =
      match llbc_path with
      | Some p -> CertJson.sha256_file p
      | None -> CertJson.sha256_file input_path
    in
    let cc = generate_crate_cert crate marked_ids crate_hash in
    let _ = write_cert input_path cc in
    ()
  end

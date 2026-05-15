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
           | _ -> CTDOpaque
         in
         {
           ctd_id = Types.TypeDeclId.to_int td.def_id;
           ctd_name = bare_name;
           ctd_kind = kind;
         })

(** Run the interpreter on every function in the crate, capturing per-function
    event traces. *)
let generate_crate_cert (crate : crate) (marked_ids : marked_ids)
    (crate_hash : string) : CertEvent.crate_cert =
  let trans_ctx = compute_contexts crate in
  let fun_certs : CertEvent.fun_cert list =
    List.filter_map (collect_for_fun trans_ctx marked_ids)
      (FunDeclId.Map.values crate.fun_decls)
  in
  let type_decls = collect_type_decls crate in
  {
    cc_fmt_version = CertEvent.cert_fmt_version;
    cc_crate_hash = crate_hash;
    cc_type_decls = type_decls;
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

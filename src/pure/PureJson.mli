(** JSON serializer for the Pure IR.

    One-way OCaml -> JSON. The Rust crate [rust/pure-ir/] is the sole
    consumer. See {!documentation/pure-ir-json-export-plan.md} for the
    round-trip decision.

    As of Phase 2 the emitter covers every constructor of [Pure.ty],
    [Pure.literal] / [Pure.literal_type], [Pure.qualif], [Pure.pat] /
    [Pure.tpat], [Pure.binop], and [Pure.expr]; plus the full decl
    envelope ([fun_sig], [fun_body], [fun_decl], [type_decl],
    [global_decl], [trait_decl], [trait_impl]). The 89 fixture files
    under [tests/llbc/*.llbc] all parse on the [post-s2p] stage with no
    [UNSUPPORTED] markers.

    Some opaque-or-redundant fields are intentionally dropped from the
    emit because no Rust consumer needs them:
    - [item_meta], [span], [llbc_generics] — Charon source/position meta
      kept around in OCaml only for pretty-name derivation.
    - [builtin_info] payloads — summarised by a single tag.
    - [emeta] payloads — meta-info for OCaml-side pretty-naming.
    - [mplace] — meta-place information.

    Encoding convention: every tagged sum serializes as
    [{"kind": "VariantName", "payload": <data>}]. Records become JSON
    objects whose field names match the OCaml field names verbatim.
    Identifiers (anything from [IdGen]) serialize as JSON ints via
    [<Module>.to_int]. *)

val literal_to_json : Pure.literal -> Yojson.Basic.t
val literal_type_to_json : Pure.literal_type -> Yojson.Basic.t
val ty_to_json : Pure.ty -> Yojson.Basic.t
val expr_to_json : Pure.expr -> Yojson.Basic.t
val texpr_to_json : Pure.texpr -> Yojson.Basic.t
val fun_decl_to_json : Pure.fun_decl -> Yojson.Basic.t
val type_decl_to_json : Pure.type_decl -> Yojson.Basic.t
val global_decl_to_json : Pure.global_decl -> Yojson.Basic.t
val trait_decl_to_json : Pure.trait_decl -> Yojson.Basic.t
val trait_impl_to_json : Pure.trait_impl -> Yojson.Basic.t

val crate_to_json :
  crate_name:string ->
  stage:string ->
  type_decls:Pure.type_decl list ->
  fun_decls:Pure.fun_decl list ->
  global_decls:Pure.global_decl list ->
  trait_decls:Pure.trait_decl list ->
  trait_impls:Pure.trait_impl list ->
  Yojson.Basic.t

val pure_ir_fmt_version : int

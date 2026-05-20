(** JSON serializer for the Pure IR.

    One-way OCaml -> JSON. The Rust crate [rust/pure-ir/] is the sole
    consumer. See {!documentation/pure-ir-json-export-plan.md} for the
    round-trip decision.

    The emitter covers every constructor of [Pure.ty],
    [Pure.literal] / [Pure.literal_type], [Pure.qualif], [Pure.pat] /
    [Pure.tpat], [Pure.binop], and [Pure.expr]; plus the full decl
    envelope ([fun_sig], [fun_body], [fun_decl], [type_decl],
    [global_decl], [trait_decl], [trait_impl]). The 89 fixture files
    under [tests/llbc/*.llbc] all parse on the [post-s2p] stage with no
    [UNSUPPORTED] markers.

    [pure_ir_fmt_version = 2] (was 1 in earlier Phase-2 commits): we
    now carry source spans + Charon attribute info end-to-end, with no
    flag — the dump grows ~2-3x relative to v1 but no consumer is
    forced to inspect the new fields:
    - [item_meta] rides on every decl ([fun_decl], [type_decl],
      [global_decl], [trait_decl], [trait_impl]), carrying [name],
      [span], [source_text], [attr_info] (attributes, inline, rename,
      public), [is_local], [opacity], and [lang_item].
    - [loop.span] is emitted alongside the rest of the loop payload.
    - The [Meta of emeta * texpr] expression node ships the full
      [emeta] payload — including the [mplace] structures embedded in
      [Assignment], [SymbolicAssignments], [SymbolicPlaces], and
      [MPlace]. [mplace] itself is a recursive sum encoded as a tagged
      union ([PlaceLocal] / [PlaceGlobal] / [PlaceProjection]).
    - [EError]'s optional [Meta.span] is no longer stripped.

    The span shape mirrors [CertJson.json_cert_source_span] verbatim:
    [{"file", "beg_line", "beg_col", "end_line", "end_col"}]. Future
    consumers can share a parser. Charon [name] (a [path_elem list]) is
    emitted as a structured JSON array — the heavy [PeImpl] and
    [PeInstantiated] variants opaque-encode (just the tag) so the
    schema stays bounded; [PeIdent] and [PeTarget] carry their full
    payloads.

    Still summarised by tag only (no consumer needs the internals):
    - [llbc_generics] — original Charon generics, kept in OCaml only
      for pretty-name derivation.
    - [builtin_info] payloads on decls.
    - [item_source] variants — the constructor tag suffices.

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

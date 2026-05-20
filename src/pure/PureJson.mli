(** JSON serializer for the Pure IR (Phase 1).

    One-way OCaml -> JSON. The Rust crate [rust/pure-ir/] is the sole
    consumer. See {!documentation/pure-ir-json-export-plan.md} for the
    round-trip decision.

    Phase 1 covers a minimal subset:
    - {!Pure.literal} — all variants
    - {!Pure.literal_type} — all variants
    - {!Pure.ty} — only [TLiteral] and [TArrow]; others emit
      [{"kind": "UNSUPPORTED", "payload": "<VariantName>"}]
    - {!Pure.expr} — only [FVar] / [BVar] / [Const] / [App]; others use
      the same UNSUPPORTED stub
    - {!Pure.fun_decl} — minimal envelope (def_id, name, signature, body)
    - type/global/trait decls — stub form
      [{"name": "...", "_unsupported": true}]

    Encoding convention (Phase 1): every tagged sum (literal / ty / expr)
    serializes as [{"kind": "VariantName", "payload": <data>}]. This makes
    the Rust side a drop-in [#[serde(tag = "kind", content = "payload")]]
    enum. Unsupported variants share the kind ["UNSUPPORTED"] with a
    string payload naming the missing constructor. *)

val literal_to_json : Pure.literal -> Yojson.Basic.t
val literal_type_to_json : Pure.literal_type -> Yojson.Basic.t
val ty_to_json : Pure.ty -> Yojson.Basic.t
val expr_to_json : Pure.expr -> Yojson.Basic.t
val texpr_to_json : Pure.texpr -> Yojson.Basic.t
val fun_decl_to_json : Pure.fun_decl -> Yojson.Basic.t

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

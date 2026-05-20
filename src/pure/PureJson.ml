(** Phase 1 JSON emitter for the Pure IR — see {!PureJson.mli}. *)

open Pure

let pure_ir_fmt_version = 1

(* ---------- Tagged-enum helper ---------- *)

(** Emit a tagged variant as [{"kind": tag, "payload": data}]. Nullary
    variants pass [`Null] for [data]; the Rust side will be a struct
    enum where serde fills in the absent fields. *)
let tagged (tag : string) (payload : Yojson.Basic.t) : Yojson.Basic.t =
  `Assoc [ ("kind", `String tag); ("payload", payload) ]

(** Stub for variants we have not implemented yet in Phase 1. *)
let unsupported (variant_name : string) : Yojson.Basic.t =
  tagged "UNSUPPORTED" (`String variant_name)

(* ---------- Identifiers ---------- *)

let json_id (to_int : 'a -> int) (id : 'a) : Yojson.Basic.t = `Int (to_int id)

let json_fvar_id : fvar_id -> Yojson.Basic.t = json_id FVarId.to_int
let json_bvar_id : bvar_id -> Yojson.Basic.t = json_id BVarId.to_int
let json_fun_decl_id : fun_decl_id -> Yojson.Basic.t =
  json_id FunDeclId.to_int

let json_bvar (b : bvar) : Yojson.Basic.t =
  `Assoc [ ("scope", `Int b.scope); ("id", json_bvar_id b.id) ]

(* ---------- Literal types & literals ---------- *)

let json_int_ty (t : int_ty) : Yojson.Basic.t =
  `String
    (match t with
    | Isize -> "Isize"
    | I8 -> "I8"
    | I16 -> "I16"
    | I32 -> "I32"
    | I64 -> "I64"
    | I128 -> "I128")

let json_u_int_ty (t : u_int_ty) : Yojson.Basic.t =
  `String
    (match t with
    | Usize -> "Usize"
    | U8 -> "U8"
    | U16 -> "U16"
    | U32 -> "U32"
    | U64 -> "U64"
    | U128 -> "U128")

let json_float_ty (t : float_type) : Yojson.Basic.t =
  `String
    (match t with
    | F16 -> "F16"
    | F32 -> "F32"
    | F64 -> "F64"
    | F128 -> "F128")

let literal_type_to_json (t : literal_type) : Yojson.Basic.t =
  match t with
  | TInt ty -> tagged "TInt" (json_int_ty ty)
  | TUInt ty -> tagged "TUInt" (json_u_int_ty ty)
  | TFloat ty -> tagged "TFloat" (json_float_ty ty)
  | TBool -> tagged "TBool" `Null
  | TChar -> tagged "TChar" `Null
  | TPureNat -> tagged "TPureNat" `Null
  | TPureInt -> tagged "TPureInt" `Null

let json_scalar_value (sv : scalar_value) : Yojson.Basic.t =
  match sv with
  | Values.UnsignedScalar (t, n) ->
      `Assoc
        [
          ("signed", `Bool false);
          ("ty", json_u_int_ty t);
          ("value", `String (Z.to_string n));
        ]
  | Values.SignedScalar (t, n) ->
      `Assoc
        [
          ("signed", `Bool true);
          ("ty", json_int_ty t);
          ("value", `String (Z.to_string n));
        ]

let literal_to_json (lit : literal) : Yojson.Basic.t =
  match lit with
  | VScalar sv -> tagged "VScalar" (json_scalar_value sv)
  | VFloat { float_value; float_ty } ->
      tagged "VFloat"
        (`Assoc
          [
            ("value", `String float_value);
            ("ty", json_float_ty float_ty);
          ])
  | VBool b -> tagged "VBool" (`Bool b)
  | VChar c -> tagged "VChar" (`Int (Uchar.to_int c))
  | VByteStr bs -> tagged "VByteStr" (`List (List.map (fun i -> `Int i) bs))
  | VStr s -> tagged "VStr" (`String s)
  | VPureNat n -> tagged "VPureNat" (`String (Z.to_string n))
  | VPureInt n -> tagged "VPureInt" (`String (Z.to_string n))

(* ---------- Types ---------- *)

let rec ty_to_json (ty : ty) : Yojson.Basic.t =
  match ty with
  | TLiteral lt -> tagged "TLiteral" (literal_type_to_json lt)
  | TArrow (input, output) ->
      tagged "TArrow"
        (`Assoc [ ("input", ty_to_json input); ("output", ty_to_json output) ])
  | TAdt _ -> unsupported "TAdt"
  | TVar _ -> unsupported "TVar"
  | TTraitType _ -> unsupported "TTraitType"
  | TNever -> unsupported "TNever"
  | TDynTrait _ -> unsupported "TDynTrait"
  | TError -> unsupported "TError"

(* ---------- Expressions ---------- *)

let rec expr_to_json (e : expr) : Yojson.Basic.t =
  match e with
  | FVar id -> tagged "FVar" (json_fvar_id id)
  | BVar b -> tagged "BVar" (json_bvar b)
  | Const lit -> tagged "Const" (literal_to_json lit)
  | App (f, a) ->
      tagged "App"
        (`Assoc [ ("fun", texpr_to_json f); ("arg", texpr_to_json a) ])
  | CVar _ -> unsupported "CVar"
  | Lambda _ -> unsupported "Lambda"
  | Qualif _ -> unsupported "Qualif"
  | Let _ -> unsupported "Let"
  | Switch _ -> unsupported "Switch"
  | Loop _ -> unsupported "Loop"
  | StructUpdate _ -> unsupported "StructUpdate"
  | Meta _ -> unsupported "Meta"
  | EError _ -> unsupported "EError"

and texpr_to_json (te : texpr) : Yojson.Basic.t =
  `Assoc [ ("e", expr_to_json te.e); ("ty", ty_to_json te.ty) ]

(* ---------- Function signatures & bodies ----------
   Phase 1: we expose just enough of the signature to drive the Rust
   smoke test. The signature input/output types use [ty_to_json] (so
   non-literal types become UNSUPPORTED stubs). Bodies' input patterns
   are not yet encoded — we emit the input count instead. *)

let fun_sig_to_json (sg : fun_sig) : Yojson.Basic.t =
  `Assoc
    [
      ("inputs", `List (List.map ty_to_json sg.inputs));
      ("output", ty_to_json sg.output);
    ]

let fun_body_to_json (fb : fun_body) : Yojson.Basic.t =
  `Assoc
    [
      (* [tpat] is not yet covered; we surface the arity for now. *)
      ("num_inputs", `Int (List.length fb.inputs));
      ("body", texpr_to_json fb.body);
    ]

let fun_decl_to_json (fd : fun_decl) : Yojson.Basic.t =
  let body_json : Yojson.Basic.t =
    match fd.body with
    | None -> `Null
    | Some b -> fun_body_to_json b
  in
  `Assoc
    [
      ("def_id", json_fun_decl_id fd.def_id);
      ("name", `String fd.name);
      ("signature", fun_sig_to_json fd.signature);
      ("is_global_decl_body", `Bool fd.is_global_decl_body);
      ("num_loops", `Int fd.num_loops);
      ("body", body_json);
    ]

(* ---------- Other decls (stubbed) ---------- *)

let type_decl_stub (td : type_decl) : Yojson.Basic.t =
  `Assoc
    [
      ("def_id", json_id Pure.TypeDeclId.to_int td.def_id);
      ("_unsupported", `Bool true);
    ]

let global_decl_stub (gd : global_decl) : Yojson.Basic.t =
  `Assoc
    [
      ("def_id", json_id Pure.GlobalDeclId.to_int gd.def_id);
      ("name", `String gd.name);
      ("_unsupported", `Bool true);
    ]

let trait_decl_stub (td : trait_decl) : Yojson.Basic.t =
  `Assoc [ ("name", `String td.name); ("_unsupported", `Bool true) ]

let trait_impl_stub (ti : trait_impl) : Yojson.Basic.t =
  `Assoc [ ("name", `String ti.name); ("_unsupported", `Bool true) ]

(* ---------- Crate envelope ---------- *)

let crate_to_json ~(crate_name : string) ~(stage : string)
    ~(type_decls : type_decl list) ~(fun_decls : fun_decl list)
    ~(global_decls : global_decl list) ~(trait_decls : trait_decl list)
    ~(trait_impls : trait_impl list) : Yojson.Basic.t =
  `Assoc
    [
      ("pure_ir_fmt_version", `Int pure_ir_fmt_version);
      ("stage", `String stage);
      ("crate_name", `String crate_name);
      ("type_decls", `List (List.map type_decl_stub type_decls));
      ("fun_decls", `List (List.map fun_decl_to_json fun_decls));
      ("global_decls", `List (List.map global_decl_stub global_decls));
      ("trait_decls", `List (List.map trait_decl_stub trait_decls));
      ("trait_impls", `List (List.map trait_impl_stub trait_impls));
    ]

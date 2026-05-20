(** JSON emitter for the Pure IR — see {!PureJson.mli}.

    Encoding convention (kept consistent across Phase 1, Phase 2 and the
    Phase 2 + spans/attrs bump to v2): every tagged sum serializes as
    [{"kind": "Variant", "payload": <data>}]. Records serialize as JSON
    objects whose field names match the OCaml field names verbatim
    (snake_case). Lists become JSON arrays. Identifiers (anything from
    [IdGen]) serialize as JSON ints via [<Module>.to_int]. Starting at
    [pure_ir_fmt_version = 2], source spans and attribute info ride
    along on every decl, loop, and meta-expression — see the .mli
    docstring for the surface. *)

open Pure

let pure_ir_fmt_version = 2

(* ---------- Tagged-enum helper ---------- *)

(** Emit a tagged variant as [{"kind": tag, "payload": data}]. Nullary
    variants pass [`Null] for [data]. *)
let tagged (tag : string) (payload : Yojson.Basic.t) : Yojson.Basic.t =
  `Assoc [ ("kind", `String tag); ("payload", payload) ]

(* ---------- Identifiers ---------- *)

let json_id (to_int : 'a -> int) (id : 'a) : Yojson.Basic.t = `Int (to_int id)

let json_fvar_id : fvar_id -> Yojson.Basic.t = json_id FVarId.to_int
let json_bvar_id : bvar_id -> Yojson.Basic.t = json_id BVarId.to_int
let json_fun_decl_id : fun_decl_id -> Yojson.Basic.t =
  json_id FunDeclId.to_int
let json_type_decl_id : type_decl_id -> Yojson.Basic.t =
  json_id Pure.TypeDeclId.to_int
let json_global_decl_id : global_decl_id -> Yojson.Basic.t =
  json_id Pure.GlobalDeclId.to_int
let json_trait_decl_id : trait_decl_id -> Yojson.Basic.t =
  json_id Pure.TraitDeclId.to_int
let json_trait_impl_id : trait_impl_id -> Yojson.Basic.t =
  json_id Pure.TraitImplId.to_int
let json_trait_clause_id : trait_clause_id -> Yojson.Basic.t =
  json_id Pure.TraitClauseId.to_int
let json_trait_method_id : trait_method_id -> Yojson.Basic.t =
  json_id Pure.TraitMethodId.to_int
let json_assoc_type_id : assoc_type_id -> Yojson.Basic.t =
  json_id Types.AssocTypeId.to_int
let json_assoc_const_id : assoc_const_id -> Yojson.Basic.t =
  json_id Types.AssocConstId.to_int
let json_type_var_id : type_var_id -> Yojson.Basic.t =
  json_id Pure.TypeVarId.to_int
let json_const_generic_var_id : const_generic_var_id -> Yojson.Basic.t =
  json_id Types.ConstGenericVarId.to_int
let json_variant_id : variant_id -> Yojson.Basic.t =
  json_id Pure.VariantId.to_int
let json_field_id : field_id -> Yojson.Basic.t =
  json_id Pure.FieldId.to_int
let json_loop_id : loop_id -> Yojson.Basic.t = json_id Pure.LoopId.to_int

let json_bvar (b : bvar) : Yojson.Basic.t =
  `Assoc [ ("scope", `Int b.scope); ("id", json_bvar_id b.id) ]

let json_de_bruijn_var (f : 'a -> Yojson.Basic.t) (v : 'a de_bruijn_var) :
    Yojson.Basic.t =
  match v with
  | Bound (db_id, x) ->
      tagged "Bound" (`Assoc [ ("db", `Int db_id); ("value", f x) ])
  | Free x -> tagged "Free" (f x)

let json_option (f : 'a -> Yojson.Basic.t) (o : 'a option) : Yojson.Basic.t =
  match o with None -> `Null | Some x -> f x

(* ---------- Atomic types ---------- *)

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

let json_integer_type (t : integer_type) : Yojson.Basic.t =
  match t with
  | Values.Signed s -> tagged "Signed" (json_int_ty s)
  | Values.Unsigned u -> tagged "Unsigned" (json_u_int_ty u)

let json_overflow_mode (m : overflow_mode) : Yojson.Basic.t =
  `String
    (match m with
    | Expressions.OPanic -> "OPanic"
    | Expressions.OUB -> "OUB"
    | Expressions.OWrap -> "OWrap")

let json_mutability (m : mutability) : Yojson.Basic.t =
  `String (match m with Mut -> "Mut" | Const -> "Const")

let json_array_or_slice (x : array_or_slice) : Yojson.Basic.t =
  `String (match x with Array -> "Array" | Slice -> "Slice")

(* ---------- Source spans + Charon item meta ----------

   We carry full Charon source spans + attribute info on every decl,
   loop, and meta-expression starting at [pure_ir_fmt_version = 2].
   The span shape mirrors [CertJson.json_cert_source_span] verbatim
   (same field names) so any future consumer can share a parser. *)

(** Extract the filename string out of a Charon [file_name] sum. *)
let file_name_to_string (fn : Meta.file_name) : string =
  match fn with
  | Virtual s | Local s | NotReal s -> s

(** Emit a Charon [span] as [{file, beg_line, beg_col, end_line, end_col}].
    Matches [CertJson.json_cert_source_span] exactly. *)
let json_span (sp : Meta.span) : Yojson.Basic.t =
  let d = sp.data in
  `Assoc
    [
      ("file", `String (file_name_to_string d.file.name));
      ("beg_line", `Int d.beg_loc.line);
      ("beg_col", `Int d.beg_loc.col);
      ("end_line", `Int d.end_loc.line);
      ("end_col", `Int d.end_loc.col);
    ]

let json_inline_attr (a : Meta.inline_attr) : Yojson.Basic.t =
  `String
    (match a with
    | Hint -> "Hint"
    | Never -> "Never"
    | Always -> "Always")

let json_raw_attribute (r : Meta.raw_attribute) : Yojson.Basic.t =
  `Assoc
    [
      ("path", `String r.path);
      ("args", json_option (fun s -> `String s) r.args);
    ]

let json_attribute (a : Meta.attribute) : Yojson.Basic.t =
  match a with
  | AttrOpaque -> tagged "AttrOpaque" `Null
  | AttrExclude -> tagged "AttrExclude" `Null
  | AttrRename s -> tagged "AttrRename" (`String s)
  | AttrVariantsPrefix s -> tagged "AttrVariantsPrefix" (`String s)
  | AttrVariantsSuffix s -> tagged "AttrVariantsSuffix" (`String s)
  | AttrDocComment s -> tagged "AttrDocComment" (`String s)
  | AttrUnknown r -> tagged "AttrUnknown" (json_raw_attribute r)

let json_attr_info (ai : Meta.attr_info) : Yojson.Basic.t =
  `Assoc
    [
      ("attributes", `List (List.map json_attribute ai.attributes));
      ("inline", json_option json_inline_attr ai.inline);
      ("rename", json_option (fun s -> `String s) ai.rename);
      ("public", `Bool ai.public);
    ]

(** [disambiguator] is an [IdGen] id; expose as an int. *)
let json_disambiguator (d : Pure.Disambiguator.id) : Yojson.Basic.t =
  `Int (Pure.Disambiguator.to_int d)

(** Charon [path_elem] — opaque-encode the heavy [PeImpl] / [PeInstantiated]
    variants that carry nested binders / impl-elem payloads. Consumers
    can recover the human-readable form by joining [PeIdent] strings; the
    impl/instantiated markers stay as opaque tags so the schema doesn't
    blow up. *)
let json_path_elem (pe : Types.path_elem) : Yojson.Basic.t =
  match pe with
  | PeIdent (s, d) ->
      tagged "PeIdent"
        (`Assoc [ ("name", `String s); ("disambiguator", json_disambiguator d) ])
  | PeImpl _ -> tagged "PeImpl" `Null
  | PeInstantiated _ -> tagged "PeInstantiated" `Null
  | PeTarget s -> tagged "PeTarget" (`String s)

let json_charon_name (n : Types.name) : Yojson.Basic.t =
  `List (List.map json_path_elem n)

let json_item_opacity (o : Types.item_opacity) : Yojson.Basic.t =
  `String
    (match o with
    | Transparent -> "Transparent"
    | Foreign -> "Foreign"
    | ItemOpaque -> "ItemOpaque"
    | Invisible -> "Invisible")

let json_item_meta (im : Types.item_meta) : Yojson.Basic.t =
  `Assoc
    [
      ("name", json_charon_name im.name);
      ("span", json_span im.span);
      ("source_text", json_option (fun s -> `String s) im.source_text);
      ("attr_info", json_attr_info im.attr_info);
      ("is_local", `Bool im.is_local);
      ("opacity", json_item_opacity im.opacity);
      ("lang_item", json_option (fun s -> `String s) im.lang_item);
    ]

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

let json_builtin_ty (b : builtin_ty) : Yojson.Basic.t =
  match b with
  | TResult -> tagged "TResult" `Null
  | TSum -> tagged "TSum" `Null
  | TLoopResult -> tagged "TLoopResult" `Null
  | TError -> tagged "TError" `Null
  | TFuel -> tagged "TFuel" `Null
  | TArray -> tagged "TArray" `Null
  | TSlice -> tagged "TSlice" `Null
  | TStr -> tagged "TStr" `Null
  | TRawPtr m -> tagged "TRawPtr" (json_mutability m)

(* ---------- Types ---------- *)

let rec ty_to_json (ty : ty) : Yojson.Basic.t =
  match ty with
  | TLiteral lt -> tagged "TLiteral" (literal_type_to_json lt)
  | TArrow (input, output) ->
      tagged "TArrow"
        (`Assoc [ ("input", ty_to_json input); ("output", ty_to_json output) ])
  | TAdt (tid, gargs) ->
      tagged "TAdt"
        (`Assoc
          [ ("type_id", json_type_id tid); ("generics", json_generic_args gargs) ])
  | TVar dv ->
      tagged "TVar" (json_de_bruijn_var json_type_var_id dv)
  | TTraitType (tref, aid) ->
      tagged "TTraitType"
        (`Assoc
          [
            ("trait_ref", json_trait_ref tref);
            ("assoc_type_id", json_assoc_type_id aid);
          ])
  | TNever -> tagged "TNever" `Null
  | TDynTrait dp -> tagged "TDynTrait" (json_dyn_predicate dp)
  | TError -> tagged "TError" `Null

and json_type_id (tid : type_id) : Yojson.Basic.t =
  match tid with
  | TAdtId id -> tagged "TAdtId" (json_type_decl_id id)
  | TTuple -> tagged "TTuple" `Null
  | TBuiltin b -> tagged "TBuiltin" (json_builtin_ty b)

and json_generic_args (g : generic_args) : Yojson.Basic.t =
  `Assoc
    [
      ("types", `List (List.map ty_to_json g.types));
      ( "const_generics",
        `List (List.map json_const_generic g.const_generics) );
      ("trait_refs", `List (List.map json_trait_ref g.trait_refs));
    ]

and json_const_generic (cg : const_generic) : Yojson.Basic.t =
  match cg with
  | CgGlobal gid -> tagged "CgGlobal" (json_global_decl_id gid)
  | CgVar dv ->
      tagged "CgVar" (json_de_bruijn_var json_const_generic_var_id dv)
  | CgValue lit -> tagged "CgValue" (literal_to_json lit)

and json_trait_ref (tr : trait_ref) : Yojson.Basic.t =
  `Assoc
    [
      ("trait_id", json_trait_instance_id tr.trait_id);
      ("trait_decl_ref", json_trait_decl_ref tr.trait_decl_ref);
    ]

and json_trait_decl_ref (r : trait_decl_ref) : Yojson.Basic.t =
  `Assoc
    [
      ("trait_decl_id", json_trait_decl_id r.trait_decl_id);
      ("decl_generics", json_generic_args r.decl_generics);
    ]

and json_fun_decl_ref (r : fun_decl_ref) : Yojson.Basic.t =
  `Assoc
    [
      ("fun_id", json_fun_decl_id r.fun_id);
      ("fun_generics", json_generic_args r.fun_generics);
    ]

and json_global_decl_ref (r : global_decl_ref) : Yojson.Basic.t =
  `Assoc
    [
      ("global_id", json_global_decl_id r.global_id);
      ("global_generics", json_generic_args r.global_generics);
    ]

and json_trait_instance_id (id : trait_instance_id) : Yojson.Basic.t =
  match id with
  | Self -> tagged "Self" `Null
  | TraitImpl (impl_id, gargs) ->
      tagged "TraitImpl"
        (`Assoc
          [
            ("impl_id", json_trait_impl_id impl_id);
            ("generics", json_generic_args gargs);
          ])
  | Clause dv ->
      tagged "Clause" (json_de_bruijn_var json_trait_clause_id dv)
  | ParentClause (parent, decl_id, clause_id) ->
      tagged "ParentClause"
        (`Assoc
          [
            ("parent", json_trait_instance_id parent);
            ("trait_decl_id", json_trait_decl_id decl_id);
            ("clause_id", json_trait_clause_id clause_id);
          ])
  | BuiltinOrAuto bi -> tagged "BuiltinOrAuto" (json_builtin_impl_data bi)
  | UnknownTrait s -> tagged "UnknownTrait" (`String s)

and json_builtin_impl_data (b : builtin_impl_data) : Yojson.Basic.t =
  `String
    (match b with
    | BuiltinCopy -> "BuiltinCopy"
    | BuiltinClone -> "BuiltinClone"
    | BuiltinDiscriminantKind -> "BuiltinDiscriminantKind"
    | BuiltinFn -> "BuiltinFn"
    | BuiltinFnMut -> "BuiltinFnMut"
    | BuiltinFnOnce -> "BuiltinFnOnce")

and json_dyn_predicate (dp : dyn_predicate) : Yojson.Basic.t =
  `Assoc [ ("params", json_generic_params dp.params) ]

and json_generic_params (gp : generic_params) : Yojson.Basic.t =
  `Assoc
    [
      ("types", `List (List.map json_type_param gp.types));
      ( "const_generics",
        `List (List.map json_const_generic_param gp.const_generics) );
      ("trait_clauses", `List (List.map json_trait_param gp.trait_clauses));
    ]

and json_type_param (tp : type_param) : Yojson.Basic.t =
  `Assoc [ ("index", json_type_var_id tp.index); ("name", `String tp.name) ]

and json_const_generic_param (cgp : const_generic_param) : Yojson.Basic.t =
  `Assoc
    [
      ("index", json_const_generic_var_id cgp.index);
      ("name", `String cgp.name);
      ("ty", literal_type_to_json cgp.ty);
    ]

and json_trait_param (tp : trait_param) : Yojson.Basic.t =
  `Assoc
    [
      ("clause_id", json_trait_clause_id tp.clause_id);
      ("trait_id", json_trait_decl_id tp.trait_id);
      ("generics", json_generic_args tp.generics);
    ]

let json_trait_type_constraint (c : trait_type_constraint) : Yojson.Basic.t =
  `Assoc
    [
      ("trait_ref", json_trait_ref c.trait_ref);
      ("type_id", json_assoc_type_id c.type_id);
      ("ty", ty_to_json c.ty);
    ]

let json_predicates (p : predicates) : Yojson.Basic.t =
  `Assoc
    [
      ( "trait_type_constraints",
        `List (List.map json_trait_type_constraint p.trait_type_constraints)
      );
    ]

(* ---------- Operators ---------- *)

let json_binop (b : binop) : Yojson.Basic.t =
  let ity t = ("ty", json_integer_type t) in
  let om m = ("overflow_mode", json_overflow_mode m) in
  match b with
  | BitXor t -> tagged "BitXor" (`Assoc [ ity t ])
  | BitAnd t -> tagged "BitAnd" (`Assoc [ ity t ])
  | BitOr t -> tagged "BitOr" (`Assoc [ ity t ])
  | Eq ty -> tagged "Eq" (`Assoc [ ("ty", ty_to_json ty) ])
  | Ne ty -> tagged "Ne" (`Assoc [ ("ty", ty_to_json ty) ])
  | Lt t -> tagged "Lt" (`Assoc [ ity t ])
  | Le t -> tagged "Le" (`Assoc [ ity t ])
  | Ge t -> tagged "Ge" (`Assoc [ ity t ])
  | Gt t -> tagged "Gt" (`Assoc [ ity t ])
  | Add (m, t) -> tagged "Add" (`Assoc [ om m; ity t ])
  | Sub (m, t) -> tagged "Sub" (`Assoc [ om m; ity t ])
  | Mul (m, t) -> tagged "Mul" (`Assoc [ om m; ity t ])
  | Div (m, t) -> tagged "Div" (`Assoc [ om m; ity t ])
  | Rem (m, t) -> tagged "Rem" (`Assoc [ om m; ity t ])
  | AddChecked t -> tagged "AddChecked" (`Assoc [ ity t ])
  | SubChecked t -> tagged "SubChecked" (`Assoc [ ity t ])
  | MulChecked t -> tagged "MulChecked" (`Assoc [ ity t ])
  | Shl (m, t1, t2) ->
      tagged "Shl"
        (`Assoc
          [
            om m;
            ("lhs_ty", json_integer_type t1);
            ("rhs_ty", json_integer_type t2);
          ])
  | Shr (m, t1, t2) ->
      tagged "Shr"
        (`Assoc
          [
            om m;
            ("lhs_ty", json_integer_type t1);
            ("rhs_ty", json_integer_type t2);
          ])
  | Cmp t -> tagged "Cmp" (`Assoc [ ity t ])
  | BoolOr -> tagged "BoolOr" `Null

let json_cast_kind (ck : cast_kind) : Yojson.Basic.t =
  match ck with
  | CastLit (a, b) ->
      tagged "CastLit"
        (`Assoc
          [ ("src", literal_type_to_json a); ("dst", literal_type_to_json b) ])
  | CastRawPtr ((a, ma), (b, mb)) ->
      tagged "CastRawPtr"
        (`Assoc
          [
            ( "src",
              `Assoc
                [
                  ("ty", literal_type_to_json a);
                  ("mutability", json_mutability ma);
                ] );
            ( "dst",
              `Assoc
                [
                  ("ty", literal_type_to_json b);
                  ("mutability", json_mutability mb);
                ] );
          ])

let json_unop (u : unop) : Yojson.Basic.t =
  match u with
  | Not o -> tagged "Not" (json_option json_integer_type o)
  | Neg t -> tagged "Neg" (json_integer_type t)
  | Cast ck -> tagged "Cast" (json_cast_kind ck)
  | ArrayToSlice -> tagged "ArrayToSlice" `Null

(* ---------- Qualifiers ---------- *)

let json_pure_builtin_fun_id (id : pure_builtin_fun_id) : Yojson.Basic.t =
  match id with
  | Return -> tagged "Return" `Null
  | Fail -> tagged "Fail" `Null
  | Assert -> tagged "Assert" `Null
  | Loop arity -> tagged "Loop" (`Int arity)
  | RecLoopCall arity -> tagged "RecLoopCall" (`Int arity)
  | FuelDecrease -> tagged "FuelDecrease" `Null
  | FuelEqZero -> tagged "FuelEqZero" `Null
  | UpdateAtIndex aos -> tagged "UpdateAtIndex" (json_array_or_slice aos)
  | ToResult -> tagged "ToResult" `Null
  | Discriminant -> tagged "Discriminant" `Null
  | ResultUnwrapMut -> tagged "ResultUnwrapMut" `Null
  | GetTarget -> tagged "GetTarget" `Null

(** Charon's [LlbcAst.fun_id] (alias of [Types.fun_id]) — either a regular
    Charon decl-id or a builtin. We summarise the builtin variant as a
    string for now; the Rust side does not need its internal structure
    yet. *)
let json_llbc_fun_id (id : llbc_fun_id) : Yojson.Basic.t =
  match id with
  | Types.FRegular fid ->
      tagged "FRegular" (json_fun_decl_id fid)
  | Types.FBuiltin _ ->
      (* The exact [builtin_fun_id] payload is large and downstream
         consumers don't need its structure; stringify the constructor. *)
      tagged "FBuiltin" `Null

let json_fn_ptr_kind (k : fn_ptr_kind) : Yojson.Basic.t =
  match k with
  | FunId id -> tagged "FunId" (json_llbc_fun_id id)
  | TraitMethod (tref, mid, fid) ->
      tagged "TraitMethod"
        (`Assoc
          [
            ("trait_ref", json_trait_ref tref);
            ("method_id", json_trait_method_id mid);
            ("fun_decl_id", json_fun_decl_id fid);
          ])

let json_regular_fun_id ((k, lo) : regular_fun_id) : Yojson.Basic.t =
  `Assoc
    [
      ("kind", json_fn_ptr_kind k);
      ( "loop",
        json_option
          (fun (lid, is_body) ->
            `Assoc
              [
                ("loop_id", json_loop_id lid); ("is_body", `Bool is_body);
              ])
          lo );
    ]

let json_fun_id (id : fun_id) : Yojson.Basic.t =
  match id with
  | FromLlbc rid -> tagged "FromLlbc" (json_regular_fun_id rid)
  | Pure pid -> tagged "Pure" (json_pure_builtin_fun_id pid)

let json_fun_or_op_id (id : fun_or_op_id) : Yojson.Basic.t =
  match id with
  | Fun fid -> tagged "Fun" (json_fun_id fid)
  | Unop u -> tagged "Unop" (json_unop u)
  | Binop b -> tagged "Binop" (json_binop b)

let json_adt_cons_id (a : adt_cons_id) : Yojson.Basic.t =
  `Assoc
    [
      ("adt_id", json_type_id a.adt_id);
      ("variant_id", json_option json_variant_id a.variant_id);
    ]

let json_projection (p : projection) : Yojson.Basic.t =
  `Assoc
    [
      ("adt_id", json_type_id p.adt_id);
      ("field_id", json_field_id p.field_id);
    ]

let json_qualif_id (q : qualif_id) : Yojson.Basic.t =
  match q with
  | FunOrOp x -> tagged "FunOrOp" (json_fun_or_op_id x)
  | Global gid -> tagged "Global" (json_global_decl_id gid)
  | AdtCons c -> tagged "AdtCons" (json_adt_cons_id c)
  | Proj p -> tagged "Proj" (json_projection p)
  | ScalarValProj t -> tagged "ScalarValProj" (json_integer_type t)
  | TraitConst (tr, cid) ->
      tagged "TraitConst"
        (`Assoc
          [
            ("trait_ref", json_trait_ref tr);
            ("assoc_const_id", json_assoc_const_id cid);
          ])
  | MkDynTrait tr -> tagged "MkDynTrait" (json_trait_ref tr)
  | LoopOp -> tagged "LoopOp" `Null

let json_qualif (q : qualif) : Yojson.Basic.t =
  `Assoc
    [
      ("id", json_qualif_id q.id);
      ("generics", json_generic_args q.generics);
    ]

(* ---------- Patterns ---------- *)

let json_var (v : var) : Yojson.Basic.t =
  `Assoc
    [
      ("basename", json_option (fun s -> `String s) v.basename);
      ("ty", ty_to_json v.ty);
    ]

let json_fvar (v : fvar) : Yojson.Basic.t =
  `Assoc
    [
      ("id", json_fvar_id v.id);
      ("basename", json_option (fun s -> `String s) v.basename);
      ("ty", ty_to_json v.ty);
    ]

let json_local_id (id : Expressions.local_id) : Yojson.Basic.t =
  `Int (Expressions.LocalId.to_int id)

let json_field_proj_kind (k : Expressions.field_proj_kind) : Yojson.Basic.t =
  match k with
  | ProjAdt (tdid, vid) ->
      tagged "ProjAdt"
        (`Assoc
          [
            ("type_decl_id", json_type_decl_id tdid);
            ("variant_id", json_option json_variant_id vid);
          ])
  | ProjTuple arity -> tagged "ProjTuple" (`Int arity)

let json_mprojection_elem (m : mprojection_elem) : Yojson.Basic.t =
  `Assoc
    [
      ("pkind", json_field_proj_kind m.pkind);
      ("field_id", json_field_id m.field_id);
    ]

(** Meta-places encode source-level provenance. Starting at
    [pure_ir_fmt_version = 2] we ship the structural payload. *)
let rec json_mplace (p : mplace) : Yojson.Basic.t =
  match p with
  | PlaceLocal (lid, name) ->
      tagged "PlaceLocal"
        (`Assoc
          [
            ("local_id", json_local_id lid);
            ("name", json_option (fun s -> `String s) name);
          ])
  | PlaceGlobal gref -> tagged "PlaceGlobal" (json_global_decl_ref gref)
  | PlaceProjection (parent, elem) ->
      tagged "PlaceProjection"
        (`Assoc
          [
            ("parent", json_mplace parent);
            ("elem", json_mprojection_elem elem);
          ])

let rec json_pat (p : pat) : Yojson.Basic.t =
  match p with
  | PConstant lit -> tagged "PConstant" (literal_to_json lit)
  | PBound (v, mp) ->
      tagged "PBound"
        (`Assoc
          [ ("var", json_var v); ("mplace", json_option json_mplace mp) ])
  | PIgnored -> tagged "PIgnored" `Null
  | POpen (v, mp) ->
      tagged "POpen"
        (`Assoc
          [ ("fvar", json_fvar v); ("mplace", json_option json_mplace mp) ])
  | PAdt ap -> tagged "PAdt" (json_adt_pat ap)

and json_adt_pat (a : adt_pat) : Yojson.Basic.t =
  `Assoc
    [
      ("variant_id", json_option json_variant_id a.variant_id);
      ("fields", `List (List.map json_tpat a.fields));
    ]

and json_tpat (tp : tpat) : Yojson.Basic.t =
  `Assoc [ ("pat", json_pat tp.pat); ("ty", ty_to_json tp.ty) ]

(* ---------- Expressions ---------- *)

let rec expr_to_json (e : expr) : Yojson.Basic.t =
  match e with
  | FVar id -> tagged "FVar" (json_fvar_id id)
  | BVar b -> tagged "BVar" (json_bvar b)
  | CVar id -> tagged "CVar" (json_const_generic_var_id id)
  | Const lit -> tagged "Const" (literal_to_json lit)
  | App (f, a) ->
      tagged "App"
        (`Assoc [ ("fun", texpr_to_json f); ("arg", texpr_to_json a) ])
  | Lambda (pat, body) ->
      tagged "Lambda"
        (`Assoc [ ("pat", json_tpat pat); ("body", texpr_to_json body) ])
  | Qualif q -> tagged "Qualif" (json_qualif q)
  | Let (monadic, pat, bound, body) ->
      tagged "Let"
        (`Assoc
          [
            ("monadic", `Bool monadic);
            ("pat", json_tpat pat);
            ("bound", texpr_to_json bound);
            ("body", texpr_to_json body);
          ])
  | Switch (scrut, body) ->
      tagged "Switch"
        (`Assoc
          [ ("scrutinee", texpr_to_json scrut); ("body", json_switch_body body) ])
  | Loop l -> tagged "Loop" (json_loop l)
  | StructUpdate su -> tagged "StructUpdate" (json_struct_update su)
  | Meta (m, e) ->
      tagged "Meta"
        (`Assoc [ ("meta", json_emeta m); ("expr", texpr_to_json e) ])
  | EError (span, s) ->
      tagged "EError"
        (`Assoc
          [ ("span", json_option json_span span); ("message", `String s) ])

and texpr_to_json (te : texpr) : Yojson.Basic.t =
  `Assoc [ ("e", expr_to_json te.e); ("ty", ty_to_json te.ty) ]

and json_switch_body (sb : switch_body) : Yojson.Basic.t =
  match sb with
  | If (t, e) ->
      tagged "If"
        (`Assoc
          [ ("then_branch", texpr_to_json t); ("else_branch", texpr_to_json e) ])
  | Match brs -> tagged "Match" (`List (List.map json_match_branch brs))

and json_match_branch (m : match_branch) : Yojson.Basic.t =
  `Assoc [ ("pat", json_tpat m.pat); ("branch", texpr_to_json m.branch) ]

and json_loop (l : loop) : Yojson.Basic.t =
  `Assoc
    [
      ("loop_id", json_loop_id l.loop_id);
      ("span", json_span l.span);
      ("output_tys", `List (List.map ty_to_json l.output_tys));
      ("num_output_values", `Int l.num_output_values);
      ("inputs", `List (List.map texpr_to_json l.inputs));
      ("num_input_conts", `Int l.num_input_conts);
      ("loop_body", json_loop_body l.loop_body);
      ("to_rec", `Bool l.to_rec);
    ]

and json_loop_body (lb : loop_body) : Yojson.Basic.t =
  `Assoc
    [
      ("inputs", `List (List.map json_tpat lb.inputs));
      ("loop_body", texpr_to_json lb.loop_body);
    ]

and json_struct_update (su : struct_update) : Yojson.Basic.t =
  `Assoc
    [
      ("struct_id", json_type_id su.struct_id);
      ("init", json_option texpr_to_json su.init);
      ( "updates",
        `List
          (List.map
             (fun (fid, te) ->
               `Assoc
                 [ ("field_id", json_field_id fid); ("expr", texpr_to_json te) ])
             su.updates) );
    ]

(** Meta-expressions carry pretty-naming hints and source-place info.
    Starting at [pure_ir_fmt_version = 2] we ship the full payload —
    including the [mplace] structures the variants embed. *)
and json_emeta (m : emeta) : Yojson.Basic.t =
  match m with
  | Assignment (dst, value, origin) ->
      tagged "Assignment"
        (`Assoc
          [
            ("dst", json_mplace dst);
            ("value", texpr_to_json value);
            ("origin", json_option json_mplace origin);
          ])
  | SymbolicAssignments pairs ->
      tagged "SymbolicAssignments"
        (`List
          (List.map
             (fun (mv, value) ->
               `Assoc
                 [
                   ("mvar", texpr_to_json mv);
                   ("value", texpr_to_json value);
                 ])
             pairs))
  | SymbolicPlaces pairs ->
      tagged "SymbolicPlaces"
        (`List
          (List.map
             (fun (mv, name) ->
               `Assoc
                 [
                   ("mvar", texpr_to_json mv); ("name", `String name);
                 ])
             pairs))
  | MPlace p -> tagged "MPlace" (json_mplace p)
  | Tag s -> tagged "Tag" (`String s)
  | TypeAnnot -> tagged "TypeAnnot" `Null

(* ---------- Signatures & bodies ---------- *)

let json_explicit (e : explicit) : Yojson.Basic.t =
  `String (match e with Explicit -> "Explicit" | Implicit -> "Implicit")

let json_known (k : known) : Yojson.Basic.t =
  `String (match k with Known -> "Known" | Unknown -> "Unknown")

let json_explicit_info (ei : explicit_info) : Yojson.Basic.t =
  `Assoc
    [
      ("explicit_types", `List (List.map json_explicit ei.explicit_types));
      ( "explicit_const_generics",
        `List (List.map json_explicit ei.explicit_const_generics) );
    ]

let json_known_info (ki : known_info) : Yojson.Basic.t =
  `Assoc
    [
      ("known_types", `List (List.map json_known ki.known_types));
      ( "known_const_generics",
        `List (List.map json_known ki.known_const_generics) );
    ]

let json_fun_effect_info (fi : fun_effect_info) : Yojson.Basic.t =
  `Assoc
    [
      ("can_fail", `Bool fi.can_fail);
      ("can_diverge", `Bool fi.can_diverge);
      ("is_rec", `Bool fi.is_rec);
    ]

let json_fun_sig_info (fi : fun_sig_info) : Yojson.Basic.t =
  `Assoc
    [
      ("effect_info", json_fun_effect_info fi.effect_info);
      ("ignore_output", `Bool fi.ignore_output);
    ]

(** [back_effect_info] is a [RegionGroupId.Map.t]. We flatten it to a
    list of [(region_group_id, effect_info)] pairs so the Rust side can
    deserialize without modelling Aeneas's map module. *)
let json_back_effect_info (m : fun_effect_info Pure.RegionGroupId.Map.t) :
    Yojson.Basic.t =
  `List
    (Pure.RegionGroupId.Map.bindings m
    |> List.map (fun (rgid, ei) ->
           `Assoc
             [
               ("region_group_id", `Int (Pure.RegionGroupId.to_int rgid));
               ("effect_info", json_fun_effect_info ei);
             ]))

let fun_sig_to_json (sg : fun_sig) : Yojson.Basic.t =
  `Assoc
    [
      ("generics", json_generic_params sg.generics);
      ("explicit_info", json_explicit_info sg.explicit_info);
      ("known_from_trait_refs", json_known_info sg.known_from_trait_refs);
      (* [llbc_generics] is an opaque Charon record carried purely for
         pretty-name derivation. The Rust consumer does not need it. *)
      ("preds", json_predicates sg.preds);
      ("inputs", `List (List.map ty_to_json sg.inputs));
      ("output", ty_to_json sg.output);
      ("fwd_info", json_fun_sig_info sg.fwd_info);
      ("back_effect_info", json_back_effect_info sg.back_effect_info);
    ]

let fun_body_to_json (fb : fun_body) : Yojson.Basic.t =
  `Assoc
    [
      ("inputs", `List (List.map json_tpat fb.inputs));
      ("body", texpr_to_json fb.body);
    ]

let json_backend_attributes (ba : backend_attributes) : Yojson.Basic.t =
  `Assoc [ ("reducible", `Bool ba.reducible) ]

(** [item_source] is a Charon enum with deep payloads (trait refs etc.).
    Downstream consumers don't need it; we surface the constructor tag. *)
let json_item_source (s : Pure.item_source) : Yojson.Basic.t =
  match s with
  | Types.TopLevelItem -> tagged "TopLevelItem" `Null
  | Types.ClosureItem _ -> tagged "ClosureItem" `Null
  | Types.TraitDeclItem _ -> tagged "TraitDeclItem" `Null
  | Types.TraitImplItem _ -> tagged "TraitImplItem" `Null
  | _ -> tagged "OtherItemSource" `Null

let fun_decl_to_json (fd : fun_decl) : Yojson.Basic.t =
  `Assoc
    [
      ("def_id", json_fun_decl_id fd.def_id);
      ("item_meta", json_item_meta fd.item_meta);
      ( "builtin_info",
        json_option
          (fun _ -> tagged "BuiltinFunInfo" `Null)
          fd.builtin_info );
      ("src", json_item_source fd.src);
      ("backend_attributes", json_backend_attributes fd.backend_attributes);
      ("num_loops", `Int fd.num_loops);
      ( "loop_id",
        json_option
          (fun (lid, is_body) ->
            `Assoc
              [
                ("loop_id", json_loop_id lid); ("is_body", `Bool is_body);
              ])
          fd.loop_id );
      ("loop_pos", `List (List.map (fun i -> `Int i) fd.loop_pos));
      ("name", `String fd.name);
      ("signature", fun_sig_to_json fd.signature);
      ("is_global_decl_body", `Bool fd.is_global_decl_body);
      ("body", json_option fun_body_to_json fd.body);
    ]

(* ---------- Type / global / trait decls ---------- *)

let json_field (f : field) : Yojson.Basic.t =
  `Assoc
    [
      ("field_name", json_option (fun s -> `String s) f.field_name);
      ("field_ty", ty_to_json f.field_ty);
    ]

let json_variant (v : variant) : Yojson.Basic.t =
  `Assoc
    [
      ("variant_name", `String v.variant_name);
      ("fields", `List (List.map json_field v.fields));
      ("discriminant", `Int v.discriminant);
      ("ty", literal_type_to_json v.ty);
    ]

let json_type_decl_kind (k : type_decl_kind) : Yojson.Basic.t =
  match k with
  | Struct fields -> tagged "Struct" (`List (List.map json_field fields))
  | Enum variants -> tagged "Enum" (`List (List.map json_variant variants))
  | Opaque -> tagged "Opaque" `Null

let type_decl_to_json (td : type_decl) : Yojson.Basic.t =
  `Assoc
    [
      ("def_id", json_type_decl_id td.def_id);
      ("name", `String td.name);
      ("item_meta", json_item_meta td.item_meta);
      ("generics", json_generic_params td.generics);
      ("explicit_info", json_explicit_info td.explicit_info);
      ("kind", json_type_decl_kind td.kind);
      ("preds", json_predicates td.preds);
    ]

let global_decl_to_json (gd : global_decl) : Yojson.Basic.t =
  `Assoc
    [
      ("def_id", json_global_decl_id gd.def_id);
      ("name", `String gd.name);
      ("span", json_span gd.span);
      ("item_meta", json_item_meta gd.item_meta);
      ("generics", json_generic_params gd.generics);
      ("explicit_info", json_explicit_info gd.explicit_info);
      ("preds", json_predicates gd.preds);
      ("ty", ty_to_json gd.ty);
      ("output_ty", ty_to_json gd.output_ty);
      ("can_fail", `Bool gd.can_fail);
      ("src", json_item_source gd.src);
      ("body_id", json_fun_decl_id gd.body_id);
    ]

(** Encode a [Pure.binder]. Most consumers only care about
    [binder_value] + [binder_generics]; we ship [binder_preds] and
    [binder_explicit_info] for completeness and drop [binder_llbc_generics]. *)
let json_binder (f : 'a -> Yojson.Basic.t) (b : 'a Pure.binder) :
    Yojson.Basic.t =
  `Assoc
    [
      ("binder_value", f b.binder_value);
      ("binder_generics", json_generic_params b.binder_generics);
      ("binder_preds", json_predicates b.binder_preds);
      ( "binder_explicit_info",
        json_explicit_info b.binder_explicit_info );
    ]

let trait_decl_to_json (td : trait_decl) : Yojson.Basic.t =
  `Assoc
    [
      ("def_id", json_trait_decl_id td.def_id);
      ("name", `String td.name);
      ("item_meta", json_item_meta td.item_meta);
      ("generics", json_generic_params td.generics);
      ("explicit_info", json_explicit_info td.explicit_info);
      ("preds", json_predicates td.preds);
      ("parent_clauses", `List (List.map json_trait_param td.parent_clauses));
      ( "consts",
        `List
          (List.map
             (fun (cid, name, ty) ->
               `Assoc
                 [
                   ("assoc_const_id", json_assoc_const_id cid);
                   ("name", `String name);
                   ("ty", ty_to_json ty);
                 ])
             td.consts) );
      ( "types",
        `List
          (List.map
             (fun (tid, name) ->
               `Assoc
                 [
                   ("assoc_type_id", json_assoc_type_id tid);
                   ("name", `String name);
                 ])
             td.types) );
      ( "methods",
        `List
          (List.map
             (fun (mid, name, b) ->
               `Assoc
                 [
                   ("method_id", json_trait_method_id mid);
                   ("name", `String name);
                   ("binder", json_binder json_fun_decl_ref b);
                 ])
             td.methods) );
    ]

let trait_impl_to_json (ti : trait_impl) : Yojson.Basic.t =
  `Assoc
    [
      ("def_id", json_trait_impl_id ti.def_id);
      ("name", `String ti.name);
      ("item_meta", json_item_meta ti.item_meta);
      ("impl_trait", json_trait_decl_ref ti.impl_trait);
      ("generics", json_generic_params ti.generics);
      ("explicit_info", json_explicit_info ti.explicit_info);
      ("preds", json_predicates ti.preds);
      ( "parent_trait_refs",
        `List (List.map json_trait_ref ti.parent_trait_refs) );
      ( "consts",
        `List
          (List.map
             (fun (cid, name, gref) ->
               `Assoc
                 [
                   ("assoc_const_id", json_assoc_const_id cid);
                   ("name", `String name);
                   ("global_ref", json_global_decl_ref gref);
                 ])
             ti.consts) );
      ( "types",
        `List
          (List.map
             (fun (tid, name, ty) ->
               `Assoc
                 [
                   ("assoc_type_id", json_assoc_type_id tid);
                   ("name", `String name);
                   ("ty", ty_to_json ty);
                 ])
             ti.types) );
      ( "methods",
        `List
          (List.map
             (fun (mid, name, b) ->
               `Assoc
                 [
                   ("method_id", json_trait_method_id mid);
                   ("name", `String name);
                   ("binder", json_binder json_fun_decl_ref b);
                 ])
             ti.methods) );
    ]

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
      ("type_decls", `List (List.map type_decl_to_json type_decls));
      ("fun_decls", `List (List.map fun_decl_to_json fun_decls));
      ("global_decls", `List (List.map global_decl_to_json global_decls));
      ("trait_decls", `List (List.map trait_decl_to_json trait_decls));
      ("trait_impls", `List (List.map trait_impl_to_json trait_impls));
    ]

(** See {!LlbcJson} (.mli). *)

open Types
open Expressions
open Values
open LlbcAst

(* ---------- Yojson helpers ---------- *)

(** Tagged-variant constructor: payloads serialize as
    [{"<Tag>": payload}], nullary variants as the bare string. *)
let tagged (s : string) (payload : Yojson.Basic.t) : Yojson.Basic.t =
  `Assoc [ s, payload ]

let json_opt (f : 'a -> Yojson.Basic.t) : 'a option -> Yojson.Basic.t = function
  | None -> `Null
  | Some x -> f x

let json_string s : Yojson.Basic.t = `String s

(* ---------- Identifier wrappers ---------- *)

let j_type_decl_id id : Yojson.Basic.t = `Int (TypeDeclId.to_int id)
let j_fun_decl_id id : Yojson.Basic.t = `Int (FunDeclId.to_int id)
let j_trait_decl_id id : Yojson.Basic.t = `Int (TraitDeclId.to_int id)
let j_trait_impl_id id : Yojson.Basic.t = `Int (TraitImplId.to_int id)
let j_field_id id : Yojson.Basic.t = `Int (FieldId.to_int id)
let j_variant_id id : Yojson.Basic.t = `Int (VariantId.to_int id)
let j_local_id id : Yojson.Basic.t = `Int (LocalId.to_int id)

(* ---------- Literal types & literals ----------
   Mirror Charon's `Generated_Values.ml` serde shape; the Lean parser
   ([parseLitTy]/[parseLiteral]) only reads `Bool` / `Char` / `Int` /
   `UInt` / `Float` / `Scalar`. *)

let j_int_ty (t : int_ty) : Yojson.Basic.t =
  let s = match t with
    | Isize -> "Isize"
    | I8 -> "I8" | I16 -> "I16" | I32 -> "I32" | I64 -> "I64" | I128 -> "I128"
  in
  `String s

let j_uint_ty (t : u_int_ty) : Yojson.Basic.t =
  let s = match t with
    | Usize -> "Usize"
    | U8 -> "U8" | U16 -> "U16" | U32 -> "U32" | U64 -> "U64" | U128 -> "U128"
  in
  `String s

let j_float_ty (t : float_type) : Yojson.Basic.t =
  let s = match t with
    | F16 -> "F16" | F32 -> "F32" | F64 -> "F64" | F128 -> "F128"
  in `String s

let j_literal_type (t : literal_type) : Yojson.Basic.t =
  match t with
  | TBool -> `String "Bool"
  | TChar -> `String "Char"
  | TInt k -> tagged "Int" (j_int_ty k)
  | TUInt k -> tagged "UInt" (j_uint_ty k)
  | TFloat k -> tagged "Float" (j_float_ty k)

let j_scalar (sv : scalar_value) : Yojson.Basic.t =
  match sv with
  | UnsignedScalar (t, n) ->
      tagged "Unsigned"
        (`List [ j_uint_ty t; `String (Z.to_string n) ])
  | SignedScalar (t, n) ->
      tagged "Signed"
        (`List [ j_int_ty t; `String (Z.to_string n) ])

let j_literal (lit : literal) : Yojson.Basic.t =
  match lit with
  | VScalar sv -> tagged "Scalar" (j_scalar sv)
  | VFloat { float_value; float_ty } ->
      tagged "Float"
        (`Assoc
          [ "value", `String float_value; "ty", j_float_ty float_ty ])
  | VBool b -> tagged "Bool" (`Bool b)
  | VChar c -> tagged "Char" (`Int (Uchar.to_int c))
  | VByteStr bs -> tagged "ByteStr" (`List (List.map (fun i -> `Int i) bs))
  | VStr s -> tagged "Str" (`String s)

(* ---------- ref_kind ---------- *)

let j_ref_kind (k : ref_kind) : Yojson.Basic.t =
  match k with
  | RMut -> `String "Mut"
  | RShared -> `String "Shared"

(* ---------- Types (LlbcTy) ----------
   Mirror Charon's `ty_kind` serde shape that the Lean
   [parseLlbcTy] consumes. *)

let rec j_ty (t : ty) : Yojson.Basic.t =
  (* `ty = ty_kind hash_consed`; on the OCaml side the hash-cons is
     transparent, so [t] is itself the `ty_kind`. *)
  j_ty_kind t

and j_ty_kind (k : ty_kind) : Yojson.Basic.t =
  match k with
  | TNever -> `String "Never"
  | TLiteral lt -> tagged "Literal" (j_literal_type lt)
  | TAdt tdr ->
      (* Charon shape: { id; generics }; id is `type_id`; the Lean
         parser pulls `generics.types` (and dispatches on `id`'s
         tag — Tuple / Adt / Builtin). *)
      let id_json : Yojson.Basic.t = match tdr.id with
        | TAdtId tid -> tagged "Adt" (j_type_decl_id tid)
        | TTuple -> `String "Tuple"
        | TBuiltin bty ->
            let name = match bty with
              | TBox -> "Box"
              | TStr -> "Str"
            in
            tagged "Builtin" (`String name)
      in
      let generics_json : Yojson.Basic.t =
        `Assoc
          [ "types", `List (List.map j_ty tdr.generics.types) ]
      in
      tagged "Adt" (`Assoc [ "id", id_json; "generics", generics_json ])
  | TVar dbv ->
      let n = match dbv with
        | Free i -> TypeVarId.to_int i
        | Bound (_, i) -> TypeVarId.to_int i
      in
      tagged "TypeVar" (tagged "Free" (`Int n))
  | TRef (_region, inner, k) ->
      (* `[region, ty, ref_kind]`; we don't structure regions, emit 0. *)
      tagged "Ref" (`List [ `Int 0; j_ty inner; j_ref_kind k ])
  | TRawPtr (inner, k) ->
      tagged "RawPtr" (`List [ j_ty inner; j_ref_kind k ])
  | TArray (elem, ce) ->
      (* M9.7m: emit the real const-generic length when it's a
         literal so the Lean parser's `Array` branch lifts to a
         structured `tArray elem n` (the parity test needs this so
         the structured-source translator emits `Array <elem> N#usize`
         where the flat-source translator emits the same).
         Non-literal lengths (CVar, CTraitConst, …) stay opaque. *)
      let kind_json = match ce.kind with
        | CLiteral lit -> tagged "Literal" (j_literal lit)
        | _ -> tagged "Opaque" (`String "len")
      in
      tagged "Array"
        (`List
          [ j_ty elem;
            `Assoc [ "kind", kind_json ] ])
  | TSlice inner -> tagged "Slice" (j_ty inner)
  | TFnPtr _ -> tagged "FnPtr" `Null
  | TFnDef _ -> tagged "FnDef" `Null
  | TDynTrait _ -> tagged "DynTrait" `Null
  | TPtrMetadata _ -> tagged "PtrMetadata" `Null
  | TTraitType _ -> tagged "TraitType" `Null
  | TError s -> tagged "Error" (`String s)

(* ---------- Places, projections ---------- *)

let j_projection_elem (pe : projection_elem) : Yojson.Basic.t =
  match pe with
  | Deref -> `String "Deref"
  | PtrMetadata -> `String "PtrMetadata"
  | Field (pk, fid) ->
      let pk_json = match pk with
        | ProjAdt (tid, vid) ->
            let vid_json = match vid with
              | None -> `Null
              | Some v -> j_variant_id v
            in
            tagged "Adt"
              (`List [ j_type_decl_id tid; vid_json ])
        | ProjTuple n -> tagged "Tuple" (`Int n)
      in
      tagged "Field" (`List [ pk_json; j_field_id fid ])
  | ProjIndex (_op, from_end) ->
      tagged "Index"
        (`Assoc
          [ "offset", `Assoc [ "kind", tagged "Opaque" `Null ];
            "from_end", `Bool from_end ])
  | Subslice (_from, _to_, from_end) ->
      tagged "Subslice"
        (`Assoc
          [ "from", `Assoc [ "kind", tagged "Opaque" `Null ];
            "to", `Assoc [ "kind", tagged "Opaque" `Null ];
            "from_end", `Bool from_end ])

(** Look up a global's qualified name from a [global_decl_ref].
    Falls back to a synthetic `global#<id>` token when the lookup
    fails (defensive — Charon shouldn't emit dangling refs). *)
let global_decl_ref_name (crate : crate) (gref : global_decl_ref) : string =
  match GlobalDeclId.Map.find_opt gref.id crate.global_decls with
  | Some def ->
      let env = Print.crate_to_fmt_env crate in
      Print.name_to_string env def.item_meta.name
  | None -> Printf.sprintf "global#%d" (GlobalDeclId.to_int gref.id)

(** Walk a Charon nested [place] into the Lean parser's flat shape
    [{local, projection, ty, global?}]. We collect projections
    right-to-left.

    [PlaceGlobal] is rendered as a [local: 0] sentinel with the
    qualified global name attached via an extra [global] field;
    Lean's [parseLlbcPlace] reads this back into
    [LlbcPlace.globalName : Option String]. Forward.lean uses it to
    pre-seed the var-map for global-initializer bodies (post-pre-pass
    LLBC encodes `&PlaceGlobal(g)` as a fresh local L bound to
    `RvRef(PlaceGlobal g)`; without preserving [g] here, the cert
    walker has no way to recover the source global, and emits typed
    placeholders for `static S3 = P3` and friends). *)
let j_place (crate : crate) (p : place) : Yojson.Basic.t =
  let global_name = ref None in
  (* Session 7 Item 2: surface the global's generic instantiation
     (types + const_generics) alongside the qualified name so the
     Lean Forward translator can emit a typed call like
     `let g ← constants.V.LEN T N` for `V::<N, T>::LEN`. *)
  let global_generics = ref None in
  let env = Print.crate_to_fmt_env crate in
  let rec walk (p : place) (acc : projection_elem list)
      : int * projection_elem list * ty =
    match p.kind with
    | PlaceLocal lid -> LocalId.to_int lid, acc, p.ty
    | PlaceProjection (sub, pe) -> walk sub (pe :: acc)
    | PlaceGlobal gref ->
        global_name := Some (global_decl_ref_name crate gref);
        let gs = gref.generics in
        let tys = List.map (Print.ty_to_string env) gs.types in
        let cgs =
          List.map (Print.constant_expr_to_string env) gs.const_generics
        in
        global_generics := Some (tys, cgs);
        0, acc, p.ty
  in
  let (local, proj, ty) = walk p [] in
  let base =
    [ "local", `Int local;
      "projection", `List (List.map j_projection_elem proj);
      "ty", j_ty ty ]
  in
  let fields = match !global_name with
    | None -> base
    | Some n ->
      let g_fields = [ "global", `String n ] in
      let gg_fields = match !global_generics with
        | Some (tys, cgs)
          when not (List.is_empty tys && List.is_empty cgs) ->
            [ "global_generics",
              `Assoc
                [ "types", `List (List.map (fun s -> `String s) tys);
                  "const_generics",
                  `List (List.map (fun s -> `String s) cgs) ] ]
        | _ -> []
      in
      base @ g_fields @ gg_fields
  in
  `Assoc fields

(* ---------- Operands ---------- *)

let j_operand (crate : crate) (op : operand) : Yojson.Basic.t =
  match op with
  | Copy p -> tagged "Copy" (j_place crate p)
  | Move p -> tagged "Move" (j_place crate p)
  | Constant ce ->
      (* Lean parser expects `{kind: {Literal: <literal>}, ty}` and
         falls back to `constOpaque "const:<tag>"` for non-literal
         constants. We emit `Literal` for VLiteral kinds and an
         opaque tag otherwise. *)
      let kind_json = match ce.kind with
        | CLiteral lit -> tagged "Literal" (j_literal lit)
        | _ -> tagged "Opaque" (`String "constant")
      in
      tagged "Const"
        (`Assoc [ "kind", kind_json; "ty", j_ty ce.ty ])

(* ---------- Rvalues ---------- *)

let j_binop (op : binop) : Yojson.Basic.t =
  `String (CertEvent.cert_binop_string op)

let j_unop (op : unop) : Yojson.Basic.t =
  let s = match op with
    | Not -> "Not"
    | Neg _ -> "Neg"
    | Cast _ -> "Cast"
  in `String s

let j_borrow_kind (k : borrow_kind) : Yojson.Basic.t =
  match k with
  | BShared -> `String "Shared"
  | BMut -> `String "Mut"
  | BTwoPhaseMut -> `String "TwoPhaseMut"
  | BShallow -> `String "Shallow"
  | BUniqueImmutable -> `String "UniqueImmutable"

let j_aggregate_kind (ak : aggregate_kind) : Yojson.Basic.t =
  match ak with
  | AggregatedAdt (tdr, vid, fid) ->
      let id_json : Yojson.Basic.t = match tdr.id with
        | TAdtId tid -> tagged "Adt" (j_type_decl_id tid)
        | TTuple -> `String "Tuple"
        | TBuiltin _ -> tagged "Builtin" `Null
      in
      let tdr_json : Yojson.Basic.t =
        `Assoc
          [ "id", id_json;
            "generics", `Assoc [ "types", `List (List.map j_ty tdr.generics.types) ] ]
      in
      let vid_json = json_opt j_variant_id vid in
      let fid_json = json_opt j_field_id fid in
      tagged "Adt" (`List [ tdr_json; vid_json; fid_json ])
  | AggregatedArray (ty, _ce) ->
      tagged "Array"
        (`List
          [ j_ty ty;
            `Assoc [ "kind", tagged "Opaque" (`String "len") ] ])
  | AggregatedRawPtr (ty, k) ->
      tagged "RawPtr" (`List [ j_ty ty; j_ref_kind k ])

let j_rvalue (crate : crate) (rv : rvalue) : Yojson.Basic.t =
  match rv with
  | Use op -> tagged "Use" (j_operand crate op)
  | RvRef (place, kind, _ptr_meta) ->
      tagged "Ref"
        (`Assoc
          [ "place", j_place crate place;
            "kind", j_borrow_kind kind;
            "ptr_metadata", `Null ])
  | RawPtr (place, kind, _ptr_meta) ->
      tagged "RawPtr"
        (`Assoc
          [ "place", j_place crate place;
            "kind", j_ref_kind kind;
            "ptr_metadata", `Null ])
  | BinaryOp (bop, l, r) ->
      tagged "BinaryOp"
        (`List [ j_binop bop; j_operand crate l; j_operand crate r ])
  | UnaryOp (uop, o) ->
      tagged "UnaryOp" (`List [ j_unop uop; j_operand crate o ])
  | NullaryOp _ -> tagged "Opaque" (`String "NullaryOp")
  | Discriminant p -> tagged "Discriminant" (j_place crate p)
  | Aggregate (ak, ops) ->
      tagged "Aggregate"
        (`List [ j_aggregate_kind ak; `List (List.map (j_operand crate) ops) ])
  | Len _ -> tagged "Opaque" (`String "Len")
  | Repeat (op, ty, _ce) ->
      tagged "Repeat"
        (`List
          [ j_operand crate op; j_ty ty;
            `Assoc [ "kind", tagged "Opaque" (`String "count") ] ])
  | ShallowInitBox _ -> tagged "Opaque" (`String "ShallowInitBox")

(* ---------- Spans (reuse the existing helper) ---------- *)

(** Lean's [parseSourceSpan] accepts the legacy
    [{file, beg_line, beg_col, end_line, end_col}] shape that
    [CertJson.json_cert_source_span] emits. We extract a
    [cert_source_span] from any Charon [span] and reuse it. *)
let j_span (sp : Meta.span) : Yojson.Basic.t =
  let data = sp.data in
  let file = match data.file.name with
    | Virtual s | Local s | NotReal s -> s
  in
  let cs : CertEvent.cert_source_span =
    { ss_file = file;
      ss_beg_line = data.beg_loc.line;
      ss_beg_col = data.beg_loc.col;
      ss_end_line = data.end_loc.line;
      ss_end_col = data.end_loc.col }
  in
  CertJson.json_cert_source_span cs

(* ---------- Function calls ---------- *)

(** Resolve a [trait_method_id] to its declared method name (a
    [trait_item_name = string]) by looking it up in the crate's
    associated-item-names table. Falls back to a `method<id>`
    stringification when the lookup fails (e.g. when the crate
    record is stale for a built-in trait). *)
let method_name_of (crate : crate) (trait_id : trait_decl_id)
    (mid : trait_method_id) : string =
  try Charon.GAstUtils.get_method_name crate trait_id mid
  with Not_found -> Printf.sprintf "method%d" (TraitMethodId.to_int mid)

(* The Lean parser reads a call payload as:
     {func: <{Regular|Dynamic}-tagged>, args: [...], dest: <place>}
   where the inner of `Regular` is the fn_ptr `{kind, generics}` and
   `Dynamic` wraps an operand. *)
let j_call (crate : crate) (c : call) : Yojson.Basic.t =
  let func_json = match c.func with
    | FnOpRegular fp ->
        let kind_json = match fp.kind with
          | FunId (FRegular fid) ->
              tagged "Fun" (tagged "Regular" (j_fun_decl_id fid))
          | FunId (FBuiltin _) ->
              tagged "Fun" (tagged "Builtin" `Null)
          | TraitMethod (tref, mid, _fid) ->
              let trait_id = tref.trait_decl_ref.binder_value.id in
              let mname = method_name_of crate trait_id mid in
              tagged "TraitMethod"
                (`List
                  [ `Assoc [ "id", j_trait_decl_id trait_id ];
                    `String mname ])
        in
        tagged "Regular"
          (`Assoc [ "kind", kind_json; "generics", `Null ])
    | FnOpDynamic op -> tagged "Dynamic" (j_operand crate op)
  in
  `Assoc
    [ "func", func_json;
      "args", `List (List.map (j_operand crate) c.args);
      "dest", j_place crate c.dest ]

(* ---------- Statements / blocks / switches ---------- *)

let rec j_block (crate : crate) (b : block) : Yojson.Basic.t =
  `Assoc
    [ "span", j_span b.span;
      "statements",
        `List (List.map (j_statement crate) b.statements) ]

and j_statement (crate : crate) (s : statement) : Yojson.Basic.t =
  `Assoc
    [ "span", j_span s.span;
      "kind", j_statement_kind crate s.kind ]

and j_statement_kind (crate : crate) (k : statement_kind) : Yojson.Basic.t =
  match k with
  | Assign (p, rv) -> tagged "Assign" (`List [ j_place crate p; j_rvalue crate rv ])
  | SetDiscriminant (p, vid) ->
      tagged "SetDiscriminant" (`List [ j_place crate p; j_variant_id vid ])
  | CopyNonOverlapping _ -> tagged "Opaque" (`String "CopyNonOverlapping")
  | StorageLive lid -> tagged "StorageLive" (j_local_id lid)
  | StorageDead lid -> tagged "StorageDead" (j_local_id lid)
  | PlaceMention _ -> tagged "Opaque" (`String "PlaceMention")
  | Drop (p, _tref, _dk) ->
      (* Lean reads `[place, fn_ptr, drop_kind]` but only uses the place. *)
      tagged "Drop" (`List [ j_place crate p; `Null; `Null ])
  | Assert (asrt, _ak) ->
      tagged "Assert"
        (`Assoc
          [ "assert",
            `Assoc
              [ "cond", j_operand crate asrt.cond;
                "expected", `Bool asrt.expected ];
            "on_failure", `Null ])
  | Call c -> tagged "Call" (j_call crate c)
  | Abort _ak -> `String "Nop"  (* tolerated as opaque on Lean side *)
  | Return -> `String "Return"
  | Break n -> tagged "Break" (`Int n)
  | Continue n -> tagged "Continue" (`Int n)
  | Nop -> `String "Nop"
  | Switch sw -> tagged "Switch" (j_switch crate sw)
  | Loop b -> tagged "Loop" (j_block crate b)
  | Error s -> tagged "Opaque" (`String ("Error:" ^ s))

and j_switch (crate : crate) (sw : switch) : Yojson.Basic.t =
  match sw with
  | If (op, t_blk, e_blk) ->
      tagged "If"
        (`List
          [ j_operand crate op; j_block crate t_blk; j_block crate e_blk ])
  | SwitchInt (op, lty, arms, dflt) ->
      let arms_json : Yojson.Basic.t =
        `List
          (List.map
             (fun (lits, blk) ->
               `List
                 [ `List (List.map j_literal lits);
                   j_block crate blk ])
             arms)
      in
      tagged "SwitchInt"
        (`List
          [ j_operand crate op; j_literal_type lty;
            arms_json; j_block crate dflt ])
  | Match (place, arms, dflt_opt) ->
      let arms_json : Yojson.Basic.t =
        `List
          (List.map
             (fun (vids, blk) ->
               `List
                 [ `List (List.map j_variant_id vids);
                   j_block crate blk ])
             arms)
      in
      let dflt_json = match dflt_opt with
        | None -> `Null
        | Some b -> j_block crate b
      in
      tagged "Match" (`List [ j_place crate place; arms_json; dflt_json ])

(* ---------- ItemMeta ---------- *)

(** Lean's [parseItemMeta] accepts:
    * [name] as a string (we pre-render via [Print.name_to_string]),
    * [span] as the legacy [SourceSpan] shape ([CertJson] emits),
    * [attr_info], [extra] as opaque,
    * [source_text], [lang_item] as optional strings.
*)
let j_item_meta (env : Print.fmt_env) (im : item_meta) : Yojson.Basic.t =
  let name = Print.name_to_string env im.name in
  (* Session 7 Item 1a: expose [public] so the Lean side can emit the
     `Visibility: public` docstring line, matching mainline's
     [extract_comment_with_span ~public]. *)
  let attr_info_json : Yojson.Basic.t =
    `Assoc [ "public", `Bool im.attr_info.public ]
  in
  `Assoc
    [ "name", `String name;
      "attr_info", attr_info_json;
      "source_text", json_opt json_string im.source_text;
      "lang_item", json_opt json_string im.lang_item;
      "span", j_span im.span;
      "extra", `Null ]

(* ---------- Generic params, signatures ---------- *)

let j_trait_param_for_gp (env : Print.fmt_env) (crate : crate)
    (clause : trait_param) : Yojson.Basic.t =
  let tdr = clause.trait.binder_value in
  let name = match TraitDeclId.Map.find_opt tdr.id crate.trait_decls with
    | Some td -> Print.name_to_string env td.item_meta.name
    | None -> "__UnknownTrait"
  in
  let type_param = match tdr.generics.types with
    | TVar (Free i) :: _ -> TypeVarId.to_int i
    | TVar (Bound (_, i)) :: _ -> TypeVarId.to_int i
    | _ -> 0
  in
  CertJson.json_trait_clause (name, type_param)

let j_generic_params (env : Print.fmt_env) (crate : crate)
    (gp : generic_params) : Yojson.Basic.t =
  (* Lean's [parseLlbcGenericParams] walks each entry and pulls a
     `name` string. We emit the indexed shape. *)
  let mk_name_entry (name : string) : Yojson.Basic.t =
    `Assoc [ "name", `String name ]
  in
  let regions_json =
    `List
      (List.map
        (fun (rp : region_param) ->
          let n = Option.value rp.name ~default:"" in
          mk_name_entry n)
        gp.regions)
  in
  let types_json =
    `List
      (List.map
        (fun (tp : type_param) -> mk_name_entry tp.name)
        gp.types)
  in
  let cg_json =
    `List
      (List.map
        (fun (cp : const_generic_param) ->
          mk_name_entry cp.name)
        gp.const_generics)
  in
  let tc_json =
    `List (List.map (j_trait_param_for_gp env crate) gp.trait_clauses)
  in
  `Assoc
    [ "regions", regions_json;
      "types", types_json;
      "const_generics", cg_json;
      "trait_clauses", tc_json ]

let j_fun_sig (env : Print.fmt_env) (crate : crate)
    (gp : generic_params) (sg : fun_sig) : Yojson.Basic.t =
  `Assoc
    [ "inputs", `List (List.map j_ty sg.inputs);
      "output", j_ty sg.output;
      "generics", j_generic_params env crate gp ]

(* ---------- Fields, variants, type-decl kind ---------- *)

let j_field (i : int) (f : field) : Yojson.Basic.t =
  `Assoc
    [ "idx", `Int i;
      "name", json_opt json_string f.field_name;
      "ty", j_ty f.field_ty;
      "attr_info", `Null ]

let j_variant (i : int) (v : variant) : Yojson.Basic.t =
  let fields = List.mapi j_field v.fields in
  `Assoc
    [ "id", `Int i;
      "name", `String v.variant_name;
      "fields", `List fields;
      "discriminant", j_literal v.discriminant;
      "attr_info", `Null ]

let j_type_decl_kind (k : type_decl_kind) : Yojson.Basic.t =
  match k with
  | Struct fields ->
      tagged "Struct" (`List (List.mapi j_field fields))
  | Enum variants ->
      tagged "Enum" (`List (List.mapi j_variant variants))
  | Union fields ->
      tagged "Union" (`List (List.mapi j_field fields))
  | Opaque -> `String "Opaque"
  | Alias ty -> tagged "Alias" (j_ty ty)
  | TDeclError s -> tagged "Opaque" (`String ("TDeclError:" ^ s))

(* ---------- TypeDecl, FunDecl, TraitDecl, TraitImpl ---------- *)

let j_type_decl (env : Print.fmt_env) (crate : crate)
    (td : type_decl) : Yojson.Basic.t =
  `Assoc
    [ "id", j_type_decl_id td.def_id;
      "item_meta", j_item_meta env td.item_meta;
      "generics", j_generic_params env crate td.generics;
      "kind", j_type_decl_kind td.kind;
      "is_tuple_struct",
        `Bool (TypesAnalysis.type_decl_is_tuple_struct td);
      "repr_options", `Null;
      "ptr_metadata", `Null;
      "src", `Null;
      "is_global_initializer", `Bool false ]

let j_fun_decl (env : Print.fmt_env) (crate : crate)
    (fd : fun_decl) : Yojson.Basic.t =
  (* Session 7 Item 1d: emit per-local source names alongside the
     existing types-only array so the Lean side can preserve the
     user's `x` / `y` instead of synthesising `x1` / `x2`. Index 0 is
     the return slot (typically unnamed); 1..arg_count are the
     params; the rest are locals introduced during MIR lowering. *)
  let body_json, locals_types_json, locals_names_json = match fd.body with
    | StructuredBody body ->
        (j_block crate body.body,
         `List (List.map (fun (l : local) -> j_ty l.local_ty)
                  body.locals.locals),
         `List (List.map (fun (l : local) ->
                  match l.name with
                  | Some s -> `String s
                  | None -> `Null)
                  body.locals.locals))
    | _ -> `Null, `List [], `List []
  in
  let is_global_init = match fd.is_global_initializer with
    | None -> `Bool false
    | Some _ -> `Bool true
  in
  `Assoc
    [ "id", j_fun_decl_id fd.def_id;
      "item_meta", j_item_meta env fd.item_meta;
      "signature", j_fun_sig env crate fd.generics fd.signature;
      "body", body_json;
      "locals_types", locals_types_json;
      "locals_names", locals_names_json;
      "is_global_initializer", is_global_init;
      "src", `Null ]

let j_trait_method_entry (env : Print.fmt_env) (crate : crate)
    (m : trait_method binder) : Yojson.Basic.t =
  let v = m.binder_value in
  let sg_json =
    (* Look up the fun_decl_ref's id to fetch the actual signature. *)
    match FunDeclId.Map.find_opt v.item.id crate.fun_decls with
    | Some fd ->
        j_fun_sig env crate fd.generics fd.signature
    | None ->
        `Assoc [ "inputs", `List []; "output", `Null;
                 "generics", j_generic_params env crate m.binder_params ]
  in
  let has_default = match FunDeclId.Map.find_opt v.item.id crate.fun_decls with
    | Some fd -> (match fd.body with
        | StructuredBody _ -> true
        | _ -> false)
    | None -> false
  in
  let default_fn_id =
    if has_default then j_fun_decl_id v.item.id else `Null
  in
  `Assoc
    [ "name", `String v.name;
      "signature", sg_json;
      "has_default", `Bool has_default;
      "default_fn_id", default_fn_id ]

let j_trait_decl (env : Print.fmt_env) (crate : crate)
    (td : trait_decl) : Yojson.Basic.t =
  `Assoc
    [ "id", j_trait_decl_id td.def_id;
      "item_meta", j_item_meta env td.item_meta;
      "generics", j_generic_params env crate td.generics;
      "methods",
        `List
          (List.map
             (fun (_id, b) -> j_trait_method_entry env crate b)
             (TraitMethodId.Map.bindings td.methods));
      "types", `List [];
      "consts", `List [];
      "implied_clauses", `List [];
      "vtable", `Null ]

let j_trait_impl_method (crate : crate) (trait_id : trait_decl_id)
    (mid : trait_method_id) (b : fun_decl_ref binder) : Yojson.Basic.t =
  let name = method_name_of crate trait_id mid in
  let fn_id = b.binder_value.id in
  `Assoc
    [ "name", `String name;
      "fn_id", j_fun_decl_id fn_id ]

let j_trait_impl (env : Print.fmt_env) (crate : crate)
    (impl : trait_impl) : Yojson.Basic.t =
  let trait_decl_id = impl.impl_trait.id in
  let self_type_decl_id : Yojson.Basic.t =
    match impl.impl_trait.generics.types with
    | TAdt { id = TAdtId tid; _ } :: _ -> j_type_decl_id tid
    | _ -> `Null
  in
  let self_type : Yojson.Basic.t =
    match impl.impl_trait.generics.types with
    | hd :: _ -> j_ty hd
    | _ -> `Null
  in
  `Assoc
    [ "id", j_trait_impl_id impl.def_id;
      "item_meta", j_item_meta env impl.item_meta;
      "trait_decl_id", j_trait_decl_id trait_decl_id;
      "impl_trait", `Null;
      "self_type_decl_id", self_type_decl_id;
      "self_type", self_type;
      "generics", j_generic_params env crate impl.generics;
      "methods",
        `List
          (List.map
             (fun (mid, b) ->
               j_trait_impl_method crate trait_decl_id mid b)
             (TraitMethodId.Map.bindings impl.methods));
      "consts", `List [];
      "types", `List [];
      "implied_trait_refs", `Null;
      "vtable", `Null ]

(* ---------- Top-level program ---------- *)

let crate_to_json (crate : crate) : Yojson.Basic.t =
  let env =
    Print.Contexts.decls_ctx_to_fmt_env (Interp.compute_contexts crate)
  in
  let type_decls =
    TypeDeclId.Map.values crate.type_decls
    |> List.map (j_type_decl env crate)
  in
  let fun_decls =
    FunDeclId.Map.values crate.fun_decls
    |> List.map (j_fun_decl env crate)
  in
  let trait_decls =
    TraitDeclId.Map.values crate.trait_decls
    |> List.map (j_trait_decl env crate)
  in
  let trait_impls =
    TraitImplId.Map.values crate.trait_impls
    |> List.map (j_trait_impl env crate)
  in
  `Assoc
    [ "type_decls", `List type_decls;
      "fun_decls", `List fun_decls;
      "trait_decls", `List trait_decls;
      "trait_impls", `List trait_impls;
      "global_decls", `Null;
      "charon_version", `String "";
      "extra", `Null ]

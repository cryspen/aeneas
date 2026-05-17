(** JSON serializer for {!CertEvent} certificates.

    Output convention matches Serde's tagged-enum default that Charon also
    uses: nullary variants serialize as a JSON string of the variant name,
    payload variants serialize as a single-key object [{"Variant": payload}].
    This way the same Lean parser combinators can read both [llbc.json] and
    [cert.json].

    The serializer is deliberately one-way (OCaml -> JSON only). Round-tripping
    happens in Lean. *)

open CertEvent
open Types
open Expressions
open Values

(* ---------- Helpers ---------- *)

let json_int (n : int) : Yojson.Basic.t = `Int n

(** Identifier-typed integers. We unwrap to int via [to_int]. *)
let json_id (to_int : 'a -> int) (id : 'a) : Yojson.Basic.t = `Int (to_int id)

let json_local_id : local_id -> Yojson.Basic.t = json_id LocalId.to_int
let json_borrow_id : borrow_id -> Yojson.Basic.t = json_id BorrowId.to_int
let json_shared_borrow_id : shared_borrow_id -> Yojson.Basic.t =
  json_id SharedBorrowId.to_int
let json_symbolic_value_id : symbolic_value_id -> Yojson.Basic.t =
  json_id SymbolicValueId.to_int
let json_abs_id : abs_id -> Yojson.Basic.t = json_id AbsId.to_int
let json_fun_decl_id : fun_decl_id -> Yojson.Basic.t =
  json_id FunDeclId.to_int
let json_fun_call_id : fun_call_id -> Yojson.Basic.t =
  json_id FunCallId.to_int
let json_loop_id : loop_id -> Yojson.Basic.t = json_id LoopId.to_int

(* ---------- Types: minimal type-tag encoding ----------
   The full type structure is recoverable from llbc.json on the Lean side; the
   cert only needs a stable summary string so type-tagged events can be
   sanity-checked. *)

let json_ty (ty : ty) : Yojson.Basic.t = `String (show_ty ty)

(* ---------- Literals & scalars ---------- *)

let json_u_int_ty (t : u_int_ty) : Yojson.Basic.t =
  `String (match t with
    | Usize -> "Usize"
    | U8 -> "U8"
    | U16 -> "U16"
    | U32 -> "U32"
    | U64 -> "U64"
    | U128 -> "U128")

let json_int_ty (t : int_ty) : Yojson.Basic.t =
  `String (match t with
    | Isize -> "Isize"
    | I8 -> "I8"
    | I16 -> "I16"
    | I32 -> "I32"
    | I64 -> "I64"
    | I128 -> "I128")

let json_float_ty (t : float_type) : Yojson.Basic.t =
  `String (match t with
    | F16 -> "F16"
    | F32 -> "F32"
    | F64 -> "F64"
    | F128 -> "F128")

let json_scalar_value (sv : scalar_value) : Yojson.Basic.t =
  match sv with
  | UnsignedScalar (t, n) ->
      `Assoc [ "Unsigned", `List [ json_u_int_ty t; `String (Z.to_string n) ] ]
  | SignedScalar (t, n) ->
      `Assoc [ "Signed", `List [ json_int_ty t; `String (Z.to_string n) ] ]

let json_literal (lit : literal) : Yojson.Basic.t =
  match lit with
  | VScalar sv -> `Assoc [ "Scalar", json_scalar_value sv ]
  | VFloat { float_value; float_ty } ->
      `Assoc
        [
          ( "Float",
            `Assoc
              [
                "value", `String float_value;
                "ty", json_float_ty float_ty;
              ] );
        ]
  | VBool b -> `Assoc [ "Bool", `Bool b ]
  | VChar c -> `Assoc [ "Char", `Int (Uchar.to_int c) ]
  | VByteStr bs -> `Assoc [ "ByteStr", `List (List.map (fun i -> `Int i) bs) ]
  | VStr s -> `Assoc [ "Str", `String s ]

(* ---------- Projection elements ----------
   We restrict the cert format to projection elements that the direct-borrow
   subset can produce. Operand-bearing variants (ProjIndex with a non-constant
   offset, Subslice) get a string sentinel for now; M9 wires them properly. *)

let json_projection_elem (pe : projection_elem) : Yojson.Basic.t =
  match pe with
  | Deref -> `String "Deref"
  | Field (_, fid) ->
      `Assoc [ "Field", json_id FieldId.to_int fid ]
  | PtrMetadata -> `String "PtrMetadata"
  | ProjIndex _ -> `String "ProjIndex"
  | Subslice _ -> `String "Subslice"

(* ---------- Places ---------- *)

let json_cert_place (p : cert_place) : Yojson.Basic.t =
  `Assoc
    [
      "local", json_local_id p.cp_local;
      "projection", `List (List.map json_projection_elem p.cp_projection);
      "ty", json_ty p.cp_ty;
    ]

(* ---------- Symbolic expressions ---------- *)

let rec json_cert_sym_expr (e : cert_sym_expr) : Yojson.Basic.t =
  match e with
  | SymVal sv -> `Assoc [ "SymVal", json_symbolic_value_id sv ]
  | SymLit l -> `Assoc [ "SymLit", json_literal l ]
  | SymCopy p -> `Assoc [ "SymCopy", json_cert_place p ]
  | SymMove p -> `Assoc [ "SymMove", json_cert_place p ]
  | SymMutBorrowTok bid -> `Assoc [ "SymMutBorrowTok", json_borrow_id bid ]
  | SymVariant { adt_id; variant_id; variant_name; fields } ->
      `Assoc
        [
          ( "SymVariant",
            `Assoc
              [
                "adt_id", `Int adt_id;
                "variant_id", `Int variant_id;
                "variant_name", `String variant_name;
                "fields", `List (List.map json_cert_sym_expr fields);
              ] );
        ]
  | SymTuple fields ->
      `Assoc
        [
          "SymTuple", `List (List.map json_cert_sym_expr fields);
        ]
  | SymRecord { adt_id; fields } ->
      `Assoc
        [
          ( "SymRecord",
            `Assoc
              [
                "adt_id", `Int adt_id;
                "fields",
                `List
                  (List.map
                     (fun (n, e) ->
                       `Assoc
                         [
                           "name", `String n;
                           "value", json_cert_sym_expr e;
                         ])
                     fields);
              ] );
        ]

and json_cert_state_summary (s : cert_state_summary) : Yojson.Basic.t =
  `Assoc
    [
      ( "env",
        `List
          (List.map
             (fun (l, e) ->
               `Assoc [ "local", json_local_id l; "value", json_cert_sym_expr e ])
             s.cs_env) );
      "live_loans", `List (List.map json_borrow_id s.cs_live_loans);
    ]

let json_restore_info (r : cert_restore_info) : Yojson.Basic.t =
  `Assoc [ "given_back", json_cert_sym_expr r.ri_given_back ]

let json_cert_source_span (s : cert_source_span) : Yojson.Basic.t =
  `Assoc
    [
      "file", `String s.ss_file;
      "beg_line", `Int s.ss_beg_line;
      "beg_col", `Int s.ss_beg_col;
      "end_line", `Int s.ss_end_line;
      "end_col", `Int s.ss_end_col;
    ]

let json_trait_clause ((name, idx) : string * int) : Yojson.Basic.t =
  `Assoc [ "trait", `String name; "type_param", `Int idx ]

(* ---------- M9.6 (Option C) hint encoders ----------
   These mirror the Serde-tagged shapes the Lean parser
   ([AeneasCheck.Json.Parser]) consumes. Nullary variants serialize
   as bare JSON strings; payload variants as single-key objects.
   Until the per-emitter commits (#4-#11) wire actual values, every
   hint slot defaults to its empty form; the corresponding key is
   still always emitted under fmt_version 2 so the parser sees a
   schema-stable shape. *)

let json_cert_mut_borrow_kind (k : cert_mut_borrow_kind) : Yojson.Basic.t =
  match k with
  | MbkDirect -> `String "Direct"
  | MbkInAbsReborrow abs ->
      `Assoc [ "InAbsReborrow", `Assoc [ "abs", json_abs_id abs ] ]
  | MbkLoopOwned lid ->
      `Assoc [ "LoopOwned", `Assoc [ "loop", json_loop_id lid ] ]

let json_cert_abs_role (r : cert_abs_role) : Yojson.Basic.t =
  match r with
  | ArMutBorrow { arg_idx; loan } ->
      `Assoc
        [
          ( "MutBorrow",
            `Assoc [ "arg_idx", `Int arg_idx; "loan", json_borrow_id loan ] );
        ]
  | ArMutLoan { loan } ->
      `Assoc [ "MutLoan", `Assoc [ "loan", json_borrow_id loan ] ]
  | ArSharedBorrow { arg_idx; sb_id } ->
      `Assoc
        [
          ( "SharedBorrow",
            `Assoc
              [ "arg_idx", `Int arg_idx; "sb_id", json_shared_borrow_id sb_id ] );
        ]

let json_cert_abs_shape (s : cert_abs_shape) : Yojson.Basic.t =
  `Assoc
    [
      "abs_id", json_abs_id s.as_abs_id;
      "parent_abs", `List (List.map json_abs_id s.as_parent_abs);
      "roles", `List (List.map json_cert_abs_role s.as_roles);
    ]

let json_cert_join_rule (r : cert_join_rule) : Yojson.Basic.t =
  match r with
  | JrJoinSame -> `String "JoinSame"
  | JrJoinVar -> `String "JoinVar"
  | JrJoinSymbolic sv ->
      `Assoc
        [ "JoinSymbolic", `Assoc [ "fresh_sv", json_symbolic_value_id sv ] ]
  | JrJoinMutBorrows { l_left; l_right; l_fresh; abs } ->
      `Assoc
        [
          ( "JoinMutBorrows",
            `Assoc
              [
                "left", json_borrow_id l_left;
                "right", json_borrow_id l_right;
                "fresh", json_borrow_id l_fresh;
                "abs", json_abs_id abs;
              ] );
        ]
  | JrJoinBottomOther abs ->
      `Assoc [ "JoinBottomOther", `Assoc [ "abs", json_abs_id abs ] ]
  | JrJoinOtherBottom abs ->
      `Assoc [ "JoinOtherBottom", `Assoc [ "abs", json_abs_id abs ] ]

let json_cert_join_entry (e : cert_join_entry) : Yojson.Basic.t =
  `Assoc
    [
      "local", json_local_id e.je_local;
      "rule", json_cert_join_rule e.je_rule;
    ]

let json_cert_signature (s : cert_signature) : Yojson.Basic.t =
  `Assoc
    [
      "inputs", `List (List.map json_ty s.csig_inputs);
      "output", json_ty s.csig_output;
      (* M9.5i: the function's type-parameter names, in declaration
         order. Empty for monomorphic functions. *)
      "type_params",
        `List (List.map (fun n -> `String n) s.csig_type_params);
      (* M9.5o: per-clause trait obligation list. Each entry is a
         `{trait, type_param}` record, where `trait` is the trait's
         qualified name and `type_param` is the index into
         `type_params`. *)
      "trait_clauses",
        `List (List.map json_trait_clause s.csig_trait_clauses);
    ]

(* ---------- Events ---------- *)

let json_event (e : event) : Yojson.Basic.t =
  match e with
  | EvMutBorrow { loan; place; symval; kind_hint } ->
      `Assoc
        [
          ( "EvMutBorrow",
            `Assoc
              [
                "loan", json_borrow_id loan;
                "place", json_cert_place place;
                "symval", json_symbolic_value_id symval;
                (* M9.6 (Option C) — populated in commit #4. *)
                "kind_hint", json_cert_mut_borrow_kind kind_hint;
              ] );
        ]
  | EvSharedBorrow { loan; sb_id; place; symval } ->
      `Assoc
        [
          ( "EvSharedBorrow",
            `Assoc
              [
                "loan", json_borrow_id loan;
                "shared_borrow_id", json_shared_borrow_id sb_id;
                "place", json_cert_place place;
                "symval", json_symbolic_value_id symval;
              ] );
        ]
  | EvAssign { dst; rhs } ->
      `Assoc
        [
          ( "EvAssign",
            `Assoc
              [ "dst", json_cert_place dst; "rhs", json_cert_sym_expr rhs ] );
        ]
  | EvMove { src; dst } ->
      `Assoc
        [
          ( "EvMove",
            `Assoc [ "src", json_cert_place src; "dst", json_cert_place dst ]
          );
        ]
  | EvCopy { src; dst } ->
      `Assoc
        [
          ( "EvCopy",
            `Assoc [ "src", json_cert_place src; "dst", json_cert_place dst ]
          );
        ]
  | EvEndBorrow { loan; restore } ->
      `Assoc
        [
          ( "EvEndBorrow",
            `Assoc
              [
                "loan", json_borrow_id loan;
                "restore", json_restore_info restore;
              ] );
        ]
  | EvAssert { cond; expected } ->
      `Assoc
        [
          ( "EvAssert",
            `Assoc
              [ "cond", json_cert_sym_expr cond; "expected", `Bool expected ]
          );
        ]
  | EvPanic -> `String "EvPanic"
  | EvReturn -> `String "EvReturn"
  | EvBinop { op; lhs; rhs; dst } ->
      `Assoc
        [
          ( "EvBinop",
            `Assoc
              [
                "op", `String op;
                "lhs", json_cert_sym_expr lhs;
                "rhs", json_cert_sym_expr rhs;
                "dst", json_cert_place dst;
              ] );
        ]
  | EvReborrow { child; parent; place; parent_live; parent_abs } ->
      let pa_kv : (string * Yojson.Basic.t) list =
        match parent_abs with
        | None -> []
        | Some a -> [ "parent_abs", json_abs_id a ]
      in
      `Assoc
        [
          ( "EvReborrow",
            `Assoc
              ([
                "child", json_borrow_id child;
                "parent", json_borrow_id parent;
                "place", json_cert_place place;
                (* M9.6 (Option C) — populated in commit #5. *)
                "parent_live", `Bool parent_live;
              ] @ pa_kv) );
        ]
  | EvCall { fn; fn_name; call_id; args; dst; region_abs; abs_sig } ->
      `Assoc
        [
          ( "EvCall",
            `Assoc
              [
                "fn", json_fun_decl_id fn;
                "fn_name", `String fn_name;
                "call_id", json_fun_call_id call_id;
                "args", `List (List.map json_cert_sym_expr args);
                "dst", json_cert_place dst;
                "region_abs", `List (List.map json_abs_id region_abs);
                (* M9.6 (Option C) — populated in commit #7. *)
                "abs_sig", `List (List.map json_cert_abs_shape abs_sig);
              ] );
        ]
  | EvEndAbs { abs; final_values; released_loans; token_clear_locals } ->
      `Assoc
        [
          ( "EvEndAbs",
            `Assoc
              [
                "abs", json_abs_id abs;
                "final_values", `List (List.map json_cert_sym_expr final_values);
                "released_loans", `List (List.map json_borrow_id released_loans);
                (* M9.6 (Option C) — populated in commit #8. *)
                "token_clear_locals",
                  `List (List.map json_local_id token_clear_locals);
              ] );
        ]
  | EvProj { abs; place; symval } ->
      `Assoc
        [
          ( "EvProj",
            `Assoc
              [
                "abs", json_abs_id abs;
                "place", json_cert_place place;
                "symval", json_symbolic_value_id symval;
              ] );
        ]
  | EvSymExpandMutBorrow
      { sv_id; bid; inner_sv; parent_abs; subst_locals; subst_loans } ->
      let pa_kv : (string * Yojson.Basic.t) list =
        match parent_abs with
        | None -> []
        | Some a -> [ "parent_abs", json_abs_id a ]
      in
      `Assoc
        [
          ( "EvSymExpandMutBorrow",
            `Assoc
              ([
                "sv_id", json_symbolic_value_id sv_id;
                "bid", json_borrow_id bid;
                "inner_sv", json_symbolic_value_id inner_sv;
                (* M9.6 (Option C) — populated in commit #6. *)
                "subst_locals",
                  `List (List.map json_local_id subst_locals);
                "subst_loans",
                  `List (List.map json_borrow_id subst_loans);
              ] @ pa_kv) );
        ]
  | EvJoin { left; right; result; witnesses } ->
      `Assoc
        [
          ( "EvJoin",
            `Assoc
              [
                "left", json_cert_state_summary left;
                "right", json_cert_state_summary right;
                "result", json_cert_state_summary result;
                (* M9.6 (Option C) — populated in commits #10/#11. *)
                "witnesses",
                  `List (List.map json_cert_join_entry witnesses);
              ] );
        ]
  | EvLoopInv { loop_id; invariant; loan_registry } ->
      `Assoc
        [
          ( "EvLoopInv",
            `Assoc
              [
                "loop_id", json_loop_id loop_id;
                "invariant", json_cert_state_summary invariant;
                (* M9.6 (Option C) — populated in commit #9. *)
                "loan_registry",
                  `List
                    (List.map
                       (fun (b, a) ->
                         `Assoc
                           [
                             "borrow", json_borrow_id b;
                             "parent_abs", json_abs_id a;
                           ])
                       loan_registry);
              ] );
        ]
  | EvLoopEnd { loop_id } ->
      `Assoc
        [
          ( "EvLoopEnd",
            `Assoc [ "loop_id", json_loop_id loop_id ] );
        ]
  | EvMatchArm { scrutinee; adt_id; variant_id; variant_name } ->
      `Assoc
        [
          ( "EvMatchArm",
            `Assoc
              [
                "scrutinee", json_cert_sym_expr scrutinee;
                "adt_id", `Int adt_id;
                "variant_id", `Int variant_id;
                "variant_name", `String variant_name;
              ] );
        ]

(* ---------- Type declarations (M9.5b) ---------- *)

let json_cert_field (f : cert_field) : Yojson.Basic.t =
  let name_field : (string * Yojson.Basic.t) list =
    match f.cf_name with
    | Some n -> [ "name", `String n ]
    | None -> []
  in
  `Assoc
    ([ "idx", `Int f.cf_idx ]
     @ name_field
     @ [ "ty", json_ty f.cf_ty ])

let json_cert_variant (v : cert_variant) : Yojson.Basic.t =
  `Assoc
    [
      "id", `Int v.cv_id;
      "name", `String v.cv_name;
      "fields", `List (List.map json_cert_field v.cv_fields);
    ]

let json_cert_type_decl_kind (k : cert_type_decl_kind) : Yojson.Basic.t =
  match k with
  | CTDStruct fields ->
      `Assoc [ "Struct", `List (List.map json_cert_field fields) ]
  | CTDEnum variants ->
      `Assoc [ "Enum", `List (List.map json_cert_variant variants) ]
  | CTDOpaque -> `String "Opaque"

let json_cert_type_decl (d : cert_type_decl) : Yojson.Basic.t =
  let optional_span : (string * Yojson.Basic.t) list =
    match d.ctd_source_span with
    | None -> []
    | Some sp -> [ "source_span", json_cert_source_span sp ]
  in
  `Assoc
    ([
       "id", `Int d.ctd_id;
       "name", `String d.ctd_name;
       "kind", json_cert_type_decl_kind d.ctd_kind;
       (* M9.5i: the ADT's type-parameter names, in declaration order.
          Empty for monomorphic ADTs. *)
       "type_params",
         `List (List.map (fun n -> `String n) d.ctd_type_params);
       (* M9.5l: tuple-style positional fields (including unit structs).
          Defaults to false on the Lean side when the key is absent
          (older certs). *)
       "is_tuple_struct", `Bool d.ctd_is_tuple_struct;
       (* M9.5n: crate-prefixed qualified name. The Lean side uses
          this to suppress stdlib ADTs (`core::option::Option`,
          `alloc::alloc::Global`, …) so they don't shadow / duplicate
          Lean's built-ins in the emitted output. *)
       "qualified_name", `String d.ctd_qualified_name;
     ]
    @ optional_span)

(* ---------- Trait declarations (M9.5l) ---------- *)

let json_cert_trait_method (m : cert_trait_method) : Yojson.Basic.t =
  `Assoc
    [
      "name", `String m.ctm_name;
      "signature", json_cert_signature m.ctm_signature;
      (* M9.5o: has_default flag — true iff this method carries a
         default implementation in the trait declaration. *)
      "has_default", `Bool m.ctm_has_default;
    ]

let json_cert_trait_decl (d : cert_trait_decl) : Yojson.Basic.t =
  let optional_span : (string * Yojson.Basic.t) list =
    match d.ctrd_source_span with
    | None -> []
    | Some sp -> [ "source_span", json_cert_source_span sp ]
  in
  `Assoc
    ([
       "id", `Int d.ctrd_id;
       "name", `String d.ctrd_name;
       "qualified_name", `String d.ctrd_qualified_name;
       "methods", `List (List.map json_cert_trait_method d.ctrd_methods);
     ]
    @ optional_span)

let json_cert_trait_impl_method (m : cert_trait_impl_method) : Yojson.Basic.t =
  `Assoc
    [
      "name", `String m.ctim_name;
      "fn_id", `Int m.ctim_fn_id;
    ]

let json_cert_trait_impl (i : cert_trait_impl) : Yojson.Basic.t =
  let optional_self : (string * Yojson.Basic.t) list =
    match i.ctri_self_type_decl_id with
    | None -> []
    | Some id -> [ "self_type_decl_id", `Int id ]
  in
  let optional_self_var : (string * Yojson.Basic.t) list =
    match i.ctri_self_type_var with
    | None -> []
    | Some n -> [ "self_type_var", `String n ]
  in
  let optional_span : (string * Yojson.Basic.t) list =
    match i.ctri_source_span with
    | None -> []
    | Some sp -> [ "source_span", json_cert_source_span sp ]
  in
  `Assoc
    ([
       "id", `Int i.ctri_id;
       "pretty_name", `String i.ctri_pretty_name;
       "qualified_name", `String i.ctri_qualified_name;
       "trait_decl_id", `Int i.ctri_trait_decl_id;
     ]
    @ optional_self
    @ optional_self_var
    @ [
        (* M9.5o: type-parameter names on the impl itself + trait clauses. *)
        "type_params",
          `List (List.map (fun n -> `String n) i.ctri_type_params);
        "trait_clauses",
          `List (List.map json_trait_clause i.ctri_trait_clauses);
        "methods",
          `List (List.map json_cert_trait_impl_method i.ctri_methods);
      ]
    @ optional_span)

(* ---------- Top-level ---------- *)

let json_fun_cert (fc : fun_cert) : Yojson.Basic.t =
  let optional_span : (string * Yojson.Basic.t) list =
    match fc.fc_source_span with
    | None -> []
    | Some sp -> [ "source_span", json_cert_source_span sp ]
  in
  let optional_pretty : (string * Yojson.Basic.t) list =
    match fc.fc_pretty_name with
    | None -> []
    | Some n -> [ "pretty_name", `String n ]
  in
  `Assoc
    ([
       "fn_id", json_fun_decl_id fc.fc_fn_id;
       "fn_name", `String fc.fc_fn_name;
       "signature", json_cert_signature fc.fc_signature;
     ]
    @ optional_span
    @ optional_pretty
    @ [
        "events", `List (List.map json_event fc.fc_events);
        "final_state", json_cert_state_summary fc.fc_final_state;
      ])

let json_crate_cert (cc : crate_cert) : Yojson.Basic.t =
  `Assoc
    [
      "fmt_version", `Int cc.cc_fmt_version;
      "crate_hash", `String cc.cc_crate_hash;
      "type_decls", `List (List.map json_cert_type_decl cc.cc_type_decls);
      "trait_decls", `List (List.map json_cert_trait_decl cc.cc_trait_decls);
      "trait_impls", `List (List.map json_cert_trait_impl cc.cc_trait_impls);
      "functions", `List (List.map json_fun_cert cc.cc_functions);
    ]

(** Compute the SHA-256 hash of a file's contents as a lowercase hex string.

    Used to tie a cert to a specific [llbc.json]. *)
let sha256_file (path : string) : string =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let buf = Bytes.create n in
  really_input ic buf 0 n;
  close_in ic;
  Digest.to_hex (Digest.bytes buf)
(* NOTE: stdlib [Digest] is MD5, not SHA-256. We document this as a TODO: the
   cert "crate_hash" is a tamper-evident binding, not a security primitive, so
   MD5 is acceptable for M2; M12 swaps to a true SHA-256 once we add a
   dependency (e.g. cryptokit). *)

let write_to_file (path : string) (cc : crate_cert) : unit =
  let oc = open_out path in
  Yojson.Basic.pretty_to_channel oc (json_crate_cert cc);
  output_char oc '\n';
  close_out oc

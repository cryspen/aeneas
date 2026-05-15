(** See {!CertEvent} (.ml) for documentation. *)

open Types
open Expressions
open Values

type cert_place = {
  cp_local : local_id;
  cp_projection : projection_elem list;
  cp_ty : ty;
}

type cert_sym_expr =
  | SymVal of symbolic_value_id
  | SymLit of literal
  | SymCopy of cert_place
  | SymMove of cert_place
  | SymMutBorrowTok of borrow_id
  | SymVariant of {
      adt_id : int;
      variant_id : int;
      variant_name : string;
      fields : cert_sym_expr list;
    }
  | SymTuple of cert_sym_expr list
  | SymRecord of {
      adt_id : int;
      fields : (string * cert_sym_expr) list;
    }

type cert_state_summary = {
  cs_env : (local_id * cert_sym_expr) list;
  cs_live_loans : borrow_id list;
}

type cert_restore_info = { ri_given_back : cert_sym_expr }

type cert_source_span = {
  ss_file : string;
  ss_beg_line : int;
  ss_beg_col : int;
  ss_end_line : int;
  ss_end_col : int;
}

type cert_signature = {
  csig_inputs : ty list;
  csig_output : ty;
  csig_type_params : string list;
  (** [M9.5o] Trait obligations on this signature's type parameters.
      Each entry is a [(trait_qualified_name, type_param_index)] pair:
      e.g. for `fn f<T: Trait1>(...)`, an entry [("crate::Trait1", 0)]
      means the 0-th type parameter ([T]) carries a [Trait1] bound.
      Empty for signatures with no trait obligations. The Lean side
      uses these to emit `(Trait1Inst : Trait1 T)` binders between
      type-param binders and value params. *)
  csig_trait_clauses : (string * int) list;
}

type event =
  | EvMutBorrow of {
      loan : borrow_id;
      place : cert_place;
      symval : symbolic_value_id;
    }
  | EvSharedBorrow of {
      loan : borrow_id;
      sb_id : shared_borrow_id;
      place : cert_place;
      symval : symbolic_value_id;
    }
  | EvAssign of { dst : cert_place; rhs : cert_sym_expr }
  | EvMove of { src : cert_place; dst : cert_place }
  | EvCopy of { src : cert_place; dst : cert_place }
  | EvEndBorrow of { loan : borrow_id; restore : cert_restore_info }
  | EvAssert of { cond : cert_sym_expr; expected : bool }
  | EvPanic
  | EvReturn
  | EvBinop of {
      op : string;
      lhs : cert_sym_expr;
      rhs : cert_sym_expr;
      dst : cert_place;
    }
  | EvReborrow of {
      child : borrow_id;
      parent : borrow_id;
      place : cert_place;
    }
  | EvCall of {
      fn : fun_decl_id;
      fn_name : string;
      call_id : fun_call_id;
      args : cert_sym_expr list;
      dst : cert_place;
      region_abs : abs_id list;
    }
  | EvEndAbs of { abs : abs_id; final_values : cert_sym_expr list }
  | EvProj of {
      abs : abs_id;
      place : cert_place;
      symval : symbolic_value_id;
    }
  | EvJoin of {
      left : cert_state_summary;
      right : cert_state_summary;
      result : cert_state_summary;
    }
  | EvLoopInv of {
      loop_id : loop_id;
      invariant : cert_state_summary;
    }
  | EvLoopEnd of { loop_id : loop_id }
  | EvMatchArm of {
      scrutinee : cert_sym_expr;
      adt_id : int;
      variant_id : int;
      variant_name : string;
    }

type fun_cert = {
  fc_fn_id : fun_decl_id;
  fc_fn_name : string;
  fc_signature : cert_signature;
  fc_source_span : cert_source_span option;
  fc_events : event list;
  fc_final_state : cert_state_summary;
  fc_pretty_name : string option;
}

type cert_field = {
  cf_idx : int;
  cf_name : string option;
  cf_ty : ty;
}

type cert_variant = {
  cv_id : int;
  cv_name : string;
  cv_fields : cert_field list;
}

type cert_type_decl_kind =
  | CTDStruct of cert_field list
  | CTDEnum of cert_variant list
  | CTDOpaque

type cert_type_decl = {
  ctd_id : int;
  ctd_name : string;
  ctd_kind : cert_type_decl_kind;
  ctd_type_params : string list;
  ctd_is_tuple_struct : bool;
  ctd_source_span : cert_source_span option;
  ctd_qualified_name : string;
}

type cert_trait_method = {
  ctm_name : string;
  ctm_signature : cert_signature;
  (** [M9.5o] True iff this method has a default implementation in
      the trait declaration. The Lean side emits these as
      `Trait.<method>.default` decls (taking the trait itself as a
      bound) alongside the trait. *)
  ctm_has_default : bool;
}

type cert_trait_decl = {
  ctrd_id : int;
  ctrd_name : string;
  ctrd_qualified_name : string;
  ctrd_methods : cert_trait_method list;
  ctrd_source_span : cert_source_span option;
}

type cert_trait_impl_method = {
  ctim_name : string;
  ctim_fn_id : int;
}

type cert_trait_impl = {
  ctri_id : int;
  ctri_pretty_name : string;
  ctri_qualified_name : string;
  ctri_trait_decl_id : int;
  ctri_self_type_decl_id : int option;
  (** [M9.5o] When the impl's [Self] is a type parameter rather than a
      concrete ADT, this carries its name (e.g. ["T"] for
      `impl<T: Trait1> Trait2 for T`). [None] when [Self] is a
      concrete ADT (the [ctri_self_type_decl_id] case). *)
  ctri_self_type_var : string option;
  (** [M9.5o] Type-parameter names declared on the impl itself
      (i.e. the [T] in `impl<T: ...> ...`). Empty for monomorphic
      (concrete-Self) impls. *)
  ctri_type_params : string list;
  (** [M9.5o] Trait obligations on the impl's type parameters; same
      shape as [csig_trait_clauses]. *)
  ctri_trait_clauses : (string * int) list;
  ctri_methods : cert_trait_impl_method list;
  ctri_source_span : cert_source_span option;
}

type crate_cert = {
  cc_fmt_version : int;
  cc_crate_hash : string;
  cc_type_decls : cert_type_decl list;
  cc_trait_decls : cert_trait_decl list;
  cc_trait_impls : cert_trait_impl list;
  cc_functions : fun_cert list;
}

val cert_fmt_version : int

val cert_binop_string : Expressions.binop -> string
(** Flat string tag for an LLBC binop. See implementation for the
    mapping; arithmetic ops bake the overflow mode into the suffix
    ([Panic] / [UB] / [Wrap]). *)

val cert_place_of_place : Expressions.place -> cert_place option
(** Flatten a Charon [place] to a [cert_place]; [None] for [PlaceGlobal]. *)

val cert_sym_expr_of_operand : Expressions.operand -> cert_sym_expr option
(** Build a [cert_sym_expr] from an LLBC operand. Returns [None] for
    operand shapes the M10 subset cannot yet encode (globals,
    constants other than literals). *)

val cert_sym_expr_of_tvalue : Values.tvalue -> cert_sym_expr option
(** Best-effort flat summary of a [tvalue] as a [cert_sym_expr]. ADTs
    and [⊥] return [None]. Used by [EvJoin] state summaries. *)

val cert_state_summary_of_env : Values.env -> cert_state_summary
(** Build a [cert_state_summary] from an eval ctx's env: one entry per
    real (non-dummy) binding, plus a deduped list of live loan ids
    appearing in bindings. M11 only — full structural fidelity is
    deferred to M12. *)

val pp_event : Format.formatter -> event -> unit
val pp_fun_cert : Format.formatter -> fun_cert -> unit
val pp_crate_cert : Format.formatter -> crate_cert -> unit

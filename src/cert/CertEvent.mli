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
}

type crate_cert = {
  cc_fmt_version : int;
  cc_crate_hash : string;
  cc_type_decls : cert_type_decl list;
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

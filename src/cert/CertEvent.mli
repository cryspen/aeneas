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

type cert_state_summary = {
  cs_env : (local_id * cert_sym_expr) list;
  cs_live_loans : borrow_id list;
}

type cert_restore_info = { ri_given_back : cert_sym_expr }

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
  | EvReborrow of {
      child : borrow_id;
      parent : borrow_id;
      place : cert_place;
    }
  | EvCall of {
      fn : fun_decl_id;
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

type fun_cert = {
  fc_fn_id : fun_decl_id;
  fc_fn_name : string;
  fc_events : event list;
  fc_final_state : cert_state_summary;
}

type crate_cert = {
  cc_fmt_version : int;
  cc_crate_hash : string;
  cc_functions : fun_cert list;
}

val cert_fmt_version : int

val cert_place_of_place : Expressions.place -> cert_place option
(** Flatten a Charon [place] to a [cert_place]; [None] for [PlaceGlobal]. *)

val pp_event : Format.formatter -> event -> unit
val pp_fun_cert : Format.formatter -> fun_cert -> unit
val pp_crate_cert : Format.formatter -> crate_cert -> unit

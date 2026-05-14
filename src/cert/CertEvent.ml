(** Certificate events: the LLBC# evaluation trace emitted by the OCaml
    interpreter for the Lean checker to replay.

    Each constructor mirrors an LLBC# reduction rule (Fig. 4 of the 2022 paper
    and the additions in §4 / Fig. 9 of the 2024 paper). The event vocabulary
    here intentionally tracks the rule names so that the Lean side can mount a
    direct, one-rule-per-constructor replayer.

    For the M2 milestone we only define the types and the JSON shape; no
    interpreter hooks are wired yet. M3+ progressively populate events from the
    interpreter. *)

open Types
open Expressions
open Values

(** A simplified place encoding for the certificate: a local plus a list of
    projection steps. We do not reuse Charon's nested [place] form directly
    because the Lean parser benefits from a flat representation that mirrors
    the LLBC# rules' path projections. *)
type cert_place = {
  cp_local : local_id;
  cp_projection : projection_elem list;
  cp_ty : ty;
}
[@@deriving show]

(** A right-hand-side expression as it appears in a certificate event.

    During the direct-borrow subset (M2-M8) we only need a handful of shapes:
    a symbolic value reference, a literal, a place read (Move/Copy), or a
    freshly produced mutable-borrow token. Later milestones extend this. *)
type cert_sym_expr =
  | SymVal of symbolic_value_id  (** Existing symbolic value *)
  | SymLit of literal  (** Literal constant *)
  | SymCopy of cert_place  (** Value read from a place by copy *)
  | SymMove of cert_place  (** Value read from a place by move *)
  | SymMutBorrowTok of borrow_id
      (** The token produced by a [&mut] of a place: the inner borrowed value
          flows back along this borrow id when the borrow ends. *)
[@@deriving show]

(** A coarse summary of the abstract state at a particular point.

    Used by joins, loop fixpoints, and as the trace's terminal [final_state].
    Populated in M11 for joins; for the direct-borrow subset we only record
    the final environment shape (which locals hold which symbolic values /
    borrow tokens). *)
type cert_state_summary = {
  cs_env : (local_id * cert_sym_expr) list;
  cs_live_loans : borrow_id list;
}
[@@deriving show]

(** Information needed to restore a borrowed value when ending a mutable
    borrow. The [given_back] symbolic expression is the value that flows
    back to the borrow's loan upon termination. *)
type cert_restore_info = {
  ri_given_back : cert_sym_expr;
}
[@@deriving show]

(** The LLBC# trace event vocabulary.

    Direct-borrow subset (M2-M8) uses constructors marked [DB]; later
    milestones populate the rest. The serializer emits every constructor
    uniformly so a partial trace from an early milestone still validates
    against the shared JSON schema. *)
type event =
  (* === Direct-borrow subset (M2-M8) === *)
  | EvMutBorrow of {
      loan : borrow_id;
      place : cert_place;
      symval : symbolic_value_id;
    }  (** [DB] Create a fresh mutable borrow of [place]; the loan side keeps
            a symbolic value [symval] to be re-bound when the borrow ends. *)
  | EvSharedBorrow of {
      loan : borrow_id;
      sb_id : shared_borrow_id;
      place : cert_place;
      symval : symbolic_value_id;
    }  (** [DB] Create a fresh shared borrow of [place]. *)
  | EvAssign of { dst : cert_place; rhs : cert_sym_expr }
      (** [DB] Assign an rvalue to a place. *)
  | EvMove of { src : cert_place; dst : cert_place }
      (** [DB] Move [src] into [dst]; [src] becomes ⊥. *)
  | EvCopy of { src : cert_place; dst : cert_place }
      (** [DB] Copy [src] to [dst]; [src] retains its value. *)
  | EvEndBorrow of { loan : borrow_id; restore : cert_restore_info }
      (** [DB] End a mutable borrow; the inner value flows back along
          [restore]. *)
  | EvAssert of { cond : cert_sym_expr; expected : bool }
      (** [DB] An [assert] statement evaluated to a known value. *)
  | EvPanic
      (** [DB] Execution diverged via panic. *)
  | EvReturn
      (** [DB] Function returned normally. *)
  (* === Reborrows + nested borrows (M9) === *)
  | EvReborrow of {
      child : borrow_id;
      parent : borrow_id;
      place : cert_place;
    }
  (* === Function calls + abstractions (M10) === *)
  | EvCall of {
      fn : fun_decl_id;
      call_id : fun_call_id;
      args : cert_sym_expr list;
      dst : cert_place;
      region_abs : abs_id list;
    }
  | EvEndAbs of {
      abs : abs_id;
      final_values : cert_sym_expr list;
    }
  | EvProj of {
      abs : abs_id;
      place : cert_place;
      symval : symbolic_value_id;
    }
  (* === Joins + loops (M11+) === *)
  | EvJoin of {
      left : cert_state_summary;
      right : cert_state_summary;
      result : cert_state_summary;
    }
  | EvLoopInv of {
      loop_id : loop_id;
      invariant : cert_state_summary;
    }
[@@deriving show]

(** A per-function trace. *)
type fun_cert = {
  fc_fn_id : fun_decl_id;
  fc_fn_name : string;  (** Pretty name; not load-bearing for the checker. *)
  fc_events : event list;
  fc_final_state : cert_state_summary;
}
[@@deriving show]

(** Top-level certificate. *)
type crate_cert = {
  cc_fmt_version : int;
  cc_crate_hash : string;
      (** Hex SHA-256 of the LLBC JSON file's bytes; the Lean parser refuses
          mismatched (LLBC, cert) pairs. *)
  cc_functions : fun_cert list;
}
[@@deriving show]

(** Current cert format version. Bump whenever the JSON shape changes in a
    backwards-incompatible way. *)
let cert_fmt_version : int = 1

(** Convert a Charon [place] into a flat [cert_place].

    Returns [None] for [PlaceGlobal]: globals do not appear in the
    direct-borrow subset, and the trace would be ambiguous if we silently
    elided them. Later milestones extend this. *)
let cert_place_of_place (p : place) : cert_place option =
  let rec collect (acc : projection_elem list) (p : place) :
      (local_id * projection_elem list * ty) option =
    match p.kind with
    | PlaceLocal lid -> Some (lid, acc, p.ty)
    | PlaceProjection (sub, pe) -> collect (pe :: acc) sub
    | PlaceGlobal _ -> None
  in
  match collect [] p with
  | None -> None
  | Some (lid, proj, ty) ->
      Some { cp_local = lid; cp_projection = proj; cp_ty = ty }

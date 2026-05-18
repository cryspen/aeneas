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
  | SymCast of {
      target_ty : string;
      inner : cert_sym_expr;
    }

type cert_state_summary = {
  cs_env : (local_id * cert_sym_expr) list;
  cs_live_loans : borrow_id list;
}

type cert_restore_info = {
  ri_given_back : cert_sym_expr;
  (** [M10.x.0 — cert v6] env local that holds the [mutLoan]
      token an end-borrow restores; populated for
      [.direct]/[.lazyExpand] kinds, [None] otherwise. *)
  ri_holder_local : local_id option;
}

type cert_source_span = {
  ss_file : string;
  ss_beg_line : int;
  ss_beg_col : int;
  ss_end_line : int;
  ss_end_col : int;
}

(* [M9.7o-E5b] The flat [cert_signature] record was deleted alongside
   the Lean-side [Raw.FnSignature] once the structured
   [LlbcProgram.fun_decls[k].signature] became the sole source of
   typed-signature info. *)

(** [M9.6 — Option C] Rule-choice hint for [EvMutBorrow]: tells the
    Lean checker whether the borrow's lifetime is owned by an in-body
    EvMutBorrow ([MbkDirect]), by a named caller-input abstraction
    ([MbkInAbsReborrow]), or by an open loop's region abstraction
    ([MbkLoopOwned]). Lets the strict path skip the M9.5w/aa
    pragmatic inference. *)
type cert_mut_borrow_kind =
  | MbkDirect
  | MbkInAbsReborrow of abs_id
  | MbkLoopOwned of loop_id

(** [M9.6 — Option C] Role of a single avalue inside the [A_in(ρ)]
    of a function call's region abstraction. Carried inside
    [cert_abs_shape.as_roles]. *)
type cert_abs_role =
  | ArMutBorrow of { arg_idx : int; loan : borrow_id }
  | ArMutLoan of { loan : borrow_id }
  | ArSharedBorrow of { arg_idx : int; sb_id : shared_borrow_id }

(** [M9.6 — Option C] The shape of one region abstraction freshened
    by an [EvCall]: its id, the ancestor abs-ids (for nested-borrow
    contracts), and the per-avalue role list mirroring the paper's
    [A_in(ρ) { borrow^m ℓ _, loan^m ℓ' }] content. -*)
type cert_abs_shape = {
  as_abs_id : abs_id;
  as_parent_abs : abs_id list;
  as_roles : cert_abs_role list;
}

(** [M9.6 — Option C] Per-result-env-local witness of which Fig. 11
    rule the OCaml interpreter applied in an [EvJoin]. -*)
type cert_join_rule =
  | JrJoinSame
  | JrJoinSymbolic of symbolic_value_id
  | JrJoinMutBorrows of {
      l_left : borrow_id;
      l_right : borrow_id;
      l_fresh : borrow_id;
      (** [M9.8] Cert v4 bump: the fresh region abstraction
          freshened by Collapse-Dup-MutBorrow is now named
          structurally — id + parent ids + roles — so the Lean
          replayer can install it in [absRegistry] (mirroring
          [EvCall.abs_sig]) and the soundness side no longer has
          to assume the abs creation by axiom. By construction
          [abs.as_parent_abs = []] and [abs.as_roles] is the
          three-role list
          [(mutBorrow, l_left); (mutBorrow, l_right); (mutLoan, l_fresh)]. *)
      abs : cert_abs_shape;
    }
  | JrJoinVar
  | JrJoinBottomOther of abs_id
  | JrJoinOtherBottom of abs_id

(** [M10.x.0 — cert v6] Per-[cert_join_entry] delta witness.
    Carries the [JoinEntryStep] premise's content without
    transmitting the full intermediate [Ω_i] state — Lean folds
    the chain by walking these deltas. -*)
type cert_join_entry_delta =
  | JedTrivial
  | JedSymbolic of symbolic_value_id
  | JedMutBorrows of { l_fresh : borrow_id; abs_id : abs_id }
  | JedBottomOther of abs_id
  | JedOtherBottom of abs_id

(** [M9.6 — Option C] One entry of [EvJoin.witnesses].

    [M10.x.0 — cert v6] [je_delta] is the parallel paper-side
    [JoinEntryStep] premise; the Lean replayer cross-checks that
    [je_rule] and [je_delta] name the same constructor. -*)
type cert_join_entry = {
  je_local : local_id;
  je_rule : cert_join_rule;
  je_delta : cert_join_entry_delta;
}

(** [M10.x.0 — cert v6] Reference to a sub-statement in the cert's
    embedded LLBC body tree. [sr_fun_id] indexes
    [cc_llbc_program.fun_decls]; [sr_body_path] is the per-level
    path from the function-body root. -*)
type cert_stmt_ref = {
  sr_fun_id : int;
  sr_body_path : int array;
}

type event =
  | EvMutBorrow of {
      loan : borrow_id;
      place : cert_place;
      symval : symbolic_value_id;
      (** [M9.6 — Option C] Defaults to [MbkDirect] under
          fmt_version 2 until the OCaml emitter is wired (commit
          #4). The Lean side falls back to today's pragmatic
          M9.5w/aa inference whenever the hint is the default. *)
      kind_hint : cert_mut_borrow_kind;
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
      (** [M9.6 — Option C] Defaults to [false] / [None] under
          fmt_version 2 until commit #5 wires the emitter. -*)
      parent_live : bool;
      parent_abs : abs_id option;
    }
  | EvCall of {
      fn : fun_decl_id;
      fn_name : string;
      call_id : fun_call_id;
      args : cert_sym_expr list;
      dst : cert_place;
      region_abs : abs_id list;
      (** [M9.6 — Option C] One [cert_abs_shape] per freshened
          region abstraction (parallel to [region_abs]). Defaults
          to [[]] under fmt_version 2 until commit #7 wires the
          emitter. -*)
      abs_sig : cert_abs_shape list;
    }
  | EvEndAbs of {
      abs : abs_id;
      final_values : cert_sym_expr list;
      released_loans : borrow_id list;
      (** [M9.6 — Option C] Locals whose [mutLoan] token must be
          cleared when this abstraction ends. Defaults to [[]]
          until commit #8 wires the emitter; the Lean side falls
          back to today's scan-env behaviour while empty. -*)
      token_clear_locals : local_id list;
    }
  | EvSymExpandMutBorrow of {
      sv_id : symbolic_value_id;
      bid : borrow_id;
      inner_sv : symbolic_value_id;
      (** [M9.6 — Option C] Defaults to [None] / [[]] / [[]] under
          fmt_version 2 until commit #6 wires the emitter. -*)
      parent_abs : abs_id option;
      subst_locals : local_id list;
      subst_loans : borrow_id list;
    }
  | EvJoin of {
      left : cert_state_summary;
      right : cert_state_summary;
      result : cert_state_summary;
      (** [M9.6 — Option C] One entry per result-env-local in
          declaration order. Defaults to [[]] until commits #10/#11
          wire the emitter. -*)
      witnesses : cert_join_entry list;
    }
  | EvLoopInv of {
      loop_id : loop_id;
      invariant : cert_state_summary;
      (** [M9.6 — Option C] [(borrow_id, parent_abs_id)] pairs from
          the fixpoint. Defaults to [[]] until commit #9 wires the
          emitter. -*)
      loan_registry : (borrow_id * abs_id) list;
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
  fc_source_span : cert_source_span option;
  fc_events : event list;
  fc_final_state : cert_state_summary;
  fc_pretty_name : string option;
  (** [M10.x.0 — cert v6] Parallel-to-[fc_events] array of LLBC
      body-tree back-pointers; [None] for synthetic events.
      Threaded with [None] sentinels at M10.x.0; actual
      population deferred to M10.x.0b. -*)
  fc_stmt_refs : cert_stmt_ref option list;
}

(** [M9.7o-E5a] Top-level certificate. The flat ADT / trait decl
    mirrors (`cert_type_decl`, `cert_trait_decl`, `cert_trait_impl`)
    were deleted alongside cert v2; the embedded {!cc_llbc_program}
    subtree is the sole source for those decls on the Lean side. *)
type crate_cert = {
  cc_fmt_version : int;
  cc_crate_hash : string;
  cc_functions : fun_cert list;
  cc_llbc_program : Yojson.Basic.t;
      (** [M9.7d] The structured LLBC subtree, serialised by
          {!LlbcJson.crate_to_json} and embedded under the top-level
          [llbc_program] key of cert v3. *)
}

val cert_fmt_version : int
(** [M10.x.0] Bumped to 6: cert v6 adds [ri_holder_local],
    [je_delta], and [fc_stmt_refs] (v5 skipped; v4 was M9.8's
    [JrJoinMutBorrows.abs] promotion to [cert_abs_shape]). *)

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

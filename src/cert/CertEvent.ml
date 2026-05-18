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
  | SymVariant of {
      adt_id : int;
      variant_id : int;
      variant_name : string;
      fields : cert_sym_expr list;
    }
      (** [M9.5d] A C-style enum-variant construction: the result of an
          [Rvalue.Aggregate (AggregatedAdt (..., Some variant_id, None), [])]
          with zero fields. The Lean translator renders this as
          [<adt_name>.<variant_name>] (the adt name is resolved via
          [adt_id] against the cert's type-decl table).

          [M9.5f] Extends this with a [fields] list: a payload-bearing
          ctor application like [NumOrZero::Num(x)] carries one entry per
          field's [cert_sym_expr] (the operand was a place read or a
          literal). C-style variants keep [fields = []] and emit the
          bare ctor name; payload-bearing variants emit
          [<adt_name>.<variant_name> e1 e2 ... eN]. *)
  | SymTuple of cert_sym_expr list
      (** [M9.5p] A tuple aggregate construction: the result of an
          [Rvalue.Aggregate (AggregatedAdt ({id = TTuple; _}, None, None), ops)].
          The Lean translator renders this as [(e1, e2, ..., eN)]. *)
  | SymRecord of {
      adt_id : int;
      fields : (string * cert_sym_expr) list;
    }
      (** [M9.5p] A named-field struct aggregate construction: the result
          of an [Rvalue.Aggregate (AggregatedAdt ({id = TAdtId K; _}, None, None), ops)]
          where the underlying type-decl is a named-field struct. Each
          field carries its surface name (resolved via the cert type-decl
          table on the OCaml side). The Lean translator renders this as
          [{ x := e1, y := e2, ... }] (Lean record-literal syntax). *)
  | SymCast of {
      target_ty : string;
      inner : cert_sym_expr;
    }
      (** [Session 6] An [as]-cast result: [<inner> as <target_ty>]. The
          [target_ty] is a short stringified [literal_type] like
          ["i32"], ["u32"], ["usize"], or ["bool"] — matching the
          surface tags the Lean side uses for renderable Rust types.
          Emitted by the rvalue arm for [UnaryOp (Cast (CastScalar _), _)];
          consumed by the Lean cert walker to produce
          [.app "__cast::<target_ty>" #[inner]] which the Rust/Lean
          emitters render as [(inner as target_ty)] / a typed cast. *)
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
    back to the borrow's loan upon termination.

    [M10.x.0 — cert v6] [ri_holder_local] names the local in the OCaml
    [eval_ctx.env] whose [VLoan (VMutLoan loan_bid)] token the
    end-borrow restores. The emit site at [InterpBorrows.ml:1050]
    walks the env and populates this for [.direct]/[.lazyExpand]
    loan kinds; [None] for [.reborrow]/[.shared] kinds (which don't
    park a token in env) and as a sentinel when no holder is found
    (e.g. synthetic / lazy-expansion certs whose token was
    overwritten before the end-borrow). The Lean side does not yet
    consume this field at M10.x.0 — it lands here as schema
    plumbing for M10.x.9, which inverts the env-walk in
    [stepEndBorrow]. *)
type cert_restore_info = {
  ri_given_back : cert_sym_expr;
  ri_holder_local : local_id option;
}
[@@deriving show]

(** A source-code span attached to a cert function, mirroring
    [Meta.span]'s data fields. The Lean emitter uses this for the
    per-function [/-- Source: ..., lines N:M-P:Q -/] docstrings. *)
type cert_source_span = {
  ss_file : string;
  ss_beg_line : int;
  ss_beg_col : int;
  ss_end_line : int;
  ss_end_col : int;
}
[@@deriving show]

(* [M9.7o-E5b] The flat [cert_signature] record was deleted alongside
   the Lean-side [Raw.FnSignature] once the structured
   [LlbcProgram.fun_decls[k].signature] became the sole source of
   typed-signature info. The cert's per-function trace no longer
   carries its own signature copy. *)

(** [M9.6 — Option C] Rule-choice hint for [EvMutBorrow]. See
    [CertEvent.mli] for the spec; carried via [EvMutBorrow.kind_hint]. *)
type cert_mut_borrow_kind =
  | MbkDirect
  | MbkInAbsReborrow of abs_id
  | MbkLoopOwned of loop_id
[@@deriving show]

(** [M9.6 — Option C] Per-avalue role inside an [EvCall] region
    abstraction's [A_in(ρ)] content. *)
type cert_abs_role =
  | ArMutBorrow of { arg_idx : int; loan : borrow_id }
  | ArMutLoan of { loan : borrow_id }
  | ArSharedBorrow of { arg_idx : int; sb_id : shared_borrow_id }
[@@deriving show]

(** [M9.6 — Option C] Shape of one region abstraction freshened by
    an [EvCall]. *)
type cert_abs_shape = {
  as_abs_id : abs_id;
  as_parent_abs : abs_id list;
  as_roles : cert_abs_role list;
}
[@@deriving show]

(** [M9.6 — Option C] Witness of which Fig. 11 (paper) rule a single
    [EvJoin] result-env entry came from. *)
type cert_join_rule =
  | JrJoinSame
  | JrJoinSymbolic of symbolic_value_id
  | JrJoinMutBorrows of {
      l_left : borrow_id;
      l_right : borrow_id;
      l_fresh : borrow_id;
      abs : cert_abs_shape;
          (** [M9.8] Cert v4 bump: the fresh region abstraction
              created by Collapse-Dup-MutBorrow is named
              structurally (id + parents + roles) rather than only
              by id. The Lean replayer installs the shape into
              [absRegistry] using the same code path as
              [EvCall.abs_sig], so the soundness-side
              [stepJoin_witnessed_sound] no longer has to assume
              the abs creation. By construction [as_parent_abs =
              []] and [as_roles] is the three-role list
              [mutBorrow l_left; mutBorrow l_right; mutLoan l_fresh]
              (paper Fig. 11). *)
    }
  | JrJoinVar
  | JrJoinBottomOther of abs_id
  | JrJoinOtherBottom of abs_id
[@@deriving show]

(** [M10.x.0 — cert v6] Per-[cert_join_entry] delta witness. Carries
    only what the corresponding paper-side [JoinEntryStep] constructor's
    premise needs — never the full intermediate state. The chain's
    intermediate [Ω_i] is rebuilt in Lean by folding deltas. The
    constructor names are parallel to [cert_join_rule] constructors;
    the Lean replayer cross-checks the pair (see [Step.lean]
    stepJoin's v6 consistency check). Lands at M10.x.0 as schema
    plumbing for M10.x.10 (which inverts the [join] axiom into a
    fold over these deltas). *)
type cert_join_entry_delta =
  | JedTrivial
      (** Matches [JrJoinSame] / [JrJoinVar]: no state change, no
          freshness premise. *)
  | JedSymbolic of symbolic_value_id
      (** Matches [JrJoinSymbolic n]: post-state introduces [SymVal n];
          the freshness premise is an HWM fact on
          [Ω_i.symValIdFresh n]. *)
  | JedMutBorrows of { l_fresh : borrow_id; abs_id : abs_id }
      (** Matches [JrJoinMutBorrows]: the freshness premise is
          [Ω_i.loanIdFresh l_fresh ∧ Ω_i.absIdFresh abs_id]. *)
  | JedBottomOther of abs_id
      (** Matches [JrJoinBottomOther abs]: the abs must be live in
          [Ω_i.abs]; carry the absId so the Lean side can check
          registry presence. *)
  | JedOtherBottom of abs_id
      (** Mirror of [JedBottomOther]. *)
[@@deriving show]

(** [M9.6 — Option C] One entry of [EvJoin.witnesses].

    [M10.x.0 — cert v6] Carries an additional [je_delta : cert_join_entry_delta]
    witness. Redundant by construction with [je_rule] (the constructor
    names are parallel), but the redundancy lets the Lean replayer
    perform the chain fold without case-matching on [cert_join_rule]
    from outside [JoinLemmas]. *)
type cert_join_entry = {
  je_local : local_id;
  je_rule : cert_join_rule;
  je_delta : cert_join_entry_delta;
}
[@@deriving show]

(** [M10.x.0 — cert v6] Reference to a statement in the cert's embedded
    LLBC body tree. [fun_id] indexes into the cert's
    [cc_llbc_program.fun_decls] array; [body_path] is the per-sub-statement
    path from the function body's root (e.g. [[0; 2; 1]] = then-branch
    of stmt 0, nested stmt 2, sub-stmt 1).

    Used by [fun_cert.fc_stmt_refs] as a per-event back-pointer so
    Phase-E2's [replayFun_event_induct] can interleave events with the
    LLBC body tree rather than the flat event list. Not load-bearing
    for any axiom drop in the v6 campaign — landed in M10.x.0 as
    schema plumbing alongside [ri_holder_local] and
    [cert_join_entry_delta] so the schema bump only happens once. *)
type cert_stmt_ref = {
  sr_fun_id : int;
  sr_body_path : int array;
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
      kind_hint : cert_mut_borrow_kind;
          (** [M9.6 — Option C] Rule-choice hint subsuming the
              M9.5w (Deref-projection ⇒ reborrow-class) and M9.5aa
              (in-loop ⇒ lazyExpand) pragmatic inferences. Defaults
              to [MbkDirect] under fmt_version 2 until commit #4
              wires the emitter; the Lean strict path falls back to
              the M9.5w/aa inference while the hint is the default. *)
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
  | EvBinop of {
      op : string;
      lhs : cert_sym_expr;
      rhs : cert_sym_expr;
      dst : cert_place;
    }
      (** [M10] An LLBC [Rvalue.BinaryOp] reduction.

          [op] is a flat tag: arithmetic ops carry their overflow mode
          baked in ([AddPanic] / [AddWrap] / [AddUB]) so the Lean side
          can match on a single string rather than a nested algebraic
          shape. Non-arithmetic ops use the bare constructor name
          ([BitXor], [Eq], [Lt], ...). *)
  (* === Reborrows + nested borrows (M9) === *)
  | EvReborrow of {
      child : borrow_id;
      parent : borrow_id;
      place : cert_place;
      parent_live : bool;
      parent_abs : abs_id option;
          (** [M9.6 — Option C] Default [false] / [None] under
              fmt_version 2 until commit #5. When [parent_live] is
              true, the Lean strict path requires
              [SymState.loans.contains parent]; while it is false
              the [stepReborrow] fallback pre-adds the parent as a
              [.reborrow] loan if missing. *)
    }
  (* === Function calls + abstractions (M10) === *)
  | EvCall of {
      fn : fun_decl_id;
      fn_name : string;
          (** Pretty-printed qualified name of the callee, e.g.
              [core::num::u32::wrapping_add]. Used by the Lean
              translator to emit the right surface call without
              needing a builtin-id lookup table. *)
      call_id : fun_call_id;
      args : cert_sym_expr list;
      dst : cert_place;
      region_abs : abs_id list;
      abs_sig : cert_abs_shape list;
          (** [M9.6 — Option C] One [cert_abs_shape] per freshened
              region abstraction (parallel to [region_abs]).
              Encodes the paper's [A_in(ρ)] content. Defaults to
              [[]] under fmt_version 2 until commit #7. *)
    }
  | EvEndAbs of {
      abs : abs_id;
      final_values : cert_sym_expr list;
      released_loans : borrow_id list;
          (** [M9.5s] The loan ids whose lifetime ends implicitly here:
              for each [AMutBorrow (_, bid, _)] the abstraction held,
              [end_abs_borrows] drains it (turning the borrow into
              [AEndedMutBorrow] and [give_back_value]'ing the freshly
              generated symbolic into the outer-context loan slot)
              without emitting a paired [EvEndBorrow]. Listing those
              ids here lets the Lean replayer drop them from
              [SymState.loans] and [TC.liveLoans], so the
              "function ended with live borrow(s)" post-condition
              passes for the paper.rs [call_choose] pattern (input
              borrows that flowed into the call's abstraction). *)
      token_clear_locals : local_id list;
          (** [M9.6 — Option C] Locals whose [mutLoan] token must be
              cleared when this abstraction ends. Defaults to [[]]
              under fmt_version 2 until commit #8 — the Lean side
              falls back to today's scan-env behaviour while empty. *)
    }
  | EvSymExpandMutBorrow of {
      sv_id : symbolic_value_id;
      bid : borrow_id;
      inner_sv : symbolic_value_id;
      parent_abs : abs_id option;
      subst_locals : local_id list;
      subst_loans : borrow_id list;
          (** [M9.6 — Option C] Eliminate the M9.5r env-scan:
              [parent_abs] names the abstraction that owns the
              expanded borrow, [subst_locals] / [subst_loans] list
              every binding the [replace_symbolic_values] visitor
              touched. Defaults to [None] / [[]] / [[]] under
              fmt_version 2 until commit #6. *)
    }
      (** [M9.5r] The OCaml interpreter just expanded a symbolic value
          of [&mut T] type into a concrete mutable borrow. This is the
          lazy-borrow-creation moment: when a symbolic [&mut T] (e.g.
          a function-call return value, or a [&mut] parameter) gets
          dereferenced for the first time, [expand_symbolic_value_borrow]
          mints a fresh [bid] and inner symbolic value [inner_sv], then
          substitutes [sv_id ↦ SeMutRef(bid, inner_sv)] throughout the
          context.

          The Lean replayer uses this event to (a) walk every local /
          loan-given holding [.sym sv_id] and replace with [.mutLoan bid],
          (b) register loan [bid] in [SymState.loans] with [given := .sym
          inner_sv]. Without this event, a subsequent in-body
          [EvEndBorrow loan=bid] (paper.rs [test_choose] pattern) fails
          because the Lean side has no record of [bid] being live. *)
  (* === Joins + loops (M11+) === *)
  | EvJoin of {
      left : cert_state_summary;
      right : cert_state_summary;
      result : cert_state_summary;
      witnesses : cert_join_entry list;
          (** [M9.6 — Option C] Per-result-env-local Fig.-11 rule
              witness. Defaults to [[]] under fmt_version 2 until
              commits #10/#11; while empty the Lean checker uses
              the pragmatic [symExprBeq + isFreshSym] shortcut. *)
    }
  | EvLoopInv of {
      loop_id : loop_id;
      invariant : cert_state_summary;
      loan_registry : (borrow_id * abs_id) list;
          (** [M9.6 — Option C] [(borrow_id, parent_abs_id)] pairs
              from [compute_loop_entry_fixed_point]. Defaults to
              [[]] under fmt_version 2 until commit #9; while empty
              the Lean side falls back to the M9.5z scan of
              [invariant.env] for [SymMutBorrowTok n]. *)
    }
      (** [M12.0/M12.1] Emitted once per syntactic loop, immediately
          before the loop's *synthesized* body events. The
          [invariant] field carries the fixed-point's state summary
          (the per-local symbolic values at loop entry).

          M12.1 changed the placement: this event used to fire right
          after [compute_loop_entry_fixed_point], but the speculative
          body evaluations the fixed-point computation performed
          were *also* leaking into the trace. M12.1's OCaml
          restructuring suppresses those speculative emissions (see
          [Contexts.ctx_with_cert_events_suppressed]) and moves the
          [EvLoopInv] emission to right before the canonical body
          (synthesized once from [fp_ctx]), so the cert reads as

            [pre-loop events] [EvLoopInv] [body events] [EvLoopEnd]
              [post-loop events].

          The Lean translator (M12.1's T-Loop-Fixpoint walker) uses
          [EvLoopInv] as the "begin loop body" marker and
          [EvLoopEnd] as the closer. *)
  | EvLoopEnd of { loop_id : loop_id }
      (** [M12.1] Emitted immediately after the loop's synthesized
          body events. Paired with the [EvLoopInv] for the same
          [loop_id]: the events between the two form the body the
          Lean translator extracts into a [<fn>_loop.body] decl. *)
  | EvMatchArm of {
      scrutinee : cert_sym_expr;
      adt_id : int;
      variant_id : int;
      variant_name : string;
    }
      (** [M9.5d] Marks the start of one arm of a [match] on a
          symbolic ADT scrutinee. Emitted once per arm by the OCaml
          [Match] case in [InterpStatements.eval_switch] right
          after the symbolic-value expansion and right before
          evaluating the arm's body.

          The Lean translator collects consecutive [EvMatchArm]
          events with the same [scrutinee] symbolic-value id (and
          their interleaved per-arm body events) into a single
          [PExpr.match] expression. The closing of the match is
          either an [EvJoin] (when the arms share a continuation)
          or simply the end of each arm via [EvReturn] (the
          all-arms-return shape, like our [flip] fixture). *)
[@@deriving show]

(** A per-function trace.

    [M9.7o-E5b] The flat [fc_signature : cert_signature] field was
    deleted once the structured [LlbcProgram.fun_decls[k].signature]
    became the sole source of typed-signature info. The Lean checker
    pairs each [fun_cert] with its matching [LlbcFunDecl] by [fc_fn_id]
    and reads the structured signature from there. *)
type fun_cert = {
  fc_fn_id : fun_decl_id;
  fc_fn_name : string;  (** Pretty name; not load-bearing for the checker. *)
  fc_source_span : cert_source_span option;
      (** Source-code span for the per-function docstring in the
          emitted Lean. [None] for synthetic/built-in items. *)
  fc_events : event list;
  fc_final_state : cert_state_summary;
  fc_pretty_name : string option;
      (** [M9.5l] Standard-Aeneas Lean name for the function. Set for
          trait-impl method bodies (e.g.
          [Tag.Insts.Traits_basicNumeric.value]), which would
          otherwise sanitize from the Charon [{...}::value] form to
          an unwieldy expression. [None] for plain functions; the
          Lean checker falls back to sanitizing [fc_fn_name] in that
          case. *)
  fc_stmt_refs : cert_stmt_ref option list;
      (** [M10.x.0 — cert v6] Parallel array to [fc_events]: one entry
          per emitted event, in declaration order. Each entry names
          the cert's-LLBC-body sub-statement that produced the event,
          or [None] for synthetic events (loop-fixpoint markers,
          frame-pop end-borrows, etc.) that don't have a body-tree
          home.

          M10.x.0 ships this field as a length-matched array of
          [None] sentinels — the threading at the 23 emit sites is
          deferred to M10.x.0b. The shape is in place so the Lean
          parser already accepts the field; consumers (Phase E2's
          [replayFun_event_induct]) land alongside the population
          work later. *)
}
[@@deriving show]

(** [M9.7o-E5a] Top-level certificate.

    The flat ADT / trait decl mirrors (`cert_type_decl`,
    `cert_trait_decl`, `cert_trait_impl`, and their sub-types) were
    deleted once cert v2 was retired — the embedded
    {!cc_llbc_program} subtree is the sole source for those decls on
    the Lean side. *)
type crate_cert = {
  cc_fmt_version : int;
  cc_crate_hash : string;
      (** Hex SHA-256 of the LLBC JSON file's bytes; the Lean parser refuses
          mismatched (LLBC, cert) pairs. *)
  cc_functions : fun_cert list;
  cc_llbc_program : Yojson.Basic.t;
      (** [M9.7d] The structured LLBC subtree embedded under the
          top-level [llbc_program] key of cert v3. Populated by
          {!LlbcJson.crate_to_json} on the OCaml side and consumed
          by [AeneasCheck.Json.Parser.parseLlbcProgram] on the Lean
          side. The value is opaque to the OCaml-side cert pipeline:
          it is built once in [CertGen.generate_crate_cert] and
          shipped through [CertJson.json_crate_cert] verbatim. *)
}
[@@deriving show]

(** Current cert format version. Bump whenever the JSON shape changes in a
    backwards-incompatible way.

    [M9.6] v1 → v2 (Option C): adds optional hint fields to
    [EvMutBorrow], [EvReborrow], [EvCall], [EvEndAbs],
    [EvSymExpandMutBorrow], [EvJoin], [EvLoopInv]. The Lean parser
    accepts both versions; under v2 the hint fields are emitted
    (initially empty in commit #3, populated progressively across
    commits #4-#11).

    [M9.7d] v2 → v3: embeds the structured Charon LLBC subtree under
    the new top-level [llbc_program] key. Populated by
    {!LlbcJson.crate_to_json} and consumed by
    [AeneasCheck.Json.Parser.parseLlbcProgram]. Cert-v3 files keep
    all v2 fields verbatim; the Lean parser also tolerates v3 certs
    where [llbc_program] is missing (it falls back to
    [LlbcProgram.empty]).

    [M9.8] v3 → v4: [JrJoinMutBorrows] carries a full
    [cert_abs_shape] (id + parents + roles) for the fresh region
    abstraction created by Collapse-Dup-MutBorrow, replacing the
    bare [abs_id] of v3. Lets the Lean replayer install the abs
    in [absRegistry] from the cert and removes the "fresh abs"
    gap that blocked the C23 [stepJoin_witnessed_sound] general
    case (M10 soundness campaign, plan §11.1 #1 / §3.4 / §14.1).

    [M10.x.0] v4 → v6 (v5 skipped to avoid confusion with the
    earlier audit's one-field "cert v5 holderLocal" sketch). v6
    adds three orthogonal fields aimed at closing the 12 remaining
    [CertGen_faithful.*] axioms (audit
    [.claude/plans/robust-swinging-walrus.md] §"Cert v6 design"):
    - [cert_restore_info.ri_holder_local] — names the env local
      whose [mutLoan] token an [EvEndBorrow] restores (consumed in
      M10.x.9 to invert [endBorrow_direct_witness] axiom);
    - [cert_join_entry.je_delta] — per-witness paper-side
      [JoinEntryStep] premise (consumed in M10.x.10 to fold the
      [join] axiom into a derived [JoinChain]);
    - [fun_cert.fc_stmt_refs] — parallel-to-events array of LLBC
      body-tree back-pointers (Phase-E2 enabler, threaded across
      the 23 emit sites in a follow-up commit; M10.x.0 ships the
      shape with [None] sentinels).

    Back-compat: hard cut, mirroring M9.8's v3→v4 cutover. Cert
    v4 and v5 are rejected at parse time; regenerate with the
    current [aeneas -emit-cert]. *)
let cert_fmt_version : int = 6

(** Encode a Charon [binop] as a flat string tag. Arithmetic ops bake
    the overflow mode into the tag suffix ([Panic] / [UB] / [Wrap])
    so the Lean parser stays string-keyed. *)
let cert_binop_string : binop -> string =
  let mode_suffix : overflow_mode -> string = function
    | OPanic -> "Panic"
    | OUB -> "UB"
    | OWrap -> "Wrap"
  in
  function
  | BitXor -> "BitXor"
  | BitAnd -> "BitAnd"
  | BitOr -> "BitOr"
  | Eq -> "Eq" | Lt -> "Lt" | Le -> "Le"
  | Ne -> "Ne" | Ge -> "Ge" | Gt -> "Gt"
  | Add m -> "Add" ^ mode_suffix m
  | Sub m -> "Sub" ^ mode_suffix m
  | Mul m -> "Mul" ^ mode_suffix m
  | Div m -> "Div" ^ mode_suffix m
  | Rem m -> "Rem" ^ mode_suffix m
  | AddChecked -> "AddChecked"
  | SubChecked -> "SubChecked"
  | MulChecked -> "MulChecked"
  | Shl m -> "Shl" ^ mode_suffix m
  | Shr m -> "Shr" ^ mode_suffix m
  | Offset -> "Offset"
  | Cmp -> "Cmp"

(* M10.x (commit #11): the cert_*_of_* translation helpers
   ([cert_place_of_place], [cert_sym_expr_of_operand],
   [cert_sym_expr_of_tvalue], [cert_live_loans_of_tvalue],
   [cert_state_summary_of_env]) moved to [src/cert/CertObserver.ml]
   alongside the observer. [CertEvent.ml] is now a pure vocabulary
   file holding the cert-format type definitions, the on-wire
   format version, and the [cert_binop_string] tag map used by
   both the cert observer and the embedded LLBC JSON serializer. *)

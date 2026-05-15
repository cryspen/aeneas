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

(** The Rust signature of a cert function as seen by Aeneas, encoded as
    opaque-tagged type strings. The Lean checker uses [inputs] for the
    emitted parameter count; [output] is currently informational
    (downstream emitter still uses a placeholder return type until cert
    events carry per-place LLBC types in M9+). *)
type cert_signature = {
  csig_inputs : ty list;
  csig_output : ty;
  (** [M9.5i] The function's type-parameter names, in declaration order.
      For a generic Rust signature `fn get<T>(x: MyOption<T>, default: T) -> T`,
      this carries `["T"]`; for a monomorphic function it is empty. The
      Lean side renders these as implicit `{T : Type}` binders before the
      value parameters. *)
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

(** A per-function trace. *)
type fun_cert = {
  fc_fn_id : fun_decl_id;
  fc_fn_name : string;  (** Pretty name; not load-bearing for the checker. *)
  fc_signature : cert_signature;
      (** Function signature copied from [fun_decl.signature]. The
          checker uses [csig_inputs] to drive the emitted-Decl
          parameter count, replacing the M7 heuristic of inferring
          from max-local-seen-in-events. *)
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
}
[@@deriving show]

(** A struct field's projection-friendly summary, used by [cert_type_decl]
    to resolve [Field K] projections on the Lean side. Field names follow
    Charon's [field_name] convention: [None] for tuple-style positional
    fields (the Lean side falls back to [`field<K>`] in that case). *)
type cert_field = {
  cf_idx : int;
  cf_name : string option;
  cf_ty : ty;
}
[@@deriving show]

(** A variant of an enum-style ADT declaration. M9.5d only handles the
    C-style case (zero fields); payload-bearing variants will later
    populate [cv_fields]. *)
type cert_variant = {
  cv_id : int;
  cv_name : string;
  cv_fields : cert_field list;
}
[@@deriving show]

(** Kind of an ADT type declaration. M9.5b carries [Struct]; M9.5d adds
    [Enum] (with variants). Other shapes (unions, aliases) downgrade to
    [Opaque] so the Lean parser can tolerate them. *)
type cert_type_decl_kind =
  | CTDStruct of cert_field list
  | CTDEnum of cert_variant list
  | CTDOpaque
[@@deriving show]

(** A single ADT type declaration. [ctd_id] matches the OCaml
    [TypeDeclId.id] that appears inside [TAdt {id = TAdtId N; ...}]
    type strings in [cert_place.cp_ty] / [cert_signature]; the Lean side
    uses this to resolve [TAdtId N] to a struct name and field names.

    [ctd_name] is the bare ADT name (e.g. [Pair], not [reborrows::Pair]).
    The Lean translator surfaces it directly. *)
type cert_type_decl = {
  ctd_id : int;
  ctd_name : string;
  ctd_kind : cert_type_decl_kind;
  (** [M9.5i] The ADT's type-parameter names, in declaration order.
      For `enum MyOption<T> { … }`, this is `["T"]`; for a monomorphic
      struct (e.g. `Pair { fst: u32, snd: u32 }`) it is empty. The Lean
      side renders these as `(T : Type)` parameters on the
      `inductive` / `structure` declaration head, and variant payload
      types referencing `TVar (Free K)` resolve to the K-th entry of
      this list. *)
  ctd_type_params : string list;
  (** [M9.5l] True iff the struct uses tuple-style (positional) fields,
      OR is a unit struct (`struct Tag;` — zero-field tuple struct).
      The Lean side renders unit structs as `@[reducible] def Tag := Unit`
      instead of `structure Tag where`. Only meaningful for [CTDStruct];
      always false for [CTDEnum] / [CTDOpaque]. *)
  ctd_is_tuple_struct : bool;
  ctd_source_span : cert_source_span option;
  (** [M9.5l] Source span for the type decl's source-code definition.
      Used by the Lean emitter for the per-decl docstring. *)
  ctd_qualified_name : string;
  (** [M9.5n] Crate-prefixed qualified name (e.g.
      [core::option::Option], [alloc::alloc::Global],
      [issue_194_recursive_struct_projector::AVLNode]). The Lean side
      uses this to suppress emission of stdlib ADTs that already have
      a Lean equivalent ([Option], [Result], [Ordering], …), avoiding
      shadowing of the built-in [Option] in the emitted file's
      `open Aeneas Aeneas.Std` scope. *)
}
[@@deriving show]

(** [M9.5l] One method declared in a trait. The signature uses the same
    opaque-tagged form as [cert_signature] so the Lean side can recover
    parameter / return types via the existing [RawTy] parser. *)
type cert_trait_method = {
  ctm_name : string;
  ctm_signature : cert_signature;
  (** [M9.5o] True iff this method has a default implementation in
      the trait declaration. The Lean side emits these as
      `Trait.<method>.default` decls (taking the trait itself as a
      bound) alongside the trait. Default-method bodies still appear
      in [cc_functions] as standalone fun_certs, but the Lean side
      consumes the [ctm_has_default] flag here to know to emit them
      with the `.default` shape (and to suppress the duplicate
      standalone emission). *)
  ctm_has_default : bool;
}
[@@deriving show]

(** [M9.5l] A crate-level trait declaration. M9.5l only handles the
    minimal shape: no associated types, no associated constants, no
    parent traits, no const generics, no default methods. The trait
    may carry type parameters via [ctd_type_params]-style binders, but
    the M9.5l fixture only exercises the [Self : Type] case (no extra
    generics beyond Self).

    The Lean side renders this as `structure <Name> (Self : Type) where
    <method> : Self → Result <out>`. *)
type cert_trait_decl = {
  ctrd_id : int;
  ctrd_name : string;
  (** Bare trait name, e.g. [Numeric] for `traits_basic::Numeric`. *)
  ctrd_qualified_name : string;
  (** Crate-prefixed qualified name, used by the Lean docstring. *)
  ctrd_methods : cert_trait_method list;
  ctrd_source_span : cert_source_span option;
  (** Source span for the trait's `trait X { … }` block. *)
}
[@@deriving show]

(** [M9.5l] One method implemented in a trait impl. [ctim_fn_id] is the
    [fun_decl_id] of the concrete method body (which also appears as a
    standalone entry in [cc_functions]). [ctim_name] is the trait
    method's name (i.e., the name as it appears in the trait
    declaration), not the impl method's qualified name. *)
type cert_trait_impl_method = {
  ctim_name : string;
  ctim_fn_id : int;
}
[@@deriving show]

(** [M9.5l] A crate-level trait impl. [ctri_self_type_decl_id] is the
    [TypeDeclId] of the [Self] ADT (for the minimal M9.5l case where
    [Self] is a concrete user-declared ADT — generic / primitive
    self-types are out of scope). [ctri_pretty_name] is the
    standard-Aeneas Lean name for the impl, pre-computed on the OCaml
    side so the Lean checker does not have to reproduce the
    [ExtractBase.ctx_compute_trait_impl_name] machinery (which would
    require the full extraction context). For the M9.5l minimal case
    this resolves to [<SelfBare>.Insts.<CrateCapitalized><TraitBare>]. *)
type cert_trait_impl = {
  ctri_id : int;
  ctri_pretty_name : string;
  (** Lean name for the impl, e.g. [Tag.Insts.Traits_basicNumeric]. *)
  ctri_qualified_name : string;
  (** Crate-prefixed qualified name (`traits_basic::{traits_basic::Numeric
      for traits_basic::Tag}`) used by the Lean docstring. *)
  ctri_trait_decl_id : int;
  ctri_self_type_decl_id : int option;
  (** [None] when [Self] is not a user-declared ADT. M9.5l only
      consumes the [Some] case. *)
  ctri_self_type_var : string option;
  (** [M9.5o] When the impl's [Self] is a type parameter rather than a
      concrete ADT, this carries its name (e.g. ["T"] for
      `impl<T: Trait1> Trait2 for T`). Both [ctri_self_type_decl_id]
      and [ctri_self_type_var] are [None] for impls whose Self is
      neither a known ADT nor a type variable (out of scope). *)
  ctri_type_params : string list;
  (** [M9.5o] Type-parameter names declared on the impl itself
      (i.e. the [T] in `impl<T: ...> ...`). Empty for monomorphic
      (concrete-Self) impls. *)
  ctri_trait_clauses : (string * int) list;
  (** [M9.5o] Trait obligations on the impl's type parameters; same
      shape as [csig_trait_clauses]. *)
  ctri_methods : cert_trait_impl_method list;
  ctri_source_span : cert_source_span option;
}
[@@deriving show]

(** Top-level certificate. *)
type crate_cert = {
  cc_fmt_version : int;
  cc_crate_hash : string;
      (** Hex SHA-256 of the LLBC JSON file's bytes; the Lean parser refuses
          mismatched (LLBC, cert) pairs. *)
  cc_type_decls : cert_type_decl list;
      (** [M9.5b] The crate's ADT type declarations, indexed by
          [TypeDeclId]. The cert is the only source of truth for type
          shape (the companion [llbc.json] is a stub); the Lean checker
          uses this to render [structure …] decls and to resolve
          [TAdtId N] references inside event places. *)
  cc_trait_decls : cert_trait_decl list;
      (** [M9.5l] The crate's trait declarations. Empty for crates with
          no traits; the Lean parser tolerates a missing
          [trait_decls] JSON key for backwards-compat with older
          certs. *)
  cc_trait_impls : cert_trait_impl list;
      (** [M9.5l] The crate's trait implementations. Empty for crates
          with no impls. *)
  cc_functions : fun_cert list;
}
[@@deriving show]

(** Current cert format version. Bump whenever the JSON shape changes in a
    backwards-incompatible way. *)
let cert_fmt_version : int = 1

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

(** Convert a Charon operand into a [cert_sym_expr]. Returns [None]
    when the operand references a global or when place flattening
    fails (out of the direct-borrow subset). *)
let cert_sym_expr_of_operand (op : operand) : cert_sym_expr option =
  match op with
  | Copy p ->
      (match cert_place_of_place p with
       | Some cp -> Some (SymCopy cp)
       | None -> None)
  | Move p ->
      (match cert_place_of_place p with
       | Some cp -> Some (SymMove cp)
       | None -> None)
  | Constant ce ->
      (match ce.kind with
       | CLiteral lit -> Some (SymLit lit)
       | _ -> None)

(** Best-effort flat summary of a [tvalue] as a [cert_sym_expr].

    Used by [EvJoin] to record what each local holds in each branch.
    The Lean side only consumes this for naming / disambiguation when
    translating an [if then else]; full structural fidelity is M12. *)
let rec cert_sym_expr_of_tvalue (v : tvalue) : cert_sym_expr option =
  match v.value with
  | VLiteral lit -> Some (SymLit lit)
  | VSymbolic sv -> Some (SymVal sv.sv_id)
  | VBorrow (VMutBorrow (bid, _)) -> Some (SymMutBorrowTok bid)
  | VBorrow (VSharedBorrow (bid, _) | VReservedMutBorrow (bid, _)) ->
      Some (SymMutBorrowTok bid)
  | VLoan (VMutLoan bid) -> Some (SymMutBorrowTok bid)
  | VLoan (VSharedLoan (_, v')) -> cert_sym_expr_of_tvalue v'
  | VAdt _ | VBottom -> None

(** Collect live loan ids (mut + shared) visible in a [tvalue]. *)
let cert_live_loans_of_tvalue (v : tvalue) : borrow_id list =
  let acc = ref [] in
  let visitor =
    object
      inherit [_] iter_tvalue as super
      method! visit_VMutLoan env bid =
        acc := bid :: !acc;
        super#visit_VMutLoan env bid
      method! visit_VSharedLoan env bid v =
        acc := bid :: !acc;
        super#visit_VSharedLoan env bid v
    end
  in
  visitor#visit_tvalue () v;
  List.rev !acc

(** Build a [cert_state_summary] from an eval ctx's [env].

    [cs_env]: one entry per real (non-dummy) variable binding, mapping
    its local id to a best-effort [cert_sym_expr]. Bindings whose value
    cannot be flattened (e.g. ADTs or [⊥]) are dropped from the summary
    — the Lean side treats absence as "no observation," which is
    sufficient for M11's pragmatic ≤ check.

    [cs_live_loans]: every distinct mut/shared loan id appearing in
    bindings or abstractions. We don't dedup across the whole context
    (M11.0 doesn't need set semantics); the Lean side normalises if it
    cares.

    Walks the env directly rather than through visitors because we want
    to filter by [BVar] / [EAbs] separately. *)
let cert_state_summary_of_env (env : env) : cert_state_summary =
  let cs_env = ref [] in
  let cs_live_loans = ref [] in
  let visit_value v =
    cs_live_loans := List.rev_append (cert_live_loans_of_tvalue v) !cs_live_loans
  in
  List.iter
    (fun (e : env_elem) ->
      match e with
      | EBinding (BVar bv, v) ->
          (match cert_sym_expr_of_tvalue v with
           | Some se -> cs_env := (bv.index, se) :: !cs_env
           | None -> ());
          visit_value v
      | EBinding (BDummy _, v) -> visit_value v
      | EAbs abs ->
          List.iter
            (fun (av : tavalue) ->
              (* Cheap fallback: look for loan tokens inside the avalue
                 by piggy-backing on tvalue scanning where possible.
                 Visitors over [tavalue] are heavier; for M11 we keep
                 this approximate. *)
              ignore av)
            abs.avalues
      | EFrame -> ())
    env;
  let dedup_int_list xs =
    let seen = Hashtbl.create 8 in
    List.filter
      (fun x ->
        let k = BorrowId.to_int x in
        if Hashtbl.mem seen k then false
        else (Hashtbl.add seen k (); true))
      xs
  in
  {
    cs_env = List.rev !cs_env;
    cs_live_loans = dedup_int_list (List.rev !cs_live_loans);
  }

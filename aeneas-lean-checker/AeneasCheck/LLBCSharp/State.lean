import Std.Data.HashMap
import AeneasCheck.LLBCSharp.Values

/-!
LLBC# symbolic state — the executable mirror of OCaml's `eval_ctx`.

For the direct-borrow subset we track:
* per-local symbolic values (the `env`),
* the set of live mut-borrows + the symbolic value they restore upon
  ending (the `loans` map).

`SymState.empty` initializes everything to bottom; `Replay.lean`
populates locals from the function signature's input symbolic values.
-/

namespace AeneasCheck.LLBCSharp

open AeneasCheck.Raw

/-- How a loan was created. Affects how `endBorrow` restores state:
    a direct mut borrow replaces the borrowed local with a `mutLoan`
    token that the end must clear; a reborrow leaves the original
    parent's local untouched, so the end has no token to restore.
    M9.5r: `lazyExpand` loans come from EvSymExpandMutBorrow — they
    park a `mutLoan` token in the dst local (so end-borrow restores
    like `.direct`) but their lifetime is owned by the function's
    region abstraction (so they're allowed to leak past function
    exit, like `.reborrow`). -/
inductive LoanKind
  | direct
  | shared
  | reborrow
  | lazyExpand
  deriving Repr, BEq, Inhabited

/-- Info recorded for each live mut borrow: the inner symbolic value
    that flows back to the loan side upon `endBorrow`, and the loan
    kind so the end-borrow rule knows whether to scan for a `mutLoan`
    token in env. -/
structure LoanInfo where
  given : Val
  kind : LoanKind := .direct
  deriving Inhabited

structure SymState where
  /-- Per-local current value. -/
  env : Std.HashMap Nat Val
  /-- Active mut borrows. -/
  loans : Std.HashMap Nat LoanInfo
  /-- Number of locals declared in the current function. -/
  numLocals : Nat
  /-- M9.6 (Option C, plan §4.1.8): registry of region-abstraction
      shapes populated by `EvCall` (`absSig` hint, commit #7
      source) and consumed by `EvEndAbs` to validate that the
      released loans match the abstraction's recorded MutBorrow /
      MutLoan roles. Keys are abstraction ids; values are the
      paper-`A_in(ρ)`-content [AbsShape]. Empty until the first
      EvCall with non-empty `absSig` is processed. -/
  absRegistry : Std.HashMap Nat AbsShape := {}
  /-- M10.1g (soundness side): monotone high-water-mark for the loan
      ids ever allocated, regardless of whether they're still live.
      `addLoan b ...` raises this past `b`; `takeLoan` / `loans.erase`
      do *not* touch it. The replayer's checker logic never reads this
      field — it exists purely so the soundness-side `concretise`
      can mirror the paper's monotone `freshness.nextLoanId` (which
      `LStep.endBorrow_*` leaves unchanged even though the replayer
      erases the loan id). -/
  loanIdHwm : Nat := 0
  /-- M10.1i (soundness side): monotone high-water-mark for the
      abstraction ids ever installed, regardless of whether the
      entry is still in `absRegistry`. `stepCall`'s `addAbsShape`
      fold raises this past each `shape.absId`; `stepEndAbs`'s
      `absRegistry.erase` does *not* touch it. As with `loanIdHwm`,
      the replayer's checker logic never reads this field — it
      exists purely so the soundness-side `concretise` can mirror
      the paper's monotone `freshness.nextAbsId` (which
      `LStep.endAbs` leaves unchanged even though the replayer
      erases the registry entry). -/
  absIdHwm : Nat := 0
  deriving Inhabited

namespace SymState

def empty (numLocals : Nat) : SymState := {
  env := {}, loans := {}, numLocals, absRegistry := {}
}

/-- Lookup a local's current value; missing locals are `bottom`. -/
def getLocal (st : SymState) (l : Nat) : Val :=
  st.env.getD l .bottom

def setLocal (st : SymState) (l : Nat) (v : Val) : SymState :=
  { st with env := st.env.insert l v }

def hasLoan (st : SymState) (b : Nat) : Bool :=
  st.loans.contains b

def addLoan (st : SymState) (b : Nat) (inner : Val)
    (kind : LoanKind := .direct) : SymState :=
  { st with
      loans := st.loans.insert b { given := inner, kind }
      loanIdHwm := max st.loanIdHwm (b + 1) }

def takeLoan (st : SymState) (b : Nat) : Option (LoanInfo × SymState) :=
  match st.loans[b]? with
  | none => none
  | some li => some (li, { st with loans := st.loans.erase b })

/-- M10.1i (soundness side): install one `AbsShape` into
    `absRegistry`, bumping `absIdHwm` past `shape.absId`. The fold
    step `stepCall` uses to process its `absSig` array; factored out
    so the soundness-side commute lemma has a single mutator to
    target. The replayer's checker logic relies on `absRegistry`
    only — `absIdHwm` is the soundness-mirror field. -/
def addAbsShape (st : SymState) (shape : AbsShape) : SymState :=
  { st with
      absRegistry := st.absRegistry.insert shape.absId shape
      absIdHwm := max st.absIdHwm (shape.absId + 1) }

/-- M10.1i (soundness side): remove an `AbsShape` from
    `absRegistry`. Used by `stepEndAbs` to drop the closing
    abstraction's registry entry; mirrors the paper's
    `LLBCState.removeAbs`. Does *not* touch `absIdHwm` — the
    high-water-mark stays monotone so the soundness-side
    `concretise.freshness.nextAbsId` matches the paper's
    `LStep.endAbs`-leaves-freshness-unchanged contract. -/
def removeAbsShape (st : SymState) (absId : Nat) : SymState :=
  { st with absRegistry := st.absRegistry.erase absId }

end SymState

/-- M10.x.6: erase one loan id from `st.loans` only when present.
    Factored out of `stepEndAbs`'s `released` loop so the soundness
    proof can use `Array.foldl_induction` directly. `concretise` is
    insensitive to `loans` (only `env`/`absRegistry`/HWMs are read),
    so this is a `concretise`-no-op. -/
def loansEraseIfPresent (st : SymState) (loan : Nat) : SymState :=
  if st.loans.contains loan then { st with loans := st.loans.erase loan } else st

/-- M10.x.6: clear one local's `.mutLoan _` token to `.bottom`. The
    rewrite is conditional on the slot actually holding a `mutLoan`
    token — non-mutLoan slots are left untouched, including unbound
    locals (silent skip). Factored out of `stepEndAbs` for the same
    reason as `loansEraseIfPresent`. -/
def tokenClearOne (env : Std.HashMap Nat Val) (l : Nat) :
    Std.HashMap Nat Val :=
  match env[l]? with
  | some (.mutLoan _) => env.insert l .bottom
  | _ => env

/-- M10.x.7: register one `(loan_id, parent_abs)` entry from
    `EvLoopInv.loanRegistry`. Skips if the loan is already live
    (matches the OCaml interp's loop-fixpoint replay discipline:
    re-entering a loop body should be a no-op on already-tracked
    loans). The `_parentAbs` is recorded only by `Typecheck/
    Consistency.lean`'s `seenAbs`; the replayer ignores it here. -/
def loopInvRegisterLoan (st : SymState) (entry : Nat × Nat) : SymState :=
  let (b, _parentAbs) := entry
  if st.loans.contains b then st else st.addLoan b .bottom .reborrow

/-- M10.x.8: one substLocals rewrite step. If `env[l] = .sym svId`,
    overwrite to `.mutLoan bid`; otherwise unchanged. Factored out
    of `stepSymExpandMutBorrow` for the M10.x.8 commute lemma.

    The paper-side mirror is `LLBCState.substLocalOne svId bid Ω l`. -/
def substLocalsOne (svId bid : Nat) (env : Std.HashMap Nat Val) (l : Nat) :
    Std.HashMap Nat Val :=
  match env[l]? with
  | some (.sym k) => if k = svId then env.insert l (.mutLoan bid) else env
  | _ => env

/-- M10.x.9: find the first env local that holds a `mutLoan loan`
    token (in `Std.HashMap.toList` iteration order). Used as the
    env-walk fallback when `restore.holderLocal` is `none` (cf.
    `cert v6`'s `holderLocal` emit-site at `InterpBorrows.ml:1050`,
    which is itself an env walk on the OCaml side). The replayer's
    `stepEndBorrow` `.direct | .lazyExpand` arm uses this as a
    single-shot replacement for the previous `for+mut` env loop;
    the LoanTokenInvariant guarantees at most one local holds a
    given `mutLoan` token, so single-shot matches the previous
    multi-update behaviour. -/
def findHolder (st : SymState) (loan : Nat) : Option Nat :=
  (st.env.toList.find? (fun p =>
    match p.2 with
    | .mutLoan b => b == loan
    | _ => false)).map Prod.fst

/-- M10.x.8: one substLoans rewrite step. If `loans[b].given = .sym svId`,
    overwrite to `.mutLoan bid`; otherwise unchanged. Concretise-no-op
    because `concretise` does not read `loans`; kept symmetric to
    `substLocalsOne` for clean factoring. -/
def substLoansOne (svId bid : Nat) (loans : Std.HashMap Nat LoanInfo) (b : Nat) :
    Std.HashMap Nat LoanInfo :=
  match loans[b]? with
  | some li =>
    match li.given with
    | .sym k =>
      if k = svId then loans.insert b { li with given := .mutLoan bid } else loans
    | _ => loans
  | none => loans

end AeneasCheck.LLBCSharp

import AeneasCheck.Raw.CertEvent
import AeneasCheck.Raw.LLBCProgram

/-!
LLBC# symbolic values and helpers.

The Lean replayer carries a *symbolic* state — concrete values are
rare (only inside literal-valued locals). The state mirrors LLBC#'s
abstraction modulo what the direct-borrow subset uses:

* `SymVal` — bare symbolic identifier (matches `Raw.SymExpr.symVal`).
* `Lit` — a literal constant.
* `MutLoan b` — a value held as the loan side of a mut borrow `b`.
* `Bottom` — moved or uninitialized.

The full LLBC# value algebra (shared loans, region projections,
abstractions) lands in M10+.
-/

namespace AeneasCheck.LLBCSharp

open AeneasCheck.Raw

/-- A symbolic value carried by a local or by a borrow body. -/
inductive Val
  | sym (id : Nat)
  | lit (l : Lit)
  | mutLoan (borrow : Nat)
  | mutBorrow (borrow : Nat) (inner : Val)
  | bottom
  deriving Repr, Inhabited

/-- Pretty-print for diagnostics. -/
partial def Val.toString : Val → String
  | .sym n => s!"s{n}"
  | .lit (.scalar _ v) => s!"{v}"
  | .lit (.bool b) => s!"{b}"
  | .lit _ => "<lit>"
  | .mutLoan b => s!"mut-loan({b})"
  | .mutBorrow b inner => s!"mut-borrow({b}, {inner.toString})"
  | .bottom => "⊥"

instance : ToString Val := ⟨Val.toString⟩

end AeneasCheck.LLBCSharp

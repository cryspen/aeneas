import AeneasCheck.Typecheck.Stmts

/-!
Top-level typechecker entry. Glues per-function checking over the
whole crate cert.

We approximate `numLocals` by scanning the cert events for the maximum
local id referenced — this is sound for M5 because cert places never
reference locals beyond what the function actually declares; M6 swaps
this for a count derived from the LLBC function signature.
-/

namespace AeneasCheck.Typecheck

open AeneasCheck.Raw

private def placeMaxLocal (p : Place) : Nat := p.local_

private def symExprMaxLocal : SymExpr → Nat
  | .symCopy p | .symMove p => placeMaxLocal p
  | _ => 0

private def restoreMaxLocal (r : RestoreInfo) : Nat :=
  symExprMaxLocal r.givenBack

private def eventMaxLocal : Event → Nat
  | .mutBorrow _ p _ _ => placeMaxLocal p
  | .sharedBorrow _ _ p _ => placeMaxLocal p
  | .assign dst rhs => max (placeMaxLocal dst) (symExprMaxLocal rhs)
  | .move s d | .copy s d => max (placeMaxLocal s) (placeMaxLocal d)
  | .endBorrow _ r => restoreMaxLocal r
  | .assert c _ => symExprMaxLocal c
  | .binop _ l r d =>
    max (max (symExprMaxLocal l) (symExprMaxLocal r)) (placeMaxLocal d)
  | .reborrow _ _ p _ _ => placeMaxLocal p
  | .call _ _ _ args dst _ _ =>
    let argMax := args.foldl (fun a e => max a (symExprMaxLocal e)) 0
    max argMax (placeMaxLocal dst)
  | .endAbs _ vs _ _ => vs.foldl (fun a e => max a (symExprMaxLocal e)) 0
  | .proj _ p _ => placeMaxLocal p
  | _ => 0

def inferNumLocals (events : Array Event) : Nat :=
  let m := events.foldl (fun a ev => max a (eventMaxLocal ev)) 0
  m + 1

def checkFunCert (f : FunCert) : Except CheckErr Unit :=
  let numLocals := inferNumLocals f.events
  let env := FnEnv.empty f.fnId numLocals
  let work : TC Unit := do
    checkEvents f.events
    checkFnPost
  match work.run env with
  | .ok _ => .ok ()
  | .error e => .error e

def checkCrateCert (cc : CrateCert) : Except (List CheckErr) Unit := do
  let mut errs : List CheckErr := []
  for f in cc.functions do
    match checkFunCert f with
    | .ok _ => pure ()
    | .error e => errs := e :: errs
  if errs.isEmpty then .ok ()
  else .error errs.reverse

end AeneasCheck.Typecheck

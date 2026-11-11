/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Basic.Real.Basic
public meta import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public meta import Mathlib.Tactic.FieldSimp
public import CAS.Tactic.NonvanishingDischarger
public meta import CAS.Tactic.NonvanishingDischarger
public import CAS.Tactic.ProofCarrier
public meta import CAS.Tactic.ProofCarrier

/-!
# Polynomial consequences of equation hypotheses

Core `grobner` proves consequences of local polynomial equations over a commutative
ring. Explicit hints augment that context. For real equations, denominator clearing
adds polynomial consequences only with the original nonvanishing evidence.
Hypotheses are prepared on fresh copies, and failed attempts restore the tactic state.

## Main definitions

* `Method`: the operation that closed the goal, `grobner` or guarded denominator clearing.
* `attempt`: the polynomial consequence search on the main goal, with equation hints.

## Implementation notes

We do not compute Gröbner bases here. The search and its proof are those of core `grobner`
(declared in Lean's `Init/Grind/Tactics.lean`), which runs `grind` with only its commutative-ring
solver (`Lean/Meta/Tactic/Grind/Arith/CommRing/`), and the kernel checks the proof term it
builds. Our part is the preparation. Over `ℝ` we clear the denominators of the goal with
`field_simp (disch := cas_nonvanishing)` before any hint enters the context, since a hint could
become a looping simp rule; then we add the hints and the rational equations of the context as
fresh copies and clear their denominators the same way. A goal that denominator clearing alone
closes reports `Method.denominatorClearing`. The callers are the polynomial-equations stage of
`cas`, with the equation hints of `cas using`, and the elementary rewrites, with the circle
equations `sin a ^ 2 + cos a ^ 2 = 1`.
-/

public meta section

namespace CAS.Tactic.PolynomialEquations

open Lean Meta Elab Tactic

/-- The operation that completed the original goal. -/
inductive Method where
  /-- Core `grobner` closed the remaining polynomial goals. -/
  | grobner
  /-- Guarded denominator simplification closed the goal without calling `grobner`. -/
  | denominatorClearing
  deriving BEq, Repr

private def containsDivision (expression : Expr) : Bool :=
  (expression.find? fun e ↦
    e.isAppOf ``HDiv.hDiv || e.isAppOf ``Inv.inv).isSome

private def prepareDenominators (action : TSyntax `tactic) : TacticM Unit := do
  let saved ← saveState
  tryCatchRuntimeEx (evalTactic action) fun error ↦ do
    saved.restore
    if error.isRuntime then
      throw error

private def addEquation (proof : Expr) : TacticM (TSyntax `ident) := do
  let name ← mkFreshUserName `hcasPolynomialEquation
  let (_, goal) ← (← getMainGoal).note name proof
  replaceMainGoal [goal]
  return mkIdent name

/--
Try polynomial consequence search over a commutative ring, with separately elaborated
equation hints. Hints augment the local context; they are not an `only` list.

Real denominators are cleared on the goal and fresh equation copies using
`cas_nonvanishing`. Unproved nonvanishing conditions are never assumed. The successful
result contains complete evidence for the original target and identifies the operation
that closed it. Failure restores the whole tactic state and retains the exception.
-/
def attempt (equations : Array (TSyntax `term)) :
    TacticM (Except Exception (ProofCarrier.ClosedMainGoal Method)) :=
  ProofCarrier.attemptClosingMainGoal "CAS polynomial equations" <| focus do
    let (isReal, hints, rationalHypotheses) ← withMainContext do
      let target ← whnf (← instantiateMVars (← getMainTarget))
      let some (carrier, _, _) := target.eq?
        | throwError "CAS polynomial equations expects an equality over a commutative ring"
      discard <| synthInstance (← mkAppM ``CommRing #[carrier])
      let isReal ← ProofCarrier.isDefEqReadOnly carrier (mkConst ``Real)
      let mut hints := #[]
      for equation in equations do
        let proof ← Term.withoutErrToSorry <| Term.elabTerm equation none
        let proof ← ProofCarrier.checkCompletedProof "CAS polynomial equation hint" proof
        let type ← whnf (← inferType proof)
        let some (hintCarrier, _, _) := type.eq?
          | throwErrorAt equation "expected an equation hint, got{indentExpr type}"
        unless ← ProofCarrier.isDefEqReadOnly hintCarrier carrier do
          throwErrorAt equation "expected an equation over{indentExpr carrier}"
        hints := hints.push proof
      let mut rationalHypotheses := #[]
      if isReal then
        for declaration in ← getLCtx do
          unless declaration.isImplementationDetail do
            let type ← whnf (← instantiateMVars declaration.type)
            if let some (hypCarrier, _, _) := type.eq? then
              if containsDivision type &&
                  (← ProofCarrier.isDefEqReadOnly hypCarrier carrier) then
                let proof := mkFVar declaration.fvarId
                unless hints.contains proof do
                  rationalHypotheses := rationalHypotheses.push proof
      return (isReal, hints, rationalHypotheses)
    -- Prepare the goal before adding equations that could become looping simp rules.
    if isReal then
      prepareDenominators (← `(tactic| field_simp (disch := cas_nonvanishing)))
      if (← getGoals).isEmpty then
        return .denominatorClearing
    for proof in hints ++ rationalHypotheses do
      let hypothesis ← withMainContext <| addEquation proof
      if isReal && (← withMainContext <| containsDivision <$> inferType proof) then
        prepareDenominators
          (← `(tactic| field_simp (disch := cas_nonvanishing) at $hypothesis:ident))
        if (← getGoals).isEmpty then
          return .denominatorClearing
    withoutRecover <| evalTactic (← `(tactic| all_goals grobner))
    return .grobner

end CAS.Tactic.PolynomialEquations

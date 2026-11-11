/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Differential.Requirements
public import CAS.Tactic.SideConditions

/-!
# Reduction of checked-expression validity requirements

`validAtToRequirements`, `analyticSideConditionToRequirements` and `reduceValidityRequirements`
are the steps of the side-condition tactic `symbolic_assumptions` that make the individual
nonzero and positivity claims of a validity goal visible. A goal `expr.ValidAt ρ` or
`DiffExpr.AnalyticSideCondition ansatz x e` is replaced by the requirement collection that
implies it (`Verified.Expr.ValidityRequirements`, `DiffExpr.analyticRequirements`), and a goal
`requirements.Holds ρ` is evaluated to explicit lists while the environment `ρ` stays opaque.
They install no tactic syntax.

## Main definitions

* `validAtToRequirements`, `analyticSideConditionToRequirements`: replace a validity goal by its
  requirement collection.
* `reduceValidityRequirements`: evaluate the requirement collection in a `Holds` goal.

## Implementation notes

The first two steps apply the implications `Verified.Expr.ValidityRequirements.validAt_of_holds`
and `DiffExpr.analyticSideCondition_of_requirements`, so the goal they leave implies the original
one. `reduceValidityRequirements` is `reduceApplicationArgument` with the transport theorem
`Verified.Expr.ValidityRequirements.holds_of_eq`: a collection over a `Fin` index is computed by
the kernel, and its equality with the explicit lists is certified by `decide +kernel`; any other
argument is reduced at full transparency by the elaborator, and the goal is either `change`d or
transported along an `Eq.refl` proof that the kernel checks.
-/

public meta section

namespace CAS.Tactic

open Lean Elab Tactic Meta

/--
Evaluate the requirement collection in a goal `requirements.Holds ρ` while keeping the
environment `ρ` opaque. The returned goal states the same obligation for explicit lists.
-/
def reduceValidityRequirements (goal : MVarId) : MetaM MVarId :=
  reduceApplicationArgument goal ``Verified.Expr.ValidityRequirements.Holds 3 1
    ``Verified.Expr.ValidityRequirements.holds_of_eq
    "expected a ValidityRequirements.Holds goal"

/-- Apply the transport theorem to the goal and return the single hypothesis it leaves open. -/
private def applyTransport (goal : MVarId) (transport : Expr) : MetaM MVarId := do
  let goals ← goal.apply transport
  match goals with
  | [hypothesis] => return hypothesis
  | _ => throwError "the requirement transport theorem did not leave exactly one hypothesis"

/--
Replace a goal `expr.ValidAt ρ` by `(validityRequirements expr).Holds ρ`, the canonical
requirement collection that implies it.
-/
def validAtToRequirements (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity ``Verified.Expr.ValidAt 3 do
    throwError "expected a ValidAt goal"
  let args := target.getAppArgs
  applyTransport goal
    (← mkAppM ``Verified.Expr.ValidityRequirements.validAt_of_holds #[args[1]!, args[2]!])

/--
Replace a goal `DiffExpr.AnalyticSideCondition ansatz x e` by the requirement collection
`(DiffExpr.analyticRequirements ansatz e).Holds x` that implies it.
-/
def analyticSideConditionToRequirements (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity ``DiffExpr.AnalyticSideCondition 5 do
    throwError "expected an AnalyticSideCondition goal"
  let args := target.getAppArgs
  applyTransport goal
    (← mkAppM ``DiffExpr.analyticSideCondition_of_requirements #[args[2]!, args[3]!, args[4]!])

end CAS.Tactic

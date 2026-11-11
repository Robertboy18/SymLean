/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public meta import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import CAS.Tactic.RealDeriv
public meta import CAS.Tactic.RealDeriv

/-!
# Structural interval calculus from analytic hypotheses

Mathlib's interval integral is linear in its integrand under the appropriate integrability
hypotheses, and its endpoint derivative is the integrand when the hypotheses of the fundamental
theorem of calculus hold. These rules apply to opaque functions and retain their normed
codomains and actual measures. `close?` proves interval-integral goals with them alone: it does
not search for a primitive or reflect functions into scalar expressions, and a failed attempt
restores the goal.

## Implementation notes

The rules are Mathlib's, tried in this order: `intervalIntegral.integral_hasDerivAt_right` and
`intervalIntegral.integral_hasDerivAt_left` for a `HasDerivAt` goal; for an equality
`intervalIntegral.integral_add`, `intervalIntegral.integral_sub`,
`intervalIntegral.integral_neg`, `intervalIntegral.integral_smul`,
`IntervalIntegrable.integral_smul`, `intervalIntegral.integral_congr`,
`intervalIntegral.deriv_integral_right`, `intervalIntegral.deriv_integral_left`, and the
fundamental theorem `intervalIntegral.integral_eq_sub_of_hasDerivAt` with its variant
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`. Their analytic premises come from a
search of depth eight (`provePremise`) through the local hypotheses, the continuity of a
`ContinuousMap` in context, the evidence given with `using`, continuity read off smoothness
(`ContDiff.continuous` and its local forms), `fun_prop`, a supplied `HasDerivAt` family or
`RealDeriv.close`, and a few consequences such as `Continuous.intervalIntegrable`,
`ContinuousOn.intervalIntegrable` and `Continuous.stronglyMeasurableAtFilter`.
-/

public meta section

namespace CAS.Tactic.Integration.Structural

open Lean Meta Elab Tactic

/-- A completed structural proof and the Mathlib declarations used for its calculus steps. -/
structure Result where
  /-- The mathematical declarations selected by the structural route. -/
  theoremNames : Array Name
  /-- The completed proofs of the selected theorem's analytic premises, when required. -/
  analyticEvidence : Array Expr
  /-- The checked proof of the original main goal. -/
  proof : Expr

private def head (e : Expr) : Name :=
  match e.consumeMData.getAppFn with
  | .const name _ => name
  | _ => .anonymous

private def suppliedEvidence (hint? : Option (TSyntax `term)) : TacticM (Array Expr) := do
  let mut evidence := #[]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      if ← isProp decl.type then
        evidence := evidence.push (mkFVar decl.fvarId)
      else if head decl.type == ``ContinuousMap then
        evidence := evidence.push
          (← mkAppM ``ContinuousMap.continuous #[mkFVar decl.fvarId])
  if let some hint := hint? then
    let proof ← Term.withoutErrToSorry <| Term.elabTerm hint none
    let proof ← ProofCarrier.checkCompletedProof "structural integration side evidence" proof
    unless ← isProp (← inferType proof) do
      throwError "structural integration requires a proof as side evidence"
    evidence := evidence.push proof
  return evidence

-- Applying a supplied family may specialize its point and interval membership; arbitrary
-- local implications are not used as proof-search rules.
private def evidenceHead (type : Expr) : MetaM Name :=
  forallTelescope type fun _ body ↦ pure (head body)

private def continuityProjection? (target source : Expr) : Option Name :=
  match head target, head source with
  | ``Continuous, ``ContDiff => some ``ContDiff.continuous
  | ``ContinuousAt, ``ContDiffAt => some ``ContDiffAt.continuousAt
  | ``ContinuousOn, ``ContDiffOn => some ``ContDiffOn.continuousOn
  | _, _ => none

private def premiseRules (target : Expr) : Array Name :=
  match head target with
  | ``IntervalIntegrable =>
      #[``Continuous.intervalIntegrable, ``ContinuousOn.intervalIntegrable]
  | ``StronglyMeasurableAtFilter =>
      #[``Continuous.stronglyMeasurableAtFilter,
        ``MeasureTheory.AEStronglyMeasurable.stronglyMeasurableAtFilter,
        ``MeasureTheory.StronglyMeasurable.stronglyMeasurableAtFilter]
  | ``ContinuousAt => #[``Continuous.continuousAt]
  | ``ContinuousOn => #[``Continuous.continuousOn]
  | ``Continuous =>
      #[``Continuous.add, ``Continuous.sub, ``Continuous.neg,
        ``Continuous.mul, ``Continuous.smul]
  | _ => #[]

private def provePremise (evidence : Array Expr) (goal : MVarId) :
    (fuel : Nat) → TacticM (Array Name)
  | 0 => throwError "structural integration could not discharge an analytic premise"
  | fuel + 1 => goal.withContext do
      if ← goal.isAssigned then return #[]
      let target ← instantiateMVars (← goal.getType)
      if ← goal.assumptionCore then return #[]
      for proof in evidence do
        let saved ← saveState
        if ← isDefEq (← inferType proof) target then
          goal.assign proof
          return #[]
        saved.restore
        -- Starting from the supplied smoothness proof fixes its scalar field, normed
        -- structures, and order before asking for continuity.
        if let some theoremName := continuityProjection? target (← inferType proof) then
          let saved ← saveState
          try
            let continuous ← mkAppM theoremName #[proof]
            if ← isDefEq (← inferType continuous) target then
              goal.assign continuous
              return #[theoremName]
          catch error =>
            if error.isRuntime then throw error
          saved.restore
      if target.isForall then
        let (_, next) ← goal.intro1
        return ← provePremise evidence next fuel
      if #[``Continuous, ``ContinuousOn, ``ContinuousAt].contains (head target) then
        let saved ← saveState
        try
          let goals ← KernelReadBack.runTacticOnGoal goal (← `(tactic| fun_prop))
          if goals.isEmpty then return #[]
        catch error =>
          if error.isRuntime then throw error
        saved.restore
      if head target == ``HasDerivAt then
        for proof in evidence do
          if (← evidenceHead (← inferType proof)) == ``HasDerivAt then
            let saved ← saveState
            try
              let goals ← goal.apply proof
              let mut steps := #[]
              for subgoal in goals do
                steps := steps ++ (← provePremise evidence subgoal fuel)
              return steps
            catch error =>
              saved.restore
              if error.isRuntime then throw error
        let saved ← saveState
        let previousGoals ← getGoals
        try
          setGoals [goal]
          RealDeriv.close
          setGoals previousGoals
          return #[]
        catch error =>
          saved.restore
          if error.isRuntime then throw error
      for theoremName in premiseRules target do
        let saved ← saveState
        try
          let goals ← goal.applyConst theoremName
          let mut steps := #[theoremName]
          for subgoal in goals do
            steps := steps ++ (← provePremise evidence subgoal fuel)
          return steps
        catch error =>
          saved.restore
          if error.isRuntime then throw error
      throwError "structural integration needs analytic evidence for{indentExpr target}"

private def containsIntegral (target : Expr) : Bool :=
  target.getUsedConstants.contains ``intervalIntegral

private def rules (target : Expr) : Array Name :=
  if !containsIntegral target then #[]
  else if head target == ``HasDerivAt then
    #[``intervalIntegral.integral_hasDerivAt_right, ``intervalIntegral.integral_hasDerivAt_left]
  else if head target == ``Eq then
    #[``intervalIntegral.integral_add, ``intervalIntegral.integral_sub,
      ``intervalIntegral.integral_neg, ``intervalIntegral.integral_smul,
      ``IntervalIntegrable.integral_smul, ``intervalIntegral.integral_congr,
      ``intervalIntegral.deriv_integral_right, ``intervalIntegral.deriv_integral_left,
      ``intervalIntegral.integral_eq_sub_of_hasDerivAt,
      ``intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le]
  else #[]

/--
Close an interval calculus goal from actual analytic evidence.

Success closes exactly the original main goal and returns its completed proof. Refusal returns
`none` without changing the tactic state. Integral algebra retains the given measure; FTC
applications must unify with Mathlib's Lebesgue-measure theorem, including its instances.
-/
def close? (evidence? : Option (TSyntax `term) := none) : TacticM (Option Result) :=
  ProofCarrier.restoringStateOnNone <| withMainContext do
    let target ← zetaReduce (← instantiateMVars (← getMainTarget))
    let candidates := rules target
    if candidates.isEmpty then return none
    -- A contextual proof may need the certificate route's requirements type.
    let supplied? ← tryCatchRuntimeEx
      (some <$> suppliedEvidence evidence?)
      fun error ↦ do
        if error.isRuntime then throw error
        return none
    let some evidence := supplied? | return none
    for theoremName in candidates do
      let attempt ← ProofCarrier.attemptClosingMainGoal "structural interval calculus" do
        let goal ← getMainGoal
        let goals ← goal.applyConst theoremName
        let mut steps := #[theoremName]
        let mut analyticEvidence := #[]
        for subgoal in goals do
          steps := steps ++ (← provePremise evidence subgoal 8)
          let proof ← ProofCarrier.checkCompletedProof "structural analytic evidence"
            (mkMVar subgoal)
          analyticEvidence := analyticEvidence.push proof
        replaceMainGoal []
        return (steps, analyticEvidence)
      match attempt with
      | .ok closed =>
          return some {
            theoremNames := closed.value.1
            analyticEvidence := closed.value.2
            proof := closed.proof }
      | .error error => if error.isRuntime then throw error
    return none

end CAS.Tactic.Integration.Structural

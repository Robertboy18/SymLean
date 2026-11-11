/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ExactTactic
public import CAS.Tactic.Integration

/-!
# Theorem-facing symbolic integration

The integration route of `cas`. Importing this module registers it with `@[cas_route integral]`,
so `cas` proves a supported interval-integral or improper-integral identity from a checked
antiderivative, an improper one also together with the integrability of the integrand
(`IntegrableOn f D ∧ ∫ x in D, f x = v`), and `cas using h` takes the domain requirements from
`h`. On a goal of the shape
`∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x` the route first
applies Mathlib's `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt` and
proves its derivative and integrability premises from hypotheses, `HasDerivAt` facts, or checked
symbolic derivatives. The form `cas [integrate primitive := F]` checks a supplied primitive `F`
against the integrand and applies the fundamental theorem of calculus, with `using h` as above.

Each form closes the goal with a proof term or fails without changing the goal.

## Implementation notes

The work is done by `Tactic.Integration.close` of `CAS/Tactic/Integration.lean`, whose notes
describe the search, the certificate `IntegrationCheck.AntiderivativeCert` and the analytic
theorems. We register it and turn its result into the report of the route
(`Result.toRouteResult`): for each certificate the evidence holds the proof that the derivative
residual reaches zero and the proof of the domain requirements, and `Result.replay` writes the
tactic that proves the goal again (`exact` with a structural proof,
`cas [integrate primitive := F]`, `cas` or `cas using h`). For integration by parts we apply the
Mathlib theorem, close each derivative premise by `assumption`, `solve_by_elim` or
`Tactic.Integration.close` on the `HasDerivAt` goal, and each integrability premise by
`assumption` or continuity (`fun_prop`); when this fails, the whole goal goes to
`Tactic.Integration.close`. Integration by parts and the fundamental theorem of calculus are
Mathlib's. `CAS/ExactTactic.lean` does not import the antiderivative planner, which comes with
`CAS/Tactic/Integration.lean`.
-/

public meta section

namespace CAS.ExactTactic

open Lean Elab Tactic

/-- `cas [integrate primitive := F]` checks the supplied primitive `F` against the original
integrand and projects the checked identity through the interval fundamental theorem of
calculus. -/
syntax (name := casIntegratePrimitive) "[" &"integrate" &"primitive" " := " term
  (" using " term)? "]" : casArgs

private def orElseRestoring (primary fallback : TacticM Unit) : TacticM Unit := do
  let saved ← saveState
  try
    primary
  catch _ =>
    saved.restore
    fallback

private def closeDerivativeWithinAtPremise : TacticM Unit :=
  orElseRestoring
    (do evalTactic <| ← `(tactic| assumption))
    (do
      evalTactic <| ← `(tactic| intro x hx)
      orElseRestoring
        (evalTactic <| ← `(tactic| solve_by_elim))
        (do
          evalTactic <| ← `(tactic| apply HasDerivAt.hasDerivWithinAt)
          discard <| Tactic.Integration.close none))

private def closeIntervalIntegrablePremise : TacticM Unit :=
  orElseRestoring
    (do evalTactic <| ← `(tactic| assumption))
    (do
      evalTactic <| ← `(tactic| apply Continuous.intervalIntegrable)
      evalTactic <| ← `(tactic| fun_prop))

private def closeIntegrationByParts : TacticM Unit := do
  evalTactic <| ←
    `(tactic| apply intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt)
  closeDerivativeWithinAtPremise
  closeDerivativeWithinAtPremise
  closeIntervalIntegrablePremise
  closeIntervalIntegrablePremise

end CAS.ExactTactic

namespace CAS.Tactic.Integration

open Lean Meta

private def Result.replay (result : Result) : MetaM (TSyntax `tactic) := do
  if let some structural := result.structural? then
    let proof ← PrettyPrinter.delab structural.proof
    return ← `(tactic| exact $proof)
  if result.projection? == some .intervalIntegral then
    if let #[selection] := result.primitiveSelections then
      if let some function := selection.function? then
        let primitive ← PrettyPrinter.delab function
        return ← match result.requirementsSyntax? with
          | none => `(tactic| cas [integrate primitive := $primitive])
          | some requirements =>
              `(tactic| cas [integrate primitive := $primitive using $requirements])
  match result.requirementsSyntax? with
  | none => `(tactic| cas)
  | some requirements => `(tactic| cas using $requirements)

private def Result.plannerMetadata
    (result : Result) : Array Explanation.PlannerExplanationStep :=
  let improperSteps : Array Explanation.PlannerExplanationStep :=
    result.improperTheorems.map fun theoremName ↦ {
      label := "improper integral antiderivative search"
      status := .selected
      detail := s!"the primitive's limits at the infinite ends of the domain and the analytic \
        premises were checked; improper integral theorem: {theoremName}{
          if result.closedRelation then
            "; its endpoint equality rewrites the relation before arithmetic closure"
          else ""}"
    }
  if let some structural := result.structural? then
    #[{
      label := "direct interval calculus"
      status := .selected
      detail := "Mathlib theorem applications: " ++
        String.intercalate ", " (structural.theoremNames.toList.map Name.toString)
    }]
  else if result.derivativeRoute then
    #[{
      label := "checked symbolic derivative"
      status := .selected
      detail := "the derivative statement was closed by the checked derivative route"
    }]
  else if !result.primitiveSelections.isEmpty then
    (result.primitiveSelections.map fun selection ↦ {
      label := match selection.source with
        | .explicitPrimitive => "explicit primitive verification"
        | .goalPrimitive => "goal primitive verification"
        | .search => "bounded antiderivative search"
      status := .selected
      detail := s!"accepted after residual certification, interval domain discharge, \
        and conversion to the original goal; projection: {
          result.projection?.map Projection.label |>.getD ""}"
    }) ++ improperSteps
  else if !improperSteps.isEmpty then
    improperSteps
  else
    #[{
      label := if result.projection? == some .hasDerivAt then
        "checked primitive differentiation" else "symbolic antiderivative planner"
      status := .selected
      detail := s!"candidate accepted by the checked residual boundary; \
        projection: {result.projection?.map Projection.label |>.getD ""}{
          if result.closedRelation then
            s!"; {result.evidence.size} endpoint equalities rewrite the relation \
              before arithmetic closure"
          else ""}"
    }]

/-- Convert a completed integration result to route diagnostics and executable replay.
Call in the original goal's local context, where its coefficients and side evidence are in scope.
The reporting layer validates each proposed evidence step before displaying it as checked. -/
def Result.toRouteResult (result : Result) : MetaM RouteRegistry.Result := do
  let mut evidence := #[]
  if let some structural := result.structural? then
    for h : i in [:structural.analyticEvidence.size] do
      let step ← Explanation.UncheckedExplanationStep.ofProof
        s!"analytic premise {i + 1}" structural.analyticEvidence[i]
      evidence := evidence.push step
  for h : i in [:result.evidence.size] do
    let certificate := result.evidence[i]
    let suffix := if result.evidence.size = 1 then "" else s!" {i + 1}"
    let routeZero ← Explanation.UncheckedExplanationStep.ofProof
      s!"checked derivative residual{suffix} reaches zero"
      certificate.routeZeroProof
      (some ``IntegrationCheck.AntiderivativeCert.routeZero)
    let requirements ← Explanation.UncheckedExplanationStep.ofProof
      s!"antiderivative domain requirements{suffix}"
      certificate.requirementsProof
    evidence := evidence.push routeZero |>.push requirements
  return {
    replay := ← result.replay
    plannerMetadata := result.plannerMetadata
    evidence
    finalAttribution? :=
      if let some structural := result.structural? then
        structural.theoremNames[0]?
      else if result.closedRelation || result.derivativeRoute then
        none
      else if let some theoremName := result.improperTheorems[0]? then
        some theoremName
      else result.projection?.map Projection.theoremName
  }

end CAS.Tactic.Integration

namespace CAS.ExactTactic

open Lean Elab Tactic

/-- Whether `target` has the shape of the conclusion of
`intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt`:
`∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x`. -/
private def isIntegrationByPartsGoal (target : Expr) : Bool := Id.run do
  let some (_, lhs, rhs) := target.consumeMData.eq? | return false
  let isIntegral (e : Expr) := e.consumeMData.isAppOf ``intervalIntegral
  let rhs := rhs.consumeMData
  return isIntegral lhs && rhs.isAppOfArity ``HSub.hSub 6 &&
    (rhs.getArg! 4).consumeMData.isAppOfArity ``HSub.hSub 6 && isIntegral (rhs.getArg! 5)

/-- The integration route of `cas`, retaining its actual proof route. A goal of the shape of
`intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt` is first tried with one
integration-by-parts step. -/
@[cas_route integral]
def integralRoute : Tactic.RouteRegistry.Closer := fun requirements? ↦ do
  let goal ← getMainGoal
  let target ← goal.withContext do instantiateMVars (← goal.getType)
  unless isIntegrationByPartsGoal target do
    let result ← Tactic.Integration.close requirements?
    return ← goal.withContext result.toRouteResult
  let saved ← saveState
  try
    discard <| Tactic.ProofCarrier.runClosingMainGoal "integration by parts"
      closeIntegrationByParts
    return {
      replay := ← `(tactic| cas)
      plannerMetadata := #[{
        label := "integration by parts"
        status := .selected
        detail := "Mathlib's integration-by-parts theorem, with its derivative and \
          integrability premises proved"
      }]
      finalAttribution? :=
        some ``intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    }
  catch byPartsError =>
    saved.restore
    try
      let result ← Tactic.Integration.close requirements?
      goal.withContext result.toRouteResult
    catch integralError =>
      throwError "integration by parts:{indentD byPartsError.toMessageData}\n\
        checked integration:{indentD integralError.toMessageData}"

/-- The elaborator of `cas [integrate primitive := F]`. -/
@[tactic tacticCas] def evalCasIntegratePrimitive : Tactic := fun stx ↦ do
  match stx with
  | `(tactic| cas [integrate primitive := $primitive $[using $requirements]?]) =>
      Tactic.ProofCarrier.tacticEntry "cas [integrate primitive]" do
        let goal ← getMainGoal
        let result ← Tactic.Integration.close requirements (some primitive)
        discard <| recordRoute (.integral (← goal.withContext result.toRouteResult))
  | _ => throwUnsupportedSyntax

/-- `cas [integrate primitive := F]` checks the supplied primitive `F` against the original
integrand and applies the interval fundamental theorem of calculus. With `using h`, as in
`cas [integrate primitive := F using h]`, it checks `F` with the pointwise domain evidence `h` on
the whole integration interval. -/
tactic_extension tacticCas

end CAS.ExactTactic

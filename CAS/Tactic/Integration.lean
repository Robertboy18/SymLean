/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Tactic.Arithmetic
public import CAS.Tactic.Integration.Conversion
public import CAS.Tactic.Integration.Elementary
public meta import CAS.Tactic.Integration.Elementary
public import CAS.Tactic.Integration.Improper
public meta import CAS.Tactic.Integration.Improper
public import CAS.Tactic.Integration.Planning
public import CAS.Tactic.Integration.Projection
public import CAS.Tactic.Integration.Reflection
public import CAS.Tactic.Integration.Structural
public meta import CAS.Tactic.Integration.Structural
public import CAS.Tactic.Integration.Traversal

/-!
# Theorem-facing symbolic integration

`close` proves the integration goals of `cas`: an equality between an interval integral
`∫ x in a..b, f x` and a value, a `HasDerivAt` goal about a real function, the improper integrals
`∫ x in D, f x` over the half-lines `Set.Ioi a`, `Set.Ici a`, `Set.Iio a`, `Set.Iic a` and
`∫ x, f x` over the whole real line, the conjunctions `IntegrableOn f D ∧ ∫ x in D, f x = v` and
`Integrable f ∧ ∫ x, f x = v` that also state convergence, and equalities, disequalities and
order relations that contain such integrals. `CAS/IntegrationTactic.lean` registers it as the
route `integral` of `cas` and runs it for `cas [integrate primitive := F]`. Success closes the
main goal with a complete proof; a refusal restores the tactic state.

## Implementation notes

Without an explicit primitive we first try Mathlib's closed formulas (`Elementary.close`, with
`integral_pow`, `integral_rpow`, `integral_exp`, `integral_sin`, `integral_cos` and the rules for
constant factors), which need no primitive differentiable on the closed interval and so reach
integrable endpoint singularities. Then come Mathlib's linearity and fundamental theorem applied
to opaque functions from hypotheses (`Structural.close?`), which keep the user's normed codomain
and measure. A goal that already evaluates a `Verified.Expr` goes to `closeReflectedTarget`.
Every other goal is reflected into checked expressions (`Reflection.reflectFunction`), over the
reals and Lebesgue measure only, and needs an antiderivative certificate
`IntegrationCheck.AntiderivativeCert`. Its primitive comes from `cas [integrate primitive := F]`,
else from the goal's own endpoint difference `F b - F a` (`Reflection.endpointPrimitive?`), else
from the planner of `CAS/Integration/Planner.lean` (`Planning.findCertificate`). The search is
heuristic and bounded; when it finds nothing, nothing follows about the integral. A candidate
counts only once the kernel has decided that the residual route of `CAS/Integration/Check.lean`
reduces `∂ᵢ F - f` to zero (`Planning.certifyCandidate`).

The analytic step is
`IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_eval_add_smul_single` of
`CAS/Calculus/Antiderivative.lean`, which is Mathlib's
`intervalIntegral.integral_eq_sub_of_hasDerivAt` along a coordinate line; `Projection.complete`
proves its domain requirements, and an improper integral takes the half-line and whole-line
theorems through `Improper.prepare`, which proves the integrability of the integrand with the
value; an equality or relation uses the value, and a conjunction both. A `HasDerivAt` goal goes
to the checked derivative route `RealDeriv.close` first, and only when that fails is the stated
function certified as a primitive of its own symbolic derivative
(`IntegrationCheck.AntiderivativeCert.hasDerivAt_eval_add_smul_single`). `Conversion.close` turns
the reflected statement into the user's. In a relation every distinct integral is replaced by its
exact value and `Arithmetic.close` proves what remains; we attempt no estimate of an integral.
The fundamental theorem of calculus is Mathlib's; the reflection, the search and the residual
certificate are ours.
-/

public meta section

namespace CAS.Tactic.Integration

open Lean Elab Tactic Meta

/-- The analytic projection of one integral in the reflected syntax, shared by bounded
intervals and improper integrals. -/
private structure PreparedIntegral where
  certificate : Expr
  projectionProof : Expr
  requirementsProof : Expr
  localDefinitions : Array Name
  selection? : Option PrimitiveSelection := none
  improperTheorem? : Option Name := none
  /-- For an improper integral, the integrability of the reflected integrand on its domain. -/
  integrabilityProof? : Option Expr := none

/-- An ordinary integral recognised in a goal: over a bounded interval, or an improper integral
over a half-line or the whole line. -/
private inductive IntegralApplication where
  | interval (application : Reflection.IntervalIntegralApplication)
  | improper (application : Improper.Application)

/-- Recognize a bounded interval integral or an improper integral. -/
private def integralApplication? (expression : Expr) : Option IntegralApplication :=
  match Reflection.intervalIntegralApplication? expression with
  | some application => some (.interval application)
  | none =>
      match Improper.application? expression with
      | some application => some (.improper application)
      | none => none

private def prepareOrdinaryIntervalIntegral
    (application : Reflection.IntervalIntegralApplication)
    (requirementsSyntax? : Option (TSyntax `term))
    (primitive? : Option (Expr × PrimitiveSource) := none) :
    TacticM PreparedIntegral := do
  Reflection.ensureRealValue "the lower endpoint" application.lower
  Reflection.ensureRealValue "the upper endpoint" application.upper
  Reflection.ensureVolumeMeasure application.measure
  let (origin, localDefinitions, found) ←
    match primitive? with
    | some (primitive, _) => do
        let reflected ← Reflection.reflectPair application.function primitive
        let found ← Planning.certifyCandidate
          reflected.coordinate reflected.integrand reflected.candidate
        pure (reflected.origin, reflected.localDefinitions, found)
    | none => do
        let reflected ← Reflection.reflectFunction application.function
        let found ← Planning.findCertificate
          reflected.reflection.coordinate reflected.reflection.expression
        pure (reflected.reflection.origin, reflected.localDefinitions, found)
  let certificate := found.certificate
  let base ←
    mkAppM
      ``IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_eval_add_smul_single
      #[certificate, origin,
        application.lower, application.upper]
  let (projectionProof, requirementsProof) ←
    Projection.complete base requirementsSyntax? (some found.requirementsEquation)
  return {
    certificate
    projectionProof
    requirementsProof
    localDefinitions
    selection? := some {
      source := primitive?.map Prod.snd |>.getD .search
      candidate := ← mkAppM ``IntegrationCheck.AntiderivativeCert.candidate #[certificate]
      function? := primitive?.map Prod.fst
    }
  }

/-- Prepare the analytic equality of an integral of either kind. -/
private def prepareIntegral
    (application : IntegralApplication) (requirementsSyntax? : Option (TSyntax `term))
    (primitive? : Option (Expr × PrimitiveSource) := none) :
    TacticM PreparedIntegral := do
  match application with
  | .interval application =>
      prepareOrdinaryIntervalIntegral application requirementsSyntax? primitive?
  | .improper application =>
      if primitive?.isSome then
        throwError "cas [integrate primitive := ...] requires a bounded interval integral"
      let prepared ← Improper.prepare application requirementsSyntax?
      return {
        certificate := prepared.certificate
        projectionProof := prepared.projectionProof
        requirementsProof := prepared.requirementsProof
        localDefinitions := prepared.localDefinitions
        improperTheorem? := some prepared.theoremName
        integrabilityProof? := prepared.integrabilityProof?
      }

private def closeCertifiedHasDerivAt
    (application : Reflection.HasDerivAtApplication)
    (requirementsSyntax? : Option (TSyntax `term)) : TacticM Result := do
  Reflection.ensureRealValue "the derivative value" application.derivative
  Reflection.ensureRealValue "the evaluation point" application.point
  let reflected ← Reflection.reflectFunction application.function
  let certificate ←
    Planning.certifyPrimitive
      reflected.reflection.coordinate reflected.reflection.expression
  let base ←
    mkAppM
      ``IntegrationCheck.AntiderivativeCert.hasDerivAt_eval_add_smul_single
      #[certificate, reflected.reflection.origin, application.point]
  let (proof, requirementsProof) ←
    Projection.complete base requirementsSyntax?
  let result ← Projection.result .hasDerivAt certificate requirementsProof
  Conversion.close proof reflected.localDefinitions
  return result

private def closeOrdinaryHasDerivAt
    (application : Reflection.HasDerivAtApplication)
    (requirementsSyntax? : Option (TSyntax `term)) : TacticM Result := do
  match ← CAS.Tactic.ProofCarrier.attemptClosingMainGoal
      "checked symbolic differentiation" (RealDeriv.close requirementsSyntax?) with
  | .ok _ =>
      return { derivativeRoute := true }
  | .error derivativeError =>
      try
        closeCertifiedHasDerivAt application requirementsSyntax?
      catch certificateError =>
        throwError
          "cas could not prove this derivative statement.\n\
           checked derivative route:{indentD derivativeError.toMessageData}\n\
           antiderivative certificate route:{indentD certificateError.toMessageData}"

/-- Close a goal `∫ = rhs` (or `rhs = ∫`, with `reverse`) whose one side is an integral. -/
private def closeOrdinaryIntegralWithPrimitive
    (application : IntegralApplication) (reverse : Bool)
    (requirementsSyntax? : Option (TSyntax `term))
    (primitive? : Option (Expr × PrimitiveSource)) : TacticM Result := do
  let prepared ← prepareIntegral application requirementsSyntax? primitive?
  let proof ←
    if reverse then
      mkAppM ``Eq.symm #[prepared.projectionProof]
    else
      pure prepared.projectionProof
  let result ←
    Projection.result .intervalIntegral
      prepared.certificate prepared.requirementsProof
  -- An explicit primitive may unfold definitions absent from the user's goal.
  -- Unfold only occurrences in the goal, also exposing any nested local definitions.
  let mut goal ← getMainGoal
  for name in prepared.localDefinitions do
    if (← instantiateMVars (← goal.getType)).getUsedConstants.contains name then
      goal ← Meta.unfoldTarget goal name
  replaceMainGoal [goal]
  Conversion.close proof #[]
  return {
    result with
    primitiveSelections := prepared.selection?.toArray
    improperTheorems := prepared.improperTheorem?.toArray
  }

/-- Verify a stated endpoint primitive before bounded discovery. The automatic attempt
includes domain discharge and conversion, and restores the goal before falling back. -/
private def closeOrdinaryIntegral
    (application : IntegralApplication) (endpointValue : Expr) (reverse : Bool)
    (requirementsSyntax? : Option (TSyntax `term))
    (primitive? : Option Expr) : TacticM Result := do
  if let some primitive := primitive? then
    return ← closeOrdinaryIntegralWithPrimitive application reverse requirementsSyntax?
      (some (primitive, .explicitPrimitive))
  if let .interval interval := application then
    let saved ← saveState
    try
      if let some primitive ←
          Reflection.endpointPrimitive? endpointValue interval.lower interval.upper then
        return ← closeOrdinaryIntegralWithPrimitive application reverse requirementsSyntax?
          (some (primitive, .goalPrimitive))
    catch error =>
      if error.isRuntime then throw error
    saved.restore
  closeOrdinaryIntegralWithPrimitive application reverse requirementsSyntax? none

private def collectIntegralTerms
    (expression : Expr) :
    Array (Expr × IntegralApplication) :=
  let stripped := expression.consumeMData
  match integralApplication? stripped with
  | some application => #[(stripped, application)]
  | none =>
      match expression with
      | .app function argument =>
          collectIntegralTerms function ++
            collectIntegralTerms argument
      | .proj _ _ body => collectIntegralTerms body
      | .mdata _ body => collectIntegralTerms body
      | _ => #[]

private def distinctIntegralTerms
    (terms : Array (Expr × IntegralApplication)) :
    Array (Expr × IntegralApplication) :=
  terms.foldl
    (fun distinct term ↦
      if distinct.any fun candidate ↦ candidate.1 == term.1 then
        distinct
      else
        distinct.push term)
    #[]

private def convertIntegralEquality
    (integralTerm : Expr) (prepared : PreparedIntegral) :
    TacticM Expr := do
  let projectionType ← instantiateMVars (← inferType prepared.projectionProof)
  let some (_, _, generatedValue) := projectionType.eq?
    | throwError
        "cas internal error: the integral projection did not produce an equality"
  let equalityTarget ← mkEq integralTerm generatedValue
  let goalsBefore ← getGoals
  let equality ← mkFreshExprSyntheticOpaqueMVar equalityTarget
  setGoals [equality.mvarId!]
  Conversion.close prepared.projectionProof prepared.localDefinitions
  let equalityProof ←
    CAS.Tactic.ProofCarrier.validateAssignedProof
      "ordinary integral conversion" equality.mvarId! equalityTarget
  setGoals goalsBefore
  return equalityProof

private def closeOrdinaryIntegralRelation
    (target : Expr) (requirementsSyntax? : Option (TSyntax `term)) :
    TacticM Result := do
  -- A goal introduced by `have` carries metadata that the relation recognisers do not skip.
  let target := target.consumeMData
  unless target.eq?.isSome || target.ne?'.isSome ||
      target.le?.isSome || target.lt?.isSome do
    throwError
      "cas expected an equality, disequality, or order relation"
  let terms := distinctIntegralTerms (collectIntegralTerms target)
  if terms.isEmpty then
    throwError
      "cas found no ordinary interval or improper integral in this relation"
  let prepared ← terms.mapM fun (integralTerm, application) ↦ do
    let certificate ← prepareIntegral application requirementsSyntax?
    let equalityProof ← convertIntegralEquality integralTerm certificate
    pure (certificate, equalityProof)
  let goalsBefore ← getGoals
  let mut rewrittenGoal := goalsBefore[0]!
  for (_, equalityProof) in prepared do
    let rewrittenTarget ← instantiateMVars (← rewrittenGoal.getType)
    let rewriteResult ← rewrittenGoal.rewrite rewrittenTarget equalityProof
    unless rewriteResult.mvarIds.isEmpty do
      throwError
        "cas internal error: rewriting the integral relation produced \
         unresolved auxiliary goals"
    rewrittenGoal ←
      rewrittenGoal.replaceTargetEq rewriteResult.eNew rewriteResult.eqProof
  replaceMainGoal [rewrittenGoal]
  try
    Arithmetic.close
  catch error =>
    throwError
      "cas proved the exact endpoint formula, but could not close \
       the resulting arithmetic relation. The requested relation may be false \
       or may require additional analytic estimates; in the latter case, use \
       `cas` in a `calc` step and supply them explicitly.\n\
       Reduced-goal detail:{indentD error.toMessageData}"
  let evidence ← prepared.mapM fun (certificate, _) ↦
    Projection.certificateEvidence
      certificate.certificate certificate.requirementsProof
  return {
    projection? := some .intervalIntegral
    closedRelation := true
    evidence
    primitiveSelections := prepared.filterMap fun (certificate, _) ↦ certificate.selection?
    improperTheorems := prepared.filterMap fun (certificate, _) ↦ certificate.improperTheorem?
  }

/-- Close `IntegrableOn f D ∧ ∫ x in D, f x = v` over a half-line `D`, or
`Integrable f ∧ ∫ x, f x = v` over the whole line, with the equality in either direction: the
improper integral is prepared once, the goal is split by `And.intro`, and each half of the analytic
conclusion is converted to the user's syntax. -/
private def closeIntegrableAndIntegral
    (equality : Expr) (requirementsSyntax? : Option (TSyntax `term)) : TacticM Result := do
  let some (_, lhs, rhs) := equality.consumeMData.eq?
    | throwError "cas expected `IntegrableOn f D ∧ ∫ x in D, f x = v`"
  let (application, reverse) ←
    match integralApplication? lhs, integralApplication? rhs with
    | some (.improper application), none => pure (application, false)
    | none, some (.improper application) => pure (application, true)
    | _, _ =>
        throwError "cas expected `IntegrableOn f D ∧ ∫ x in D, f x = v` for an improper integral \
          over a half-line, or `Integrable f ∧ ∫ x, f x = v` over the whole line"
  let prepared ← Improper.prepare application requirementsSyntax?
  let [integrabilityGoal, equalityGoal] ← (← getMainGoal).apply (mkConst ``And.intro)
    | throwError "cas internal error: the conjunction could not be split"
  let remaining ← getGoals
  setGoals [equalityGoal]
  let equalityProof ←
    if reverse then mkAppM ``Eq.symm #[prepared.projectionProof] else pure prepared.projectionProof
  Conversion.close equalityProof prepared.localDefinitions
  let some integrabilityProof := prepared.integrabilityProof?
    | throwError "cas proved the value of the improper integral but could not move the \
        integrability of the integrand to the stated domain"
  setGoals [integrabilityGoal]
  Conversion.close integrabilityProof prepared.localDefinitions
  setGoals (remaining.drop 1)
  let result ←
    Projection.result .intervalIntegral prepared.certificate prepared.requirementsProof
  return { result with improperTheorems := #[prepared.theoremName] }

private def closeOrdinaryTarget
    (requirementsSyntax? : Option (TSyntax `term))
    (primitive? : Option Expr) : TacticM Result :=
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    if let some application := Reflection.hasDerivAtApplication? target then
      if primitive?.isSome then
        throwError "cas [integrate primitive := ...] expects a bounded interval-integral equality"
      return ← closeOrdinaryHasDerivAt application requirementsSyntax?
    if let some (_, equality) := target.consumeMData.and? then
      if primitive?.isSome then
        throwError "cas [integrate primitive := ...] expects a bounded interval-integral equality"
      return ← closeIntegrableAndIntegral equality requirementsSyntax?
    unless target.consumeMData.isAppOfArity ``Eq 3 do
      if primitive?.isSome then
        throwError "cas [integrate primitive := ...] expects a bounded interval-integral equality"
      return ← closeOrdinaryIntegralRelation target requirementsSyntax?
    let arguments := target.consumeMData.getAppArgs
    let lhs := arguments[1]!
    let rhs := arguments[2]!
    -- Keep the direct conversion for a lone integral. Relations with several
    -- integrals need every endpoint formula before arithmetic can close them.
    if (collectIntegralTerms target).size > 1 then
      if primitive?.isSome then
        throwError "cas [integrate primitive := ...] expects exactly one integral"
      return ← closeOrdinaryIntegralRelation target requirementsSyntax?
    match integralApplication? lhs, integralApplication? rhs with
    | some application, none =>
        closeOrdinaryIntegral application rhs false requirementsSyntax? primitive?
    | none, some application =>
        closeOrdinaryIntegral application lhs true requirementsSyntax? primitive?
    | some _, some _ | none, none =>
        if primitive?.isSome then
          throwError
            "cas [integrate primitive := ...] expects an integral on one side of the equality"
        closeOrdinaryIntegralRelation target requirementsSyntax?

private def closeReflectedTarget
    (requirementsSyntax? : Option (TSyntax `term)) : TacticM Result :=
  withMainContext do
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    let (projection, integrand) ← Traversal.projectionAndIntegrand target
    let coordinate ← Traversal.uniqueCoordinate target
    let found ← Planning.findCertificate coordinate integrand
    let certificate := found.certificate
    let base ← mkAppM projection.theoremName #[certificate]
    let (arguments, _, conclusion) ←
      forallMetaTelescopeReducing (← inferType base)
    unless arguments.size == projection.argumentCount do
      throwError
        "cas internal error: the selected certificate theorem has \
         an unexpected argument shape"
    unless ← isDefEq conclusion target do
      throwError
        "cas found a checked antiderivative, but its analytic \
         theorem does not match the stated primitive and coordinate geometry"
    let requirements := arguments[arguments.size - 1]!
    let requirementsProof ←
      Projection.proveRequirements requirements requirementsSyntax?
        (some found.requirementsEquation)
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars (mkAppN base arguments)
    let proofType ← instantiateMVars (← inferType proof)
    unless ← isDefEq proofType target do
      throwError
        "cas constructed a proof of{indentExpr proofType}\n\
         but the goal is{indentExpr target}"
    if proof.hasMVar ∨ proof.hasSorry then
      throwError "cas constructed incomplete analytic evidence"
    unless ← isTypeCorrect proof do
      throwError "cas constructed ill-typed analytic evidence"
    let result ← Projection.result projection certificate requirementsProof
    goal.assign proof
    replaceMainGoal []
    return result

/--
Close a supported ordinary calculus or checked-expression antiderivative goal.

Without an explicit primitive, direct Mathlib calculus rules are tried first.
For a scalar interval equality, a common endpoint function is then verified by
differentiation before bounded antiderivative search. An explicit primitive
must itself pass residual, domain, and endpoint checks; it is never silently
replaced by search.

Without explicit evidence, finite symbolic side conditions are discharged by
`symbolic_assumptions`. The `using` form first accepts the
certificate's exact requirements proposition and otherwise makes the supplied
fact available to the same checked side-condition automation; for an improper
integral the fact may also be the integrability of the integrand or its sign
on the domain.

Success requires a complete proof of the original main goal and no remaining
subgoals. A refusal restores the caller's tactic state.
-/
def close (requirementsSyntax? : Option (TSyntax `term))
    (primitiveSyntax? : Option (TSyntax `term) := none) : TacticM Result :=
  ProofCarrier.preservingStateOnFailure do
    let closed ← ProofCarrier.runClosingMainGoal "cas" do
      if primitiveSyntax?.isNone then
        let originalGoal ← getMainGoal
        if let .ok elementary ← ProofCarrier.attemptClosingMainGoal
            "elementary interval integration" (Elementary.close requirementsSyntax?) then
          let used := elementary.proof.getUsedConstants
          let theoremNames := #[``integral_pow, ``integral_rpow, ``integral_exp,
            ``integral_sin, ``integral_cos, ``intervalIntegral.integral_const,
            ``intervalIntegral.integral_same, ``intervalIntegral.integral_const_mul,
            ``intervalIntegral.integral_mul_const].filter used.contains
          let analyticEvidence ← originalGoal.withContext do
            (collectFVars {} elementary.proof).fvarIds.filterMapM fun id ↦ do
              let proof := mkFVar id
              return if ← isProp (← inferType proof) then some proof else none
          return {
            structural? := some {
              theoremNames
              analyticEvidence
              proof := elementary.proof
            }
          }
        if let some structural ← Structural.close? requirementsSyntax? then
          return {
            structural? := some {
              theoremNames := structural.theoremNames
              analyticEvidence := structural.analyticEvidence
              proof := structural.proof
            }
          }
      let usesCheckedEvaluation ← withMainContext do
        let target ← instantiateMVars (← getMainTarget)
        return target.getUsedConstants.contains ``Verified.Expr.eval
      if usesCheckedEvaluation then
        if primitiveSyntax?.isSome then
          throwError "cas [integrate primitive := ...] expects an ordinary interval integral"
        closeReflectedTarget requirementsSyntax?
      else
        withMainContext do
          let primitive? ← primitiveSyntax?.mapM fun termSyntax ↦ do
            let type ← mkArrow (mkConst ``Real) (mkConst ``Real)
            let primitive ← Term.elabTermEnsuringType termSyntax type
            Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars primitive
          closeOrdinaryTarget requirementsSyntax? primitive?
    return { closed.value with requirementsSyntax? }

end CAS.Tactic.Integration

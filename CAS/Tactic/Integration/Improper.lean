/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Tactic.Integration.Limits
public import CAS.Tactic.Integration.Planning
public meta import CAS.Tactic.Integration.Planning
public import CAS.Tactic.Integration.Projection
public import CAS.Tactic.Integration.Reflection
public meta import CAS.Tactic.Integration.Reflection

/-!
# Improper integrals

`cas` also proves the improper integrals `∫ t in D, f t` over the half-lines `D = Set.Ioi a`,
`Set.Ici a`, `Set.Iio a` and `Set.Iic a`, and the integral `∫ t, f t` of a real function over the
whole real line. `application?` recognizes these integrals, and `prepare` proves the analytic
equality in the reflected syntax, which `CAS.Tactic.Integration.Conversion` converts to the
user's statement exactly as for bounded intervals. The certificate is the same checked
antiderivative `F` that the interval route finds.

## Implementation notes

The analytic theorems are those of `CAS/Calculus/Antiderivative.lean`, which state Mathlib's
fundamental theorem on unbounded domains along a coordinate line, with the integrability of the
integrand in the conclusion:

* `IntegrationCheck.AntiderivativeCert.integrableOn_Ioi_and_integral_eq` (Mathlib's
  `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'`) on `(a, +∞)`, with the requirements on
  `[a, +∞)`;
* `IntegrationCheck.AntiderivativeCert.integrableOn_Iic_and_integral_eq`
  (`MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto'`) on `(-∞, a]`;
* `IntegrationCheck.AntiderivativeCert.integrable_and_integral_eq`
  (`MeasureTheory.integral_of_hasDerivAt_of_tendsto`) on the whole line, with the requirements
  at every point, split at `0`.

Each of them needs two facts beyond the domain requirements. The limits of `F` at the infinite
ends of the domain come from the structural procedure `Limits.limitAtTopOfBody`, run on the body
of `F` once `simp` has turned it into ordinary syntax; the limit at `-∞` is that of
`t ↦ F (-t)` at `+∞` (Mathlib's `Filter.tendsto_comp_neg_atTop_iff`). The other is a three-way
premise on the half-line, `IntegrableOn f D ∨ (∀ t ∈ D, 0 ≤ f t) ∨ ∀ t ∈ D, f t ≤ 0`, one for
each of `(-∞, 0]` and `(0, +∞)` on the whole line. We prove a sign from the membership in the
domain by `positivity`, `linarith` or `nlinarith`, or take it from the evidence given with
`using`; failing that, integrability itself, from a hypothesis in the context or from `using`
(an `Integrable f` restricts to each half-line). From a sign, the theorems deduce integrability
with Mathlib's `MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'` and
`MeasureTheory.integrableOn_Ioi_deriv_of_nonpos'` on `(a, +∞)` and, on `(-∞, a]`, where Mathlib
has no such lemma, with our `CAS.integrableOn_Iic_deriv_of_nonneg'` and
`CAS.integrableOn_Iic_deriv_of_nonpos'`. `prepare` returns both halves of the conclusion: the
integrability, moved to `Set.Ici a` by Mathlib's `integrableOn_Ici_iff_integrableOn_Ioi` and
to `Set.Iio a` by `MeasureTheory.IntegrableOn.mono_set`, and the equality.

`Set.Ici a` and `Set.Iio a` are reduced to `Set.Ioi a` and `Set.Iic a` by
`MeasureTheory.integral_Ici_eq_integral_Ioi` and `MeasureTheory.integral_Iic_eq_integral_Iio`
(and the integrability by `integrableOn_Ici_iff_integrableOn_Ioi`, `IntegrableOn.mono_set`).
A divergent integral fails closed, since the limit of the primitive or the three-way premise is
then missing; the failure message shows the subterm of the primitive without a
known limit, or the integrand.
-/

public meta section

namespace CAS.Tactic.Integration.Improper

open Lean Elab Tactic Meta

/-- The domain of an improper integral. -/
inductive Domain where
  /-- The half-line `Set.Ioi a`. -/
  | ioi (endpoint : Expr)
  /-- The half-line `Set.Ici a`. -/
  | ici (endpoint : Expr)
  /-- The half-line `Set.Iio a`. -/
  | iio (endpoint : Expr)
  /-- The half-line `Set.Iic a`. -/
  | iic (endpoint : Expr)
  /-- The whole real line, for an integral whose measure is not restricted. -/
  | line

/-- The explicit data of a real improper integral with respect to Lebesgue measure. -/
structure Application where
  /-- The integrand `fun t ↦ f t`. -/
  function : Expr
  /-- The domain of integration, with its finite endpoint. -/
  domain : Domain
  /-- The measure of the integral, before its restriction to a half-line. -/
  measure : Expr

/-- Recognize `∫ t in D, f t` for a half-line `D` (`Set.Ioi a`, `Set.Ici a`, `Set.Iio a` or
`Set.Iic a`), that is, `MeasureTheory.integral (μ.restrict D) f` over the reals, and the integral
`∫ t, f t` of a real function over the whole real line. -/
def application? (expression : Expr) : Option Application :=
  let expression := expression.consumeMData
  if !expression.isAppOfArity ``MeasureTheory.integral 7 then
    none
  else
    let arguments := expression.getAppArgs
    let function := arguments[6]!
    let measure := arguments[5]!.consumeMData
    if measure.isAppOfArity ``MeasureTheory.Measure.restrict 4 then
      let region := measure.getAppArgs[3]!.consumeMData
      let domain? : Option Domain :=
        if region.isAppOfArity ``Set.Ioi 3 then some (.ioi region.appArg!)
        else if region.isAppOfArity ``Set.Ici 3 then some (.ici region.appArg!)
        else if region.isAppOfArity ``Set.Iio 3 then some (.iio region.appArg!)
        else if region.isAppOfArity ``Set.Iic 3 then some (.iic region.appArg!)
        else none
      match domain? with
      | some domain => some { function, domain, measure := measure.getAppArgs[2]! }
      | none => none
    else if arguments[0]!.consumeMData.isConstOf ``Real &&
        arguments[1]!.consumeMData.isConstOf ``Real then
      some { function, domain := .line, measure }
    else
      none

/-- The reflected function `fun t ↦ expr.eval (origin + t • single coordinate 1)` of a
reflection along its coordinate line. -/
private def lineFunction (reflection : RealExpression.Reflection) (expr : Expr) :
    MetaM Expr :=
  withLocalDeclD `t (mkConst ``Real) fun t ↦ do
    let point ← mkAppM ``HAdd.hAdd
      #[reflection.origin, ← mkAppM ``HSMul.hSMul #[t, reflection.direction]]
    mkLambdaFVars #[t]
      (← mkAppM ``Verified.Expr.eval #[← mkAppM ``WithLp.ofLp #[point], expr])

/-- Simplify the body of a reflected coordinate-line function to ordinary real syntax, returning
the simplified body and the proof `body = simplified` (or `none` when nothing changed). -/
private def simplifyLineBody (body : Expr) : TacticM Simp.Result := do
  let simpCall ← `(tactic|
    simp [Verified.Expr.eval, IntegrationCheck.AntiderivativeCert.candidate,
      PiLp.single_apply, smul_eq_mul])
  let { ctx, simprocs, .. } ← mkSimpContext simpCall (eraseLocal := false)
  let (result, _) ← Simp.main body ctx (methods := Simp.mkDefaultMethodsCore simprocs)
  return result

/-- Prove `Tendsto F atTop (𝓝 limit)` for the reflected primitive `F`, returning the limit
together with the proof. The body is first simplified to ordinary syntax, whose limit the
structural procedure of `Limits` computes; the two functions are identified pointwise. -/
private def primitiveLimit (operation : String) (primitive : Expr) : TacticM (Expr × Expr) := do
  let real := mkConst ``Real
  withLocalDeclD `t real fun t ↦ do
    let body ← instantiateMVars (← whnfCore (mkApp primitive t))
    let simplified ← simplifyLineBody body
    let (limit, proofSimplified) ←
      Limits.limitAtTopOfBody operation t simplified.expr
    match simplified.proof? with
    | none =>
        return (limit, proofSimplified)
    | some equality =>
        -- `Tendsto.congr (fun t ↦ simplified t = body t) (h : Tendsto simplified)`.
        let pointwise ← mkLambdaFVars #[t] (← mkEqSymm equality)
        let proof ← mkAppM ``Filter.Tendsto.congr #[pointwise, proofSimplified]
        return (limit, proof)

/-- Prove `Tendsto F atBot (𝓝 limit)` for the reflected primitive `F`, returning the limit
together with the proof. The limit is that of `t ↦ F (-t)` at `+∞`, which `primitiveLimit`
computes, and Mathlib's `Filter.tendsto_comp_neg_atTop_iff` turns it into the limit at `-∞`. -/
private def primitiveLimitAtBot (operation : String) (primitive : Expr) :
    TacticM (Expr × Expr) := do
  let reflected ← withLocalDeclD `t (mkConst ``Real) fun t ↦ do
    mkLambdaFVars #[t] (mkApp primitive (← mkAppM ``Neg.neg #[t])).headBeta
  let (limit, proof) ←
    try
      primitiveLimit operation reflected
    catch error =>
      if error.isRuntime then throw error
      throwError "{operation} could not determine the limit at -∞ of the primitive `F`, read as \
        the limit at +∞ of `t ↦ F (-t)`:{indentD error.toMessageData}"
  let real := mkConst ``Real
  let iff ← mkAppOptM ``Filter.tendsto_comp_neg_atTop_iff
    #[some real, some real, none, none, none, some (← mkAppM ``nhds #[limit]), some primitive]
  return (limit, ← mkAppM ``Iff.mp #[iff, proof])

/-- The message naming a missing analytic fact about the integrand. -/
private def signFailureMessage (integrand : Expr) : MessageData :=
  m!"cas found a checked antiderivative for this improper integral but could not \
     prove the integrand integrable on its domain: neither `0 ≤ f t` nor `f t ≤ 0` was \
     established for `t` in the domain (in each of `(-∞, 0]` and `(0, +∞)` for the whole \
     line), where `f` is{indentExpr integrand}\nSupply `IntegrableOn f D` for the domain `D` \
     (`Integrable f` for the whole line), or a sign fact for every `t` in the domain, with \
     `cas using h`."

/-- The tactic proving a pointwise sign condition `∀ t, t ∈ D → 0 ≤ f t` (or `f t ≤ 0`, and with
no membership on the whole line) for the reflected integrand: the membership is unfolded, the
evaluator is simplified away, and `positivity`, linear arithmetic, or the user's evidence
finish. -/
private def signTactic (evidence? : Option (TSyntax `term)) : TacticM (TSyntax `tactic) := do
  let finish ← `(tactic|
    first
      | positivity
      | linarith
      | nlinarith
      | (have hcasPositive : 0 < t := by linarith
         positivity))
  let enter ← `(tactic|
    (intro t
     try intro ht
     try simp only [Set.mem_Ioi, Set.mem_Ici, Set.mem_Iio, Set.mem_Iic] at ht))
  match evidence? with
  | none =>
      `(tactic|
        ($enter:tactic
         simp [Verified.Expr.eval, PiLp.single_apply, smul_eq_mul]
         all_goals $finish:tactic))
  | some evidence =>
      `(tactic|
        first
          | exact $evidence
          | ($enter:tactic
             first
               | exact $evidence t ht
               | exact $evidence t
               | (have hcasEvidence := $evidence
                  simp [Verified.Expr.eval, PiLp.single_apply, smul_eq_mul] at hcasEvidence ⊢
                  all_goals $finish:tactic)
               | (simp [Verified.Expr.eval, PiLp.single_apply, smul_eq_mul]
                  all_goals $finish:tactic)))

/-- The tactic proving `IntegrableOn f D` for the reflected integrand and a half-line `D` from a
hypothesis or the user's evidence, `IntegrableOn f D` itself or `Integrable f`, restricted to `D`,
after simplifying the evaluator away when needed. -/
private def integrabilityTactic (evidence? : Option (TSyntax `term)) : TacticM (TSyntax `tactic) :=
  match evidence? with
  | none =>
      `(tactic|
        first
          | assumption
          | exact MeasureTheory.Integrable.integrableOn (by assumption)
          | (simp only [Verified.Expr.eval, PiLp.single_apply, smul_eq_mul]
             first
               | assumption
               | exact MeasureTheory.Integrable.integrableOn (by assumption)))
  | some evidence =>
      `(tactic|
        first
          | exact $evidence
          | exact ($evidence).integrableOn
          | assumption
          | exact MeasureTheory.Integrable.integrableOn (by assumption)
          | (simp [Verified.Expr.eval, PiLp.single_apply, smul_eq_mul]
             first
               | exact $evidence
               | exact ($evidence).integrableOn
               | assumption
               | exact MeasureTheory.Integrable.integrableOn (by assumption)))

/-- The analytic theorem of a domain. `Set.Ici a` uses the theorem of `Set.Ioi a`, and `Set.Iio a`
that of `Set.Iic a`; the whole line is split at `0`. -/
private def route : Domain → Name
  | .ioi _ | .ici _ => ``IntegrationCheck.AntiderivativeCert.integrableOn_Ioi_and_integral_eq
  | .iio _ | .iic _ => ``IntegrationCheck.AntiderivativeCert.integrableOn_Iic_and_integral_eq
  | .line => ``IntegrationCheck.AntiderivativeCert.integrable_and_integral_eq

/--
Try to close an analytic premise of an improper integral theorem instance, a sign condition or an
integrability statement about the reflected integrand, with the given tactic. Returns the proof or
`none`.
-/
private def proveAnalyticHypothesis (goal : MVarId) (tactic : TSyntax `tactic) :
    TacticM (Option Expr) := do
  let remaining ←
    try
      withSuppressedMessages <| evalTacticAt tactic goal
    catch _ =>
      return none
  unless remaining.isEmpty do
    return none
  let proof ← instantiateMVars (mkMVar goal)
  if proof.hasMVar ∨ proof.hasSorry then
    return none
  return some proof

/-- Prove a premise `IntegrableOn f D ∨ (∀ t ∈ D, 0 ≤ f t) ∨ ∀ t ∈ D, f t ≤ 0` of an improper
integral theorem: the two signs first, by `signTactic`, then integrability, by
`integrabilityTactic`, each on a fresh goal. Returns the proof of the disjunction or `none`. -/
private def proveIntegrabilityPremise (premise : Expr) (evidence? : Option (TSyntax `term)) :
    TacticM (Option Expr) := do
  let premise ← instantiateMVars premise
  let (``Or, #[integrable, rest]) := premise.consumeMData.getAppFnArgs
    | throwError "cas internal error: the improper integral theorem has an unexpected premise"
  let (``Or, #[nonneg, nonpos]) := rest.consumeMData.getAppFnArgs
    | throwError "cas internal error: the improper integral theorem has an unexpected premise"
  let attempt (statement : Expr) (tactic : TSyntax `tactic) : TacticM (Option Expr) := do
    let goal ← mkFreshExprSyntheticOpaqueMVar statement
    proveAnalyticHypothesis goal.mvarId! tactic
  let sign ← signTactic evidence?
  if let some proof ← attempt nonneg sign then
    return some (mkApp3 (mkConst ``Or.inr) integrable rest
      (mkApp3 (mkConst ``Or.inl) nonneg nonpos proof))
  if let some proof ← attempt nonpos sign then
    return some (mkApp3 (mkConst ``Or.inr) integrable rest
      (mkApp3 (mkConst ``Or.inr) nonneg nonpos proof))
  if let some proof ← attempt integrable (← integrabilityTactic evidence?) then
    return some (mkApp3 (mkConst ``Or.inl) integrable rest proof)
  return none

/-- The analytic projection of an improper integral, in the reflected syntax. -/
structure Prepared where
  /-- The improper integral theorem whose premises were proved. -/
  theoremName : Name
  /-- The checked antiderivative certificate. -/
  certificate : Expr
  /-- The proof `∫ t in D, integrand.eval (line t) = value` for the user's domain `D`, where the
  value is `limit - F.eval (line a)` on `Set.Ioi a` or `Set.Ici a`, `F.eval (line a) - limit` on
  `Set.Iio a` or `Set.Iic a`, and the difference of the two limits on the whole line. -/
  projectionProof : Expr
  /-- The proof of `IntegrableOn (fun t ↦ integrand.eval (line t)) D` for the user's domain `D`,
  or of `Integrable (fun t ↦ integrand.eval (line t))` on the whole line; `none` when it could not
  be moved from `Set.Ioi a` to `Set.Ici a` or from `Set.Iic a` to `Set.Iio a`, which only a goal
  that states the integrability needs. -/
  integrabilityProof? : Option Expr
  /-- The proof of the certificate's requirements on the closure of the domain. -/
  requirementsProof : Expr
  /-- Caller-local definitions unfolded while reflecting the integrand. -/
  localDefinitions : Array Name

/-- The equality `∫ t in D, f t = ∫ t in E, f t` of the integrals of the reflected integrand
`function` over the half-lines `domain a` and `target a`, proved by `tactic`. -/
private def domainRewrite (application : Application) (function endpoint : Expr)
    (domain target : Name) (tactic : TSyntax `tactic) (failure : String) : TacticM Expr := do
  let restricted (region : Name) : MetaM Expr := do
    mkAppM ``MeasureTheory.integral
      #[← mkAppM ``MeasureTheory.Measure.restrict
          #[application.measure, ← mkAppM region #[endpoint]],
        function]
  let statement ← mkEq (← restricted domain) (← restricted target)
  let some rewrite ← Limits.proveByTactic? statement tactic
    | throwError "cas internal error: {failure}"
  return rewrite

/--
Prepare the analytic equality for an improper integral: reflect the integrand, find and certify
its antiderivative through the checked planner, compute the primitive's limits at the infinite
ends of the domain, prove the domain requirements on the closure of the domain, and prove the
three-way premise of each half-line through a sign condition or the supplied evidence. The
`Set.Ici` form is reduced to `Set.Ioi` by `MeasureTheory.integral_Ici_eq_integral_Ioi` and
`integrableOn_Ici_iff_integrableOn_Ioi`, and the `Set.Iio` form to `Set.Iic` by
`MeasureTheory.integral_Iic_eq_integral_Iio` and `MeasureTheory.IntegrableOn.mono_set`.
-/
def prepare (application : Application) (requirementsSyntax? : Option (TSyntax `term)) :
    TacticM Prepared := do
  match application.domain with
  | .ioi endpoint | .ici endpoint | .iio endpoint | .iic endpoint =>
      Reflection.ensureRealValue "the endpoint of the half-line" endpoint
  | .line => pure ()
  Reflection.ensureVolumeMeasure application.measure
  let reflected ← Reflection.reflectFunction application.function
  let reflection := reflected.reflection
  let found ← Planning.findCertificate reflection.coordinate reflection.expression
  let certificate := found.certificate
  let candidate ← mkAppM ``IntegrationCheck.AntiderivativeCert.candidate #[certificate]
  let primitive ← lineFunction reflection candidate
  let integrandFunction ← lineFunction reflection reflection.expression
  -- The values after the certificate and the origin (the endpoint and the limit, or the two
  -- limits and the split point), and the proofs of the primitive's limits.
  let (values, limitProofs) ←
    match application.domain with
    | .ioi endpoint | .ici endpoint => do
        let (limit, proof) ← primitiveLimit "cas" primitive
        pure (#[endpoint, limit], #[proof])
    | .iio endpoint | .iic endpoint => do
        let (limit, proof) ← primitiveLimitAtBot "cas" primitive
        pure (#[endpoint, limit], #[proof])
    | .line => do
        let (lower, lowerProof) ← primitiveLimitAtBot "cas" primitive
        let (upper, upperProof) ← primitiveLimit "cas" primitive
        -- The whole line is split at `0`.
        pure (#[lower, upper, ← mkNumeral (mkConst ``Real) 0], #[lowerProof, upperProof])
  let theoremName := route application.domain
  let base ← mkAppM theoremName (#[certificate, reflection.origin] ++ values)
  let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType base)
  let premiseCount := if application.domain matches .line then 2 else 1
  unless arguments.size == 1 + limitProofs.size + premiseCount do
    throwError
      "cas internal error: the improper integral theorem has an unexpected argument shape"
  for (limitProof, k) in limitProofs.zipIdx do
    let limitGoal := arguments[k + 1]!.mvarId!
    unless ← isDefEq (← limitGoal.getType) (← inferType limitProof) do
      throwError
        "cas internal error: the primitive's limit statement does not match the \
         improper integral theorem"
    limitGoal.assign limitProof
  for k in [1 + limitProofs.size:arguments.size] do
    let premiseGoal := arguments[k]!.mvarId!
    let some premiseProof ← proveIntegrabilityPremise (← premiseGoal.getType) requirementsSyntax?
      | throwError (signFailureMessage application.function)
    premiseGoal.assign premiseProof
  let requirementsProof ←
    Projection.proveRequirements arguments[0]! requirementsSyntax?
      (some found.requirementsEquation)
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars (mkAppN base arguments)
  if proof.hasMVar ∨ proof.hasSorry then
    throwError "cas constructed incomplete improper integral evidence"
  unless ← isTypeCorrect proof do
    throwError "cas constructed ill-typed improper integral evidence"
  let integrability ← mkAppM ``And.left #[proof]
  let projectionProof ← mkAppM ``And.right #[proof]
  -- Move both halves from `Set.Ioi a` to `Set.Ici a` and from `Set.Iic a` to `Set.Iio a`.
  let moveIntegrability (target : Name) (tactic : TSyntax `tactic) :
      TacticM (Option Expr) := do
    let source ← instantiateMVars (← inferType integrability)
    let source := source.consumeMData
    let endpoint := match application.domain with
      | .ici endpoint | .iio endpoint => endpoint
      | _ => default
    let statement := mkApp (mkApp source.appFn!.appFn! (← mkAppM target #[endpoint]))
      source.appArg!
    let move? ← Limits.proveByTactic? (← mkArrow source statement) tactic
    return move?.map (mkApp · integrability)
  let (projectionProof, integrabilityProof?) ←
    match application.domain with
    | .ici endpoint =>
        let rewrite ← domainRewrite application integrandFunction endpoint ``Set.Ici ``Set.Ioi
          (← `(tactic| exact MeasureTheory.integral_Ici_eq_integral_Ioi))
          "the closed half-line could not be reduced to the open one"
        let moved ← moveIntegrability ``Set.Ici
          (← `(tactic|
            exact fun h ↦ (_root_.integrableOn_Ici_iff_integrableOn_Ioi (by simp)).mpr h))
        pure (← mkEqTrans rewrite projectionProof, moved)
    | .iio endpoint =>
        let rewrite ← domainRewrite application integrandFunction endpoint ``Set.Iio ``Set.Iic
          (← `(tactic|
            first
              | exact MeasureTheory.integral_Iic_eq_integral_Iio.symm
              | rw [MeasureTheory.integral_Iic_eq_integral_Iio]))
          "the open half-line could not be reduced to the closed one"
        let moved ← moveIntegrability ``Set.Iio
          (← `(tactic| exact fun h ↦ h.mono_set Set.Iio_subset_Iic_self))
        pure (← mkEqTrans rewrite projectionProof, moved)
    | _ => pure (projectionProof, some integrability)
  return {
    theoremName
    certificate
    projectionProof
    integrabilityProof?
    requirementsProof
    localDefinitions := reflected.localDefinitions
  }

end CAS.Tactic.Integration.Improper

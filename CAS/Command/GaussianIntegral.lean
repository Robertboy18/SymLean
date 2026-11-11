/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Erf
public import CAS.Command.Integration
public import CAS.IntegrationTactic

/-!
# Gaussian integrals in `#cas [integrate x]` and `cas`

The integrand `c e ^ (-α x ^ 2 + β x + γ)` with rational coefficients and `α > 0` has the
primitive `CAS.gaussianPrimitive α β γ c`, written with `CAS.erf`. The primitive is registered
twice.

* `gaussianIntegralBackend` is a backend of `#cas [integrate x]` and `#cas [integrate]`. It prints
  the report of `CAS.Command.Erf.logGaussianIntegral`, with the derivative and the interval
  integrals proved, and declines every other integrand, which then goes to the general
  integrator.
* `gaussianIntegralRoute` is a route of `cas` for the goals `∫ x in a..b, f x = v` with such an
  `f`. `CAS.integral_gaussian_eq` turns the integral into the difference of the primitive at the
  endpoints, which is written as `#cas [integrate x]` prints it and compared with `v`.

## Implementation notes

The antiderivative planner does not find these primitives, since `Verified.Expr` has no `erf`,
so we give the Gaussian its own backend and route. The theory is in
`CAS/Analysis/SpecialFunctions/Erf.lean`: completing the square writes the exponent as
`γ + β ^ 2 / (4 α) - (√α (x - β / (2 α))) ^ 2`, `CAS.hasDerivAt_gaussianPrimitive` follows by
the chain rule from `CAS.hasDerivAt_erf`, and `CAS.integral_gaussian_eq` from Mathlib's
`intervalIntegral.integral_eq_sub_of_hasDerivAt`. Both forms read the coefficients with
`FourierTransform.gauss?`, `Laplace.ratOf?` and `FourierTransform.quad?`, the readers of
`#cas [fourierTransform x ξ]`; the route first reflects the integrand of the goal
(`Tactic.Integration.Reflection.reflectFunction`) and reads it back as a `Verified.Expr`.

Nothing is searched and no Boolean certificate is decided. The backend proves the derivative and
the interval integrals together by a tactic script built in `CAS/Command/Erf.lean`, and the
kernel checks the conjunction once (`CAS.Tactic.Explanation.kernelCheckedProof`). The route
closes its goal with `CAS.integral_gaussian_eq`, the equation between `CAS.gaussianPrimitive` and
the printed primitive that `Erf.primitiveEquation` proves, and `norm_num` with `CAS.erf_zero` and
`CAS.erf_neg`; `Tactic.ProofCarrier.runClosingMainGoal` requires the script to close exactly the
main goal and validates the proof.
-/

public meta section

namespace CAS.Command.GaussianIntegral

open Lean Elab Command Meta Tactic

/-- `#cas [integrate x] e` and `#cas [integrate] e` for `e = c e ^ (-α x ^ 2 + β x + γ)` with
rational coefficients and `α > 0`: the report of `Erf.logGaussianIntegral`. Every other integrand
is declined, with the answer `false`. -/
@[cas_route integrate]
def gaussianIntegralBackend : Tactic.RouteRegistry.CommandBackend := fun stx ↦ do
  let run (x : Name) (e : TSyntax `term) : CommandElabM Bool := do
    try
      Erf.logGaussianIntegral stx x e
      return true
    catch ex =>
      match ex with
      | .internal id _ => if id == unsupportedSyntaxExceptionId then return false else throw ex
      | _ => throw ex
  match stx with
  | `(#cas [integrate $x:ident] $e:term) => run x.getId e
  | `(#cas [integrate] $e:term) =>
      match ← Erf.freeIdents e with
      | some [x] => run x e
      | _ => return false
  | _ => return false

/-- Whether a goal is an equation `∫ x in a..b, f x = v` with `Real.exp` in `f`. This is the
cheap test that selects `gaussianIntegralRoute`, which then reads the integrand. -/
def isGaussianIntervalIntegralGoal : Tactic.RouteRegistry.GoalPredicate := fun target ↦ do
  let some (_, lhs, _) := target.consumeMData.eq? | return false
  let some application :=
      Tactic.Integration.Reflection.intervalIntegralApplication? lhs.consumeMData
    | return false
  return (application.function.find? (·.isConstOf ``Real.exp)).isSome

/-- The coefficients `(c, α, β, γ)` of the main goal `∫ x in a..b, f x = v` when
`f x = c e ^ (-α x ^ 2 + β x + γ)` with rational coefficients and `α > 0`, read from the
reflection of `f`. The answer is `none` for every other goal, and for an integrand with
parameters other than `x`. -/
def gaussianCoefficients? : TacticM (Option (ℚ × ℚ × ℚ × ℚ)) := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some (_, lhs, _) := target.consumeMData.eq? | return none
  let some application :=
      Tactic.Integration.Reflection.intervalIntegralApplication? lhs.consumeMData
    | return none
  Tactic.Integration.Reflection.ensureVolumeMeasure application.measure
  let reflected ← Tactic.Integration.Reflection.reflectFunction application.function
  let integrand ← instantiateMVars reflected.reflection.expression
  let index ← Tactic.KernelReadBack.finIndexOfType (← inferType integrand)
  let some bound ← Tactic.KernelReadBack.finBound? index | return none
  unless (← Tactic.KernelReadBack.kernelWhnf bound).rawNatLit? == some 1 do return none
  let expression : Verified.Expr (Fin 1) :=
    (← Tactic.KernelReadBack.readBackExpression index integrand).mapVars fun _ ↦ .var 0
  let some (cE, A) := FourierTransform.gauss? expression | return none
  let some c := Laplace.ratOf? cE | return none
  let some [γ, β, a2] := FourierTransform.quad? A | return none
  unless a2 < 0 && c ≠ 0 do return none
  return some (c, -a2, β, γ)

/-- Bare `cas` on `∫ x in a..b, f x = v` with `f x = c e ^ (-α x ^ 2 + β x + γ)`, rational
coefficients and `α > 0`. The integrand is written as `c * Real.exp (-α * x ^ 2 + β * x + γ)` by
`ring_nf`, `CAS.integral_gaussian_eq` turns the integral into
`gaussianPrimitive α β γ c b - gaussianPrimitive α β γ c a`, and `Erf.primitiveEquation` writes
the primitive as `#cas [integrate x]` prints it. The difference is compared with `v` by `ring_nf`
or `field_simp`, after `erf 0 = 0` and `erf (-y) = -erf y`. -/
@[cas_route integral (priority := high) (goal := isGaussianIntervalIntegralGoal)]
def gaussianIntegralRoute : Tactic.RouteRegistry.Closer := fun _ ↦ do
  let some (c, α, β, γ) ← gaussianCoefficients?
    | throwError "cas: the integrand is not c * exp (-α * x ^ 2 + β * x + γ) with rational \
        coefficients and α > 0"
  let cT ← Laplace.realLit c
  let αT ← Laplace.realLit α
  let βT ← Laplace.realLit β
  let γT ← Laplace.realLit γ
  let hI := mkIdent `hP
  let hP ← Erf.primitiveEquation c α β γ hI (mkIdent `x)
  let script ← `(tactic| (
    have hα : (0 : ℝ) < $αT := by norm_num
    $hP:tactic
    refine ((intervalIntegral.integral_congr fun x _ ↦ ?_).trans
      (CAS.integral_gaussian_eq hα $βT $γT $cT _ _)).trans ?_
    all_goals first
      | (ring_nf; done)
      | (simp only [$hI:ident]
         try norm_num only [CAS.erf_zero, CAS.erf_neg, mul_zero, zero_mul, mul_one, one_mul,
           sub_zero, zero_sub, add_zero, zero_add, neg_zero, neg_mul, mul_neg, sub_neg_eq_add,
           neg_neg]
         first | done | (ring_nf; done) | (field_simp; done) | (field_simp; ring_nf; done))))
  discard <| Tactic.ProofCarrier.runClosingMainGoal "Gaussian interval integral"
    (evalTactic script)
  return {
    replay := ← `(tactic| cas)
    plannerMetadata := #[{
      label := "Gaussian integral"
      status := .selected
      detail := "CAS.integral_gaussian_eq, with the primitive written by CAS.erf"
    }]
    finalAttribution? := some ``CAS.integral_gaussian_eq
  }

end CAS.Command.GaussianIntegral

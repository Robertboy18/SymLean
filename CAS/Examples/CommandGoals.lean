/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Regularity, iterated derivatives, limits, sign conditions and real roots with bare `cas`

Bare `cas` proves continuity, differentiability on a set and analyticity of elementary functions,
iterated derivatives of a literal order, and nested derivatives under a hypothesis at the point.
It proves the statements of `#cas [limit]`, `#cas [reduce]` and `#cas [roots]` as goals: limits at
a rational point or at `atTop` and `atBot`, finite or infinite, polynomial sign conditions for
every real value, counts of distinct real roots, and roots in an interval. A `@[cas_deriv]`
theorem teaches it the derivative of a function the reflection cannot read. The refusals check a
wrong limit value at a point and at infinity, the wrong sign of an infinite limit, the two-sided
limit at a pole of odd order, a quotient whose denominator is not valid at the point, a wrong root
count, and a sign condition that fails. `cas?` reports the theorem that restates a limit for the
goal.
-/

@[expose] public section

namespace CAS.Examples.CommandGoals

set_option linter.hashCommand false

open Filter Topology _root_.Polynomial

/-! ## Regularity -/

/-- `log x / x` is continuous on the positive reals. -/
theorem continuousOn_log_div_self : ContinuousOn (fun x ↦ Real.log x / x) (Set.Ioi 0) := by
  cas

/-- The square root is differentiable on the positive reals. -/
theorem differentiableOn_sqrt : DifferentiableOn ℝ Real.sqrt (Set.Ioi 0) := by
  cas

/-- `exp (sin x) / (1 + x ^ 2)` is analytic at `0`. -/
theorem analyticAt_exp_sin_div : AnalyticAt ℝ (fun x ↦ Real.exp (Real.sin x) / (1 + x ^ 2)) 0 := by
  cas

example : Continuous (fun x : ℝ ↦ Real.sin x * Real.exp x) := by
  cas

example : AnalyticOnNhd ℝ (fun x : ℝ ↦ 1 / (1 + x ^ 2)) Set.univ := by
  cas

/--
info: 'CAS.Examples.CommandGoals.continuousOn_log_div_self' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms continuousOn_log_div_self

/--
info: 'CAS.Examples.CommandGoals.differentiableOn_sqrt' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms differentiableOn_sqrt

/--
info: 'CAS.Examples.CommandGoals.analyticAt_exp_sin_div' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms analyticAt_exp_sin_div

/-! ## Iterated and nested derivatives -/

/-- The third derivative of `sin (2 x)`. -/
theorem iteratedDeriv_three_sin_two_mul (x : ℝ) :
    iteratedDeriv 3 (fun x ↦ Real.sin (2 * x)) x = -8 * Real.cos (2 * x) := by
  cas

example (x : ℝ) (hx : 0 < x) : iteratedDerivWithin 2 Real.log (Set.Ioi 0) x = -(x ^ 2)⁻¹ := by
  cas

/-- The second derivative of the square root at a positive point, from the hypothesis `0 < x`
at that point alone. -/
theorem deriv_deriv_sqrt (x : ℝ) (hx : 0 < x) :
    deriv (fun x ↦ deriv Real.sqrt x) x = -1 / (4 * x * Real.sqrt x) := by
  cas

/--
info: 'CAS.Examples.CommandGoals.iteratedDeriv_three_sin_two_mul' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms iteratedDeriv_three_sin_two_mul

/--
info: 'CAS.Examples.CommandGoals.deriv_deriv_sqrt' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms deriv_deriv_sqrt

/-! ## Limits -/

example : Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by
  cas

example : Tendsto (fun x : ℝ ↦ (x ^ 2 - 1) / (x - 1)) (𝓝[>] 1) (𝓝 2) := by
  cas

example : Tendsto (fun x : ℝ ↦ Real.exp x + x) (𝓝 0) (𝓝 1) := by
  cas

/-- The removable singularity does not change Lean's value `sin 0 / 0 = 0`, so the limit on the
full neighbourhood is refused. -/
example : True := by
  fail_if_success have : Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝 0) (𝓝 1) := by cas
  trivial

/--
error: cas could not prove this statement of a `#cas` command.
Command theorem route:
  cas limit route: the limit is 1, not 2
-/
#guard_msgs (error, substring := true) in
example : Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝[≠] 0) (𝓝 2) := by
  cas

/-- The limit of a rational function at `atTop`, as `#cas [limit x → ∞]` proves it. -/
theorem tendsto_div_atTop :
    Tendsto (fun x : ℝ ↦ (x ^ 2 + 1) / (2 * x ^ 2 - 3)) atTop (𝓝 (1 / 2)) := by
  cas

/-- An infinite limit at `atTop`. -/
theorem tendsto_sq_atTop : Tendsto (fun x : ℝ ↦ x ^ 2) atTop atTop := by
  cas

/-- The limit of the square root at `1/10000`, a point close to the boundary of its domain:
the domain checker certifies the point and the theorem extends validity to a neighbourhood. -/
theorem tendsto_sqrt : Tendsto Real.sqrt (𝓝 (1 / 10000)) (𝓝 (1 / 100)) := by
  cas

example : Tendsto (fun x : ℝ ↦ x * Real.exp (-x)) atTop (𝓝 0) := by
  cas

example : Tendsto (fun x : ℝ ↦ 1 / x ^ 2) (𝓝[≠] 0) atTop := by
  cas

/-- An infinite limit at `atBot`. -/
example : Tendsto (fun x : ℝ ↦ x ^ 3) atBot atBot := by
  cas

/--
error: cas could not prove this statement of a `#cas` command.
Command theorem route:
  cas limit route: the limit is atBot, not atTop
-/
#guard_msgs (error, substring := true) in
example : Tendsto (fun x : ℝ ↦ x ^ 3) atBot atTop := by
  cas

/-- The two one-sided limits of `1 / x` at its pole of order `1`. -/
example : Tendsto (fun x : ℝ ↦ 1 / x) (𝓝[>] 0) atTop := by
  cas

example : Tendsto (fun x : ℝ ↦ 1 / x) (𝓝[<] 0) atBot := by
  cas

/--
error: cas could not prove this statement of a `#cas` command.
Command theorem route:
  cas limit route: 0 is a pole of odd order 1; the route proves the limit atTop on `𝓝[>] 0` and
  atBot on `𝓝[<] 0`, so there is no limit on `𝓝[≠] 0`
-/
#guard_msgs (error, whitespace := lax, substring := true) in
example : Tendsto (fun x : ℝ ↦ 1 / x) (𝓝[≠] 0) atTop := by
  cas

-- Away from `0` the function is `1 / (x + 1)`, and its limit at `0` is `1`. The exact values of
-- the symbolic derivatives at `0`, with `0 / 0 = 0`, suggest a pole of order `1`, but `x / x` is
-- not valid at `0`, and the route refuses the quotient before it states a limit or a pole.
/--
error: cas could not prove this statement of a `#cas` command.
Command theorem route:
  cas limit route: the domain checker did not certify that the denominator and its derivatives
  through order 1 are defined at 0
-/
#guard_msgs (error, whitespace := lax, substring := true) in
example : Tendsto (fun x : ℝ ↦ 1 / (x + x / x)) (𝓝[≠] 0) (𝓝 1) := by
  cas

-- `cas?` names the theorem that restates the computed limit for the goal.
/--
  [CAS.explanation.checkedStep] final proof assigned to the original goal
    Proposition: Tendsto (fun x ↦ Real.sin x / x) (𝓝[≠] 0) (𝓝 1)
    Validation: completed proof checked by the elaborator; kernel check occurs when the
    declaration is accepted
    Theorem: Verified.Expr.tendsto_div_of_univariateEval
-/
#guard_msgs (info, whitespace := lax, substring := true) in
set_option cas.verbose true in
example : Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by
  cas?

/--
error: cas could not prove this statement of a `#cas` command.
Command theorem route:
  cas limit route: the limit is 1/2, not 1
-/
#guard_msgs (error, substring := true) in
example : Tendsto (fun x : ℝ ↦ (x ^ 2 + 1) / (2 * x ^ 2 - 3)) atTop (𝓝 1) := by
  cas

/--
error: cas could not prove this statement of a `#cas` command.
Command theorem route:
  cas limit route: the limit is atTop, not 1
-/
#guard_msgs (error, substring := true) in
example : Tendsto (fun x : ℝ ↦ x ^ 2) atTop (𝓝 1) := by
  cas

/--
info: 'CAS.Examples.CommandGoals.tendsto_div_atTop' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_div_atTop

/--
info: 'CAS.Examples.CommandGoals.tendsto_sq_atTop' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_sq_atTop

/--
info: 'CAS.Examples.CommandGoals.tendsto_sqrt' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_sqrt

/-! ## Sign conditions -/

example : ∀ x : ℝ, x ^ 4 - 4 * x + 3 ≥ 0 := by
  cas

example (x : ℝ) : x ^ 4 - 4 * x + 3 ≥ 0 := by
  cas

example : ∀ x : ℝ, 0 < x ^ 2 - x + 1 := by
  cas

/-- `x ^ 4 - 4 x + 3` vanishes at `1`, so the strict inequality is refused. -/
example : True := by
  fail_if_success have : ∀ x : ℝ, x ^ 4 - 4 * x + 3 > 0 := by cas
  trivial

/-! ## Real roots -/

example : Fintype.card ((X ^ 5 - 4 * X + 2 : ℚ[X]).rootSet ℝ) = 3 := by
  cas

/-- A statement of a command that the command route does not take still reaches the other
routes: here the supplied equation simplifies the root set. -/
example (p : ℚ[X]) (h : p = 0) : Fintype.card (p.rootSet ℝ) = 0 := by
  set_option cas.grindHeartbeats 0 in cas [h]

/-- A double root counts once. -/
example : Fintype.card ((X ^ 2 - 2 * X + 1 : ℚ[X]).rootSet ℝ) = 1 := by
  cas

example : Fintype.card ((X ^ 4 - 5 * X ^ 2 + 4 : ℤ[X]).rootSet ℝ) = 4 := by
  cas

/--
error: cas could not prove this statement of a `#cas` command.
Command theorem route:
  cas root route: the polynomial has exactly 1 distinct real roots (certified), not 2
-/
#guard_msgs (error, substring := true) in
example : Fintype.card ((X ^ 2 - 2 * X + 1 : ℚ[X]).rootSet ℝ) = 2 := by
  cas

example : ∃ x : ℝ, x ^ 3 - x - 1 = 0 ∧ 21 / 16 < x ∧ x ≤ 43 / 32 := by
  cas

/-- An exact rational root is its own witness. -/
example : ∃ x : ℝ, x ^ 3 = 2 * x ^ 2 + x - 2 ∧ 3 / 2 < x := by
  cas

/-- No root of `x ^ 2 - 2` lies in `[2, 3]`. -/
example : True := by
  fail_if_success have : ∃ x : ℝ, x ^ 2 - 2 = 0 ∧ 2 ≤ x ∧ x ≤ 3 := by cas
  trivial

/-! ## A derivative rule -/

/-- The Gaussian integral from `0` to `x`, which the reflection cannot read. -/
noncomputable def gaussianIntegral (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)

/-- The fundamental theorem of calculus for `gaussianIntegral`. -/
theorem hasDerivAt_gaussianIntegral (x : ℝ) :
    HasDerivAt gaussianIntegral (Real.exp (-x ^ 2)) x :=
  (Continuous.integral_hasStrictDerivAt (by fun_prop) 0 x).hasDerivAt

/-- Before the rule is registered `cas` unfolds `gaussianIntegral`, cannot read the integral
and fails, so the chain rule is applied by hand. -/
example (x : ℝ) :
    deriv (fun x ↦ gaussianIntegral (2 * x)) x = 2 * Real.exp (-(2 * x) ^ 2) := by
  fail_if_success cas
  have h := (hasDerivAt_gaussianIntegral (2 * x)).comp x ((hasDerivAt_id x).const_mul 2)
  rw [show (fun x ↦ gaussianIntegral (2 * x)) = gaussianIntegral ∘ fun x ↦ 2 * x from rfl,
    h.deriv]
  ring

attribute [cas_deriv] hasDerivAt_gaussianIntegral

/-- With the rule registered, `cas` keeps `gaussianIntegral` folded and applies the rule with
the chain rule. -/
theorem deriv_gaussianIntegral_two_mul (x : ℝ) :
    deriv (fun x ↦ gaussianIntegral (2 * x)) x = 2 * Real.exp (-(2 * x) ^ 2) := by
  cas

example (x : ℝ) : deriv (fun x ↦ gaussianIntegral (x ^ 2)) x = 2 * x * Real.exp (-x ^ 4) := by
  cas

/--
info: 'CAS.Examples.CommandGoals.deriv_gaussianIntegral_two_mul' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms deriv_gaussianIntegral_two_mul

end CAS.Examples.CommandGoals

end

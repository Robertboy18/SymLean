/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Definite and improper integrals

`#cas [integrate x in [a, b]] f` finds a primitive `F` of `f` with `integrate?`, prints the value
`F b - F a` and proves the theorem `∫ x in a..b, f = v` by `cas`. An endpoint may be `∞` or `-∞`.
The value then takes the limit of `F` at that end, and the theorem states, over `Set.Ioi a`,
`Set.Iic b` or the whole line, that `f` is integrable there and that its integral is the value.
When no primitive is found, the refusal names `#cas [nintegrate x in [a, b]] f`, which encloses
the value numerically. The command also refuses,
before any proof, a primitive whose conditions it cannot prove on a bounded interval: the primitive
of `1 / (2 + cos x)` jumps at `π`, where `cos x + 1 ≠ 0` fails, so its value on `[0, 4]` is
refused. It refuses as well when a proof attempt runs out of heartbeats, as for the same integrand
on `[0, 1]`, where the kernel check of the primitive's certificate needs more than the quarter of
`maxHeartbeats` that the kernel checks of an attempt get.

`cas` proves the same theorems directly, an improper integral with or without its integrability.
An integrand that changes sign on a half-line needs its integrability as evidence: without it
`cas` refuses `∫ x in Set.Ioi 0, (1 - x) * exp (-x) = 0`, and with it, given by `using`, proves
it. A condition of the primitive that holds on a bounded
interval with rational endpoints, such as `cos t ≠ 0` for `tan x ^ 2` on `[0, 1]`, is proved by
the box route of `cas`. The theorems depend only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/-! ### The command -/

/--
info: #cas [integrate x in [0, 1]]
Domain: x ∈ ℝ
Input (scalar ℝ): (x * exp x)
Output (scalar ℝ; definite integral): 1
Theorem: ∫ (x : ℝ) in 0..1, x * Real.exp x = 1
-/
#guard_msgs (info, substring := true) in
#cas [integrate x in [0, 1]] (x * exp x)

/--
info: #cas [integrate x in [0, π]]
Domain: x ∈ ℝ
Input (scalar ℝ): (sin x ^ 2)
Output (scalar ℝ; definite integral): 1/2*pi
Theorem: ∫ (x : ℝ) in 0..Real.pi, Real.sin x ^ 2 = 1 / 2 * Real.pi
-/
#guard_msgs (info, substring := true) in
#cas [integrate x in [0, π]] (sin x ^ 2)

/--
info: #cas [integrate x in [0, ∞]]
Domain: x ∈ ℝ
Input (scalar ℝ): (exp (-x))
Output (scalar ℝ; definite integral): 1
Theorem: MeasureTheory.IntegrableOn (fun x ↦ Real.exp (-x)) (Set.Ioi 0) MeasureTheory.volume ∧
  ∫ (x : ℝ) in Set.Ioi 0, Real.exp (-x) = 1
-/
#guard_msgs (info, substring := true) in
#cas [integrate x in [0, ∞]] (exp (-x))

/--
info: #cas [integrate x in [-∞, 0]]
Domain: x ∈ ℝ
Input (scalar ℝ): (exp x)
Output (scalar ℝ; definite integral): 1
Theorem: MeasureTheory.IntegrableOn (fun x ↦ Real.exp x) (Set.Iic 0) MeasureTheory.volume ∧
  ∫ (x : ℝ) in Set.Iic 0, Real.exp x = 1
-/
#guard_msgs (info, substring := true) in
#cas [integrate x in [-∞, 0]] (exp x)

/--
info: #cas [integrate x in [-∞, ∞]]
Domain: x ∈ ℝ
Input (scalar ℝ): (1 / (1 + x ^ 2))
Output (scalar ℝ; definite integral): pi
Theorem: MeasureTheory.Integrable (fun x ↦ 1 / (1 + x ^ 2)) MeasureTheory.volume ∧
∫ (x : ℝ), 1 / (1 + x ^ 2) = Real.pi
-/
#guard_msgs (info, whitespace := lax, substring := true) in
#cas [integrate x in [-∞, ∞]] (1 / (1 + x ^ 2))

/--
error: the checked integrator found no supported antiderivative in coordinate 'x', so the
integral has no exact value here. For a numerical value use
`#cas [nintegrate x in [0, 1]] (exp (x ^ 2))`.
-/
#guard_msgs in
#cas [integrate x in [0, 1]] (exp (x ^ 2))

/--
error: `cas` did not prove the value 4*atan(2*sin(4)/(1 + cos(4))/sqrt(12))/sqrt(12) of the
integral: it could not prove that the conditions of the primitive 4*atan(2*sin(x)/(1 +
cos(x))/sqrt(12))/sqrt(12) hold on the interval (cos(x) + 1 ≠ 0; sin(x)^4 - 5*sin(x)^2*cos(x) -
11*sin(x)^2 + 12*cos(x) + 12 ≠ 0; cos(x) + 2 ≠ 0). Where they fail, the difference of the
primitive's values at the endpoints need not be the integral. For a numerical value use `#cas
[nintegrate x in [0, 4]] (1 / (2 + cos x))`.
-/
#guard_msgs in
#cas [integrate x in [0, 4]] (1 / (2 + cos x))

-- On `[0, 1]` and `[-1, 1]` the conditions hold, but the kernel check of the primitive's
-- certificate needs more than the quarter of `maxHeartbeats` that the kernel checks of an attempt
-- get.
/--
error: `cas` did not prove the value 4*atan(2*sin(1)/(1 + cos(1))/sqrt(12))/sqrt(12) of the
integral: its proof ran out of heartbeats, `maxHeartbeats` (200000 thousand) for the elaboration of
an attempt and a quarter of it for each kernel check; `set_option maxHeartbeats` raises both. For a
numerical value use `#cas [nintegrate x in [0, 1]] (1 / (2 + cos x))`.
-/
#guard_msgs in
#cas [integrate x in [0, 1]] (1 / (2 + cos x))

/--
error: `cas` did not prove the value (4*atan(2*sin(1)/(1 + cos(1))/sqrt(12)) - 4*atan(2*sin(-1)/(1 +
cos(-1))/sqrt(12)))/sqrt(12) of the integral: its proof ran out of heartbeats, `maxHeartbeats`
(200000 thousand) for the elaboration of an attempt and a quarter of it for each kernel check;
`set_option maxHeartbeats` raises both. For a numerical value use `#cas [nintegrate x in [-1, 1]] (1
/ (2 + cos x))`.
-/
#guard_msgs in
#cas [integrate x in [-1, 1]] (1 / (2 + cos x))

-- On `[0, 1]` the primitive of `1 / (x ^ 2 - 4)` takes logarithms of negative numbers, which the
-- value writes as those of their absolute values, as Lean defines them (`Real.log_neg_eq_log`);
-- the conversion to the stated value rewrites them the same way. On `[1, 2]` the logarithms of
-- `1 / (x ^ 2 - 1 / 4)` are those of positive numbers.
/--
info: #cas [integrate x in [0, 1]]
Domain: x ∈ ℝ
Input (scalar ℝ): (1 / (x ^ 2 - 4))
Output (scalar ℝ; definite integral): 1/4*log(1/3)
Theorem: ∫ (x : ℝ) in 0..1, 1 / (x ^ 2 - 4) = 1 / 4 * Real.log (1 / 3)
Primitive: 1/4*log((2*x - 4)/(2*x + 4))
-/
#guard_msgs (info, substring := true) in
#cas [integrate x in [0, 1]] (1 / (x ^ 2 - 4))

/--
info: #cas [integrate x in [1, 2]]
Domain: x ∈ ℝ
Input (scalar ℝ): (1 / (x ^ 2 - 1 / 4))
Output (scalar ℝ; definite integral): log(3/5) - log(1/3)
Theorem: ∫ (x : ℝ) in 1..2, 1 / (x ^ 2 - 1 / 4) = Real.log (3 / 5) - Real.log (1 / 3)
-/
#guard_msgs (info, substring := true) in
#cas [integrate x in [1, 2]] (1 / (x ^ 2 - 1 / 4))

-- The check of the conditions of the primitive of `1 / (2 + sin x)` on `[0, 4]` runs out of
-- heartbeats, which is a refusal too.
/--
error: `cas` did not prove the value (2*atan((2*sin(4)/(1 + cos(4)) + 1)/sqrt(3)) -
2*atan(1/sqrt(3)))/sqrt(3) of the integral: it could not prove that the conditions of the primitive
2*atan((2*sin(x)/(1 + cos(x)) + 1)/sqrt(3))/sqrt(3) hold on the interval (cos(x) + 1 ≠ 0;
sin(x)^2*cos(x) + 3*sin(x)^2 - 4*cos(x) - 4 ≠ 0; sin(x)^5 + 2*sin(x)^4 - 4*sin(x)^3*cos(x) -
8*sin(x)^3 - 8*sin(x)^2*cos(x) - 16*sin(x)^2 + 8*sin(x)*cos(x) + 8*sin(x) + 16*cos(x) + 16 ≠ 0;
sin(x) + 2 ≠ 0) (the check ran out of heartbeats). Where they fail, the difference of the
primitive's values at the endpoints need not be the integral. For a numerical value use `#cas
[nintegrate x in [0, 4]] (1 / (2 + sin x))`.
-/
#guard_msgs in
#cas [integrate x in [0, 4]] (1 / (2 + sin x))

/-! ### The tactic -/

@[expose] public section

namespace CAS.Examples.Integration.Definite

/-- The exponential over the half-line `(-∞, 0]`. -/
theorem exp_over_Iic : ∫ x in Set.Iic (0 : ℝ), Real.exp x = 1 := by
  cas

/-- `exp (-x)` is integrable on `(0, ∞)` and its integral there is `1`. -/
theorem integrableOn_exp_neg_Ioi :
    MeasureTheory.IntegrableOn (fun x : ℝ ↦ Real.exp (-x)) (Set.Ioi 0) ∧
      ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) = 1 := by
  cas

/-- The same on the closed half-line `[0, ∞)`, with the equality written the other way round. -/
theorem integrableOn_exp_neg_Ici :
    MeasureTheory.IntegrableOn (fun x : ℝ ↦ Real.exp (-x)) (Set.Ici 0) ∧
      1 = ∫ x in Set.Ici (0 : ℝ), Real.exp (-x) := by
  cas

/-- `exp x` is integrable on `(-∞, 0)` and its integral there is `1`. -/
theorem integrableOn_exp_Iio :
    MeasureTheory.IntegrableOn (fun x : ℝ ↦ Real.exp x) (Set.Iio 0) ∧
      ∫ x in Set.Iio (0 : ℝ), Real.exp x = 1 := by
  cas

/-- `1 / (1 + x ^ 2)` is integrable on the whole line and its integral is `π`. -/
theorem integrable_cauchy :
    MeasureTheory.Integrable (fun x : ℝ ↦ 1 / (1 + x ^ 2)) ∧
      ∫ x : ℝ, 1 / (1 + x ^ 2) = Real.pi := by
  cas

/-- `(1 - x) exp (-x)` changes sign at `1`, so no sign condition on `(0, ∞)` gives its
integrability; with the integrability as the hypothesis `h`, `cas using h` proves the value, the
limit `0` of the primitive `x exp (-x)` minus its value `0` at `0`. -/
theorem one_sub_mul_exp_neg_over_Ioi
    (h : MeasureTheory.IntegrableOn (fun x : ℝ ↦ (1 - x) * Real.exp (-x)) (Set.Ioi 0)) :
    ∫ x in Set.Ioi (0 : ℝ), (1 - x) * Real.exp (-x) = 0 := by
  cas using h

-- Without the integrability of the sign-changing integrand, `cas` refuses.
/--
Integral route:
  cas found a checked antiderivative for this improper integral but could not prove the
  integrand integrable on its domain
-/
#guard_msgs (error, whitespace := lax, substring := true) in
example : ∫ x in Set.Ioi (0 : ℝ), (1 - x) * Real.exp (-x) = 0 := by
  cas

/-- A whole-line integral. The primitive `-1 / (1 + exp x)` tends to `0` at `∞` and to `-1` at
`-∞`. -/
theorem logistic_over_line : ∫ x : ℝ, Real.exp x / (1 + Real.exp x) ^ 2 = 1 := by
  cas

/-- The whole-line integral of `1 / (1 + x ^ 2)`, from the limits `π / 2` and `-(π / 2)` of
`arctan`. -/
theorem cauchy_over_line : ∫ x : ℝ, 1 / (1 + x ^ 2) = Real.pi := by
  cas

/-- A polynomial in `sin x` and `cos x`, integrated monomial by monomial. -/
theorem sin_sq_mul_cos_sq_over_pi :
    ∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ 2 * Real.cos x ^ 2 = Real.pi / 8 := by
  cas

/-- The primitive `tan x - x` needs `cos t ≠ 0` for `t` in `[0, 1]`, which the box route proves
from `0 ≤ t` and `t ≤ 1`. -/
theorem tan_sq_over_unit : ∫ x in (0 : ℝ)..1, Real.tan x ^ 2 = Real.tan 1 - 1 := by
  cas

/-- A Gaussian integral, whose value is written with `CAS.erf`. -/
theorem gaussian_over_unit : ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2) = √Real.pi / 2 * CAS.erf 1 := by
  cas

/-- An exponential times a sine with symbolic slopes. The primitive needs `a ^ 2 + b ^ 2 ≠ 0`. -/
theorem exp_mul_sin_over_unit (a b : ℝ) (h : a ^ 2 + b ^ 2 ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.exp (a * x) * Real.sin (b * x) =
      (Real.exp a * (a * Real.sin b - b * Real.cos b) + b) / (a ^ 2 + b ^ 2) := by
  cas using h

/-- info: 'CAS.Examples.Integration.Definite.exp_over_Iic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exp_over_Iic

/-- info: 'CAS.Examples.Integration.Definite.integrableOn_exp_neg_Ioi' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integrableOn_exp_neg_Ioi

/-- info: 'CAS.Examples.Integration.Definite.integrableOn_exp_neg_Ici' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integrableOn_exp_neg_Ici

/-- info: 'CAS.Examples.Integration.Definite.integrableOn_exp_Iio' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integrableOn_exp_Iio

/-- info: 'CAS.Examples.Integration.Definite.integrable_cauchy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integrable_cauchy

/-- info: 'CAS.Examples.Integration.Definite.one_sub_mul_exp_neg_over_Ioi' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_sub_mul_exp_neg_over_Ioi

/-- info: 'CAS.Examples.Integration.Definite.logistic_over_line' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms logistic_over_line

/-- info: 'CAS.Examples.Integration.Definite.cauchy_over_line' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cauchy_over_line

/-- info: 'CAS.Examples.Integration.Definite.sin_sq_mul_cos_sq_over_pi' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sin_sq_mul_cos_sq_over_pi

/-- info: 'CAS.Examples.Integration.Definite.tan_sq_over_unit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tan_sq_over_unit

/-- info: 'CAS.Examples.Integration.Definite.gaussian_over_unit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gaussian_over_unit

/-- info: 'CAS.Examples.Integration.Definite.exp_mul_sin_over_unit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exp_mul_sin_over_unit

end CAS.Examples.Integration.Definite

end

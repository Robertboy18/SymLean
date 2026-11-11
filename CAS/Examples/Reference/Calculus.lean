/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Calculus

The compiled examples of the docstrings of the Calculus family: derivatives and gradients,
antiderivatives and definite integrals, limits, Taylor and Laurent series, and the extrema of
polynomials. Each section pins the report lines that a docstring shows and proves its theorem,
and checks the axioms of that proof.
-/

@[expose] public section

namespace CAS.Examples.Reference.Calculus

set_option linter.hashCommand false

/-! ## derive -/

/--
Output (scalar ℝ): x*(2*sin(x) + x*cos(x))
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [derive x] (x ^ 2 * sin x)

/--
Output (scalar ℝ): 1/sqrt(2*x + 2)
Conditions: x + 1 > 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [derive x] (sqrt (2 * x + 2))

/--
Output (scalar ℝ): cos(x*y)*y
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [derive x] (sin (x * y))

theorem derive_product (x : ℝ) :
    HasDerivAt (fun x ↦ x ^ 2 * Real.sin x) (2 * x * Real.sin x + x ^ 2 * Real.cos x) x := by
  cas

/--
info: 'CAS.Examples.Reference.Calculus.derive_product' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms derive_product

/--
unsupported symbolic function 'gamma'; expected abs, sin, cos, tan, sinh, cosh, tanh,
atan/arctan, asin/arcsin, acos/arccos, exp, log, or sqrt
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [derive x] (gamma x)

/--
coordinate 'x' does not match the function parameter 't'; use the parameter name or omit the
coordinate
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [derive x] (fun t : ℝ ↦ t ^ 2)

/-! ## grad -/

/--
Output (vector ℝ^2; order x, y): (2*x*y, x^2 + 3*y^2)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [grad x, y] (x ^ 2 * y + y ^ 3)

/--
Output (vector ℝ^2; order x, y): (cos(x*y)*y, cos(x*y)*x)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [grad x, y] (sin (x * y))

theorem grad_first_component (x y : ℝ) :
    HasDerivAt (fun x ↦ x ^ 2 * y + y ^ 3) (2 * x * y) x := by
  cas

/--
info: 'CAS.Examples.Reference.Calculus.grad_first_component' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms grad_first_component

/--
expression contains undeclared variables: y
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [grad x] (x * y)

/-! ## integrate -/

/--
Output (scalar ℝ; antiderivative): -(1/2*cos(x^2))
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [integrate x] (x * sin (x ^ 2))

/--
Output (scalar ℝ; antiderivative): log(log(x))
Conditions: x ≠ 0; log(x) ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [integrate x] (1 / (x * log x))

/--
Output (scalar ℝ; definite integral): 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [integrate x in [0, 1]] (x * exp x)

theorem integrate_by_parts : ∫ x in (0 : ℝ)..1, x * Real.exp x = 1 := by
  cas

/--
info: 'CAS.Examples.Reference.Calculus.integrate_by_parts' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms integrate_by_parts

/--
the checked integrator found no supported antiderivative in coordinate 'x'. Try an equivalent
supported form.
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [integrate x] (exp (x ^ 2))

/--
The denominator has a factor of degree three or more, which is not factored without Hex:
`import CASHex.Factor` (built with `lake -R -Khex=on build CASHex`) factors it
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [integrate x] (1/(x^3 - 1))

/--
#cas [integrate] could not determine the limit at +∞ of the primitive: no decay shape applies to
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [integrate x in [1, ∞]] (1 / x)

/-! ## limit -/

/--
Output (exact limit): 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [limit x → 0] (sin x / x)

/--
Output (exact limit from the terms of order 0): 1/2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [limit x → ∞] ((x^2 + 1) / (2*x^2 - 3))

/--
Output (infinite limit at a pole of order 1): ∞
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [limit x → 0 from above] (1 / x)

/--
Output (limit, the value at the point): 1/100
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [limit x → 1/10000] (sqrt x)

open Filter Topology in
theorem limit_sinc : Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by
  cas

/--
info: 'CAS.Examples.Reference.Calculus.limit_sinc' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms limit_sinc

/--
limit: expected a rational number
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [limit x → π] (sin x)

/--
limit: the domain checker did not certify that the expression is defined at 0; for a quotient
whose denominator vanishes at 0, write it as a single quotient
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [limit x → 0] (sin (1 / x))

/-! ## series -/

/--
Output (Taylor polynomial with exact coefficients): x - 1/6*x^3 + 1/120*x^5 - 1/5040*x^7 + o(x^7)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [series x 0 7] (sin x)

/--
Output (Laurent series with a pole of order 1): 1/x + 1/6*x + 7/360*x^3 + o(x^3)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [series x 0 3] (1 / sin x)

/--
Output (Taylor polynomial with exact coefficients): x - 1 - 1/2*(x - 1)^2 + 1/3*(x - 1)^3
- 1/4*(x - 1)^4 + o((x - 1)^4)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [series x 1 4] (log x)

/--
Output (Taylor polynomial with exact coefficients): 1/100 + 50*(x - 1/10000)
- 125000*(x - 1/10000)^2 + o((x - 1/10000)^2)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [series x 1/10000 2] (sqrt x)

open Filter Topology in
theorem series_sin_remainder
    (h : (fun x : ℝ ↦ Real.sin x - (x - 1 / 6 * x ^ 3)) =o[𝓝 0] fun x ↦ x ^ 3) :
    Tendsto (fun x : ℝ ↦ (Real.sin x - (x - 1 / 6 * x ^ 3)) / x ^ 3) (𝓝 0) (𝓝 0) :=
  h.tendsto_div_nhds_zero

/--
info: 'CAS.Examples.Reference.Calculus.series_sin_remainder' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms series_sin_remainder

/--
series: the domain checker did not certify that the expression and its derivatives through order
3 are defined at 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [series x 0 3] (abs x)

/--
series: the derivative of order 0 at 0 is not an exact rational number (exact values are known for
sin, cos, exp, atan, asin at 0, log, acos at 1, and square roots of rational squares)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [series x 0 3] (log x)

/--
series accepts orders up to 12
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [series x 0 13] (sin x)

/-! ## minimize -/

/--
Output (exact global minimum): min = 3 at x = 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [minimize x] (x^2 - 2*x + 4)

/--
Output (certified enclosure of the global minimum): min ∈ [-0.473, -0.472] near x = 0.62996
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [minimize x] (x^4 - x)

/--
Output (exact minimum on the interval): min = -1 at x = 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [minimize x in [0, 2]] (x^2 - 2*x)

theorem minimize_quadratic : ∀ x : ℝ, 3 ≤ x ^ 2 - 2 * x + 4 := by
  cas

/--
info: 'CAS.Examples.Reference.Calculus.minimize_quadratic' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms minimize_quadratic

/--
minimize: the polynomial is unbounded below (degree 3, leading coefficient 1), so it has no minimum
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [minimize x] (x^3 - x)

/--
minimize needs a polynomial in x with rational coefficients
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [minimize x] (sin x)

/--
minimize accepts between 1 and 6 digits
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (digits := 7) [minimize x] (x^4 - x)

/-! ## maximize -/

/--
Output (exact global maximum): max = 4 at x = 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [maximize x] (3 + 2*x - x^2)

/--
Output (certified enclosure of the maximum on the interval): max ∈ [0.384, 0.385], witness
x = 0.57735 with value ≥ 0.384
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [maximize x in [0, 1]] (x * (1 - x) * (x + 1))

theorem maximize_quadratic : ∀ x : ℝ, 3 + 2 * x - x ^ 2 ≤ 4 := by
  cas

/--
info: 'CAS.Examples.Reference.Calculus.maximize_quadratic' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms maximize_quadratic

/--
maximize: the polynomial is unbounded above (degree 2, leading coefficient 1), so it has no maximum
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [maximize x] (x^2 + 1)

/--
maximize needs rational endpoints a < b
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [maximize x in [1, 0]] (x)

end CAS.Examples.Reference.Calculus

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Rational functions and polynomials: `together`, `apart`, `collect`, `polynomialGCD`, …

The Mathematica-style algebra commands of `CAS.Command.Algebra`. Each command at the end of this
file runs in the build inside `#guard_msgs`, which checks its report, and each report's theorem
is kernel-checked when the command runs. The first block of each mode shows the theorem.

The divisor hypotheses of the `together` and `apart` theorems are needed: under Lean's total
division the identities fail where a divisor vanishes, as the first example shows at `x = 1`.
-/

namespace CAS.Examples.Algebra

/-- Without its hypothesis `x ^ 2 - 1 ≠ 0`, the partial fraction identity is false at `x = 1`,
where `1 / 0 = 0` but the right side is `-1 / 4`. -/
example : ¬ ∀ x : ℝ, 1 / (x ^ 2 - 1) = 1 / (2 * (x - 1)) - 1 / (2 * (x + 1)) := by
  intro h
  have := h 1
  norm_num at this

end CAS.Examples.Algebra

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

-- Together, Cancel, Numerator, Denominator
/--
info: #cas [together]
Domain: (x, y) ∈ ℝ^2
Input (rational function): (1/x + 1/y)
Output (common denominator): (x + y)/(x*y)
Conditions: x ≠ 0; y ≠ 0

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the common-denominator form
        Proposition: ∀ (x y : ℝ), x ≠ 0 → y ≠ 0 → 1 / x + 1 / y = (x + y) / (x * y)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [together] (1/x + 1/y)

/--
info: #cas [together]
Domain: x ∈ ℝ
Input (rational function): (1/(x^2-1) + 1/(x-1))
Output (common denominator): (x + 2)/((x - 1)*(x + 1))
Conditions: x^2 - 1 ≠ 0; x - 1 ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [together] (1/(x^2-1) + 1/(x-1))

/--
info: #cas [together]
Domain: (x, y) ∈ ℝ^2
Input (rational function): (x/2 + y/3)
Output (common denominator): (3*x + 2*y)/6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [together] (x/2 + y/3)

/--
info: #cas [together]
Domain: (x, y) ∈ ℝ^2
Input (rational function): ((x^3 - y^3)/(x^2 - y^2))
Output (common denominator): (x^2 + x*y + y^2)/(x + y)
Conditions: x^2 - y^2 ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [together] ((x^3 - y^3)/(x^2 - y^2))

/--
info: #cas [together]
Domain: (x, y) ∈ ℝ^2
Input (rational function): (1/((x*y + x - x)^2) + 1)
Output (common denominator): (x^2*y^2 + 1)/(x^2*y^2)
Conditions: (x*y + x - x)^2 ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [together] (1/((x*y + x - x)^2) + 1)

/--
info: #cas [cancel]
Domain: x ∈ ℝ
Input (rational function): ((x^2-1)/(x-1) + 1/x)
Output (cancelled): x + 1 + 1/x
Conditions: x - 1 ≠ 0; x ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [cancel] ((x^2-1)/(x-1) + 1/x)

/--
info: #cas [numerator]
Domain: (x, y) ∈ ℝ^2
Input (rational function): (1/x + 1/y)
Output (numerator): x + y
Conditions: x ≠ 0; y ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [numerator] (1/x + 1/y)

/--
info: #cas [denominator]
Domain: x ∈ ℝ
Input (rational function): (1/(x-1) - 1/(x+1))
Output (denominator): (x - 1)*(x + 1)
Conditions: x - 1 ≠ 0; x + 1 ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [denominator] (1/(x-1) - 1/(x+1))

/--
error: together: a divisor is itself a quotient; write the expression with polynomial divisors
-/
#guard_msgs (error, drop info) in
#cas [together] (1/(1 + 1/x))

set_option linter.style.longLine false in
/--
error: together: the expression is not a rational function: it has a function other than the field operations and natural powers
-/
#guard_msgs (error, drop info) in
#cas [together] (sin x / x)

-- Apart (without Hex, over the factors written in the input; `CASHex/Examples.lean` has the
-- complete factorization over `ℚ`)
set_option linter.style.longLine false in
/--
info: #cas [apart]
Domain: x ∈ ℝ
Input (rational function): (1/((x - 1)*(x + 1)))
Output (partial fractions): 1/(2*(x - 1)) - 1/(2*(x + 1))
Conditions: (x - 1)*(x + 1) ≠ 0

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the partial fraction decomposition
        Proposition: ∀ (x : ℝ), (x - 1) * (x + 1) ≠ 0 → 1 / ((x - 1) * (x + 1)) = 1 / (2 * (x - 1)) - 1 / (2 * (x + 1))
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [apart] (1/((x - 1)*(x + 1)))

set_option linter.style.longLine false in
/--
info: #cas [apart]
Domain: x ∈ ℝ
Input (rational function): (x^5/((x^2+1)*(x-1)^3))
Output (partial fractions over the written factors, refined by gcds): 1 + (x + 1)/(4*(x^2 + 1)) + 1/(2*(x - 1)^3) + 2/(x - 1)^2 + 11/(4*(x - 1))
Conditions: (x^2 + 1)*(x - 1)^3 ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [apart] (x^5/((x^2+1)*(x-1)^3))

set_option linter.style.longLine false in
-- A denominator written as one nonlinear factor: without Hex there is nothing to split.
/--
error: apart: the denominator x^2 - 1 is a single factor as written and the fraction is proper, and without Hex `apart` does not factor it: write it as a product of its factors, or use CASHex (`lake -R -Khex=on build CASHex`, `import CASHex.Factor`), which factors it completely over ℚ
-/
#guard_msgs (error, drop info) in
#cas [apart] (1/(x^2-1))

-- Over one nonlinear factor the polynomial part is still split off.
/-- Output (partial fractions over the written factors, refined by gcds): x - x/(x^2 + 1) -/
#guard_msgs (info, substring := true) in
#cas [apart] (x^3/(x^2+1))

/--
Output (partial fractions over the written factors, refined by gcds): x^2 - 1 + 2/(x^2 + 1)
-/
#guard_msgs (info, substring := true) in
#cas [apart] ((x^4 + 1)/(x^2 + 1))

-- Written factors are refined by gcds only: the common factor `x^2` of `x^4 + x^2` and
-- `x^3 + x^2` stays whole, with exponent 2, and is printed as the base of a power, as is the
-- written factor `x^3 + x - x`, the polynomial `x^3`, in the next example: the output groups the
-- power as the proved proposition does.
set_option linter.style.longLine false in
/--
info: #cas [apart]
Domain: x ∈ ℝ
Input (rational function): (1/((x^4 + x^2)*(x^3 + x^2)))
Output (partial fractions over the written factors, refined by gcds): -(x - 1)/(2*(x^2 + 1)) + 1/(2*(x + 1)) - (x - 1)/(x^2)^2
-/
#guard_msgs (info, substring := true) in
#cas [apart] (1/((x^4 + x^2)*(x^3 + x^2)))

/-- Output (partial fractions over the written factors, refined by gcds): 1/(x^3)^2 -/
#guard_msgs (info, substring := true) in
#cas [apart] (1 / ((x^3 + x - x)^2))

/--
error: apart: expected a rational function of one variable, found the variables x, y
-/
#guard_msgs (error, drop info) in
#cas [apart] (1/(x*y))

-- Rational integration splits `x` off a denominator factor of degree three or more, again while
-- the rest has degree three or more and `x` divides it, without a factor search (refusals in
-- `BasicIntegration.lean`).
/-- Output (scalar ℝ; antiderivative): log(x) - 1/2*log(x^2 + 1) -/
#guard_msgs (info, substring := true) in
#cas [integrate x] (1/(x^3 + x))

/-- Output (scalar ℝ; antiderivative): 1/2*log(x^2 + 1) - 1/2/x^2 - log(x) -/
#guard_msgs (info, substring := true) in
#cas [integrate x] (1/(x^5 + x^3))

-- Collect, Coefficient, CoefficientList, Exponent
/--
info: #cas [collect x]
Domain: (x, a, b) ∈ ℝ^3
Input (polynomial): ((1 + a*x)^2 + b*x)
Output (polynomial in x): a^2*x^2 + (2*a + b)*x + 1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the collected form
        Proposition: ∀ (x a b : ℝ), (1 + a * x) ^ 2 + b * x = a ^ 2 * x ^ 2 + (2 * a + b) * x + 1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [collect x] ((1 + a*x)^2 + b*x)

/--
info: #cas [coefficient x 2]
Domain: x ↦ X in ℝ[X], parameters in ℝ
Input (polynomial): ((x + y)^3)
Output (coefficient of x^2): 3*y

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Statement about the polynomial
        Proposition: ∀ (y : ℝ), ((Polynomial.X + Polynomial.C y) ^ 3).coeff 2 = 3 * y
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [coefficient x 2] ((x + y)^3)

/--
info: #cas [coefficient x 2]
Domain: x ↦ X in ℚ[X]
Input (polynomial): ((x + 1)^5)
Output (coefficient of x^2): 10

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [coefficient x 2] ((x + 1)^5)

/--
info: #cas [coefficientList x]
Domain: x ↦ X in ℚ[X]
Input (polynomial): ((x + 1)^3 - x/2)
Output (coefficients, constant term first): [1, 5/2, 3, 1]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [coefficientList x] ((x + 1)^3 - x/2)

/--
info: #cas [coefficientList x]
Domain: x ↦ X in ℝ[X], parameters in ℝ
Input (polynomial): (a*x^2 + b*x + c)
Output (coefficients, constant term first): [c, b, a]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [coefficientList x] (a*x^2 + b*x + c)

/--
info: #cas [exponent x]
Domain: x ↦ X in ℚ[X]
Input (polynomial): ((x + 1)^3 - x^3)
Output (degree): 2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [exponent x] ((x + 1)^3 - x^3)

set_option linter.style.longLine false in
/--
info: #cas [exponent x]
Domain: x ↦ X in ℝ[X], parameters in ℝ
Input (polynomial): (a*x^2 + x + 1)
Output (degree): 2
Conditions: a ≠ 0

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Statement about the polynomial
        Proposition: ∀ (a : ℝ), a ≠ 0 → (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.X + 1).natDegree = 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [exponent x] (a*x^2 + x + 1)

/--
error: coefficient: the expression is not a polynomial (it divides by a term with a variable)
-/
#guard_msgs (error, drop info) in
#cas [coefficient x 1] (1/x)

-- PolynomialGCD, PolynomialLCM, PolynomialQuotientRemainder, InterpolatingPolynomial
set_option linter.style.longLine false in
/--
info: #cas [polynomialGCD]
Domain: x ↦ X in ℚ[X]
Input (polynomials): (x^2 - 1, x^2 - 2*x + 1)
Output (monic gcd): x - 1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Statement in ℚ[X]
        Proposition: gcd (Polynomial.X ^ 2 - 1) (Polynomial.X ^ 2 - 2 * Polynomial.X + 1) = Polynomial.X - 1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [polynomialGCD] (x^2 - 1, x^2 - 2*x + 1)

/--
info: #cas [polynomialGCD]
Domain: x ↦ X in ℚ[X]
Input (polynomials): (x^3 - 1, x^2 + 1)
Output (monic gcd): 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [polynomialGCD] (x^3 - 1, x^2 + 1)

/--
info: #cas [polynomialGCD]
Domain: x ↦ X in ℚ[X]
Input (polynomials): (2*x^2 + 3*x + 1, 4*x^2 - 1)
Output (monic gcd): x + 1/2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [polynomialGCD] (2*x^2 + 3*x + 1, 4*x^2 - 1)

/--
info: #cas [polynomialLCM]
Domain: x ↦ X in ℚ[X]
Input (polynomials): (x^2 - 1, x^2 - 2*x + 1)
Output (monic lcm): x^3 - x^2 - x + 1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Statement in ℚ[X]
        Proposition: lcm (Polynomial.X ^ 2 - 1) (Polynomial.X ^ 2 - 2 * Polynomial.X + 1) =
          Polynomial.X ^ 3 - Polynomial.X ^ 2 - Polynomial.X + 1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [polynomialLCM] (x^2 - 1, x^2 - 2*x + 1)

set_option linter.style.longLine false in
/--
info: #cas [polynomialQuotientRemainder]
Domain: x ↦ X in ℚ[X]
Input (polynomials): (x^3 + 1, 2*x - 1)
Output ([quotient, remainder]): [1/2*x^2 + 1/4*x + 1/8, 9/8]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Statement in ℚ[X]
        Proposition: (Polynomial.X ^ 3 + 1) / (2 * Polynomial.X - 1) =
            Polynomial.C (1 / 2) * Polynomial.X ^ 2 + Polynomial.C (1 / 4) * Polynomial.X + Polynomial.C (1 / 8) ∧
          (Polynomial.X ^ 3 + 1) % (2 * Polynomial.X - 1) = Polynomial.C (9 / 8)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [polynomialQuotientRemainder] (x^3 + 1, 2*x - 1)

/--
info: #cas [polynomialQuotient]
Domain: x ↦ X in ℚ[X]
Input (polynomials): (x^4 - 1, x^2 + 1)
Output (quotient): x^2 - 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [polynomialQuotient] (x^4 - 1, x^2 + 1)

/--
info: #cas [polynomialRemainder]
Domain: x ↦ X in ℚ[X]
Input (polynomials): (x^5 + x + 1, x^2 + x + 1)
Output (remainder): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [polynomialRemainder] (x^5 + x + 1, x^2 + x + 1)

/--
info: #cas [interpolatingPolynomial x]
Domain: x ↦ X in ℚ[X]
Input (points): (0, 1), (1, 3), (2, 7)
Output (polynomial of degree at most 2): x^2 + x + 1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Values and degree in ℚ[X]
        Proposition: Polynomial.eval 0 (Polynomial.X ^ 2 + Polynomial.X + 1) = 1 ∧
          Polynomial.eval 1 (Polynomial.X ^ 2 + Polynomial.X + 1) = 3 ∧
            Polynomial.eval 2 (Polynomial.X ^ 2 + Polynomial.X + 1) = 7 ∧
              (Polynomial.X ^ 2 + Polynomial.X + 1).natDegree ≤ 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [interpolatingPolynomial x] [(0, 1), (1, 3), (2, 7)]

/--
info: #cas [interpolatingPolynomial x]
Domain: x ↦ X in ℚ[X]
Input (points): (1, 1), (2, 4), (3, 9), (4, 16)
Output (polynomial of degree at most 3): x^2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [interpolatingPolynomial x] [1, 4, 9, 16]

/--
error: polynomialGCD: expected polynomials in one variable, found x, y
-/
#guard_msgs (error, drop info) in
#cas [polynomialGCD] (x^2 - 1, y - 1)

/--
error: interpolatingPolynomial: the abscissae must be distinct
-/
#guard_msgs (error, drop info) in
#cas [interpolatingPolynomial x] [(0, 1), (0, 2)]

-- Regressions
/--
error: coefficient: the expression is not a polynomial (it divides by a term with a variable)
-/
#guard_msgs (error, drop info) in
#cas [coefficient x 0] (1 / (1 + x * (1 / x)))

/--
info: #cas [apart x]
Domain: x ∈ ℝ
Input (rational function): (1 / ((x - 100000001) * (x - 2)))
Output (partial fractions): 1/(99999999*(x - 100000001)) - 1/(99999999*(x - 2))
Conditions: (x - 100000001)*(x - 2) ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [apart x] (1 / ((x - 100000001) * (x - 2)))

/--
info: #cas [polynomialGCD]
Domain: x ↦ X in ℚ[X]
Input (polynomials): (0, x^2 - 1)
Output (monic gcd): x^2 - 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [polynomialGCD] (0, x^2 - 1)

/--
info: #cas [polynomialQuotientRemainder]
Domain: x ↦ X in ℚ[X]
Input (polynomials): (0, x + 1)
Output ([quotient, remainder]): [0, 0]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [polynomialQuotientRemainder] (0, x + 1)

/--
error: polynomialLCM: the polynomials must be nonzero (lcm 0 p = 0)
-/
#guard_msgs (error, drop info) in
#cas [polynomialLCM] (0, x)


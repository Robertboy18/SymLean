/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex

/-!
# Algebra and polynomials

The compiled examples of the docstrings of the Algebra family: simplification, expansion and
factorization, rational functions, coefficients and division of polynomials, interpolation, and
ideals of polynomials. Each section pins the report lines that a docstring shows and proves its
theorem, and checks the axioms of that proof.

## Ideals of polynomials

`#cas [groebner x, y] [f₁, ..., fₘ]` prints the reduced lexicographic Gröbner basis of the
polynomials `fᵢ`, each element scaled to coprime integer coefficients with a positive leading
coefficient, and proves, in `MvPolynomial (Fin n) ℚ`, that it spans the same ideal as they do and
that it is a Gröbner basis for `MonomialOrder.lex`. `#cas [member x, y] f [g₁, ..., gₘ]`
proves that `f` lies in the ideal of the `gᵢ` and prints `f` as a combination of them. The
equalities of ideals and the memberships are combinations with explicit cofactors, checked by
`ring`. The Gröbner property follows from Buchberger's criterion and a division of every
S-polynomial of the basis, which the kernel checks. A nonzero remainder in `member` is reported
as a failure to find a certificate, not as a proof of non-membership.

In a proof, the bare `cas` tactic closes `Ideal.span {f₁, ..., fₘ} = Ideal.span {g₁, ..., gₖ}` and
`f ∈ Ideal.span {g₁, ..., gₘ}` in a commutative ring with the same certificates, and the Gröbner
property `∀ p ∈ Ideal.span S, p ≠ 0 → ∃ g ∈ S, MonomialOrder.lex.leadingTerm g ∣ …` of a set
literal `S` in `MvPolynomial (Fin n) ℚ`, refusing a set that is not a Gröbner basis and the
property for another monomial order. The example for `MonomialOrder.degLex` needs
`import Mathlib.Data.Finsupp.MonomialOrder.DegLex`.
-/

@[expose] public section

namespace CAS.Examples.Reference.Algebra

set_option linter.hashCommand false

/-! ## simplify -/

/--
Output (scalar ℝ): x^2 + 1
Conditions: x^2 - 1 ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [simplify] ((x ^ 4 - 1) / (x ^ 2 - 1))

/--
Output (scalar ℝ): exp(x + y)
Conditions: x - y ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [simplify] (exp ((x^2 - y^2)/(x - y)))

/--
Output (scalar ℝ): a^(p - q + 3/2)
Conditions: a > 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [simplify] (a ^ p * a * sqrt a / a ^ q)

/--
Output (scalar ℝ): 1
Conditions: 1/(1/x + 1/(1 - x)) - 1 ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [simplify] ((1 / (1/x + 1/(1-x)) - 1) / (1 / (1/x + 1/(1-x)) - 1))

theorem simplify_quotient (x : ℝ) (h : x ^ 2 - 1 ≠ 0) :
    (x ^ 4 - 1) / (x ^ 2 - 1) = x ^ 2 + 1 := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.simplify_quotient' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms simplify_quotient

/--
unsupported symbolic function 'x'; expected abs, sin, cos, tan, sinh, cosh, tanh, atan/arctan,
asin/arcsin, acos/arccos, exp, log, or sqrt. If multiplication was intended, write it explicitly
with `*`
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [simplify] (x y)

/-! ## Calls and bare input: `#cas e` -/

/--
Output (exact value of Γ): 3√π/4
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (gamma (5/2))

/--
Output (binomial): 120
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (binomial 10 3)

/--
Output (scalar ℝ): x^2 + 1
Conditions: x^2 - 1 ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas ((x ^ 4 - 1) / (x ^ 2 - 1))

theorem gamma_five_halves : Real.Gamma (5 / 2) = 3 * √Real.pi / 4 := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.gamma_five_halves' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gamma_five_halves

/--
ChebyshevT takes 2 arguments, as in `ChebyshevT n x`; the call has 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (ChebyshevT 5)

/--
`#cas` computes no exact value of `erf x`; `#cas [N d] (erf x)` gives its digits
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (erf 1)

/-! ## fullSimplify -/

/--
Output (scalar ℝ): (x + 1)^5
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fullSimplify] (x^5 + 5*x^4 + 10*x^3 + 10*x^2 + 5*x + 1)

/--
Output (scalar ℝ): 0
Conditions: x ≠ 0; y ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fullSimplify] (log (x*y) - log x - log y)

/--
Output (scalar ℝ): |x + 1|
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fullSimplify] (sqrt (x^2 + 2*x + 1))

theorem fullSimplify_log (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log (x * y) - Real.log x - Real.log y = 0 := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.fullSimplify_log' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fullSimplify_log

/--
unknown complexity function size; use leafCount, depth or length
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fullSimplify size] (x + 1)

/-! ## expand -/

/--
Output (scalar ℝ): x^3*y - 2*x^3 + 3*x^2*y - 6*x^2 + 3*x*y - 6*x + y - 2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [expand] ((x + 1)^3 * (y - 2))

/--
Output (scalar ℝ): a^4 + 4*a^3*b + 6*a^2*b^2 + 4*a*b^3 + b^4
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [expand] ((a + b)^4)

/--
Output (scalar ℝ): x^3 + x^2 - 7/4*x + 1/2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [expand] ((x - 1/2)^2 * (x + 2))

theorem expand_product (x y : ℝ) :
    (x + 1) ^ 3 * (y - 2) =
      x ^ 3 * y - 2 * x ^ 3 + 3 * x ^ 2 * y - 6 * x ^ 2 + 3 * x * y - 6 * x + y - 2 := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.expand_product' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms expand_product

/--
Output (scalar ℝ): sin(x + y)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [expand] (sin (x + y))

/--
Output (scalar ℝ): 1/(x + 1)^2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [expand] (1 / (x + 1) ^ 2)

/-! ## factor -/

/--
Output (scalar ℝ): (x - 1)^2*(2*x + 1)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [factor] (2*x^3 - 3*x^2 + 1)

/--
Output (scalar ℝ): x*y*(x - y)*(x + y)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [factor] (x^3*y - x*y^3)

/--
Output (scalar ℝ): (x - 1)*(x + 1)*(x^4 + x^2 + 1)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [factor] (x^6 - 1)

theorem factor_cubic (x : ℝ) : 2 * x ^ 3 - 3 * x ^ 2 + 1 = (x - 1) ^ 2 * (2 * x + 1) := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.factor_cubic' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms factor_cubic

/--
Output (scalar ℝ): x^4 + 4
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [factor] (x^4 + 4)

/-! ## trigExpand -/

/--
Output (scalar ℝ): sin(x)*cos(y) + cos(x)*sin(y)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [trigExpand] (sin (x + y))

/--
Output (scalar ℝ): cos(x)^2 - sin(x)^2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [trigExpand] (cos (2*x))

/--
Output (scalar ℝ): (cos(x)*cos(y) + sin(x)*sin(y))*(2*sin(y)*cos(y))
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [trigExpand] (cos (x - y) * sin (2 * y))

theorem trigExpand_sin_add (x y : ℝ) :
    Real.sin (x + y) = Real.sin x * Real.cos y + Real.cos x * Real.sin y := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.trigExpand_sin_add' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms trigExpand_sin_add

/--
Output (scalar ℝ): sin(3*x)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [trigExpand] (sin (3*x))

/-! ## together -/

/--
Output (common denominator): (x + y)/(x*y)
Conditions: x ≠ 0; y ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [together] (1/x + 1/y)

/--
Output (common denominator): (x + 2)/((x - 1)*(x + 1))
Conditions: x^2 - 1 ≠ 0; x - 1 ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [together] (1/(x^2-1) + 1/(x-1))

/--
Output (common denominator): (3*x + 2*y)/6
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [together] (x/2 + y/3)

theorem together_sum (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    1 / x + 1 / y = (x + y) / (x * y) := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.together_sum' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms together_sum

/--
together: a divisor is itself a quotient; write the expression with polynomial divisors
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [together] (1/(1 + 1/x))

/--
together: the expression is not a rational function: it has a function other than the field
operations and natural powers
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [together] (sin x / x)

/-! ## cancel -/

/--
Output (cancelled): x + 1 + 1/x
Conditions: x - 1 ≠ 0; x ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [cancel] ((x^2-1)/(x-1) + 1/x)

/--
Output (cancelled): x^2 + x*y + y^2 + 1/y
Conditions: x - y ≠ 0; y ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [cancel] ((x^3 - y^3)/(x - y) + 1/y)

/--
Output (cancelled): x + y - (x^2 + x + 1)
Conditions: x - y ≠ 0; x - 1 ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [cancel] ((x^2 - y^2)/(x - y) - (x^3 - 1)/(x - 1))

theorem cancel_sum (x : ℝ) (h : x - 1 ≠ 0) :
    (x ^ 2 - 1) / (x - 1) + 1 / x = x + 1 + 1 / x := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.cancel_sum' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cancel_sum

/--
cancel: the expression is not a rational function: it has a function other than the field
operations and natural powers
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [cancel] (sin x / x)

/-! ## numerator -/

/--
Output (numerator): x + y
Conditions: x ≠ 0; y ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [numerator] (1/x + 1/y)

/--
Output (numerator): 2*x - 1
Conditions: x^2 - 1 ≠ 0; x + 1 ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [numerator] (x/(x^2 - 1) + 1/(x + 1))

theorem numerator_mul (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (1 / x + 1 / y) * (x * y) = x + y := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.numerator_mul' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms numerator_mul

/--
numerator: the expression is not a rational function: it has a function other than the field
operations and natural powers
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [numerator] (sqrt x / x)

/-! ## denominator -/

/--
Output (denominator): (x - 1)*(x + 1)
Conditions: x - 1 ≠ 0; x + 1 ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [denominator] (1/(x-1) - 1/(x+1))

/--
Output (denominator): 6
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [denominator] (x/2 + y/3)

theorem denominator_difference (x : ℝ) (h₁ : x - 1 ≠ 0) (h₂ : x + 1 ≠ 0) :
    1 / (x - 1) - 1 / (x + 1) = 2 / ((x - 1) * (x + 1)) := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.denominator_difference' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms denominator_difference

/--
denominator: a divisor is itself a quotient; write the expression with polynomial divisors
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [denominator] (1/(1 + 1/x))

/-! ## apart -/

/--
Output (partial fractions): 1/(2*(x - 1)) - 1/(2*(x + 1))
Conditions: (x - 1)*(x + 1) ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [apart] (1/((x - 1)*(x + 1)))

/--
Output (partial fractions over the written factors, refined by gcds): 1 + (x + 1)/(4*(x^2 + 1))
+ 1/(2*(x - 1)^3) + 2/(x - 1)^2 + 11/(4*(x - 1))
Conditions: (x^2 + 1)*(x - 1)^3 ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [apart] (x^5/((x^2+1)*(x-1)^3))

/--
Output (partial fractions): 1/(99999999*(x - 100000001)) - 1/(99999999*(x - 2))
Conditions: (x - 100000001)*(x - 2) ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [apart x] (1 / ((x - 100000001) * (x - 2)))

theorem apart_two_factors (x : ℝ) (h : (x - 1) * (x + 1) ≠ 0) :
    1 / ((x - 1) * (x + 1)) = 1 / (2 * (x - 1)) - 1 / (2 * (x + 1)) := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.apart_two_factors' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms apart_two_factors

/--
apart: the denominator x^2 - 1 is a single factor as written and the fraction is proper, and
without Hex `apart` does not factor it: write it as a product of its factors, or use CASHex
(`lake -R -Khex=on build CASHex`, `import CASHex.Factor`), which factors it completely over ℚ
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [apart] (1/(x^2-1))

/--
apart: expected a rational function of one variable, found the variables x, y
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [apart] (1/(x*y))

/-! ## collect -/

/--
Output (polynomial in x): a^2*x^2 + (2*a + b)*x + 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [collect x] ((1 + a*x)^2 + b*x)

/--
Output (polynomial in x): (y^2 + y)*x^2 + (y + 1)*x
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [collect x] (x*y + x^2*y + x + y^2*x^2)

theorem collect_square (x a b : ℝ) :
    (1 + a * x) ^ 2 + b * x = a ^ 2 * x ^ 2 + (2 * a + b) * x + 1 := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.collect_square' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms collect_square

/--
collect: the expression is not a polynomial (it divides by a term with a variable)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [collect x] (1/x + x)

/-! ## coefficient -/

/--
Output (coefficient of x^2): 3*y
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [coefficient x 2] ((x + y)^3)

/--
Output (coefficient of x^3): 80
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [coefficient x 3] ((1 + 2*x)^5)

open _root_.Polynomial in
theorem coefficient_binomial : ((X + 1) ^ 5 : ℚ[X]).coeff 2 = 10 := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.coefficient_binomial' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms coefficient_binomial

/--
coefficient: the expression is not a polynomial (it divides by a term with a variable)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [coefficient x 1] (1/x)

/-! ## coefficientList -/

/--
Output (coefficients, constant term first): [1, 5/2, 3, 1]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [coefficientList x] ((x + 1)^3 - x/2)

/--
Output (coefficients, constant term first): [c, b, a]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [coefficientList x] (a*x^2 + b*x + c)

open _root_.Polynomial in
theorem coefficientList_cube (h : ∀ k, ((X + 1) ^ 3 : ℚ[X]).coeff k = [1, 3, 3, 1].getD k 0) :
    ((X + 1) ^ 3 : ℚ[X]).coeff 1 = 3 :=
  h 1

/--
info: 'CAS.Examples.Reference.Algebra.coefficientList_cube' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms coefficientList_cube

/--
coefficientList: the expression is not a polynomial (it divides by a term with a variable)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [coefficientList x] (x + 1/x)

/-! ## exponent -/

/--
Output (degree): 2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [exponent x] ((x + 1)^3 - x^3)

/--
Output (degree): 2
Conditions: a ≠ 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [exponent x] (a*x^2 + x + 1)

open _root_.Polynomial in
theorem exponent_difference : ((X + 1) ^ 3 - X ^ 3 : ℚ[X]).natDegree = 2 := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.exponent_difference' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exponent_difference

/--
exponent: the polynomial is zero
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [exponent x] (0)

/-! ## polynomialGCD -/

/--
Output (monic gcd): x - 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [polynomialGCD] (x^2 - 1, x^2 - 2*x + 1)

/--
Output (monic gcd): 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [polynomialGCD] (x^3 - 1, x^2 + 1)

/--
Output (monic gcd): x + 1/2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [polynomialGCD] (2*x^2 + 3*x + 1, 4*x^2 - 1)

open _root_.Polynomial in
theorem polynomialGCD_square : gcd (X ^ 2 - 1 : ℚ[X]) (X ^ 2 - 2 * X + 1) = X - 1 := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.polynomialGCD_square' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms polynomialGCD_square

/--
polynomialGCD: expected polynomials in one variable, found x, y
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [polynomialGCD] (x^2 - 1, y - 1)

/--
polynomialGCD: gcd 0 0 = 0 is not monic; give a nonzero polynomial
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [polynomialGCD] (0, 0)

/-! ## polynomialLCM -/

/--
Output (monic lcm): x^3 - x^2 - x + 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [polynomialLCM] (x^2 - 1, x^2 - 2*x + 1)

/--
Output (monic lcm): x^4 + x^3 - x - 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [polynomialLCM] (x^2 - 1, x^3 - 1)

open _root_.Polynomial in
theorem polynomialLCM_square :
    lcm (X ^ 2 - 1 : ℚ[X]) (X ^ 2 - 2 * X + 1) = X ^ 3 - X ^ 2 - X + 1 := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.polynomialLCM_square' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms polynomialLCM_square

/--
polynomialLCM: the polynomials must be nonzero (lcm 0 p = 0)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [polynomialLCM] (0, x)

/-! ## polynomialQuotient -/

/--
Output (quotient): x^2 - 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [polynomialQuotient] (x^4 - 1, x^2 + 1)

/--
Output (quotient): 1/2*x^2 + 1/4*x + 1/8
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [polynomialQuotient] (x^3 + 1, 2*x - 1)

open _root_.Polynomial in
theorem polynomialQuotient_square : (X ^ 4 - 1 : ℚ[X]) / (X ^ 2 + 1) = X ^ 2 - 1 := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.polynomialQuotient_square' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms polynomialQuotient_square

/--
polynomialQuotient: division by the zero polynomial
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [polynomialQuotient] (x^2, 0)

/-! ## polynomialRemainder -/

/--
Output (remainder): 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [polynomialRemainder] (x^5 + x + 1, x^2 + x + 1)

/--
Output (remainder): 9/8
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [polynomialRemainder] (x^3 + 1, 2*x - 1)

open _root_.Polynomial in
theorem polynomialRemainder_linear : (X ^ 3 + 1 : ℚ[X]) % (2 * X - 1) = C (9 / 8) := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.polynomialRemainder_linear' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms polynomialRemainder_linear

/--
polynomialRemainder: division by the zero polynomial
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [polynomialRemainder] (x^2, 0)

/-! ## polynomialQuotientRemainder -/

/--
Output ([quotient, remainder]): [1/2*x^2 + 1/4*x + 1/8, 9/8]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [polynomialQuotientRemainder] (x^3 + 1, 2*x - 1)

/--
Output ([quotient, remainder]): [0, 0]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [polynomialQuotientRemainder] (0, x + 1)

open _root_.Polynomial in
theorem polynomialQuotientRemainder_linear :
    (X ^ 3 + 1 : ℚ[X]) / (2 * X - 1) = C (1 / 2) * X ^ 2 + C (1 / 4) * X + C (1 / 8) ∧
      (X ^ 3 + 1 : ℚ[X]) % (2 * X - 1) = C (9 / 8) :=
  ⟨by cas, by cas⟩

/--
info: 'CAS.Examples.Reference.Algebra.polynomialQuotientRemainder_linear' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms polynomialQuotientRemainder_linear

/--
polynomialQuotientRemainder: division by the zero polynomial
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [polynomialQuotientRemainder] (x^2, 0)

/-! ## interpolatingPolynomial -/

/--
Output (polynomial of degree at most 2): x^2 + x + 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [interpolatingPolynomial x] [(0, 1), (1, 3), (2, 7)]

/--
Output (polynomial of degree at most 3): x^2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [interpolatingPolynomial x] [1, 4, 9, 16]

/--
Output (polynomial of degree at most 2): 34/15*x^2 - 19/3*x + 18/5
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [interpolatingPolynomial x] [(1/2, 1), (2, 0), (3, 5)]

open _root_.Polynomial in
theorem interpolatingPolynomial_eval : (X ^ 2 + X + 1 : ℚ[X]).eval 2 = 7 := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.interpolatingPolynomial_eval' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms interpolatingPolynomial_eval

/--
interpolatingPolynomial: the abscissae must be distinct
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [interpolatingPolynomial x] [(0, 1), (0, 2)]

/--
expected a list of points `[(a, b), …]` or of values `[b₁, b₂, …]`
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [interpolatingPolynomial x] (1, 2)

/-! ## groebner -/

open MvPolynomial in
theorem groebner_span :
    Ideal.span {(X 0 ^ 2 + X 1 ^ 2 - 5 : MvPolynomial (Fin 2) ℚ), X 0 * X 1 - 2} =
      Ideal.span {2 * X 0 + X 1 ^ 3 - 5 * X 1, X 1 ^ 4 - 5 * X 1 ^ 2 + 4} := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.groebner_span' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms groebner_span

open MvPolynomial in
theorem groebner_basis :
    ∀ p ∈ Ideal.span ({2 * X 0 + X 1 ^ 3 - 5 * X 1, X 1 ^ 4 - 5 * X 1 ^ 2 + 4} :
        Set (MvPolynomial (Fin 2) ℚ)), p ≠ 0 →
      ∃ g ∈ ({2 * X 0 + X 1 ^ 3 - 5 * X 1, X 1 ^ 4 - 5 * X 1 ^ 2 + 4} :
        Set (MvPolynomial (Fin 2) ℚ)),
        MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm p := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.groebner_basis' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms groebner_basis

/--
expression contains undeclared variables: z
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [groebner x, y] [x^2 + z, y]

/--
groebner: x^2 + sin y is not a polynomial with rational coefficients
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [groebner x, y] [x^2 + sin y, y]

/-! ## member -/

/--
Output (a combination of the generators (checked)): x^3 - y^3 = (x^2 + x*y + y^2)*(x - y)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [member x, y, z] (x^3 - y^3) [x - y, z]

/-! ## Gröbner bases -/

/--
info: #cas [groebner x, y]
Domain: ℚ[x, y] as MvPolynomial (Fin 2) ℚ, with x = X 0, y = X 1
Input (polynomials): x^2 + y^2 - 5, x*y - 2
Output (Gröbner basis of the same ideal (checked)): 2*x + y^3 - 5*y, y^4 - 5*y^2 + 4

[CAS.Command.details] More details
  [CAS.Command.computation] Gröbner basis
    the reduced basis for the lexicographic order x > y, each element scaled to coprime integer
coefficients with a positive leading coefficient; computed by SymLean's Buchberger algorithm, 4
polynomials in the derivation, 2 in the basis
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Ideal of the inputs
        Proposition: Ideal.span {X 0 ^ 2 + X 1 ^ 2 - 5, X 0 * X 1 - 2} =
          Ideal.span {2 * X 0 + X 1 ^ 3 - 5 * X 1, X 1 ^ 4 - 5 * X 1 ^ 2 + 4}
        Validation: proof term checked by the kernel against this proposition
      [CAS.explanation.checkedStep] Gröbner property of the basis
        Proposition: ∀ p ∈ Ideal.span {2 * X 0 + X 1 ^ 3 - 5 * X 1, X 1 ^ 4 - 5 * X 1 ^ 2 + 4},
          p ≠ 0 →
            ∃ g ∈ {2 * X 0 + X 1 ^ 3 - 5 * X 1, X 1 ^ 4 - 5 * X 1 ^ 2 + 4},
              MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm p
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [groebner x, y] [x^2 + y^2 - 5, x*y - 2]

/--
info: #cas [groebner x, y, z]
Domain: ℚ[x, y, z] as MvPolynomial (Fin 3) ℚ, with x = X 0, y = X 1, z = X 2
Input (polynomials): x^2 + y^2 + z^2 - 1, x^2 + z^2 - y, x - z
Output (Gröbner basis of the same ideal (checked)): x - z, y - 2*z^2, 4*z^4 + 2*z^2 - 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [groebner x, y, z] [x^2 + y^2 + z^2 - 1, x^2 + z^2 - y, x - z]

-- An input with a rational coefficient.
/--
info: #cas [groebner x, y]
Domain: ℚ[x, y] as MvPolynomial (Fin 2) ℚ, with x = X 0, y = X 1
Input (polynomials): x/2 + y - 1, x^2 - y
Output (Gröbner basis of the same ideal (checked)): x + 2*y - 2, 4*y^2 - 9*y + 4

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [groebner x, y] [x/2 + y - 1, x^2 - y]

-- Two polynomials that generate the whole ring.
/--
info: #cas [groebner x, y]
Domain: ℚ[x, y] as MvPolynomial (Fin 2) ℚ, with x = X 0, y = X 1
Input (polynomials): x*y - 1, x
Output (Gröbner basis of the same ideal (checked)): 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [groebner x, y] [x*y - 1, x]

-- The elementary symmetric polynomials of three variables, the last one shifted by one. The kernel
-- checks a division of the S-polynomial of each of the three pairs of the basis.
/--
info: #cas [groebner x, y, z]
Domain: ℚ[x, y, z] as MvPolynomial (Fin 3) ℚ, with x = X 0, y = X 1, z = X 2
Input (polynomials): x + y + z, x*y + y*z + z*x, x*y*z - 1
Output (Gröbner basis of the same ideal (checked)): x + y + z, y^2 + y*z + z^2, z^3 - 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [groebner x, y, z] [x + y + z, x*y + y*z + z*x, x*y*z - 1]

-- The zero ideal: the basis is empty and printed as 0, and the theorems use the set `{0}`.
/--
info: #cas [groebner x, y]
Domain: ℚ[x, y] as MvPolynomial (Fin 2) ℚ, with x = X 0, y = X 1
Input (polynomials): x - x
Output (Gröbner basis of the same ideal (checked)): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [groebner x, y] [x - x]

/-! ## Membership -/

/--
info: #cas [member x, y]
Domain: ℚ[x, y] as MvPolynomial (Fin 2) ℚ, with x = X 0, y = X 1
Input (polynomial and ideal): x^2 - 1 and ⟨x*y - 1, x - y⟩
Output (a combination of the generators (checked)): x^2 - 1 = (x*y - 1) + x*(x - y)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Membership in the ideal of the generators
        Proposition: X 0 ^ 2 - 1 ∈ Ideal.span {X 0 * X 1 - 1, X 0 - X 1}
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [member x, y] (x^2 - 1) [x*y - 1, x - y]

-- A polynomial with a nonzero remainder is refused, without a claim of non-membership.
/--
error: member: x is not shown to be in the ideal: its remainder modulo the computed lexicographic
basis is x. The basis is not proved to be a Gröbner basis, so this proves nothing about
non-membership
-/
#guard_msgs (error, whitespace := lax) in
#cas [member x, y] x [x^2, y]

/-! ## In a proof -/

open MvPolynomial

/-- The ideal of the first example, with the basis that `#cas [groebner]` prints. -/
theorem span_eq_basis :
    Ideal.span {(X 0 ^ 2 + X 1 ^ 2 - 5 : MvPolynomial (Fin 2) ℚ), X 0 * X 1 - 2} =
      Ideal.span {2 * X 0 + X 1 ^ 3 - 5 * X 1, X 1 ^ 4 - 5 * X 1 ^ 2 + 4} := by
  cas

/-- The reduced basis `x - y^2, y^4 - y` of `x^2 - y, y^2 - x` is a Gröbner basis. -/
theorem groebner_basis_swap :
    ∀ p ∈ Ideal.span ({X 0 - X 1 ^ 2, X 1 ^ 4 - X 1} : Set (MvPolynomial (Fin 2) ℚ)), p ≠ 0 →
      ∃ g ∈ ({X 0 - X 1 ^ 2, X 1 ^ 4 - X 1} : Set (MvPolynomial (Fin 2) ℚ)),
        MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm p := by
  cas

/-- A Gröbner basis written with rational constants `C q`. -/
theorem groebner_basis_rational :
    ∀ p ∈ Ideal.span ({X 0 - C (1 / 2), X 1 ^ 2 + C 3 * X 1} : Set (MvPolynomial (Fin 2) ℚ)),
      p ≠ 0 → ∃ g ∈ ({X 0 - C (1 / 2), X 1 ^ 2 + C 3 * X 1} : Set (MvPolynomial (Fin 2) ℚ)),
        MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm p := by
  cas

-- The inputs `x^2 - y, y^2 - x` themselves are not a Gröbner basis, so `cas` refuses them.
/--
the basis is not a Gröbner basis for `MonomialOrder.lex`: the S-polynomial of X 0 ^ 2 - X 1 and
X 1 ^ 2 - X 0 leaves the remainder -X 1 ^ 4 + X 1 on division by the basis
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example :
    ∀ p ∈ Ideal.span ({X 0 ^ 2 - X 1, X 1 ^ 2 - X 0} : Set (MvPolynomial (Fin 2) ℚ)), p ≠ 0 →
      ∃ g ∈ ({X 0 ^ 2 - X 1, X 1 ^ 2 - X 0} : Set (MvPolynomial (Fin 2) ℚ)),
        MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm p := by
  cas

/-- Zero and repeated elements of the set are allowed. -/
theorem groebner_basis_zero_duplicate :
    ∀ p ∈ Ideal.span ({X 0 - X 1, 0, X 0 - X 1} : Set (MvPolynomial (Fin 2) ℚ)), p ≠ 0 →
      ∃ g ∈ ({X 0 - X 1, 0, X 0 - X 1} : Set (MvPolynomial (Fin 2) ℚ)),
        MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm p := by
  cas

-- The Gröbner property for another monomial order is refused before any division, even for a
-- set that has it.
/--
on a goal `∀ p ∈ Ideal.span S, p ≠ 0 → ∃ …`, `cas` proves only the Gröbner property for
`MonomialOrder.lex`
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example :
    ∀ p ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 2) ℚ)), p ≠ 0 →
      ∃ g ∈ ({X 0, X 1} : Set (MvPolynomial (Fin 2) ℚ)),
        MonomialOrder.degLex.leadingTerm g ∣ MonomialOrder.degLex.leadingTerm p := by
  cas

-- The whole goal is compared with the property for the set inside `Ideal.span` up to reducible
-- definitional equality, which does not identify equal sets: the same set listed in another order
-- after `∃ g ∈` is refused by this comparison, before the set literal is read.
/--
error: cas expected a checked semantic proposition, reflected equality, arithmetic relation, an
ordinary inequality on real variables bounded by rational literal hypotheses (a two-sided bound
`a ≤ f x ∧ f x ≤ b`, a membership `f x ∈ Set.Icc a b`, or a universally quantified bound), or the
statement of a `#cas` command (a limit, a polynomial root count, a polynomial sign condition)
Command theorem route:
  cas sign route expected a quantifier over ℝ
Box enclosure route:
  cas box route: the goal has the head symbol `Exists`; the route proves `f x ≤ c`, `f x < c`,
  `c ≤ f x`, `c < f x`, `|f x| ≤ c`, `|f x| < c`, `a ≤ f x ∧ f x ≤ b` (also with `<`),
  `f x ∈ Set.Icc a b` (also `Set.Ioo`, `Set.Ico`, `Set.Ioc`), `f x ≤ g x`, and conjunctions of
  these, with `c`, `a`, `b` closed and every real variable bounded by hypotheses `a ≤ x` and
  `x ≤ b`, `x ∈ Set.Icc a b`, or `|x| ≤ r` with rational literal endpoints
Registered route ideal:
  cas: on a goal `∀ p ∈ Ideal.span S, p ≠ 0 → ∃ …`, `cas` proves only the Gröbner property for
  `MonomialOrder.lex`, `∃ g ∈ S, MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm
  p` with the same set `S`; other monomial orders and other conclusions are not supported
Grind fallback:
  `grind` failed (`set_option trace.cas.fallback true` shows its diagnostics)
norm_num fallback:
  norm_num did not close the goal
-/
#guard_msgs (whitespace := lax) in
example :
    ∀ p ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 2) ℚ)), p ≠ 0 →
      ∃ g ∈ ({X 1, X 0} : Set (MvPolynomial (Fin 2) ℚ)),
        MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm p := by
  cas

/-- The membership of the membership example. -/
theorem mem_span_mvPolynomial :
    (X 0 ^ 2 - 1 : MvPolynomial (Fin 2) ℚ) ∈ Ideal.span {X 0 * X 1 - 1, X 0 - X 1} := by
  cas

/-- The same membership for real numbers. -/
theorem mem_span_real (a b : ℝ) : a ^ 2 - 1 ∈ Ideal.span {a * b - 1, a - b} := by
  cas

/-- The cofactors `1` and `a` are integers, so the membership also holds in `ℤ`. -/
theorem mem_span_int (a b : ℤ) : a ^ 2 - 1 ∈ Ideal.span {a * b - 1, a - b} := by
  cas

-- A certificate that divides by 2 needs a ℚ-algebra, so `cas` refuses it in `ℤ`.
/-- the certificate divides by 2, and ℤ is not a ℚ-algebra -/
#guard_msgs (error, substring := true) in
example (a : ℤ) : a ∈ Ideal.span {2 * a, a ^ 2} := by
  cas

/--
info: 'CAS.Examples.Reference.Algebra.span_eq_basis' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms span_eq_basis

/--
info: 'CAS.Examples.Reference.Algebra.groebner_basis_swap' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms groebner_basis_swap

/--
info: 'CAS.Examples.Reference.Algebra.groebner_basis_rational' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms groebner_basis_rational

/--
info: 'CAS.Examples.Reference.Algebra.groebner_basis_zero_duplicate' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms groebner_basis_zero_duplicate

/--
info: 'CAS.Examples.Reference.Algebra.mem_span_mvPolynomial' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_span_mvPolynomial

/--
info: 'CAS.Examples.Reference.Algebra.mem_span_real' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_span_real

/-- info: 'CAS.Examples.Reference.Algebra.mem_span_int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_span_int

/-! ## Gröbner certificates

`CAS.Polynomial.Sparse.groebnerCertified`, the checker behind the Gröbner property, evaluated by
the kernel on small lists: a missing quotient counts as zero, and zero and repeated elements are
allowed. -/

section

open CAS.Polynomial.Sparse

-- The S-polynomial of `x` and `y` is zero, so the empty certificate is accepted.
example :
    groebnerCertified [ofTerms (n := 2) [(1, [1, 0])], ofTerms [(1, [0, 1])]] [] = true := by
  decide +kernel

-- The S-polynomial of `y` and `x + y` is `-y ^ 2 = (-y) * y`. The certificate gives only the
-- quotient `-y` of `y`; the missing quotient of `x + y` counts as zero.
example :
    groebnerCertified [ofTerms (n := 2) [(1, [0, 1])], ofTerms [(1, [1, 0]), (1, [0, 1])]]
      [[[], [ofTerms [(-1, [0, 1])]]]] = true := by
  decide +kernel

-- Missing quotients count as zero and are not skipped: the empty certificate of `y, x + y` is
-- refused.
example :
    groebnerCertified [ofTerms (n := 2) [(1, [0, 1])], ofTerms [(1, [1, 0]), (1, [0, 1])]]
      [] = false := by
  decide +kernel

-- The zero polynomial and a repeated element: every S-polynomial is zero.
example :
    groebnerCertified [ofTerms (n := 2) [(1, [1, 0])], ofTerms [], ofTerms [(1, [1, 0])]]
      [] = true := by
  decide +kernel

end

end CAS.Examples.Reference.Algebra

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Special functions

The compiled examples of the docstrings of the special functions that `#cas` evaluates as calls:
the Chebyshev, Hermite, Legendre and Bernoulli polynomials in monomials and at rational points,
the Bernoulli numbers, exact values of the zeta and Gamma functions, and decimal enclosures of the
error function and of the Bessel functions. Each section pins the report lines that a docstring
shows and proves its theorem, and checks the axioms of that proof.
-/

@[expose] public section

namespace CAS.Examples.Reference.SpecialFunctions

set_option linter.hashCommand false

/-! ## ChebyshevT -/

/--
Output (polynomial with integer coefficients): 16*x^5 - 20*x^3 + 5*x
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (ChebyshevT 5 x)

/--
Output (polynomial with integer coefficients): t
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [expand] (ChebyshevT 1 t)

/--
Output (exact rational value): 1/2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (ChebyshevT 5 (1/2))

theorem chebyshevT_five_at_half
    (h : ∀ (R : Type) [CommRing R], Polynomial.Chebyshev.T R 5 =
      16 * Polynomial.X ^ 5 - 20 * Polynomial.X ^ 3 + 5 * Polynomial.X) :
    (Polynomial.Chebyshev.T ℝ 5).eval (1 / 2) = 1 / 2 := by
  rw [h ℝ]
  norm_num

/--
info: 'CAS.Examples.Reference.SpecialFunctions.chebyshevT_five_at_half' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms chebyshevT_five_at_half

/--
ChebyshevT accepts degrees up to 80
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (ChebyshevT 81 x)

/-! ## ChebyshevU -/

/--
Output (polynomial with integer coefficients): 16*x^4 - 12*x^2 + 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (ChebyshevU 4 x)

/--
Output (polynomial with integer coefficients): 4*x^2 - 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [expand] (ChebyshevU 2 x)

theorem chebyshevU_four_at_one
    (h : ∀ (R : Type) [CommRing R], Polynomial.Chebyshev.U R 4 =
      16 * Polynomial.X ^ 4 - 12 * Polynomial.X ^ 2 + 1) :
    (Polynomial.Chebyshev.U ℝ 4).eval 1 = 5 := by
  rw [h ℝ]
  norm_num

/--
info: 'CAS.Examples.Reference.SpecialFunctions.chebyshevU_four_at_one' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms chebyshevU_four_at_one

/--
ChebyshevU accepts degrees up to 80
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (ChebyshevU 81 x)

/-! ## HermiteH -/

/--
Output (polynomial with integer coefficients): 16*x^4 - 48*x^2 + 12
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (HermiteH 4 x)

/--
Output (polynomial with integer coefficients): 32*x^5 - 160*x^3 + 120*x
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [expand] (HermiteH 5 x)

theorem hermiteH_four_at_zero
    (h : ∀ x : ℝ, √2 ^ 4 * Polynomial.aeval (√2 * x) (Polynomial.hermite 4) =
      16 * x ^ 4 - 48 * x ^ 2 + 12) :
    √2 ^ 4 * Polynomial.aeval (√2 * 0) (Polynomial.hermite 4) = 12 := by
  rw [h 0]
  norm_num

/--
info: 'CAS.Examples.Reference.SpecialFunctions.hermiteH_four_at_zero' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hermiteH_four_at_zero

/--
HermiteH accepts degrees up to 60
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (HermiteH 61 x)

/-! ## HermiteHe -/

/--
Output (polynomial with integer coefficients): x^4 - 6*x^2 + 3
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (HermiteHe 4 x)

/--
Output (polynomial with integer coefficients): x^3 - 3*x
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [expand] (HermiteHe 3 x)

theorem hermiteHe_four_at_one
    (h : Polynomial.hermite 4 = Polynomial.X ^ 4 - 6 * Polynomial.X ^ 2 + 3) :
    (Polynomial.hermite 4).eval 1 = -2 := by
  rw [h]
  norm_num

/--
info: 'CAS.Examples.Reference.SpecialFunctions.hermiteHe_four_at_one' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hermiteHe_four_at_one

/--
HermiteHe accepts degrees up to 80
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (HermiteHe 81 x)

/-! ## LegendreP -/

/--
Output (polynomial with exact rational coefficients): 5/2*x^3 - 3/2*x
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (LegendreP 3 x)

/--
Output (polynomial with exact rational coefficients): 63/8*x^5 - 35/4*x^3 + 15/8*x
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [expand] (LegendreP 5 x)

/--
Output (exact rational value): -1/8
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (LegendreP 2 (1/2))

theorem legendre_three_at_half
    (h : ∀ x : ℝ,
      (CAS.Analysis.SpecialFunctions.legendre 3).eval x = 5 / 2 * x ^ 3 - 3 / 2 * x) :
    (CAS.Analysis.SpecialFunctions.legendre 3).eval (1 / 2) = -7 / 16 := by
  rw [h]
  norm_num

/--
info: 'CAS.Examples.Reference.SpecialFunctions.legendre_three_at_half' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms legendre_three_at_half

/--
LegendreP accepts degrees up to 30
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (LegendreP 31 x)

/-! ## BernoulliB n x -/

/--
Output (polynomial with exact rational coefficients): x^4 - 2*x^3 + x^2 - 1/30
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (BernoulliB 4 x)

/--
Output (polynomial with exact rational coefficients): x - 1/2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [expand] (BernoulliB 1 x)

theorem bernoulliB_four_at_half
    (h : ∀ x : ℝ, Polynomial.aeval x (Polynomial.bernoulli 4) =
      x ^ 4 - 2 * x ^ 3 + x ^ 2 - 1 / 30) :
    Polynomial.aeval (1 / 2 : ℝ) (Polynomial.bernoulli 4) = 7 / 240 := by
  rw [h]
  norm_num

/--
info: 'CAS.Examples.Reference.SpecialFunctions.bernoulliB_four_at_half' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bernoulliB_four_at_half

/--
BernoulliB accepts degrees up to 60
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (BernoulliB 61 x)

/-! ## BernoulliB n -/

/--
Output (Bernoulli number): 5/66
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (BernoulliB 10)

/--
Output (Bernoulli number): -1/2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (BernoulliB 1)

/--
Output (Bernoulli number): -174611/330
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (BernoulliB 20)

theorem bernoulli_ten : bernoulli 10 = 5 / 66 := by
  rw [CAS.Analysis.SpecialFunctions.bernoulli_eq_numerators]
  decide +kernel

/--
info: 'CAS.Examples.Reference.SpecialFunctions.bernoulli_ten' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bernoulli_ten

/--
BernoulliB computes Bₙ for n ≤ 60
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (BernoulliB 61)

/-! ## zeta -/

/--
Output (exact value of ζ): pi^2/6
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (zeta 2)

/--
Output (exact value of ζ): pi^4/90
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (zeta 4)

/--
Output (exact value of ζ): -1/12
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (zeta (-1))

theorem six_mul_zeta_two (h : riemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6) :
    6 * riemannZeta 2 = (Real.pi : ℂ) ^ 2 := by
  rw [h]
  ring

/--
info: 'CAS.Examples.Reference.SpecialFunctions.six_mul_zeta_two' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms six_mul_zeta_two

/--
zeta: unsupported formula at the odd integer `3`; exact values are computed at even positive and
at nonpositive integers
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (zeta 3)

/--
zeta: s = 1 is the pole of ζ; Mathlib's riemannZeta 1 is a convention, not a value of the
series, and is not reported
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (zeta 1)

/--
zeta: exact values are computed at integers
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (zeta (1/2))

/-! ## gamma -/

/--
Output (exact value of Γ): 24
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (gamma 5)

/--
Output (exact value of Γ): 3√π/4
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (gamma (5/2))

/--
Output (exact value of Γ): 4√π/3
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (gamma (-3/2))

/--
Output (exact value of Γ): 0 (Mathlib's value at the pole -3; Mathematica: ComplexInfinity)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (gamma (-3))

theorem gamma_seven_halves : Real.Gamma (7 / 2) = 15 / 8 * √Real.pi := by
  cas

/--
info: 'CAS.Examples.Reference.SpecialFunctions.gamma_seven_halves' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gamma_seven_halves

/--
gamma: exact values are computed at integers and half-integers; `1/3` is neither
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (gamma (1/3))

/--
gamma needs a closed expression; free symbols: x
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (gamma x)

/--
gamma: unsupported symbolic function 'foo'; expected abs, sin, cos, tan, sinh, cosh, tanh,
atan/arctan, asin/arcsin, acos/arccos, exp, log, or sqrt. If multiplication was intended, write
it explicitly with `*`
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (gamma (foo 1))

/-! ## erf -/

/--
Output (decimal enclosure of width at most 10^-30, with 30 terms of the series):
[0.8427007929497148693412206350826, 0.8427007929497148693412206350827]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [N 30] (erf 1)

theorem erf_one_pos (h : 21 / 25 ≤ CAS.erf 1 ∧ CAS.erf 1 ≤ 17 / 20) : 0 < CAS.erf 1 := by
  linarith [h.1]

/--
info: 'CAS.Examples.Reference.SpecialFunctions.erf_one_pos' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms erf_one_pos

/--
erf accepts rational points with |q| ≤ 10 and a denominator of at most 1000
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [N 10] (erf 11)

/-! ## BesselJ -/

/--
Output (decimal enclosure of width at most 10^-10, with 8 terms of the series):
[0.76519768655, 0.76519768656]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [N 10] (BesselJ 0 1)

theorem besselJ_zero_one_pos
    (h : ∃ r : ℝ, Complex.besselJ (0 : ℂ) (1 : ℂ) = r ∧ 3 / 4 ≤ r ∧ r ≤ 4 / 5) :
    ∃ r : ℝ, Complex.besselJ (0 : ℂ) (1 : ℂ) = r ∧ 0 < r := by
  obtain ⟨r, hr, hlo, -⟩ := h
  exact ⟨r, hr, by linarith⟩

/--
info: 'CAS.Examples.Reference.SpecialFunctions.besselJ_zero_one_pos' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms besselJ_zero_one_pos

/--
BesselJ accepts integer orders
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [N 5] (BesselJ (1/2) 1)

end CAS.Examples.Reference.SpecialFunctions

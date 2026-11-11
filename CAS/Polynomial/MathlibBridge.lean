/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import CAS.Polynomial.Sparse

/-!
# Bridge from sparse polynomials to Mathlib polynomials

The executable computer algebra system uses ordered sparse lists because their
normalization, division, and certificate checkers reduce predictably in the
kernel. Mathlib's `Polynomial` carries the algebra and root theory used in theorems.

In one variable, `toRatPolynomial` and `toRealPolynomial` interpret a sparse list as a Mathlib
polynomial; they preserve evaluation (`eval_toRealPolynomial`), commute with differentiation
(`toRealPolynomial_derivative`), and identify roots (`evalReal_eq_zero_iff_isRoot`).

The conversions to Mathlib preserve evaluation exactly but are not injective: sparse lists may
contain zero coefficients and repeated monomials, which Mathlib combines in its canonical
polynomial value.
-/

@[expose] public section

namespace CAS.Polynomial.Sparse

/-! ## Univariate bridge -/

/-- Interpret a sparse univariate polynomial as a Mathlib polynomial over `ℚ`. -/
noncomputable def toRatPolynomial : Univariate → Polynomial ℚ
  | [] => 0
  | term :: rest =>
      Polynomial.monomial (term.2 (0 : Fin 1)) term.1 +
        toRatPolynomial rest

/-- Rational evaluation agrees with the Mathlib polynomial interpretation. -/
theorem eval_toRatPolynomial (polynomial : Univariate) (x : ℚ) :
    (toRatPolynomial polynomial).eval x = evalRat polynomial x := by
  induction polynomial with
  | nil => simp [toRatPolynomial, evalRat]
  | cons term rest ih => simp [toRatPolynomial, evalRat, ih]

/-- Interpret a sparse univariate polynomial as a Mathlib polynomial over `ℝ`. -/
noncomputable def toRealPolynomial (polynomial : Univariate) : Polynomial ℝ :=
  (toRatPolynomial polynomial).map (algebraMap ℚ ℝ)

/-- Real evaluation agrees with the sparse real evaluator. -/
theorem eval_toRealPolynomial (polynomial : Univariate) (x : ℝ) :
    (toRealPolynomial polynomial).eval x = evalReal polynomial x := by
  rw [toRealPolynomial, Polynomial.eval_map]
  induction polynomial with
  | nil => simp [toRatPolynomial, evalReal]
  | cons term rest ih => simp [toRatPolynomial, evalReal, ih]

/-- Sparse formal differentiation agrees with Mathlib polynomial differentiation. -/
theorem toRealPolynomial_derivative (polynomial : Univariate) :
    toRealPolynomial (derivative (0 : Fin 1) polynomial) =
      (toRealPolynomial polynomial).derivative := by
  refine Polynomial.funext fun x ↦ ?_
  have h := Polynomial.hasDerivAt (toRealPolynomial polynomial) x
  simp only [eval_toRealPolynomial] at h ⊢
  exact (hasDerivAt_evalReal polynomial x).unique h

/-- Sparse real roots are exactly roots of the Mathlib real polynomial. -/
theorem evalReal_eq_zero_iff_isRoot (polynomial : Univariate) (x : ℝ) :
    evalReal polynomial x = 0 ↔
      (toRealPolynomial polynomial).IsRoot x := by
  rw [Polynomial.IsRoot, eval_toRealPolynomial]

/-- A checked sparse zero difference yields exact Mathlib polynomial equality. -/
theorem toRatPolynomial_eq_of_isZero_sub
    (left right : Univariate)
    (hzero : isZero (Verified.Expr.Alg.mvSub left right) = true) :
    toRatPolynomial left = toRatPolynomial right := by
  refine Polynomial.funext fun x ↦ ?_
  have h := evalReal_eq_zero_of_isZero hzero (x : ℝ)
  rw [evalReal_sub, evalReal_ratCast, evalReal_ratCast, sub_eq_zero, Rat.cast_inj] at h
  rwa [eval_toRatPolynomial, eval_toRatPolynomial]

end CAS.Polynomial.Sparse

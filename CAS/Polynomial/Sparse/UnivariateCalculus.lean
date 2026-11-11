/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import CAS.Polynomial.Sparse.Semantics

/-!
# Univariate sparse polynomial calculus

The shared sparse representation in one variable, `Sparse.Univariate := MvPoly 1`: exact
rational evaluation `evalRat`, real evaluation `evalReal` (agreeing with the multivariate
semantics by `evalReal_eq_mvPolyVal`), the formal derivative `derivative`, and the analytic
theorems `hasDerivAt_evalReal` and `iteratedDeriv_evalReal` identifying formal differentiation
with the real derivative.
-/

@[expose] public section

namespace CAS.Polynomial.Sparse

open CAS
open CAS.Verified.Expr.Alg (MvPoly)

/-- Sparse rational-coefficient univariate polynomials. -/
abbrev Univariate := MvPoly 1

/-- The unique univariate monomial exponent vector of a given degree. -/
def univariateMonomial (degree : Nat) :
    Verified.Expr.Alg.MvMonomial 1 :=
  fun _ ↦ degree

/-- Canonical zero sparse polynomial in any dimension. -/
def zero {n : Nat} : MvPoly n := []

/-- Canonical one-term univariate polynomial `coefficient * x^degree`. -/
def monomial (coefficient : Rat) (degree : Nat) : Univariate :=
  if coefficient = 0 then
    zero
  else
    [(coefficient, univariateMonomial degree)]

/-- Multiply a sparse polynomial by a rational scalar. -/
def scale {n : Nat} (coefficient : Rat) (polynomial : MvPoly n) : MvPoly n :=
  Verified.Expr.Alg.mvScaleMonomial coefficient
    (Verified.Expr.Alg.mvOne n) polynomial

/--
Differentiate a sparse polynomial in coordinate `i`.

The result is canonicalized after terms independent of `i` are removed.
-/
def derivative {n : Nat} (i : Fin n) (polynomial : MvPoly n) : MvPoly n :=
  Verified.Expr.Alg.mvNormalize <|
    (Verified.Expr.Alg.mvNormalize polynomial).filterMap fun term ↦
      let exponent : Nat := term.2 i
      if exponent = 0 then
        none
      else
        some
          (term.1 * (exponent : Rat),
            fun j ↦ if j = i then exponent.pred else term.2 j)

/-- Degree of a sparse polynomial in one selected coordinate. -/
def degreeAt {n : Nat} (i : Fin n) (polynomial : MvPoly n) : Nat :=
  (Verified.Expr.Alg.mvNormalize polynomial).foldl
    (fun degree term ↦ max degree (term.2 i)) 0

/-- Coefficient of `x^degree` in a normalized univariate polynomial. -/
def coefficient (degree : Nat) (polynomial : Univariate) : Rat :=
  (Verified.Expr.Alg.mvNormalize polynomial).foldl
    (fun total term ↦
      if term.2 (0 : Fin 1) = degree then total + term.1 else total)
    0

/-- Exact evaluation of a sparse univariate polynomial at a rational point. -/
def evalRat : Univariate → Rat → Rat
  | [], _ => 0
  | term :: rest, x =>
      term.1 * x ^ (term.2 (0 : Fin 1)) + evalRat rest x

/-- Real evaluation of a sparse univariate polynomial. -/
noncomputable def evalReal : Univariate → ℝ → ℝ
  | [], _ => 0
  | term :: rest, x =>
      (term.1 : ℝ) * x ^ (term.2 (0 : Fin 1)) + evalReal rest x

/-- Rational evaluation and real evaluation agree after casting. -/
theorem evalReal_ratCast (polynomial : Univariate) (x : Rat) :
    evalReal polynomial (x : ℝ) = (evalRat polynomial x : Rat) := by
  induction polynomial with
  | nil => simp [evalReal, evalRat]
  | cons term rest ih => simp [evalReal, evalRat, ih]

private theorem monomialVal_single (x : ℝ)
    (monomial : Verified.Expr.Alg.MvMonomial 1) :
    Verified.Expr.Alg.mvMonomialVal
      (EuclideanSpace.single (0 : Fin 1) x) monomial =
        x ^ monomial (0 : Fin 1) := by
  simp [Verified.Expr.Alg.mvMonomialVal, ← Fin.prod_univ_def]

/-- The shared real evaluator agrees with the multivariate polynomial semantics. -/
theorem evalReal_eq_mvPolyVal (polynomial : Univariate) (x : ℝ) :
    evalReal polynomial x =
      Verified.Expr.Alg.mvPolyVal
        (EuclideanSpace.single (0 : Fin 1) x) polynomial := by
  induction polynomial with
  | nil => simp [evalReal, Verified.Expr.Alg.mvPolyVal]
  | cons term rest ih =>
      simp [evalReal, Verified.Expr.Alg.mvPolyVal, Verified.Expr.Alg.mvTermVal,
        monomialVal_single, ih]

/-- Canonicalization preserves real univariate polynomial evaluation. -/
theorem evalReal_normalize (polynomial : Univariate) (x : ℝ) :
    evalReal (Verified.Expr.Alg.mvNormalize polynomial) x =
      evalReal polynomial x := by
  rw [evalReal_eq_mvPolyVal, evalReal_eq_mvPolyVal,
    Verified.Expr.Alg.mvPolyVal_normalize]

/-- Exact sparse addition agrees with pointwise real addition. -/
theorem evalReal_add (left right : Univariate) (x : ℝ) :
    evalReal (Verified.Expr.Alg.mvAdd left right) x =
      evalReal left x + evalReal right x := by
  simp only [evalReal_eq_mvPolyVal, Verified.Expr.Alg.mvPolyVal_add]

/-- Exact sparse subtraction agrees with pointwise real subtraction. -/
theorem evalReal_sub (left right : Univariate) (x : ℝ) :
    evalReal (Verified.Expr.Alg.mvSub left right) x =
      evalReal left x - evalReal right x := by
  simp only [evalReal_eq_mvPolyVal, Verified.Expr.Alg.mvPolyVal_sub]

/-- Exact sparse multiplication agrees with pointwise real multiplication. -/
theorem evalReal_mul (left right : Univariate) (x : ℝ) :
    evalReal (Verified.Expr.Alg.mvMulPoly left right) x =
      evalReal left x * evalReal right x := by
  simp only [evalReal_eq_mvPolyVal, Verified.Expr.Alg.mvPolyVal_mulPoly]

/-- Exact sparse powers agree with pointwise real powers. -/
theorem evalReal_pow (polynomial : Univariate) (exponent : Nat) (x : ℝ) :
    evalReal (Verified.Expr.Alg.mvPowPoly polynomial exponent) x =
      evalReal polynomial x ^ exponent := by
  simp only [evalReal_eq_mvPolyVal, Verified.Expr.Alg.mvPolyVal_powPoly]

/--
Differentiate a univariate sparse list without canonicalizing its term order.

This transparent form is useful for certificate checking. Use `derivative`
when a canonical sparse result is required.
-/
def derivativeRaw (polynomial : Univariate) : Univariate :=
  polynomial.filterMap fun term ↦
    let exponent : Nat := term.2 (0 : Fin 1)
    if exponent = 0 then
      none
    else
      some
        (term.1 * (exponent : Rat),
          fun j ↦ if j = (0 : Fin 1) then exponent.pred else term.2 j)

private theorem derivative_eq_normalize_rawDerivative
    (polynomial : Univariate) :
    derivative (0 : Fin 1) polynomial =
      Verified.Expr.Alg.mvNormalize
        (derivativeRaw (Verified.Expr.Alg.mvNormalize polynomial)) := by
  rfl

/-- The transparent sparse derivative has the expected analytic semantics. -/
theorem hasDerivAt_evalRealRaw (polynomial : Univariate) (x : ℝ) :
    HasDerivAt (evalReal polynomial)
      (evalReal (derivativeRaw polynomial) x) x := by
  induction polynomial with
  | nil => simpa [evalReal, derivativeRaw] using hasDerivAt_const x (0 : ℝ)
  | cons term rest ih =>
      obtain ⟨c, m⟩ := term
      refine ((((hasDerivAt_id x).pow (m 0)).const_mul (c : ℝ)).add ih).congr_deriv ?_
      by_cases hzero : m 0 = 0
      · simp [derivativeRaw, hzero]
      · simp [derivativeRaw, hzero, evalReal]
        ring

/-- Formal sparse differentiation has the expected analytic derivative. -/
theorem hasDerivAt_evalReal (polynomial : Univariate) (x : ℝ) :
    HasDerivAt (evalReal polynomial)
      (evalReal (derivative (0 : Fin 1) polynomial) x) x := by
  rw [derivative_eq_normalize_rawDerivative, evalReal_normalize,
    ← funext (evalReal_normalize polynomial)]
  exact hasDerivAt_evalRealRaw _ x

/-- Sparse polynomial evaluation is continuous. -/
theorem continuous_evalReal (polynomial : Univariate) :
    Continuous (evalReal polynomial) :=
  continuous_iff_continuousAt.mpr fun x ↦
    (hasDerivAt_evalReal polynomial x).continuousAt

/-- Repeated sparse differentiation denotes repeated real differentiation. -/
theorem iteratedDeriv_evalReal (polynomial : Univariate) (order : ℕ) :
    iteratedDeriv order (evalReal polynomial) =
      evalReal ((derivative (0 : Fin 1))^[order] polynomial) := by
  induction order with
  | zero => simp
  | succ order ih =>
      rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
      exact funext fun x ↦ (hasDerivAt_evalReal _ x).deriv

end CAS.Polynomial.Sparse

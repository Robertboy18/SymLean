/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import CAS.Polynomial.CoefficientEval

/-!
# Rational coefficient lists as polynomials

A list `l : List ℚ` of coefficients, lowest degree first, is the polynomial
`coeffEval l x = l₀ + x (l₁ + x (l₂ + …))`. The list operations are computable, so finite
checks can evaluate them, and each comes with its evaluation identity: sums
(`coeffAdd`), products (`coeffMul`), powers (`coeffPow`) and derivatives (`coeffDeriv`, with
`hasDerivAt_coeffEval`), next to those of `CAS.Polynomial.CoefficientEval` (adding a constant,
scalar multiples, multiplication by `X - c`, the Taylor shift). The exact integrals are
`∫₋₁¹ x ^ j p (x) dx = coeffIntegralFrom j l` and, for the compositions with the cosine,
`∫₀^π p (cos θ) sin θ dθ = coeffIntegralFrom 0 l` and
`∫₀^π p (cos θ) dθ = π coeffCosIntegralFrom 0 l` (`integral_coeffEval_cos_mul_sin`,
`integral_coeffEval_cos`).
-/

@[expose] public section

namespace CAS.Polynomial

open Set
open scoped BigOperators

/-- The moment `∫₋₁¹ x ^ k`: `2 / (k + 1)` for even `k`, zero for odd `k`. -/
def unitMoment (k : ℕ) : ℚ :=
  if Even k then 2 / (k + 1) else 0

/-- `∫₋₁¹ x ^ k = unitMoment k`. -/
theorem integral_pow_eq_unitMoment (k : ℕ) :
    ∫ x in (-1 : ℝ)..1, x ^ k = unitMoment k := by
  rw [integral_pow, unitMoment]
  rcases Nat.even_or_odd k with hk | hk
  · norm_num [hk, hk.add_one.neg_one_pow]
  · simp [hk.add_one.neg_one_pow, Nat.not_even_iff_odd.mpr hk]

/-! ### Coefficient lists -/

/-- The exact value of `∫₋₁¹ x ^ j p (x)` for the coefficient list `l` of `p`. -/
def coeffIntegralFrom (j : ℕ) : List ℚ → ℚ
  | [] => 0
  | a :: l => a * unitMoment j + coeffIntegralFrom (j + 1) l

/-- For every `j` and coefficient list `l` of `p`, `∫₋₁¹ x ^ j p (x) dx = coeffIntegralFrom j l`. -/
theorem integral_pow_mul_coeffEval (j : ℕ) (l : List ℚ) :
    ∫ x in (-1 : ℝ)..1, x ^ j * coeffEval l x = coeffIntegralFrom j l := by
  induction l generalizing j with
  | nil => simp [coeffIntegralFrom]
  | cons a l ih =>
    simp only [coeffEval_cons, mul_add, ← mul_assoc, ← pow_succ]
    rw [intervalIntegral.integral_add, ih, intervalIntegral.integral_mul_const,
      integral_pow_eq_unitMoment, coeffIntegralFrom]
    · push_cast
      ring
    · exact ((continuous_pow j).mul continuous_const).intervalIntegrable _ _
    · exact ((continuous_pow _).mul (continuous_coeffEval l)).intervalIntegrable _ _

/-- The coefficients of `∏ (X - ξ)²` over the list of nodes. -/
def nodalSquareCoeffs (nodes : List ℚ) : List ℚ :=
  nodes.foldr (fun c l ↦ coeffMulLinear c (coeffMulLinear c l)) [1]

/-- `nodalSquareCoeffs nodes` is the coefficient list of `∏ (X - ξ)²` over the nodes: it evaluates
at every real `x` to the product of `(x - ξ)²` over `nodes`. -/
theorem coeffEval_nodalSquareCoeffs (nodes : List ℚ) (x : ℝ) :
    coeffEval (nodalSquareCoeffs nodes) x = (nodes.map fun c : ℚ ↦ (x - c) ^ 2).prod := by
  induction nodes with
  | nil => simp [nodalSquareCoeffs]
  | cons c l ih =>
    simp only [nodalSquareCoeffs, List.foldr_cons] at ih ⊢
    rw [coeffEval_coeffMulLinear, coeffEval_coeffMulLinear, ih, List.map_cons, List.prod_cons]
    ring


/-! ### Arithmetic -/

/-- The sum of two coefficient lists. -/
def coeffAdd : List ℚ → List ℚ → List ℚ
  | [], m => m
  | l, [] => l
  | a :: l, b :: m => (a + b) :: coeffAdd l m

/-- `coeffAdd l m` evaluates to the sum of the evaluations of `l` and `m`, for lists of any
lengths. -/
theorem coeffEval_coeffAdd (l m : List ℚ) (x : ℝ) :
    coeffEval (coeffAdd l m) x = coeffEval l x + coeffEval m x := by
  fun_induction coeffAdd l m with
  | case1 | case2 => simp
  | case3 a l b m ih =>
    simp only [coeffEval_cons, ih, Rat.cast_add]
    ring

/-- The product of two coefficient lists. -/
def coeffMul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: l, m => coeffAdd (coeffScale a m) (0 :: coeffMul l m)

/-- `coeffMul l m` evaluates to the product of the evaluations of `l` and `m`. -/
theorem coeffEval_coeffMul (l m : List ℚ) (x : ℝ) :
    coeffEval (coeffMul l m) x = coeffEval l x * coeffEval m x := by
  induction l with
  | nil => simp [coeffMul]
  | cons a l ih =>
    simp only [coeffMul, coeffEval_coeffAdd, coeffEval_coeffScale, coeffEval_cons, ih,
      Rat.cast_zero]
    ring

/-- The `k`th power of a coefficient list. -/
def coeffPow (l : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | k + 1 => coeffMul l (coeffPow l k)

/-- `coeffPow l k` evaluates to the `k`th power of the evaluation of `l`, for every `k`. -/
theorem coeffEval_coeffPow (l : List ℚ) (k : ℕ) (x : ℝ) :
    coeffEval (coeffPow l k) x = coeffEval l x ^ k := by
  induction k with
  | zero => simp [coeffPow]
  | succ k ih => rw [coeffPow, coeffEval_coeffMul, ih, pow_succ, mul_comm]

/-- The derivative of a coefficient list: `(a + X q)' = q + X q'`. -/
def coeffDeriv : List ℚ → List ℚ
  | [] => []
  | _ :: l => coeffAdd l (0 :: coeffDeriv l)

/-- The polynomial of `l` has at every real `x` the derivative given by the list `coeffDeriv l`. -/
theorem hasDerivAt_coeffEval (l : List ℚ) (x : ℝ) :
    HasDerivAt (coeffEval l) (coeffEval (coeffDeriv l) x) x := by
  induction l generalizing x with
  | nil => exact hasDerivAt_const x 0
  | cons a l ih =>
    refine (((hasDerivAt_id x).mul (ih x)).const_add (a : ℝ)).congr_deriv ?_
    simp only [coeffDeriv, coeffEval_coeffAdd, coeffEval_cons, Rat.cast_zero, id]
    ring

/-! ### Integrals of compositions with the cosine -/

/-- `∫₀^π p (cos θ) sin θ dθ = ∫₋₁¹ p`. -/
theorem integral_coeffEval_cos_mul_sin (l : List ℚ) :
    ∫ θ in (0 : ℝ)..Real.pi, coeffEval l (Real.cos θ) * Real.sin θ = coeffIntegralFrom 0 l := by
  have h := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := Real.pi) (f := Real.cos)
    (f' := fun θ ↦ -Real.sin θ) (fun θ _ ↦ Real.hasDerivAt_cos θ)
    (Real.continuous_sin.neg.continuousOn) (continuous_coeffEval l)
  simp only [Function.comp_apply, Real.cos_zero, Real.cos_pi, mul_neg,
    intervalIntegral.integral_neg, intervalIntegral.integral_symm (-1) 1, neg_inj] at h
  rw [h, ← integral_pow_mul_coeffEval 0 l]
  simp

/-- The moments `∫₀^π cos ^ k θ dθ / π`: `1, 0` and `(k + 1) / (k + 2)` times the moment two
orders below. -/
def cosMoment : ℕ → ℚ
  | 0 => 1
  | 1 => 0
  | k + 2 => (k + 1) / (k + 2) * cosMoment k

/-- For every `k`, `∫₀^π cos ^ k θ dθ = π cosMoment k`. -/
theorem integral_cos_pow_eq_cosMoment (k : ℕ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ k = Real.pi * cosMoment k := by
  fun_induction cosMoment k with
  | case1 | case2 => simp
  | case3 k ih =>
    rw [integral_cos_pow, ih]
    simp
    ring

/-- The exact value of `∫₀^π cos ^ j θ p (cos θ) dθ / π` for the coefficient list `l` of `p`. -/
def coeffCosIntegralFrom (j : ℕ) : List ℚ → ℚ
  | [] => 0
  | a :: l => a * cosMoment j + coeffCosIntegralFrom (j + 1) l

/-- For every `j` and coefficient list `l` of `p`,
`∫₀^π cos ^ j θ p (cos θ) dθ = π coeffCosIntegralFrom j l`. -/
theorem integral_cos_pow_mul_coeffEval_cos (j : ℕ) (l : List ℚ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ j * coeffEval l (Real.cos θ) =
      Real.pi * coeffCosIntegralFrom j l := by
  induction l generalizing j with
  | nil => simp [coeffCosIntegralFrom]
  | cons a l ih =>
    simp only [coeffEval_cons, mul_add, ← mul_assoc, ← pow_succ]
    rw [intervalIntegral.integral_add, ih, intervalIntegral.integral_mul_const,
      integral_cos_pow_eq_cosMoment, coeffCosIntegralFrom]
    · push_cast
      ring
    · exact ((Real.continuous_cos.pow j).mul continuous_const).intervalIntegrable _ _
    · exact ((Real.continuous_cos.pow _).mul
        ((continuous_coeffEval l).comp Real.continuous_cos)).intervalIntegrable _ _

/-- `∫₀^π p (cos θ) dθ = π coeffCosIntegralFrom 0 l`. -/
theorem integral_coeffEval_cos (l : List ℚ) :
    ∫ θ in (0 : ℝ)..Real.pi, coeffEval l (Real.cos θ) = Real.pi * coeffCosIntegralFrom 0 l := by
  rw [← integral_cos_pow_mul_coeffEval_cos 0 l]
  simp

end CAS.Polynomial

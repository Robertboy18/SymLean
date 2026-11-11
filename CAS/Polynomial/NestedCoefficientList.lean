/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.CoefficientList

/-!
# Polynomials in two variables as lists of coefficient lists

A list `M = [m₀, m₁, …]` of coefficient lists is the polynomial `∑ j, X ^ j m_j(Y)`, evaluated by
Horner's rule in `X` (`nestedEval M x y`). Sums, scalar multiples, products by a polynomial in
`Y` and by `X`, and the two partial derivatives are computable list operations, each with its
evaluation identity. `hasDerivAt_nestedEval` is the chain rule along a curve
`s ↦ (f s, g s)`: the derivative is `∂_X M · f' + ∂_Y M · g'`. On `[-1, 1] ^ 2` the absolute
value is at most the sum of the absolute values of the coefficients
(`abs_nestedEval_le_nestedNorm`).

## Main definitions

* `nestedEval`: the value `∑ j, x ^ j m_j(y)` of `M = [m₀, m₁, …]`.
* `nestedAdd`: the sum of two nested lists; `nestedScale`, `nestedMulInner` and `nestedShift` are
  the products by a scalar, by a polynomial `p(Y)` and by `X`.
* `nestedDerivOuter`: the partial derivative in `X`; `nestedDerivInner` is the one in `Y`.
* `nestedTrim`: the nested list without trailing zeros in its entries and without trailing empty
  entries.
* `nestedNorm`: the sum of the absolute values of all the coefficients.

## Main results

* `nestedEval_nestedAdd`: `nestedAdd M M'` evaluates to the sum of the values of `M` and `M'`;
  `nestedEval_nestedScale`, `nestedEval_nestedMulInner` and `nestedEval_nestedShift` are the other
  evaluation identities.
* `hasDerivAt_nestedEval`: along a curve `s ↦ (f s, g s)` the derivative of the value is
  `∂_X M · f' + ∂_Y M · g'`.
* `hasDerivAt_nestedEval_outer`: the partial derivative in `x` for fixed `y`;
  `hasDerivAt_nestedEval_inner` is the one in `y` for fixed `x`.
* `nestedEval_nestedTrim`: trimming does not change the value.
* `abs_nestedEval_le_nestedNorm`: for `|x| ≤ 1` and `|y| ≤ 1`, `|nestedEval M x y| ≤ nestedNorm M`.
-/

@[expose] public section

namespace CAS.Polynomial

/-- The value `∑ j, x ^ j m_j(y)` of `M = [m₀, m₁, …]`. -/
noncomputable def nestedEval (M : List (List ℚ)) (x y : ℝ) : ℝ :=
  M.foldr (fun m acc ↦ coeffEval m y + x * acc) 0

/-- The empty nested list evaluates to `0`. -/
@[simp] theorem nestedEval_nil (x y : ℝ) : nestedEval [] x y = 0 := rfl

/-- Horner's rule in `x`: `m :: M` evaluates to `m(y) + x · M(x, y)`. -/
@[simp] theorem nestedEval_cons (m : List ℚ) (M : List (List ℚ)) (x y : ℝ) :
    nestedEval (m :: M) x y = coeffEval m y + x * nestedEval M x y := rfl

/-- The sum of two nested lists. -/
def nestedAdd : List (List ℚ) → List (List ℚ) → List (List ℚ)
  | [], M => M
  | M, [] => M
  | m :: M, m' :: M' => coeffAdd m m' :: nestedAdd M M'

/-- `nestedAdd M M'` evaluates to the sum of the values of `M` and `M'`. -/
theorem nestedEval_nestedAdd (M M' : List (List ℚ)) (x y : ℝ) :
    nestedEval (nestedAdd M M') x y = nestedEval M x y + nestedEval M' x y := by
  fun_induction nestedAdd M M' with
  | case1 | case2 => simp
  | case3 m M m' M' ih =>
    simp only [nestedEval_cons, coeffEval_coeffAdd, ih]
    ring

/-- A scalar multiple of a nested list. -/
def nestedScale (c : ℚ) (M : List (List ℚ)) : List (List ℚ) := M.map (coeffScale c)

/-- `nestedScale c M` evaluates to `c` times the value of `M`. -/
theorem nestedEval_nestedScale (c : ℚ) (M : List (List ℚ)) (x y : ℝ) :
    nestedEval (nestedScale c M) x y = c * nestedEval M x y := by
  induction M with
  | nil => simp [nestedScale]
  | cons m M ih =>
    simp only [nestedScale, List.map_cons, nestedEval_cons, coeffEval_coeffScale] at ih ⊢
    linear_combination x * ih

/-- The product by the polynomial `p(Y)`. -/
def nestedMulInner (p : List ℚ) (M : List (List ℚ)) : List (List ℚ) := M.map (coeffMul p)

/-- `nestedMulInner p M` evaluates to `p(y)` times the value of `M`. -/
theorem nestedEval_nestedMulInner (p : List ℚ) (M : List (List ℚ)) (x y : ℝ) :
    nestedEval (nestedMulInner p M) x y = coeffEval p y * nestedEval M x y := by
  induction M with
  | nil => simp [nestedMulInner]
  | cons m M ih =>
    simp only [nestedMulInner, List.map_cons, nestedEval_cons, coeffEval_coeffMul] at ih ⊢
    linear_combination x * ih

/-- The product by `X`. -/
def nestedShift (M : List (List ℚ)) : List (List ℚ) := [] :: M

/-- `nestedShift M` evaluates to `x` times the value of `M`. -/
theorem nestedEval_nestedShift (M : List (List ℚ)) (x y : ℝ) :
    nestedEval (nestedShift M) x y = x * nestedEval M x y := by
  simp [nestedShift]

/-- The partial derivative in `Y`. -/
def nestedDerivInner (M : List (List ℚ)) : List (List ℚ) := M.map coeffDeriv

/-- The partial derivative in `X`: `(m + X R)' = R + X R'`. -/
def nestedDerivOuter : List (List ℚ) → List (List ℚ)
  | [] => []
  | _ :: M => nestedAdd M (nestedShift (nestedDerivOuter M))

/-- The chain rule along a curve `s ↦ (f s, g s)`. -/
theorem hasDerivAt_nestedEval (M : List (List ℚ)) {f g : ℝ → ℝ} {f' g' s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun u ↦ nestedEval M (f u) (g u))
      (nestedEval (nestedDerivOuter M) (f s) (g s) * f' +
        nestedEval (nestedDerivInner M) (f s) (g s) * g') s := by
  induction M with
  | nil =>
    simpa [nestedDerivOuter, nestedDerivInner] using hasDerivAt_const s (0 : ℝ)
  | cons m M ih =>
    refine (((hasDerivAt_coeffEval m (g s)).comp s hg).add (hf.mul ih)).congr_deriv ?_
    simp only [nestedDerivOuter, nestedDerivInner, List.map_cons, nestedEval_nestedAdd,
      nestedEval_nestedShift, nestedEval_cons]
    ring

/-- The partial derivative in `x` for fixed `y`. -/
theorem hasDerivAt_nestedEval_outer (M : List (List ℚ)) (x y : ℝ) :
    HasDerivAt (fun u ↦ nestedEval M u y) (nestedEval (nestedDerivOuter M) x y) x := by
  simpa using hasDerivAt_nestedEval M (hasDerivAt_id x) (hasDerivAt_const x y)

/-- The partial derivative in `y` for fixed `x`. -/
theorem hasDerivAt_nestedEval_inner (M : List (List ℚ)) (x y : ℝ) :
    HasDerivAt (fun u ↦ nestedEval M x u) (nestedEval (nestedDerivInner M) x y) y := by
  simpa using hasDerivAt_nestedEval M (hasDerivAt_const y x) (hasDerivAt_id y)

/-! ### Trailing zeros -/

/-- The coefficient list without its trailing zeros. -/
def coeffTrim : List ℚ → List ℚ
  | [] => []
  | a :: l =>
    match coeffTrim l with
    | [] => if a = 0 then [] else [a]
    | b :: m => a :: b :: m

/-- Removing trailing zeros does not change the value of a coefficient list. -/
theorem coeffEval_coeffTrim (l : List ℚ) (x : ℝ) : coeffEval (coeffTrim l) x = coeffEval l x := by
  fun_induction coeffTrim l with
  | case1 => rfl
  | case2 l h ih | case3 _ l h _ ih | case4 _ l _ _ h ih => simp [← ih, h]

/-- The nested list without trailing zeros in its entries and without trailing empty entries. -/
def nestedTrim : List (List ℚ) → List (List ℚ)
  | [] => []
  | m :: M =>
    match nestedTrim M with
    | [] => if coeffTrim m = [] then [] else [coeffTrim m]
    | n :: N => coeffTrim m :: n :: N

/-- Removing trailing zeros and trailing empty entries does not change the value of a nested list.
-/
theorem nestedEval_nestedTrim (M : List (List ℚ)) (x y : ℝ) :
    nestedEval (nestedTrim M) x y = nestedEval M x y := by
  fun_induction nestedTrim M with
  | case1 => rfl
  | case2 m M hM h ih | case3 m M hM h ih => simp [← ih, hM, ← coeffEval_coeffTrim m y, h]
  | case4 m M _ _ hM ih => simp [← ih, hM, coeffEval_coeffTrim]

/-! ### Coefficient norms -/

/-- The sum of the absolute values of the coefficients. -/
def coeffNorm (l : List ℚ) : ℚ := (l.map fun c ↦ |c|).sum

/-- The coefficient norm is nonnegative. -/
theorem coeffNorm_nonneg (l : List ℚ) : 0 ≤ coeffNorm l :=
  List.sum_nonneg (by simp)

/-- For `|y| ≤ 1`, the value of a coefficient list at `y` is at most its coefficient norm in
absolute value. -/
theorem abs_coeffEval_le_coeffNorm (l : List ℚ) {y : ℝ} (hy : |y| ≤ 1) :
    |coeffEval l y| ≤ coeffNorm l := by
  induction l with
  | nil => simp [coeffNorm]
  | cons c l ih =>
    simp only [coeffNorm, coeffEval_cons, List.map_cons, List.sum_cons, Rat.cast_add,
      Rat.cast_abs] at ih ⊢
    refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hy).trans ih

/-- The sum of the coefficient norms of the entries. -/
def nestedNorm (M : List (List ℚ)) : ℚ := (M.map coeffNorm).sum

/-- The nested norm is nonnegative. -/
theorem nestedNorm_nonneg (M : List (List ℚ)) : 0 ≤ nestedNorm M :=
  List.sum_nonneg (by simp [coeffNorm_nonneg])

/-- For `|x| ≤ 1` and `|y| ≤ 1`, `|nestedEval M x y| ≤ nestedNorm M`. -/
theorem abs_nestedEval_le_nestedNorm (M : List (List ℚ)) {x y : ℝ} (hx : |x| ≤ 1)
    (hy : |y| ≤ 1) : |nestedEval M x y| ≤ nestedNorm M := by
  induction M with
  | nil => simp [nestedNorm]
  | cons m M ih =>
    simp only [nestedNorm, nestedEval_cons, List.map_cons, List.sum_cons, Rat.cast_add] at ih ⊢
    refine (abs_add_le _ _).trans (add_le_add (abs_coeffEval_le_coeffNorm m hy) ?_)
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hx).trans ih

end CAS.Polynomial

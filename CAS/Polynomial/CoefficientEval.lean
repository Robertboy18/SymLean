/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Evaluating rational coefficient lists

A list `l : List ℚ` of coefficients, lowest degree first, is the polynomial
`l₀ + x (l₁ + x (l₂ + …))`. `coeffEval l x` evaluates it at a real `x` and `coeffEvalRat l q`
at a rational `q`, both by Horner's rule. The rational evaluation is computable, so finite checks
evaluate it, and `coeffEval_ratCast` gives the real value at a rational point.

The list operations each come with their evaluation identity: adding a constant
(`coeffAddHead`) or a monomial (`coeffAddAt`), scalar multiples (`coeffScale`), multiplication
by `X - c` (`coeffMulLinear`) and by `∏ (X - rᵢ)` (`coeffProdLinear`), and the Taylor shift
`l (c + X)` (`coeffShift`). `coeffEq` compares two lists up to trailing zeros.

`AlgRoot.real a lo hi` picks a real root of `a` in `(lo, hi)` with `Classical.epsilon`. When
`lo < hi` and `a` changes sign between the rational endpoints, the pick is such a root
(`AlgRoot.real_spec`, by the intermediate value theorem).
-/

@[expose] public section

namespace CAS.Polynomial

/-- The value at `x` of the polynomial with coefficient list `l`, lowest degree first, by
Horner's rule. -/
def coeffEval (l : List ℚ) (x : ℝ) : ℝ :=
  l.foldr (fun c acc ↦ (c : ℝ) + x * acc) 0

/-- The empty coefficient list evaluates to `0` at every real `x`. -/
@[simp] theorem coeffEval_nil (x : ℝ) : coeffEval [] x = 0 := rfl

/-- Horner's rule: `coeffEval (c :: l) x = c + x * coeffEval l x`. -/
@[simp] theorem coeffEval_cons (c : ℚ) (l : List ℚ) (x : ℝ) :
    coeffEval (c :: l) x = c + x * coeffEval l x := rfl

/-- The value at a rational `q` of the polynomial with coefficient list `l`, computed in `ℚ`. -/
def coeffEvalRat : List ℚ → ℚ → ℚ
  | [], _ => 0
  | c :: l, q => c + q * coeffEvalRat l q

/-- At a rational point the real evaluation is the rational one. -/
theorem coeffEval_ratCast (l : List ℚ) (q : ℚ) : coeffEval l q = coeffEvalRat l q := by
  induction l <;> simp [coeffEvalRat, *]

/-- For every coefficient list `l`, the function `coeffEval l : ℝ → ℝ` is continuous. -/
theorem continuous_coeffEval (l : List ℚ) : Continuous (coeffEval l) := by
  induction l with
  | nil => exact continuous_const
  | cons a l ih => exact continuous_const.add (continuous_id.mul ih)

/-! ### Operations on coefficient lists -/

/-- Add `c` to the constant coefficient. -/
def coeffAddHead (c : ℚ) : List ℚ → List ℚ
  | [] => [c]
  | a :: l => (c + a) :: l

/-- Adding `c` to the constant coefficient adds `c` to the value:
`coeffEval (coeffAddHead c l) x = c + coeffEval l x`. -/
theorem coeffEval_coeffAddHead (c : ℚ) (l : List ℚ) (x : ℝ) :
    coeffEval (coeffAddHead c l) x = c + coeffEval l x := by
  cases l <;> simp [coeffAddHead, add_assoc]

/-- Add `a Xᵏ`. -/
def coeffAddAt : ℕ → ℚ → List ℚ → List ℚ
  | 0, a, l => coeffAddHead a l
  | k + 1, a, [] => 0 :: coeffAddAt k a []
  | k + 1, a, b :: l => b :: coeffAddAt k a l

/-- Adding `a Xᵏ` adds `a xᵏ` to the value:
`coeffEval (coeffAddAt k a l) x = a * x ^ k + coeffEval l x`, also for `k ≥ l.length`. -/
theorem coeffEval_coeffAddAt : ∀ (k : ℕ) (a : ℚ) (l : List ℚ) (x : ℝ),
    coeffEval (coeffAddAt k a l) x = a * x ^ k + coeffEval l x
  | 0, a, l, x => by simp [coeffAddAt, coeffEval_coeffAddHead]
  | k + 1, a, [], x => by
    simp only [coeffAddAt, coeffEval_cons, coeffEval_coeffAddAt k, coeffEval_nil, Rat.cast_zero]
    ring
  | k + 1, a, b :: l, x => by
    simp only [coeffAddAt, coeffEval_cons, coeffEval_coeffAddAt k]
    ring

/-- A scalar multiple of a coefficient list. -/
def coeffScale (c : ℚ) (l : List ℚ) : List ℚ := l.map (c * ·)

/-- Scaling the coefficients by `c` scales the value:
`coeffEval (coeffScale c l) x = c * coeffEval l x`. -/
theorem coeffEval_coeffScale (c : ℚ) (l : List ℚ) (x : ℝ) :
    coeffEval (coeffScale c l) x = c * coeffEval l x := by
  induction l with
  | nil => simp [coeffScale]
  | cons a l ih =>
    simp only [coeffScale, List.map_cons, coeffEval_cons, Rat.cast_mul] at ih ⊢
    rw [ih]
    ring

/-- Multiplication by `X - c` on coefficient lists. -/
def coeffMulLinear (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: l => (-c * a) :: coeffAddHead a (coeffMulLinear c l)

/-- Multiplication by `X - c`: `coeffEval (coeffMulLinear c l) x = (x - c) * coeffEval l x`. -/
theorem coeffEval_coeffMulLinear (c : ℚ) (l : List ℚ) (x : ℝ) :
    coeffEval (coeffMulLinear c l) x = (x - c) * coeffEval l x := by
  induction l with
  | nil => simp [coeffMulLinear]
  | cons a l ih =>
    simp only [coeffMulLinear, coeffEval_cons, coeffEval_coeffAddHead, ih, Rat.cast_mul,
      Rat.cast_neg]
    ring

/-- The coefficients of `∏ (X - rᵢ) · q`. -/
def coeffProdLinear (rs q : List ℚ) : List ℚ := rs.foldr coeffMulLinear q

/-- Multiplication by `∏ (X - rᵢ)`: `coeffProdLinear rs q` evaluates at `x` to the product of the
`x - r` over `r ∈ rs` times `coeffEval q x`. -/
theorem coeffEval_coeffProdLinear (rs q : List ℚ) (x : ℝ) :
    coeffEval (coeffProdLinear rs q) x = (rs.map fun r : ℚ ↦ x - r).prod * coeffEval q x := by
  induction rs with
  | nil => simp [coeffProdLinear]
  | cons r rs ih =>
    simp only [coeffProdLinear, List.foldr_cons] at ih ⊢
    rw [coeffEval_coeffMulLinear, ih, List.map_cons, List.prod_cons, mul_assoc]

/-- The Taylor shift: the coefficients of `l (c + X)`, by Horner's rule. -/
def coeffShift (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: l => coeffAddHead a (coeffMulLinear (-c) (coeffShift c l))

/-- The Taylor shift: `coeffEval (coeffShift c l) u = coeffEval l (c + u)` for every real `u`. -/
theorem coeffEval_coeffShift (c : ℚ) (l : List ℚ) (u : ℝ) :
    coeffEval (coeffShift c l) u = coeffEval l (c + u) := by
  induction l with
  | nil => simp [coeffShift]
  | cons a l ih =>
    simp only [coeffShift, coeffEval_coeffAddHead, coeffEval_coeffMulLinear, ih, coeffEval_cons,
      Rat.cast_neg]
    ring

/-- Whether every coefficient of a list is zero. -/
def coeffAllZero : List ℚ → Bool
  | [] => true
  | a :: l => decide (a = 0) && coeffAllZero l

/-- A coefficient list that `coeffAllZero` accepts evaluates to `0` at every real `x`. -/
theorem coeffEval_eq_zero_of_coeffAllZero : ∀ {l : List ℚ}, coeffAllZero l = true →
    ∀ x : ℝ, coeffEval l x = 0
  | [], _, _ => rfl
  | a :: l, h, x => by
    simp only [coeffAllZero, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [coeffEval_cons, coeffEval_eq_zero_of_coeffAllZero h.2 x, h.1]
    simp

/-- Whether two coefficient lists are equal up to trailing zeros. The recursion is structural in
the first list, so the kernel evaluates it. -/
def coeffEq : List ℚ → List ℚ → Bool
  | [], m => coeffAllZero m
  | a :: l, [] => coeffAllZero (a :: l)
  | a :: l, b :: m => decide (a = b) && coeffEq l m

/-- Two coefficient lists that `coeffEq` accepts, equal up to trailing zeros, have the same value at
every real `x`. -/
theorem coeffEval_eq_of_coeffEq : ∀ {l m : List ℚ}, coeffEq l m = true →
    ∀ x : ℝ, coeffEval l x = coeffEval m x
  | [], m, h, x => by
    simp only [coeffEq] at h
    rw [coeffEval_nil, coeffEval_eq_zero_of_coeffAllZero h x]
  | a :: l, [], h, x => by
    simp only [coeffEq] at h
    rw [coeffEval_nil, coeffEval_eq_zero_of_coeffAllZero h x]
  | a :: l, b :: m, h, x => by
    simp only [coeffEq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [coeffEval_cons, coeffEval_cons, coeffEval_eq_of_coeffEq h.2 x, h.1]

end CAS.Polynomial

namespace CAS.AlgRoot

open CAS.Polynomial

/-- For `lo < hi` and a sign change `coeffEvalRat a lo * coeffEvalRat a hi < 0` at the rational
endpoints, `coeffEval a` has a root in the open interval `(lo, hi)`. -/
theorem exists_real_root (a : List ℚ) {lo hi : ℚ} (hlt : lo < hi)
    (hsign : coeffEvalRat a lo * coeffEvalRat a hi < 0) :
    ∃ r ∈ Set.Ioo (lo : ℝ) hi, coeffEval a r = 0 := by
  have hab : (lo : ℝ) ≤ hi := by exact_mod_cast hlt.le
  have hc := (continuous_coeffEval a).continuousOn (s := Set.Icc (lo : ℝ) hi)
  rcases mul_neg_iff.mp hsign with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · exact intermediate_value_Ioo' hab hc (by simp [coeffEval_ratCast, hlo, hhi])
  · exact intermediate_value_Ioo hab hc (by simp [coeffEval_ratCast, hlo, hhi])

/-- A root of `coeffEval a` in `(lo, hi)`, chosen by `Classical.epsilon`. One exists when `lo < hi`
and `a` changes sign at the rational endpoints, and then the value is such a root (`real_spec`).
When `(lo, hi)` contains no root the value is unspecified, as is the choice among several roots. -/
noncomputable def real (a : List ℚ) (lo hi : ℚ) : ℝ :=
  Classical.epsilon fun r ↦ r ∈ Set.Ioo (lo : ℝ) hi ∧ coeffEval a r = 0

/-- For `lo < hi` and `coeffEvalRat a lo * coeffEvalRat a hi < 0`, `real a lo hi` lies in the open
interval `(lo, hi)` and is a root of `coeffEval a`. -/
theorem real_spec (a : List ℚ) {lo hi : ℚ} (hlt : lo < hi)
    (hsign : coeffEvalRat a lo * coeffEvalRat a hi < 0) :
    real a lo hi ∈ Set.Ioo (lo : ℝ) hi ∧ coeffEval a (real a lo hi) = 0 :=
  Classical.epsilon_spec (exists_real_root a hlt hsign)

end CAS.AlgRoot

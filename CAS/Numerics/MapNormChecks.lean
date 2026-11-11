/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.MatrixPositivity
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Chebyshev

/-!
# Integer checks of the two Gram bounds of a coordinate map

For a coordinate map `g ↦ ∑ⱼ ⟪qⱼ, g⟫ φⱼ` and a matrix `Z = Zi / 2^z` of integers `Zi`, the two
hypotheses of the coordinate-map bound become positivity of integer matrices, certified by
`ldltCheck`.

* `form_le_of_ldltCheck_massMapMatrix`: the matrix `g 2^(2z) I - K (a Ziᵀ S Zi + b Ziᵀ Zi)` over
  `2^(p + 2z)` gives `K (a/2^p cᵀ S c + b/2^p |c|²) ≤ g/2^p |y|²` for `c = Z y`.
* `form_le_of_ldltCheck_captureMapMatrix`: with the scales `λᵢ = lamᵢ / 2^e`, a center
  `Hc / 2^t` within `2^-h` of a symmetric form `H`, the matrix
  `Λ Zi Ziᵀ Λ - Hc 2^(2e + 2z - t) - n 2^(2e + 2z - h) I` over `2^(2e + 2z)` gives
  `∑ᵢⱼ Hᵢⱼ / (λᵢ λⱼ) aᵢ aⱼ ≤ |Zᵀ a|²`.

`sum_sum_mul_mul_le_of_abs_sub_le` bounds a quadratic form by an entrywise close one, with the
loss `n e |c|²`.

## Implementation notes

Each bound reduces to the positive semidefiniteness of one integer matrix: untrusted code
proposes the factor `L` and the weights `d`, and the kernel runs `ldltCheck` with `τ = 0`
(`form_nonneg_of_ldltCheck`). Every scale is a power of two, so the matrices have integer
entries (in the capture bound once `t, h ≤ 2e + 2z`). There the form `H` is known only within
`2^-h` per entry, through its center `Hc / 2^t`; the term `n 2^(2e + 2z - h) I` of
`captureMapMatrix` pays for that error, by `sum_sum_mul_mul_le_of_abs_sub_le`.
-/

@[expose] public section

open Finset

namespace CAS.Numerics

variable {n : ℕ}

/-- The integer matrix `g 2^(2z) I - K (a Ziᵀ S Zi + b Ziᵀ Zi)`. -/
def massMapMatrix (Zi S : Fin n → Fin n → ℤ) (z K a b g : ℕ) (i j : Fin n) : ℤ :=
  (if i = j then (g : ℤ) * 2 ^ (2 * z) else 0) -
    K * (a * ∑ k, Zi k i * ∑ l, S k l * Zi l j + b * ∑ k, Zi k i * Zi k j)

/-- The integer matrix `Λ Zi Ziᵀ Λ - Hc 2^(2e + 2z - t) - n 2^(2e + 2z - h) I`. -/
def captureMapMatrix (Zi : Fin n → Fin n → ℤ) (lam : Fin n → ℤ) (Hc : Fin n → Fin n → ℤ)
    (z e t h : ℕ) (i j : Fin n) : ℤ :=
  lam i * lam j * ∑ k, Zi i k * Zi j k - Hc i j * 2 ^ (2 * e + 2 * z - t) -
    if i = j then (n : ℤ) * 2 ^ (2 * e + 2 * z - h) else 0

private theorem form_nonneg_of_ldltCheck {M L : Fin n → Fin n → ℤ} {d : Fin n → ℕ} {s : ℕ}
    (h : ldltCheck M L d s 0 = true) (y : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, ((M i j : ℝ) / 2 ^ s) * y i * y j := by
  have := quadForm_ge_of_ldltCheck M L d s 0 h y
  simpa using this

private theorem sum_sum_ite_mul (f : Fin n → ℝ) (y : Fin n → ℝ) :
    ∑ i, ∑ j, (if i = j then f i else 0) * y i * y j = ∑ i, f i * y i ^ 2 := by
  refine sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [Ne.symm hj])
    (fun h ↦ absurd (mem_univ i) h)]
  simp only [↓reduceIte]
  ring

private theorem sum4_comm (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ k, ∑ l, ∑ i, ∑ j, f k l i j = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j :=
  calc ∑ k, ∑ l, ∑ i, ∑ j, f k l i j = ∑ k, ∑ i, ∑ l, ∑ j, f k l i j :=
        sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ l, ∑ j, f k l i j := Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ j, ∑ l, f k l i j :=
        sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := sum_congr rfl fun _ _ ↦ Finset.sum_comm

private theorem sum3_comm (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ k, ∑ i, ∑ j, f k i j = ∑ i, ∑ j, ∑ k, f k i j :=
  calc ∑ k, ∑ i, ∑ j, f k i j = ∑ i, ∑ k, ∑ j, f k i j := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, f k i j := sum_congr rfl fun _ _ ↦ Finset.sum_comm

/-- **The mass check.** -/
theorem form_le_of_ldltCheck_massMapMatrix {Zi S L : Fin n → Fin n → ℤ} {d : Fin n → ℕ}
    {z p K a b g : ℕ} (h : ldltCheck (massMapMatrix Zi S z K a b g) L d (p + 2 * z) 0 = true)
    (y : Fin n → ℝ) :
    (K : ℝ) * ((a : ℝ) / 2 ^ p * ∑ k, ∑ l, (S k l : ℝ) *
        (∑ i, (Zi k i : ℝ) / 2 ^ z * y i) * (∑ j, (Zi l j : ℝ) / 2 ^ z * y j) +
      (b : ℝ) / 2 ^ p * ∑ k, (∑ i, (Zi k i : ℝ) / 2 ^ z * y i) ^ 2) ≤
      (g : ℝ) / 2 ^ p * ∑ i, y i ^ 2 := by
  have h0 := form_nonneg_of_ldltCheck h y
  set D : ℝ := 2 ^ (p + 2 * z)
  have hz : D = 2 ^ p * 2 ^ z * 2 ^ z := by simp only [D]; ring
  have hD : D ≠ 0 := by positivity
  set T : Fin n → Fin n → ℝ := fun i j ↦ ∑ k, (Zi k i : ℝ) * ∑ l, (S k l : ℝ) * Zi l j
  set U : Fin n → Fin n → ℝ := fun i j ↦ ∑ k, (Zi k i : ℝ) * Zi k j
  have hM : ∀ i j, ((massMapMatrix Zi S z K a b g i j : ℤ) : ℝ) / D * y i * y j =
      (((if i = j then (g : ℤ) * 2 ^ (2 * z) else 0 : ℤ) : ℝ) / D) * y i * y j -
        (K : ℝ) * a * (T i j / D * y i * y j) - (K : ℝ) * b * (U i j / D * y i * y j) := by
    intro i j
    simp only [massMapMatrix, T, U]
    push_cast
    field_simp
    ring
  have hS : ∑ i, ∑ j, T i j / D * y i * y j =
      1 / 2 ^ p * ∑ k, ∑ l, (S k l : ℝ) * (∑ i, (Zi k i : ℝ) / 2 ^ z * y i) *
        (∑ j, (Zi l j : ℝ) / 2 ^ z * y j) := by
    simp only [T, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    rw [Finset.sum_comm]
    refine Eq.trans ?_ (sum4_comm _).symm
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦
      sum_congr rfl fun l _ ↦ ?_
    rw [hz]
    field_simp
  have hB : ∑ i, ∑ j, U i j / D * y i * y j =
      1 / 2 ^ p * ∑ k, (∑ i, (Zi k i : ℝ) / 2 ^ z * y i) ^ 2 := by
    simp only [U, sq, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    refine Eq.trans ?_ (sum3_comm _).symm
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ ?_
    rw [hz]
    field_simp
  have hG : ∑ i, ∑ j, (((if i = j then (g : ℤ) * 2 ^ (2 * z) else 0 : ℤ) : ℝ) / D) *
      y i * y j = (g : ℝ) / 2 ^ p * ∑ i, y i ^ 2 := by
    have : ∀ i j : Fin n, (((if i = j then (g : ℤ) * 2 ^ (2 * z) else 0 : ℤ) : ℝ) / D) =
        if i = j then (g : ℝ) / 2 ^ p else 0 := fun i j ↦ by
      split_ifs
      · push_cast
        rw [hz, show (2 : ℝ) ^ (2 * z) = 2 ^ z * 2 ^ z by ring]
        field_simp
      · simp
    simp only [this]
    rw [sum_sum_ite_mul (fun _ ↦ (g : ℝ) / 2 ^ p), Finset.mul_sum]
  simp only [hM, Finset.sum_sub_distrib, ← Finset.mul_sum, hG, hS, hB] at h0
  set X := ∑ k, ∑ l, (S k l : ℝ) * (∑ i, (Zi k i : ℝ) / 2 ^ z * y i) *
    (∑ j, (Zi l j : ℝ) / 2 ^ z * y j)
  set Y := ∑ k, (∑ i, (Zi k i : ℝ) / 2 ^ z * y i) ^ 2
  have e : (K : ℝ) * ((a : ℝ) / 2 ^ p * X + (b : ℝ) / 2 ^ p * Y) =
      (K : ℝ) * a * (1 / 2 ^ p * X) + (K : ℝ) * b * (1 / 2 ^ p * Y) := by ring
  rw [e]
  linarith

/-- A quadratic form close to another entrywise. -/
theorem sum_sum_mul_mul_le_of_abs_sub_le {A B : Fin n → Fin n → ℝ} {e : ℝ} (he : 0 ≤ e)
    (h : ∀ i j, |A i j - B i j| ≤ e) (c : Fin n → ℝ) :
    ∑ i, ∑ j, c i * c j * A i j ≤ ∑ i, ∑ j, c i * c j * B i j + n * e * ∑ j, c j ^ 2 := by
  have h1 : ∀ i j, c i * c j * A i j ≤ c i * c j * B i j + e * (|c i| * |c j|) := by
    intro i j
    have hcc : |c i * c j * (A i j - B i j)| ≤ e * (|c i| * |c j|) := by
      rw [abs_mul, abs_mul, mul_comm e]
      exact mul_le_mul_of_nonneg_left (h i j) (by positivity)
    linarith [le_abs_self (c i * c j * (A i j - B i j))]
  have h2 : ∑ i, ∑ j, e * (|c i| * |c j|) = e * (∑ i, |c i|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    exact sum_congr rfl fun i _ ↦ by rw [Finset.mul_sum]
  have h3 : (∑ i, |c i|) ^ 2 ≤ n * ∑ j, c j ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n))) (f := fun i ↦ |c i|)
    simpa only [card_univ, Fintype.card_fin, sq_abs] using this
  calc ∑ i, ∑ j, c i * c j * A i j
      ≤ ∑ i, ∑ j, (c i * c j * B i j + e * (|c i| * |c j|)) :=
        sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ h1 i j
    _ = ∑ i, ∑ j, c i * c j * B i j + e * (∑ i, |c i|) ^ 2 := by
        simp only [Finset.sum_add_distrib, h2]
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left h3 he]

/-- **The capture check.** -/
theorem form_le_of_ldltCheck_captureMapMatrix {Zi Hc L : Fin n → Fin n → ℤ} {lam : Fin n → ℤ}
    {d : Fin n → ℕ} {z e t h : ℕ} (ht : t ≤ 2 * e + 2 * z) (hh : h ≤ 2 * e + 2 * z)
    (hchk : ldltCheck (captureMapMatrix Zi lam Hc z e t h) L d (2 * e + 2 * z) 0 = true)
    {H : Fin n → Fin n → ℝ} (hH : ∀ i j, |H i j - (Hc i j : ℝ) / 2 ^ t| ≤ 1 / 2 ^ h)
    (hlam : ∀ i, lam i ≠ 0) (a : Fin n → ℝ) :
    ∑ i, ∑ j, H i j / (((lam i : ℝ) / 2 ^ e) * ((lam j : ℝ) / 2 ^ e)) * a i * a j ≤
      ∑ k, (∑ j, (Zi j k : ℝ) / 2 ^ z * a j) ^ 2 := by
  set μ : Fin n → ℝ := fun i ↦ (lam i : ℝ) / 2 ^ e
  have hμ : ∀ i, μ i ≠ 0 := fun i ↦ div_ne_zero (Int.cast_ne_zero.mpr (hlam i)) (by positivity)
  set y : Fin n → ℝ := fun i ↦ a i / μ i
  have ha : ∀ i, a i = μ i * y i := fun i ↦ by simp only [y]; field_simp [hμ i]
  have h1 : ∑ i, ∑ j, H i j / (μ i * μ j) * a i * a j = ∑ i, ∑ j, y i * y j * H i j :=
    sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by
      rw [ha i, ha j]; field_simp [hμ i, hμ j]
  have h2 := sum_sum_mul_mul_le_of_abs_sub_le (by positivity) hH y
  have h0 := form_nonneg_of_ldltCheck hchk y
  set s := 2 * e + 2 * z
  have hst : (2 : ℝ) ^ s = 2 ^ (s - t) * 2 ^ t := by rw [← pow_add, Nat.sub_add_cancel ht]
  have hsh : (2 : ℝ) ^ s = 2 ^ (s - h) * 2 ^ h := by rw [← pow_add, Nat.sub_add_cancel hh]
  have hs : (2 : ℝ) ^ s = 2 ^ e * 2 ^ e * (2 ^ z * 2 ^ z) := by simp only [s]; ring
  have hM : ∀ i j, ((captureMapMatrix Zi lam Hc z e t h i j : ℤ) : ℝ) / 2 ^ s * y i * y j =
      μ i * μ j * (∑ k, (Zi i k : ℝ) / 2 ^ z * ((Zi j k : ℝ) / 2 ^ z)) * y i * y j -
        y i * y j * ((Hc i j : ℝ) / 2 ^ t) -
          (if i = j then (n : ℝ) * (1 / 2 ^ h) else 0) * y i * y j := by
    intro i j
    simp only [captureMapMatrix, μ]
    push_cast
    have e1 : ((lam i : ℝ) * lam j * ∑ k, (Zi i k : ℝ) * Zi j k) / 2 ^ s =
        (lam i : ℝ) / 2 ^ e * ((lam j : ℝ) / 2 ^ e) *
          ∑ k, (Zi i k : ℝ) / 2 ^ z * ((Zi j k : ℝ) / 2 ^ z) := by
      rw [hs, Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
      exact sum_congr rfl fun k _ ↦ by field_simp
    have e2 : (Hc i j : ℝ) * 2 ^ (s - t) / 2 ^ s = (Hc i j : ℝ) / 2 ^ t := by
      rw [hst]; field_simp
    have e3 : ((if i = j then (n : ℝ) * 2 ^ (s - h) else 0) / 2 ^ s) =
        if i = j then (n : ℝ) * (1 / 2 ^ h) else 0 := by
      split_ifs
      · rw [hsh]; field_simp
      · simp
    rw [sub_div, sub_div, e1, e2, e3]
    ring
  simp only [hM, Finset.sum_sub_distrib] at h0
  rw [sum_sum_ite_mul (fun _ ↦ (n : ℝ) * (1 / 2 ^ h)) y, ← Finset.mul_sum] at h0
  have h3 : ∑ i, ∑ j, μ i * μ j * (∑ k, (Zi i k : ℝ) / 2 ^ z * ((Zi j k : ℝ) / 2 ^ z)) *
      y i * y j = ∑ k, (∑ j, (Zi j k : ℝ) / 2 ^ z * a j) ^ 2 := by
    simp only [sq, Finset.mul_sum, Finset.sum_mul]
    refine Eq.trans ?_ (sum3_comm _).symm
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ ?_
    rw [ha i, ha j]
    ring
  rw [h3] at h0
  rw [show (∑ i, ∑ j, H i j / ((lam i : ℝ) / 2 ^ e * ((lam j : ℝ) / 2 ^ e)) * a i * a j) =
    ∑ i, ∑ j, H i j / (μ i * μ j) * a i * a j from rfl, h1]
  linarith

end CAS.Numerics

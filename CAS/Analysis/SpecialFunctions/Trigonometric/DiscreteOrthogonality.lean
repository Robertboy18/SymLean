/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity.Finset

/-!
# Discrete orthogonality of cosines at equally spaced angles

Let `h_j` be the trapezoid factor of the node `j` among `0, …, N`: `1/2` at `j = 0` and
`j = N`, and `1` in between. For an integer `p` the trapezoid sum
`∑_{j ≤ N} h_j cos (j p π / N)` equals `N` when `2N` divides `p` and vanishes otherwise.
Multiplied by `sin (p π / (2N))` the sum telescopes to `cos (p π / (2N)) sin (p π) / 2 = 0`.
A product of cosines of frequencies `k, m ≤ N` splits into the frequencies `k + m` and
`k - m`, which gives the discrete orthogonality of the cosines `cos (j k π / N)` (the
type-I discrete cosine transform). Every list of moments `μ_0, …, μ_N` of the cosines
`cos (k x)` is therefore reproduced by the node values at `x_n = n π / N` with the weights
`w_n = (2/N) h_n ∑_{k ≤ N} h_k μ_k cos (n k π / N)`. Over `N` equally spaced points of the
full circle, the sum of `cos (k x)` is `N` when `N` divides `k` and zero otherwise, and the
sum of `sin (k x)` vanishes.

The angles are written `j * (k * π / N)` for the nodes `j π / N` of `[0, π]` and
`k * (2 * π * j / N)` for the points `2π j / N` of the circle.

## Main results

* `sum_trapezoidFactor_mul_cos_int`, `sum_trapezoidFactor_mul_cos_nat`: the trapezoid sum of
  `cos (j p π / N)`.
* `trapezoidFactor_mul_sum_cos_mul_cos`: discrete orthogonality of the cosines.
* `sum_cosineRuleWeight_mul_cos`: the weights `cosineRuleWeight N μ` reproduce every moment
  `μ m` with `m ≤ N`.
* `sum_range_cos_mul_two_pi`, `sum_range_sin_mul_two_pi`: equally weighted sums over the
  circle.
-/

@[expose] public noncomputable section

namespace CAS.Analysis

open Finset

/-- The trapezoid factor of the node `j` among `0, …, N`: `1/2` at the two endpoints and `1`
at the interior nodes. -/
def trapezoidFactor (N j : ℕ) : ℝ :=
  if j = 0 ∨ j = N then 1 / 2 else 1

/-- The trapezoid factor of the first node `0` is `1/2`, for every `N`. -/
@[simp]
theorem trapezoidFactor_zero (N : ℕ) : trapezoidFactor N 0 = 1 / 2 :=
  ite_eq_left (Or.inl rfl)

/-- The trapezoid factor of the last node `N` is `1/2`. -/
@[simp]
theorem trapezoidFactor_self (N : ℕ) : trapezoidFactor N N = 1 / 2 :=
  ite_eq_left (Or.inr rfl)

/-- The trapezoid factor of an interior node `0 < j < N` is `1`. -/
theorem trapezoidFactor_of_pos_of_lt {N j : ℕ} (hj : 0 < j) (hjN : j < N) :
    trapezoidFactor N j = 1 :=
  ite_eq_right (by omega)

/-- Every trapezoid factor is positive, for all `N` and `j`. -/
theorem trapezoidFactor_pos (N j : ℕ) : 0 < trapezoidFactor N j := by
  unfold trapezoidFactor
  split_ifs <;> norm_num

/-- Every trapezoid factor is at most `1`, for all `N` and `j`. -/
theorem trapezoidFactor_le_one (N j : ℕ) : trapezoidFactor N j ≤ 1 := by
  unfold trapezoidFactor
  split_ifs <;> norm_num

/-- Every trapezoid factor is at least `1/2`, for all `N` and `j`. -/
theorem half_le_trapezoidFactor (N j : ℕ) : 1 / 2 ≤ trapezoidFactor N j := by
  unfold trapezoidFactor
  split_ifs <;> norm_num

/-- A trapezoid-weighted sum is the sum of the averages of neighbouring values. -/
theorem sum_range_trapezoidFactor_mul {N : ℕ} (hN : 0 < N) (g : ℕ → ℝ) :
    ∑ j ∈ range (N + 1), trapezoidFactor N j * g j =
      ∑ j ∈ range N, (g j + g (j + 1)) / 2 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hin : ∀ j ∈ range M, trapezoidFactor (M + 1) (j + 1) * g (j + 1) = g (j + 1) :=
    fun j hj ↦ by rw [trapezoidFactor_of_pos_of_lt j.succ_pos (by simpa using hj), one_mul]
  rw [sum_range_succ, sum_range_succ', sum_congr rfl hin, ← sum_div, sum_add_distrib,
    sum_range_succ (fun j ↦ g (j + 1)), sum_range_succ' g, trapezoidFactor_zero,
    trapezoidFactor_self]
  ring

/-- The trapezoid factors of the nodes `0, …, N` add up to `N`. -/
theorem sum_trapezoidFactor {N : ℕ} (hN : 0 < N) :
    ∑ j ∈ range (N + 1), trapezoidFactor N j = N := by
  simpa [one_add_one_eq_two] using sum_range_trapezoidFactor_mul hN (fun _ ↦ (1 : ℝ))

/-- Multiplied by `sin (x / 2)`, the trapezoid sum of `cos (j x)` telescopes. -/
theorem sin_half_mul_sum_trapezoidFactor_mul_cos {N : ℕ} (hN : 0 < N) (x : ℝ) :
    Real.sin (x / 2) * ∑ j ∈ range (N + 1), trapezoidFactor N j * Real.cos (j * x) =
      Real.cos (x / 2) * Real.sin (N * x) / 2 := by
  rw [sum_range_trapezoidFactor_mul hN (fun j : ℕ ↦ Real.cos (j * x)), mul_sum]
  have key : ∀ j : ℕ, Real.sin (x / 2) *
      ((Real.cos (j * x) + Real.cos (((j + 1 : ℕ) : ℝ) * x)) / 2) =
      Real.cos (x / 2) / 2 * (Real.sin (((j + 1 : ℕ) : ℝ) * x) - Real.sin (j * x)) := by
    intro j
    have h1 : (j : ℝ) * x = (j + 1 / 2) * x - x / 2 := by ring
    have h2 : ((j + 1 : ℕ) : ℝ) * x = (j + 1 / 2) * x + x / 2 := by push_cast; ring
    rw [h1, h2, Real.cos_sub, Real.cos_add, Real.sin_add, Real.sin_sub]
    ring
  rw [sum_congr rfl fun j _ ↦ key j, ← mul_sum,
    sum_range_sub (fun j : ℕ ↦ Real.sin (j * x)) N]
  simp only [Nat.cast_zero, zero_mul, Real.sin_zero, sub_zero]
  ring

/-- The trapezoid sum of `cos (j p π / N)` over the nodes `j = 0, …, N` is `N` when `2N`
divides `p` and zero otherwise. -/
theorem sum_trapezoidFactor_mul_cos_int {N : ℕ} (hN : 0 < N) (p : ℤ) :
    ∑ j ∈ range (N + 1), trapezoidFactor N j * Real.cos (j * (p * Real.pi / N)) =
      if 2 * (N : ℤ) ∣ p then (N : ℝ) else 0 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  split_ifs with hp
  · obtain ⟨m, rfl⟩ := hp
    have hcos (j : ℕ) : Real.cos (j * (((2 * (N : ℤ) * m : ℤ) : ℝ) * Real.pi / N)) = 1 := by
      rw [show (j : ℝ) * (((2 * (N : ℤ) * m : ℤ) : ℝ) * Real.pi / N) =
          ((j * m : ℤ) : ℝ) * (2 * Real.pi) by push_cast; field_simp, Real.cos_int_mul_two_pi]
    simpa only [hcos, mul_one] using sum_trapezoidFactor hN
  · have hsin : Real.sin (p * Real.pi / N / 2) ≠ 0 := by
      rw [Ne, Real.sin_eq_zero_iff]
      rintro ⟨n, hn⟩
      refine hp ⟨n, ?_⟩
      field_simp at hn
      have := Real.pi_pos
      exact_mod_cast (by nlinarith [hn] : (p : ℝ) = 2 * N * n)
    have h := sin_half_mul_sum_trapezoidFactor_mul_cos hN (p * Real.pi / N)
    rw [show (N : ℝ) * (p * Real.pi / N) = p * Real.pi by field_simp, Real.sin_int_mul_pi,
      mul_zero, zero_div] at h
    exact (mul_eq_zero.mp h).resolve_left hsin

/-- The trapezoid sum of `cos (j k π / N)` for a natural frequency `k`. -/
theorem sum_trapezoidFactor_mul_cos_nat {N : ℕ} (hN : 0 < N) (k : ℕ) :
    ∑ j ∈ range (N + 1), trapezoidFactor N j * Real.cos (j * (k * Real.pi / N)) =
      if 2 * N ∣ k then (N : ℝ) else 0 := by
  exact_mod_cast sum_trapezoidFactor_mul_cos_int hN k

/-- Discrete orthogonality of the cosines `cos (j k π / N)`, `k ≤ N`, for the trapezoid
weights: the sum vanishes for `k ≠ m`, and `h_k` times the sum is `N / 2` for `k = m`. -/
theorem trapezoidFactor_mul_sum_cos_mul_cos {N : ℕ} (hN : 0 < N) {k m : ℕ} (hk : k ≤ N)
    (hm : m ≤ N) :
    trapezoidFactor N k * ∑ j ∈ range (N + 1), trapezoidFactor N j *
        (Real.cos (j * (k * Real.pi / N)) * Real.cos (j * (m * Real.pi / N))) =
      if k = m then (N : ℝ) / 2 else 0 := by
  have hsplit : ∑ j ∈ range (N + 1), trapezoidFactor N j *
        (Real.cos (j * (k * Real.pi / N)) * Real.cos (j * (m * Real.pi / N))) =
      ((∑ j ∈ range (N + 1), trapezoidFactor N j *
          Real.cos (j * ((((k : ℤ) + m : ℤ) : ℝ) * Real.pi / N))) +
        ∑ j ∈ range (N + 1), trapezoidFactor N j *
          Real.cos (j * ((((k : ℤ) - m : ℤ) : ℝ) * Real.pi / N))) / 2 := by
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [show (j : ℝ) * ((((k : ℤ) + m : ℤ) : ℝ) * Real.pi / N) =
        j * (k * Real.pi / N) + j * (m * Real.pi / N) by push_cast; ring,
      show (j : ℝ) * ((((k : ℤ) - m : ℤ) : ℝ) * Real.pi / N) =
        j * (k * Real.pi / N) - j * (m * Real.pi / N) by push_cast; ring,
      Real.cos_add, Real.cos_sub]
    ring
  have hnd {p : ℤ} (hp : p ≠ 0) (hlt : |p| < 2 * N) : ¬ 2 * (N : ℤ) ∣ p :=
    fun hd ↦ hp (Int.eq_zero_of_abs_lt_dvd hd hlt)
  rw [hsplit, sum_trapezoidFactor_mul_cos_int hN, sum_trapezoidFactor_mul_cos_int hN]
  rcases eq_or_ne k m with rfl | hkm
  · rw [sub_self, ite_eq_left (dvd_zero _), ite_eq_left rfl]
    by_cases hend : k = 0 ∨ k = N
    · obtain ⟨hd, hk2⟩ : 2 * (N : ℤ) ∣ (k : ℤ) + k ∧ trapezoidFactor N k = 1 / 2 := by
        rcases hend with rfl | rfl
        · simp
        · exact ⟨⟨1, by ring⟩, trapezoidFactor_self k⟩
      rw [ite_eq_left hd, hk2]
      ring
    · rw [ite_eq_right (hnd (p := k + k) (by omega) (abs_lt.mpr ⟨by omega, by omega⟩)),
        trapezoidFactor_of_pos_of_lt (by omega) (by omega)]
      ring
  · rw [ite_eq_right (hnd (p := k + m) (by omega) (abs_lt.mpr ⟨by omega, by omega⟩)),
      ite_eq_right (hnd (p := k - m) (by omega) (abs_sub_lt_iff.mpr ⟨by omega, by omega⟩)),
      ite_eq_right hkm]
    ring

/-- The weights of the interpolatory cosine rule with the nodes `x_n = n π / N`,
`n = 0, …, N`, for the moments `μ`: `w_n = (2/N) h_n ∑_{k ≤ N} h_k μ_k cos (n k π / N)`. -/
def cosineRuleWeight (N : ℕ) (μ : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 / N * trapezoidFactor N n *
    ∑ k ∈ range (N + 1), trapezoidFactor N k * μ k * Real.cos (n * (k * Real.pi / N))

/-- The cosine rule reproduces the moment `μ m` of every frequency `m ≤ N`. -/
theorem sum_cosineRuleWeight_mul_cos {N : ℕ} (hN : 0 < N) (μ : ℕ → ℝ) {m : ℕ}
    (hm : m ≤ N) :
    ∑ n ∈ range (N + 1), cosineRuleWeight N μ n * Real.cos (n * (m * Real.pi / N)) =
      μ m := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc ∑ n ∈ range (N + 1), cosineRuleWeight N μ n * Real.cos (n * (m * Real.pi / N))
      = 2 / N * ∑ k ∈ range (N + 1), μ k * (trapezoidFactor N k *
          ∑ n ∈ range (N + 1), trapezoidFactor N n *
            (Real.cos (n * (k * Real.pi / N)) * Real.cos (n * (m * Real.pi / N)))) := by
        simp only [cosineRuleWeight, mul_sum, sum_mul]
        rw [sum_comm]
        refine sum_congr rfl fun k _ ↦ sum_congr rfl fun n _ ↦ ?_
        ring
    _ = 2 / N * ∑ k ∈ range (N + 1), μ k * (if k = m then (N : ℝ) / 2 else 0) := by
        congr 1
        refine sum_congr rfl fun k hk ↦ ?_
        rw [trapezoidFactor_mul_sum_cos_mul_cos hN (Nat.lt_succ_iff.mp (mem_range.mp hk)) hm]
    _ = μ m := by
        simp only [mul_ite, mul_zero, sum_ite_eq', mem_range, Nat.lt_succ_iff.mpr hm, ite_true]
        field_simp

/-- Over the `N` points `2π j / N` of the circle, the sum of `cos (k x)` is `N` when `N`
divides `k` and zero otherwise. -/
theorem sum_range_cos_mul_two_pi {N : ℕ} (hN : 0 < N) (k : ℕ) :
    ∑ j ∈ range N, Real.cos (k * (2 * Real.pi * j / N)) = if N ∣ k then (N : ℝ) else 0 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  set g : ℕ → ℝ := fun j ↦ Real.cos (j * (((2 * k : ℕ) : ℝ) * Real.pi / N)) with hg
  have hT := sum_trapezoidFactor_mul_cos_nat hN (2 * k)
  rw [sum_range_trapezoidFactor_mul hN g, ← sum_div, sum_add_distrib] at hT
  simp only [Nat.mul_dvd_mul_iff_left two_pos] at hT
  have hgN : g N = g 0 := by
    simp only [hg, Nat.cast_zero, zero_mul, Real.cos_zero]
    rw [show (N : ℝ) * (((2 * k : ℕ) : ℝ) * Real.pi / N) = ((k : ℤ) : ℝ) * (2 * Real.pi) by
      push_cast; field_simp, Real.cos_int_mul_two_pi]
  have hfun (j : ℕ) : Real.cos (k * (2 * Real.pi * j / N)) = g j := by
    rw [hg]
    push_cast
    ring_nf
  rw [← hT, sum_congr rfl fun j _ ↦ hfun j]
  linarith [sum_range_succ g N, sum_range_succ' g N]

/-- Over the `N` points `2π j / N` of the circle, the sum of `sin (k x)` vanishes. -/
theorem sum_range_sin_mul_two_pi {N : ℕ} (k : ℕ) :
    ∑ j ∈ range N, Real.sin (k * (2 * Real.pi * j / N)) = 0 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  set f : ℕ → ℝ := fun j ↦ Real.sin (k * (2 * Real.pi * j / N)) with hf
  have hfN : f N = 0 := by
    simp only [hf]
    rw [show (k : ℝ) * (2 * Real.pi * N / N) = ((2 * k : ℕ) : ℝ) * Real.pi by
      push_cast; field_simp, Real.sin_nat_mul_pi]
  have hrefl : ∀ j ∈ range (N + 1), f (N + 1 - 1 - j) = -f j := by
    intro j hj
    simp only [hf, Nat.add_sub_cancel, Nat.cast_sub (Nat.lt_succ_iff.mp (mem_range.mp hj))]
    rw [show (k : ℝ) * (2 * Real.pi * ((N : ℝ) - j) / N) =
        ((k : ℤ) : ℝ) * (2 * Real.pi) - k * (2 * Real.pi * j / N) by
      push_cast; field_simp, Real.sin_int_mul_two_pi_sub]
  have hsum := sum_range_reflect f (N + 1)
  rw [sum_congr rfl hrefl, sum_neg_distrib, sum_range_succ, hfN, add_zero] at hsum
  linarith

end CAS.Analysis

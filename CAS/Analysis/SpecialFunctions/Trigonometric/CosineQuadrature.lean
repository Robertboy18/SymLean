/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.SpecialFunctions.Trigonometric.DiscreteOrthogonality
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

/-!
# Exact trigonometric quadrature

A cosine series `f (β) = ∑_{k ≤ D} a_k cos (2kβ)` is even about `0` and about `π/2`. On the
quarter period `[0, π/2]` the trapezoid rule with the nodes `β_j = j π / (2N)` and the
weights `(π / (2N)) h_j` integrates it exactly when `D < 2N`: the rule sees each mode
`cos (2kβ)` through the trapezoid sum of `cos (j k π / N)`, which vanishes for `0 < k < 2N`.
The weighted integral `∫_0^{π/2} f (θ) sin θ dθ` has the moments
`∫_0^{π/2} cos (2kθ) sin θ dθ = 1 / (1 - 4k²)`; on the same nodes the weights
`(2/N) h_n ∑_{k ≤ N} h_k cos (2kθ_n) / (1 - 4k²)` integrate it exactly when `D ≤ N`, by the
discrete orthogonality of the cosines.

Both rules need integrands that are even about `0` and about `π/2`. A cosine series
`∑_{k ≤ D} a_k cos (kβ)` with odd frequencies is still integrated over `[0, π/2]` exactly, with
`D ≤ N`, by the cosine rule of the moments `∫_0^{π/2} cos (kβ) dβ` on the nodes `n π / N` of
`[0, π]`, which uses the values of the series beyond `π/2`.

The sine weights are at least `1 / (2N (2N + 1))`, hence positive for `N > 0`, and they add up
to `1`. Computed from approximations of `cos (m π / (2N))` with error `ε`, they are correct to
within `2ε / N`.

## Node conventions

The quarter-period rules use the `N + 1` nodes `j π / (2N)`, `j = 0, …, N`, of `[0, π/2]`. The
cosine rule uses the `N + 1` nodes `j π / N` of `[0, π]`. A mode `cos (2kβ)` at the quarter node
`j π / (2N)` is `cos (j (k π / N))`, the form in which the discrete sums are stated.

## Main results

* `integral_cosSeries_eq_trapezoid`, `integral_cosSeries_mul_sin_eq_rule`: the two quarter-period
  rules.
* `integral_cosSeries_eq_quarterCosineRule`: odd and even frequencies on `[0, π/2]`.
* `one_div_le_quarterSinWeight`, `sum_quarterSinWeight`,
  `abs_quarterSinWeight_sub_quarterSinWeightApprox_le`: bounds and enclosures of the sine
  weights.

## References

* NIST Digital Library of Mathematical Functions, §3.5 Quadrature, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/3.5>. The Clenshaw-Curtis weights (3.5.16) on the points `cos (k π / n)`;
  with `n = 2N` and `x = cos θ`, `quarterSinWeight N` is (3.5.16) for an even integrand, folded
  onto `[0, 1]`.
* C. W. Clenshaw and A. R. Curtis, "A method for numerical integration on an automatic
  computer", *Numerische Mathematik* 2 (1960), pp. 197-205, <https://doi.org/10.1007/BF01386223>.
  The origin of the rule.
-/

@[expose] public noncomputable section

namespace CAS.Analysis

open Finset

/-! ### Moments of the cosine modes -/

/-- `∫_0^{π/2} cos (2kβ) dβ` is `π/2` for `k = 0` and zero otherwise. -/
theorem integral_cos_two_mul_nat_mul_zero_to_pi_div_two (k : ℕ) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), Real.cos (2 * k * β) =
      if k = 0 then Real.pi / 2 else 0 := by
  split_ifs with hk
  · simp [hk]
  · rw [intervalIntegral.integral_comp_mul_left Real.cos (by simpa using hk), integral_cos,
      show 2 * (k : ℝ) * (Real.pi / 2) = k * Real.pi by ring, Real.sin_nat_mul_pi]
    simp

/-- `∫_0^π cos (kx) dx` is `π` for `k = 0` and zero otherwise. -/
theorem integral_cos_nat_mul_zero_to_pi (k : ℕ) :
    ∫ x in (0 : ℝ)..Real.pi, Real.cos (k * x) = if k = 0 then Real.pi else 0 := by
  split_ifs with hk
  · simp [hk]
  · rw [intervalIntegral.integral_comp_mul_left Real.cos (by exact_mod_cast hk), integral_cos,
      Real.sin_nat_mul_pi]
    simp

/-- The moments of `sin θ dθ` on the quarter period: `∫_0^{π/2} cos (2kθ) sin θ dθ =
1 / (1 - 4k²)`. -/
theorem integral_cos_two_mul_nat_mul_mul_sin_zero_to_pi_div_two (k : ℕ) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (2 * k * θ) * Real.sin θ =
      1 / (1 - 4 * (k : ℝ) ^ 2) := by
  have h₁ : 2 * (k : ℝ) - 1 ≠ 0 := by exact_mod_cast (by omega : (2 * k - 1 : ℤ) ≠ 0)
  have h₂ : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
  have h₃ : 1 - 4 * (k : ℝ) ^ 2 ≠ 0 := by exact_mod_cast (by omega : (1 - 4 * k ^ 2 : ℤ) ≠ 0)
  have hF (θ : ℝ) : HasDerivAt
      (fun θ ↦ Real.cos ((2 * k - 1) * θ) / (2 * (2 * k - 1)) -
        Real.cos ((2 * k + 1) * θ) / (2 * (2 * k + 1)))
      (Real.cos (2 * k * θ) * Real.sin θ) θ := by
    refine ((((hasDerivAt_id' θ).const_mul _).cos.div_const _).sub
      (((hasDerivAt_id' θ).const_mul _).cos.div_const _)).congr_deriv ?_
    rw [show (2 * (k : ℝ) - 1) * θ = 2 * k * θ - θ by ring,
      show (2 * (k : ℝ) + 1) * θ = 2 * k * θ + θ by ring, Real.sin_sub, Real.sin_add]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ ↦ hF θ)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have c₁ : Real.cos ((2 * k - 1) * (Real.pi / 2)) = 0 :=
    Real.cos_eq_zero_iff.mpr ⟨k - 1, by push_cast; ring⟩
  have c₂ : Real.cos ((2 * k + 1) * (Real.pi / 2)) = 0 :=
    Real.cos_eq_zero_iff.mpr ⟨k, by push_cast; ring⟩
  simp only [c₁, c₂, mul_zero, Real.cos_zero, zero_div, sub_zero]
  rw [eq_div_iff h₃]
  field_simp
  ring

/-- The moments of `sin θ dθ` on `[0, π]`: `∫_0^π cos (kθ) sin θ dθ = (1 + (-1)^k) / (1 - k²)`.
For `k = 1` both sides vanish (the right side through division by zero). -/
theorem integral_cos_nat_mul_mul_sin_zero_to_pi (k : ℕ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.cos (k * θ) * Real.sin θ =
      (1 + (-1) ^ k) / (1 - (k : ℝ) ^ 2) := by
  rcases eq_or_ne k 1 with rfl | hk
  · simp only [Nat.cast_one, one_mul, mul_comm (Real.cos _), integral_sin_mul_cos₁]
    norm_num
  · have h₁ : (k : ℝ) - 1 ≠ 0 := by exact_mod_cast (by omega : (k - 1 : ℤ) ≠ 0)
    have h₂ : (k : ℝ) + 1 ≠ 0 := by positivity
    have h₃ : 1 - (k : ℝ) ^ 2 ≠ 0 := by
      rw [show 1 - (k : ℝ) ^ 2 = -((k - 1) * (k + 1)) by ring, neg_ne_zero]
      exact mul_ne_zero h₁ h₂
    have hF (θ : ℝ) : HasDerivAt
        (fun θ ↦ Real.cos ((k - 1) * θ) / (2 * (k - 1)) -
          Real.cos ((k + 1) * θ) / (2 * (k + 1)))
        (Real.cos (k * θ) * Real.sin θ) θ := by
      refine ((((hasDerivAt_id' θ).const_mul _).cos.div_const _).sub
        (((hasDerivAt_id' θ).const_mul _).cos.div_const _)).congr_deriv ?_
      rw [show ((k : ℝ) - 1) * θ = k * θ - θ by ring,
        show ((k : ℝ) + 1) * θ = k * θ + θ by ring, Real.sin_sub, Real.sin_add]
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ ↦ hF θ)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    have c₁ : Real.cos (((k : ℝ) - 1) * Real.pi) = -(-1) ^ k := by
      rw [sub_mul, one_mul, Real.cos_sub_pi, Real.cos_nat_mul_pi]
    have c₂ : Real.cos (((k : ℝ) + 1) * Real.pi) = -(-1) ^ k := by
      rw [add_mul, one_mul, Real.cos_add_pi, Real.cos_nat_mul_pi]
    simp only [c₁, c₂, mul_zero, Real.cos_zero]
    field_simp
    ring

/-! ### The quarter-period rules -/

/-- The weight of the node `j π / (2N)` in the trapezoid rule on `[0, π/2]` with `N`
subintervals: `π / (4N)` at the endpoints and `π / (2N)` in between. -/
def quarterTrapezoidWeight (N j : ℕ) : ℝ :=
  Real.pi / (2 * N) * trapezoidFactor N j

/-- The weight of the node `θ_n = n π / (2N)` in the rule for `∫_0^{π/2} f (θ) sin θ dθ`:
`(2/N) h_n ∑_{k ≤ N} h_k cos (2k θ_n) / (1 - 4k²)`. -/
def quarterSinWeight (N n : ℕ) : ℝ :=
  2 / N * trapezoidFactor N n * ∑ k ∈ range (N + 1),
    trapezoidFactor N k * Real.cos (2 * k * (n * Real.pi / (2 * N))) / (1 - 4 * (k : ℝ) ^ 2)

/-- The sine weights are the cosine-rule weights of the moments `1 / (1 - 4k²)`. -/
theorem quarterSinWeight_eq_cosineRuleWeight (N n : ℕ) :
    quarterSinWeight N n = cosineRuleWeight N (fun k ↦ 1 / (1 - 4 * (k : ℝ) ^ 2)) n := by
  unfold quarterSinWeight cosineRuleWeight
  congr 1
  refine sum_congr rfl fun k _ ↦ ?_
  rw [show 2 * (k : ℝ) * (n * Real.pi / (2 * N)) = n * (k * Real.pi / N) by ring]
  ring

/-- The trapezoid rule on `[0, π/2]` applied to `cos (2kβ)` for `k < 2N`. -/
theorem sum_quarterTrapezoidWeight_mul_cos {N k : ℕ} (hk : k < 2 * N) :
    ∑ j : Fin (N + 1), quarterTrapezoidWeight N j * Real.cos (2 * k * (j * Real.pi / (2 * N))) =
      if k = 0 then Real.pi / 2 else 0 := by
  have hN : 0 < N := by omega
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ quarterTrapezoidWeight N j *
    Real.cos (2 * k * (j * Real.pi / (2 * N))))]
  have h (j : ℕ) : quarterTrapezoidWeight N j * Real.cos (2 * k * (j * Real.pi / (2 * N))) =
      Real.pi / (2 * N) * (trapezoidFactor N j * Real.cos (j * (k * Real.pi / N))) := by
    rw [quarterTrapezoidWeight,
      show 2 * (k : ℝ) * (j * Real.pi / (2 * N)) = j * (k * Real.pi / N) by ring]
    ring
  rw [sum_congr rfl fun j _ ↦ h j, ← mul_sum, sum_trapezoidFactor_mul_cos_nat hN]
  rcases eq_or_ne k 0 with rfl | hk0
  · simp [field]
  · rw [ite_eq_right (fun h ↦ hk0 (Nat.eq_zero_of_dvd_of_lt h hk)), ite_eq_right hk0, mul_zero]

/-- The sine rule applied to `cos (2kθ)` for `k ≤ N` gives the moment `1 / (1 - 4k²)`. -/
theorem sum_quarterSinWeight_mul_cos {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) :
    ∑ n : Fin (N + 1), quarterSinWeight N n * Real.cos (2 * k * (n * Real.pi / (2 * N))) =
      1 / (1 - 4 * (k : ℝ) ^ 2) := by
  rw [Fin.sum_univ_eq_sum_range (fun n ↦ quarterSinWeight N n *
    Real.cos (2 * k * (n * Real.pi / (2 * N))))]
  have h (n : ℕ) : quarterSinWeight N n * Real.cos (2 * k * (n * Real.pi / (2 * N))) =
      cosineRuleWeight N (fun k ↦ 1 / (1 - 4 * (k : ℝ) ^ 2)) n *
        Real.cos (n * (k * Real.pi / N)) := by
    rw [quarterSinWeight_eq_cosineRuleWeight,
      show 2 * (k : ℝ) * (n * Real.pi / (2 * N)) = n * (k * Real.pi / N) by ring]
  rw [sum_congr rfl fun n _ ↦ h n,
    sum_cosineRuleWeight_mul_cos hN (fun k ↦ 1 / (1 - 4 * (k : ℝ) ^ 2)) hk]

/-- The trapezoid rule on `[0, π/2]` with `N` subintervals integrates every cosine series
`∑_{k ≤ D} a_k cos (2kβ)` with `D < 2N` exactly. -/
theorem integral_cosSeries_eq_trapezoid {D N : ℕ} (hDN : D < 2 * N) (a : Fin (D + 1) → ℝ) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), ∑ k, a k * Real.cos (2 * k * β) =
      ∑ j : Fin (N + 1), quarterTrapezoidWeight N j *
        ∑ k, a k * Real.cos (2 * k * (j * Real.pi / (2 * N))) := by
  rw [intervalIntegral.integral_finsetSum fun k _ ↦
    Continuous.intervalIntegrable (by fun_prop) _ _]
  simp only [intervalIntegral.integral_const_mul,
    integral_cos_two_mul_nat_mul_zero_to_pi_div_two, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← sum_quarterTrapezoidWeight_mul_cos (N := N) (k := k) (by omega), mul_sum]
  exact sum_congr rfl fun j _ ↦ by ring

/-- The sine rule on `[0, π/2]` with the nodes `n π / (2N)` integrates
`(∑_{k ≤ D} a_k cos (2kθ)) sin θ` exactly when `D ≤ N`. The hypothesis `0 < N` is needed: for
`N = 0` the factor `2 / N` of the weight is `0` in Lean, so the rule gives `0`, while the
integral of `a_0 sin θ` is `a_0`. -/
theorem integral_cosSeries_mul_sin_eq_rule {D N : ℕ} (hN : 0 < N) (hDN : D ≤ N)
    (a : Fin (D + 1) → ℝ) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2), (∑ k, a k * Real.cos (2 * k * θ)) * Real.sin θ =
      ∑ n : Fin (N + 1), quarterSinWeight N n *
        ∑ k, a k * Real.cos (2 * k * (n * Real.pi / (2 * N))) := by
  simp only [sum_mul]
  rw [intervalIntegral.integral_finsetSum fun k _ ↦
    Continuous.intervalIntegrable (by fun_prop) _ _]
  simp only [mul_assoc (a _), intervalIntegral.integral_const_mul,
    integral_cos_two_mul_nat_mul_mul_sin_zero_to_pi_div_two, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← sum_quarterSinWeight_mul_cos hN (k := k) (by omega), mul_sum]
  exact sum_congr rfl fun n _ ↦ by ring

/-- The moment `∫_0^{π/2} cos (kx) dx`: `π/2` for `k = 0` and `sin (kπ/2) / k` otherwise. -/
def quarterCosineMoment (k : ℕ) : ℝ :=
  if k = 0 then Real.pi / 2 else Real.sin (k * Real.pi / 2) / k

/-- For every natural `k`, `∫_0^{π/2} cos (k x) dx = quarterCosineMoment k`, that is `π/2` for
`k = 0` and `sin (k π / 2) / k` otherwise. -/
theorem integral_cos_nat_mul_zero_to_pi_div_two (k : ℕ) :
    ∫ x in (0 : ℝ)..(Real.pi / 2), Real.cos (k * x) = quarterCosineMoment k := by
  unfold quarterCosineMoment
  split_ifs with hk
  · subst hk
    simp
  · have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    rw [intervalIntegral.integral_comp_mul_left Real.cos hk', integral_cos,
      show (k : ℝ) * (Real.pi / 2) = k * Real.pi / 2 by ring]
    simp only [mul_zero, Real.sin_zero, sub_zero, smul_eq_mul]
    field_simp

/-- The weight of the node `n π / N`, `n = 0, …, N`, in the rule for `∫_0^{π/2} f (β) dβ`: the
cosine rule of the moments `quarterCosineMoment`. -/
def quarterCosineWeight (N n : ℕ) : ℝ :=
  cosineRuleWeight N quarterCosineMoment n

/-- A cosine series `∑_{k ≤ D} a_k cos (kβ)` of any parity is integrated over `[0, π/2]` exactly
by its values at the nodes `n π / N` of `[0, π]` when `D ≤ N` and `0 < N`. -/
theorem integral_cosSeries_eq_quarterCosineRule {D N : ℕ} (hN : 0 < N) (hDN : D ≤ N)
    (a : Fin (D + 1) → ℝ) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), ∑ k, a k * Real.cos (k * β) =
      ∑ n : Fin (N + 1), quarterCosineWeight N n *
        ∑ k, a k * Real.cos (k * (n * Real.pi / N)) := by
  rw [intervalIntegral.integral_finsetSum fun k _ ↦
    Continuous.intervalIntegrable (by fun_prop) _ _]
  simp only [intervalIntegral.integral_const_mul, integral_cos_nat_mul_zero_to_pi_div_two,
    mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [Fin.sum_univ_eq_sum_range (fun n ↦ quarterCosineWeight N n *
    (a k * Real.cos ((k : ℕ) * (n * Real.pi / N)))),
    ← sum_cosineRuleWeight_mul_cos hN quarterCosineMoment (m := k) (by omega), mul_sum]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [quarterCosineWeight,
    show ((k : ℕ) : ℝ) * (n * Real.pi / N) = n * ((k : ℕ) * Real.pi / N) by ring]
  ring

/-- The trapezoid weights on `[0, π/2]` add up to `π/2`. -/
theorem sum_quarterTrapezoidWeight {N : ℕ} (hN : 0 < N) :
    ∑ j : Fin (N + 1), quarterTrapezoidWeight N j = Real.pi / 2 := by
  have h := sum_quarterTrapezoidWeight_mul_cos (N := N) (k := 0) (by omega)
  simpa only [Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one, ite_true] using h

/-- For `0 < N`, every trapezoid weight `quarterTrapezoidWeight N j` on `[0, π/2]` is positive (for
every `j`, inside or outside `0, …, N`). -/
theorem quarterTrapezoidWeight_pos {N : ℕ} (hN : 0 < N) (j : ℕ) :
    0 < quarterTrapezoidWeight N j := by
  have : (0 : ℝ) < N := by exact_mod_cast hN
  exact mul_pos (by positivity) (trapezoidFactor_pos N j)

/-- The sine weights add up to `∫_0^{π/2} sin θ dθ = 1`. -/
theorem sum_quarterSinWeight {N : ℕ} (hN : 0 < N) :
    ∑ n : Fin (N + 1), quarterSinWeight N n = 1 := by
  have h := sum_quarterSinWeight_mul_cos hN (Nat.zero_le N)
  simpa only [Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, div_one] using h

/-- `∑_{k < N} 1 / (4 (k + 1)² - 1) = N / (2N + 1)`, a telescoping sum. -/
theorem sum_range_one_div_four_mul_sq_sub_one (N : ℕ) :
    ∑ k ∈ range N, 1 / (4 * ((k : ℝ) + 1) ^ 2 - 1) = (N : ℝ) / (2 * N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    have : 4 * ((N : ℝ) + 1) ^ 2 - 1 ≠ 0 := by nlinarith [N.cast_nonneg (α := ℝ)]
    push_cast
    field_simp
    ring

/-- The terms `k ≥ 1` of a trapezoid-weighted series against the moments `1 / (1 - 4k²)`, with
values bounded by `B`, sum to at most `B N / (2N + 1)` in absolute value. -/
theorem abs_sum_trapezoidFactor_mul_div_le (N : ℕ) (g : ℕ → ℝ) {B : ℝ}
    (hg : ∀ k, |g k| ≤ B) :
    |∑ k ∈ range N, trapezoidFactor N (k + 1) * g (k + 1) /
        (1 - 4 * ((k + 1 : ℕ) : ℝ) ^ 2)| ≤ B * ((N : ℝ) / (2 * N + 1)) := by
  rw [← sum_range_one_div_four_mul_sq_sub_one, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ ↦ ?_)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hpos : 0 < 4 * ((k : ℝ) + 1) ^ 2 - 1 := by nlinarith
  rw [show 1 - 4 * ((k + 1 : ℕ) : ℝ) ^ 2 = -(4 * ((k : ℝ) + 1) ^ 2 - 1) by push_cast; ring,
    div_neg, abs_neg, abs_div, abs_mul, abs_of_pos hpos, abs_of_pos (trapezoidFactor_pos _ _),
    mul_one_div]
  refine div_le_div_of_nonneg_right ?_ hpos.le
  exact (mul_le_mul (trapezoidFactor_le_one _ _) (hg _) (abs_nonneg _) zero_le_one).trans_eq
    (one_mul B)

/-- The constant mode contributes `h_0 g_0 = g_0 / 2` to a trapezoid-weighted series against
the moments `1 / (1 - 4k²)`. -/
theorem sum_trapezoidFactor_mul_div_eq (N : ℕ) (g : ℕ → ℝ) :
    ∑ k ∈ range (N + 1), trapezoidFactor N k * g k / (1 - 4 * (k : ℝ) ^ 2) =
      g 0 / 2 + ∑ k ∈ range N, trapezoidFactor N (k + 1) * g (k + 1) /
        (1 - 4 * ((k + 1 : ℕ) : ℝ) ^ 2) := by
  rw [sum_range_succ', add_comm, trapezoidFactor_zero]
  simp only [Nat.cast_zero]
  ring

/-- The inner sum of a sine weight lies between `1 / (2 (2N + 1))` and `1`. -/
theorem quarterSinWeight_inner_mem (N n : ℕ) :
    ∑ k ∈ range (N + 1), trapezoidFactor N k *
        Real.cos (2 * k * (n * Real.pi / (2 * N))) / (1 - 4 * (k : ℝ) ^ 2) ∈
      Set.Icc ((1 : ℝ) / (2 * (2 * N + 1))) 1 := by
  rw [Set.mem_Icc,
    sum_trapezoidFactor_mul_div_eq N (fun k ↦ Real.cos (2 * k * (n * Real.pi / (2 * N))))]
  have h := abs_le.mp (abs_sum_trapezoidFactor_mul_div_le N
    (fun k ↦ Real.cos (2 * k * (n * Real.pi / (2 * N)))) (B := 1)
    (fun k ↦ Real.abs_cos_le_one _))
  simp only [Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, one_mul] at h ⊢
  have hle : (N : ℝ) / (2 * N + 1) ≤ 1 / 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hlow : 1 / (2 * (2 * (N : ℝ) + 1)) = 1 / 2 - N / (2 * N + 1) := by
    field_simp
    ring
  rw [hlow]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Every sine weight is at least `1 / (2N (2N + 1))`, hence positive when `N > 0`. -/
theorem one_div_le_quarterSinWeight (N n : ℕ) :
    (1 : ℝ) / (2 * N * (2 * N + 1)) ≤ quarterSinWeight N n := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [quarterSinWeight]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hlow, -⟩ := quarterSinWeight_inner_mem N n
  have hh := half_le_trapezoidFactor N n
  have hd : (0 : ℝ) < 2 * N + 1 := by positivity
  calc (1 : ℝ) / (2 * N * (2 * N + 1)) = 2 / N * (1 / 2) * (1 / (2 * (2 * N + 1))) := by
        field_simp
    _ ≤ quarterSinWeight N n := by
        unfold quarterSinWeight
        gcongr

/-- For `0 < N`, every sine weight `quarterSinWeight N n` is positive (for every `n`). -/
theorem quarterSinWeight_pos {N : ℕ} (hN : 0 < N) (n : ℕ) : 0 < quarterSinWeight N n := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  exact lt_of_lt_of_le (by positivity) (one_div_le_quarterSinWeight N n)

/-- A sine weight computed from approximations `c m` of `cos (m π / (2N))`; the table index of
`cos (2k θ_n)` is `2kn`. -/
def quarterSinWeightApprox (N n : ℕ) (c : ℕ → ℝ) : ℝ :=
  2 / N * trapezoidFactor N n *
    ∑ k ∈ range (N + 1), trapezoidFactor N k * c (2 * k * n) / (1 - 4 * (k : ℝ) ^ 2)

/-- If `c m` approximates `cos (m π / (2N))` to within `ε` for every `m`, the approximate sine
weight is within `2ε / N` of the sine weight. -/
theorem abs_quarterSinWeight_sub_quarterSinWeightApprox_le {N : ℕ} (hN : 0 < N) (n : ℕ)
    {c : ℕ → ℝ} {ε : ℝ} (hc : ∀ m : ℕ, |c m - Real.cos (m * Real.pi / (2 * N))| ≤ ε) :
    |quarterSinWeight N n - quarterSinWeightApprox N n c| ≤ 2 * ε / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (hc 0)
  set g : ℕ → ℝ := fun k ↦ Real.cos (2 * k * (n * Real.pi / (2 * N))) - c (2 * k * n) with hg
  have hgb : ∀ k, |g k| ≤ ε := by
    intro k
    rw [hg, abs_sub_comm]
    have h := hc (2 * k * n)
    rwa [show ((2 * k * n : ℕ) : ℝ) * Real.pi / (2 * N) = 2 * k * (n * Real.pi / (2 * N)) by
      push_cast; ring] at h
  have hdiff : quarterSinWeight N n - quarterSinWeightApprox N n c =
      2 / N * trapezoidFactor N n *
        ∑ k ∈ range (N + 1), trapezoidFactor N k * g k / (1 - 4 * (k : ℝ) ^ 2) := by
    unfold quarterSinWeight quarterSinWeightApprox
    rw [← mul_sub, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun k _ ↦ ?_
    rw [hg]
    ring
  have hsum : |∑ k ∈ range (N + 1), trapezoidFactor N k * g k / (1 - 4 * (k : ℝ) ^ 2)| ≤ ε := by
    rw [sum_trapezoidFactor_mul_div_eq]
    have hle : (N : ℝ) / (2 * N + 1) ≤ 1 / 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    have h₁ := abs_le.mp ((abs_sum_trapezoidFactor_mul_div_le N g hgb).trans
      (mul_le_mul_of_nonneg_left hle hε))
    have h₀ := abs_le.mp (hgb 0)
    exact abs_le.mpr ⟨by linarith [h₀.1, h₁.1], by linarith [h₀.2, h₁.2]⟩
  rw [hdiff, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / N),
    abs_of_pos (trapezoidFactor_pos N n)]
  calc _ ≤ 2 / N * 1 * ε := by
        gcongr
        exact trapezoidFactor_le_one N n
    _ = 2 * ε / N := by ring

end CAS.Analysis

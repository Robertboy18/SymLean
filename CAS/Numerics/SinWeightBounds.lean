/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.SpecialFunctions.Trigonometric.CosineQuadrature
public import CAS.Numerics.PackedSlots
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Upper bounds of the sine-rule weights from stored cosines

The weight of the node `n π / (2N)` in the exact rule for `∫_0^{π/2} f(θ) sin θ dθ` is
`(2/N) h_n ∑_{k ≤ N} h_k cos (2k θ_n) / (1 - 4k²)` (`quarterSinWeight`). With the cosines
replaced by stored values `(word m - 2^63) / 2^62` of a table of `64`-bit offset words, every
term with `k ≥ 1` is `2 h_k (2^63 - word) / (2^63 (4k² - 1))`. On the grid `2^-q` with
`q ≥ 63` the approximate weight is exactly a quotient over `N 2^q` (`quarterSinWeightApprox_eq`,
with the numerator `sinWeightExact`); rounding the two parts of each term up and down bounds it
above by a natural-number computation (`sinWeightUpper`). Together with the table error this
bounds the weight (`quarterSinWeight_le_sinWeightUpper`). `quarterTrapezoidWeight_le` bounds the
trapezoid weights in the same form, from `π < 3.141593`.

## Implementation notes

The weights involve cosines that the kernel cannot evaluate, so we bound them through a stored
table whose cosines are within `2 ^ (-62)` (`TrigTableWords`). This moves each weight by at most
`2 / (N 2 ^ 62)` (`TrigTableQuadrature`), the hypothesis of
`quarterSinWeight_le_sinWeightUpper`, and the term `2 ^ (q - 61)` of `sinWeightUpper` covers it.
Each term with `k ≥ 1` splits into a positive part, rounded up with the ceiling
`(a + d - 1) / d`, and a negative part, rounded down; the term `k = 0` is exact. The bound is
then a quotient of natural-number sums (`natSum`) by `N 2 ^ q`, where `q ≥ 63` makes the scale
`2 ^ (q - 63)` of the words a natural number. A proof evaluates `sinWeightUpper` in the kernel
and needs nothing else per node: the outward rounding and the table error are accounted for
once, in `quarterSinWeight_le_sinWeightUpper`. `SinWeightLowerBounds` rounds the other way, from
the same identity `quarterSinWeightApprox_eq`.
-/

@[expose] public section

namespace CAS.Numerics

open CAS.Analysis Finset

/-- Twice the trapezoid factor, `1` at the end nodes and `2` inside. -/
def trapezoidDouble (N k : ℕ) : ℕ := cond (Nat.beq k 0 || Nat.beq k N) 1 2

/-- `trapezoidDouble N k` is twice the trapezoid factor `trapezoidFactor N k`, as a real number. -/
theorem trapezoidDouble_eq (N k : ℕ) : (trapezoidDouble N k : ℝ) = 2 * trapezoidFactor N k := by
  unfold trapezoidDouble trapezoidFactor
  by_cases h0 : k = 0
  · simp [h0]
  · by_cases h1 : k = N
    · simp [h1]
    · simp [Bool.eq_false_iff.mpr fun e ↦ h0 (Nat.eq_of_beq_eq_true e),
        Bool.eq_false_iff.mpr fun e ↦ h1 (Nat.eq_of_beq_eq_true e), h0, h1]

/-- The rounded-up part of the weight sum, the same at every node: the term
`trapezoidDouble N 0 * word 0 * 2 ^ (q - 63)` plus, for `i < N`, the ceiling of
`trapezoidDouble N (i + 1) * 2 ^ q / (4 * (i + 1) ^ 2 - 1)`, a natural division after adding
the denominator minus one. -/
def sinWeightPos (N q : ℕ) (word : ℕ → ℕ) : ℕ :=
  trapezoidDouble N 0 * word 0 * 2 ^ (q - 63) +
    natSum N fun i ↦ (trapezoidDouble N (i + 1) * 2 ^ q + (4 * (i + 1) ^ 2 - 1) - 1) /
      (4 * (i + 1) ^ 2 - 1)

/-- The rounded-down part of the weight sum at node `n`. -/
def sinWeightNeg (N q : ℕ) (word : ℕ → ℕ) (n : ℕ) : ℕ :=
  trapezoidDouble N 0 * 2 ^ q +
    natSum N fun i ↦ trapezoidDouble N (i + 1) * word (2 * (i + 1) * n) * 2 ^ (q - 63) /
      (4 * (i + 1) ^ 2 - 1)

/-- The numerator of the weight bound at node `n` over `N 2^q`; the last term covers the table
error. -/
def sinWeightUpper (N q : ℕ) (word : ℕ → ℕ) (n : ℕ) : ℕ :=
  trapezoidDouble N n * (sinWeightPos N q word - sinWeightNeg N q word n) + 2 ^ (q - 61)

/-- `a / d ≤ ⌈a / d⌉` with the ceiling computed as `(a + d - 1) / d` in `ℕ`. -/
theorem le_natCast_ceilDiv (a d : ℕ) (hd : 0 < d) :
    (a : ℝ) / d ≤ (((a + d - 1) / d : ℕ) : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  have := Nat.lt_div_mul_add (a := a + d - 1) hd
  exact_mod_cast (by omega : a ≤ (a + d - 1) / d * d)

/-- The numerator of `quarterSinWeightApprox` over `N 2^q`, before rounding: the term `k = 0` and,
for `k = i + 1 ≤ N`, the difference of the two quotients that `sinWeightPos` rounds up and
`sinWeightNeg` rounds down. -/
noncomputable def sinWeightExact (N q : ℕ) (word : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((trapezoidDouble N 0 * word 0 * 2 ^ (q - 63) : ℕ) : ℝ) -
      ((trapezoidDouble N 0 * 2 ^ q : ℕ) : ℝ) +
    ∑ i ∈ range N, ((((trapezoidDouble N (i + 1) * 2 ^ q : ℕ) : ℝ) -
      ((trapezoidDouble N (i + 1) * word (2 * (i + 1) * n) * 2 ^ (q - 63) : ℕ) : ℝ)) /
        ((4 * (i + 1) ^ 2 - 1 : ℕ) : ℝ))

/-- For `0 < N` and `63 ≤ q`, the approximate sine weight with cosines
`(word m - 2^63) / 2^62` is exactly `trapezoidDouble N n * sinWeightExact N q word n / (N 2^q)`,
for every word table and node. -/
theorem quarterSinWeightApprox_eq {N q : ℕ} (hN : 0 < N) (hq : 63 ≤ q) (word : ℕ → ℕ) (n : ℕ) :
    quarterSinWeightApprox N n (fun m ↦ ((word m : ℝ) - 2 ^ 63) / 2 ^ 62) =
      trapezoidDouble N n * sinWeightExact N q word n / (N * 2 ^ q) := by
  have hq' : (2 : ℝ) ^ q = 2 ^ 63 * 2 ^ (q - 63) := by rw [← pow_add, Nat.add_sub_cancel' hq]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h0 : trapezoidFactor N 0 * (((word (2 * 0 * n) : ℝ) - 2 ^ 63) / 2 ^ 62) /
      (1 - 4 * ((0 : ℕ) : ℝ) ^ 2) = (((trapezoidDouble N 0 * word 0 * 2 ^ (q - 63) : ℕ) : ℝ) -
        ((trapezoidDouble N 0 * 2 ^ q : ℕ) : ℝ)) / 2 ^ q := by
    push_cast
    simp only [trapezoidDouble_eq, zero_mul]
    rw [hq']
    field_simp
    ring
  have hk : ∀ i ∈ range N, trapezoidFactor N (i + 1) *
      (((word (2 * (i + 1) * n) : ℝ) - 2 ^ 63) / 2 ^ 62) / (1 - 4 * ((i + 1 : ℕ) : ℝ) ^ 2) =
      ((((trapezoidDouble N (i + 1) * 2 ^ q : ℕ) : ℝ) -
        ((trapezoidDouble N (i + 1) * word (2 * (i + 1) * n) * 2 ^ (q - 63) : ℕ) : ℝ)) /
          ((4 * (i + 1) ^ 2 - 1 : ℕ) : ℝ)) / 2 ^ q := fun i _ ↦ by
    have hd : 1 ≤ 4 * (i + 1) ^ 2 := Nat.succ_le_of_lt (by positivity)
    have hdr : ((4 * (i + 1) ^ 2 - 1 : ℕ) : ℝ) = 4 * ((i : ℝ) + 1) ^ 2 - 1 := by
      rw [Nat.cast_sub hd]
      push_cast
      ring
    have hi1 : (1 : ℝ) ≤ (i : ℝ) + 1 := by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    have hdpos : (0 : ℝ) < 4 * ((i : ℝ) + 1) ^ 2 - 1 := by nlinarith
    have : (1 : ℝ) - 4 * ((i : ℝ) + 1) ^ 2 ≠ 0 := by linarith
    rw [hdr]
    push_cast
    rw [trapezoidDouble_eq, hq']
    field_simp
    ring
  rw [quarterSinWeightApprox, sum_range_succ', sum_congr rfl hk, h0, ← sum_div, sinWeightExact,
    trapezoidDouble_eq N n]
  field_simp
  ring

/-- The approximate sine weight with cosines `(word m - 2^63) / 2^62` is at most the
natural-number bound over `N 2^q` (before the table error term). -/
theorem quarterSinWeightApprox_le (N q : ℕ) (hN : 0 < N) (hq : 63 ≤ q) (word : ℕ → ℕ) (n : ℕ) :
    quarterSinWeightApprox N n (fun m ↦ ((word m : ℝ) - 2 ^ 63) / 2 ^ 62) ≤
      (trapezoidDouble N n : ℝ) * ((sinWeightPos N q word : ℝ) - sinWeightNeg N q word n) /
        (N * 2 ^ q) := by
  rw [quarterSinWeightApprox_eq hN hq]
  have hd (i : ℕ) : 0 < 4 * (i + 1) ^ 2 - 1 := by
    have : 0 < (i + 1) ^ 2 := by positivity
    omega
  have h1 := sum_le_sum fun i (_ : i ∈ range N) ↦
    le_natCast_ceilDiv (trapezoidDouble N (i + 1) * 2 ^ q) _ (hd i)
  have h2 := sum_le_sum fun i (_ : i ∈ range N) ↦ (Nat.cast_div_le (α := ℝ)
    (m := trapezoidDouble N (i + 1) * word (2 * (i + 1) * n) * 2 ^ (q - 63))
    (n := 4 * (i + 1) ^ 2 - 1))
  gcongr
  simp only [sinWeightExact, sinWeightPos, sinWeightNeg, natSum_eq_sum, Nat.cast_add,
    Nat.cast_sum, sub_div, sum_sub_distrib]
  linarith

/-- The sine weights are at most `sinWeightUpper / (N 2^q)` when the stored cosines are
within `2^-62` of the exact ones. -/
theorem quarterSinWeight_le_sinWeightUpper (N q : ℕ) (hN : 0 < N) (hq : 63 ≤ q)
    (word : ℕ → ℕ) (n : ℕ)
    (h : |quarterSinWeight N n -
      quarterSinWeightApprox N n (fun m ↦ ((word m : ℝ) - 2 ^ 63) / 2 ^ 62)| ≤
        2 / (N * 2 ^ 62)) :
    quarterSinWeight N n ≤ (sinWeightUpper N q word n : ℝ) / (N * 2 ^ q) := by
  have h1 := quarterSinWeightApprox_le N q hN hq word n
  have h2 := (abs_le.mp h).2
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsub : (sinWeightPos N q word : ℝ) - sinWeightNeg N q word n ≤
      ((sinWeightPos N q word - sinWeightNeg N q word n : ℕ) : ℝ) := by
    rcases le_total (sinWeightNeg N q word n) (sinWeightPos N q word) with hle | hle
    · rw [Nat.cast_sub hle]
    · rw [Nat.sub_eq_zero_of_le hle, Nat.cast_zero]
      exact sub_nonpos.mpr (by exact_mod_cast hle)
  have hq'' : (2 : ℝ) ^ q = 2 ^ 61 * 2 ^ (q - 61) := by
    rw [← pow_add, Nat.add_sub_cancel' (by omega)]
  calc quarterSinWeight N n ≤ (trapezoidDouble N n : ℝ) * ((sinWeightPos N q word : ℝ) -
        sinWeightNeg N q word n) / (N * 2 ^ q) + 2 / (N * 2 ^ 62) := by linarith
    _ ≤ (trapezoidDouble N n : ℝ) * ((sinWeightPos N q word - sinWeightNeg N q word n : ℕ) :
        ℝ) / (N * 2 ^ q) + 2 / (N * 2 ^ 62) := by gcongr
    _ = _ := by
      rw [sinWeightUpper]
      push_cast
      rw [hq'']
      field_simp

/-- The trapezoid weights with `π < 3.141593`. -/
theorem quarterTrapezoidWeight_le (N j : ℕ) (hN : 0 < N) :
    quarterTrapezoidWeight N j ≤ 3141593 * (trapezoidDouble N j : ℝ) / (4000000 * N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 ≤ trapezoidFactor N j := by unfold trapezoidFactor; split_ifs <;> norm_num
  rw [quarterTrapezoidWeight, trapezoidDouble_eq,
    show 3141593 * (2 * trapezoidFactor N j) / (4000000 * (N : ℝ)) =
      3.141593 / (2 * N) * trapezoidFactor N j by field_simp; ring]
  gcongr
  exact Real.pi_lt_d6.le

end CAS.Numerics

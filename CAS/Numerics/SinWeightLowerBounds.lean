/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.SinWeightBounds

/-!
# Lower bounds of the sine-rule weights from stored cosines

The counterpart of `SinWeightBounds`: rounding the positive part of every term of
`quarterSinWeightApprox` down and the negative part up bounds the weight below by a
natural-number computation over `N 2^q` (`sinWeightLower`), less the table error
(`le_quarterSinWeight_of_sinWeightLower`).

## Implementation notes

Both bounds are corollaries of the exact identity `quarterSinWeightApprox_eq` of
`SinWeightBounds`, with the roundings reversed here, and the kernel again evaluates only the
natural-number sums. The one difference is the subtraction: natural subtraction truncates at
`0`, which is harmless in an upper bound but not in a lower one. We therefore require
`0 < sinWeightLower`, which shows that neither subtraction in `sinWeightLower` truncated.
-/

@[expose] public section

namespace CAS.Numerics

open CAS.Analysis Finset

/-- The rounded-down positive part of the weight sum. -/
def sinWeightPosLow (N q : ℕ) (word : ℕ → ℕ) : ℕ :=
  trapezoidDouble N 0 * word 0 * 2 ^ (q - 63) +
    natSum N fun i ↦ trapezoidDouble N (i + 1) * 2 ^ q / (4 * (i + 1) ^ 2 - 1)

/-- The rounded-up negative part of the weight sum at node `n`. -/
def sinWeightNegHigh (N q : ℕ) (word : ℕ → ℕ) (n : ℕ) : ℕ :=
  trapezoidDouble N 0 * 2 ^ q +
    natSum N fun i ↦ (trapezoidDouble N (i + 1) * word (2 * (i + 1) * n) * 2 ^ (q - 63) +
      (4 * (i + 1) ^ 2 - 1) - 1) / (4 * (i + 1) ^ 2 - 1)

/-- The numerator of the lower bound at node `n` over `N 2^q`, less the table error (truncated at
`0`). -/
def sinWeightLower (N q : ℕ) (word : ℕ → ℕ) (n : ℕ) : ℕ :=
  trapezoidDouble N n * (sinWeightPosLow N q word - sinWeightNegHigh N q word n) - 2 ^ (q - 61)


/-- The approximate sine weight with cosines `(word m - 2^63) / 2^62` is at least the
natural-number bound over `N 2^q` (before the table error term). -/
theorem le_quarterSinWeightApprox (N q : ℕ) (hN : 0 < N) (hq : 63 ≤ q) (word : ℕ → ℕ) (n : ℕ) :
    (trapezoidDouble N n : ℝ) * ((sinWeightPosLow N q word : ℝ) - sinWeightNegHigh N q word n) /
        (N * 2 ^ q) ≤
      quarterSinWeightApprox N n (fun m ↦ ((word m : ℝ) - 2 ^ 63) / 2 ^ 62) := by
  rw [quarterSinWeightApprox_eq hN hq]
  have hd (i : ℕ) : 0 < 4 * (i + 1) ^ 2 - 1 := by
    have : 0 < (i + 1) ^ 2 := by positivity
    omega
  have h1 := sum_le_sum fun i (_ : i ∈ range N) ↦ (Nat.cast_div_le (α := ℝ)
    (m := trapezoidDouble N (i + 1) * 2 ^ q) (n := 4 * (i + 1) ^ 2 - 1))
  have h2 := sum_le_sum fun i (_ : i ∈ range N) ↦
    le_natCast_ceilDiv (trapezoidDouble N (i + 1) * word (2 * (i + 1) * n) * 2 ^ (q - 63)) _
      (hd i)
  gcongr
  simp only [sinWeightExact, sinWeightPosLow, sinWeightNegHigh, natSum_eq_sum, Nat.cast_add,
    Nat.cast_sum, sub_div, sum_sub_distrib]
  linarith

/-- **Lower bound of a sine weight.** When the stored cosines are within `2^-62` of the exact
ones, every weight is at least `sinWeightLower / (N 2^q)`. -/
theorem le_quarterSinWeight_of_sinWeightLower (N q : ℕ) (hN : 0 < N) (hq : 63 ≤ q)
    (word : ℕ → ℕ) (n : ℕ)
    (h : |quarterSinWeight N n -
      quarterSinWeightApprox N n (fun m ↦ ((word m : ℝ) - 2 ^ 63) / 2 ^ 62)| ≤
        2 / (N * 2 ^ 62)) (hpos : 0 < sinWeightLower N q word n) :
    (sinWeightLower N q word n : ℝ) / (N * 2 ^ q) ≤ quarterSinWeight N n := by
  have h1 := le_quarterSinWeightApprox N q hN hq word n
  have h2 := (abs_le.mp h).1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hq'' : (2 : ℝ) ^ q = 2 ^ 61 * 2 ^ (q - 61) := by
    rw [← pow_add, Nat.add_sub_cancel' (by omega)]
  unfold sinWeightLower at hpos ⊢
  have hle : sinWeightNegHigh N q word n ≤ sinWeightPosLow N q word := by
    by_contra hc
    rw [show sinWeightPosLow N q word - sinWeightNegHigh N q word n = 0 by omega] at hpos
    simp at hpos
  rw [Nat.cast_sub (Nat.sub_pos_iff_lt.1 hpos).le, Nat.cast_mul, Nat.cast_sub hle]
  calc _ = (trapezoidDouble N n : ℝ) * ((sinWeightPosLow N q word : ℝ) -
        sinWeightNegHigh N q word n) / (N * 2 ^ q) - 2 / (N * 2 ^ 62) := by
        push_cast
        rw [hq'']
        field_simp
    _ ≤ _ := by linarith

end CAS.Numerics

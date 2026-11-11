/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.Polynomial
public import CAS.Numerics.PackedSlots
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic

/-!
# Balanced sums of certified integer bounds

`CoefficientTree.sumMap a f offset` adds `f (offset + i) (lookup i)` over the leaves of a
coefficient tree in one pass, and `CoefficientTree.sumMap_eq_sum_lookup` identifies it with the
finite sum over `i < 2 ^ depth`. The plain sum of the leaves is `pack 1`
(`CoefficientTree.sum_lookup`). `CoefficientTree.sum_le_sumMap` turns row bounds
`f i ≤ upper i (lookup i) / denom` for `i < n ≤ 2 ^ depth` into
`∑ i, f i ≤ sumMap upper 0 / denom`; the padding rows past `n` add natural numbers, so they can
only raise the bound.

## Implementation notes

`CoefficientTree.sumMap` walks the tree as `CoefficientTree.check` of [Polynomial](Polynomial.lean)
does, with an addition in place of the conjunction: one call of `f` per leaf and one addition of the
two halves per inner node, where reading the leaves through `CoefficientTree.lookup` would descend
`depth` branches for each of them. A caller proves the natural-number bound `a.sumMap upper 0 ≤ N`
for a concrete tree as one closed statement by evaluation, and `CoefficientTree.sum_le_sumMap`
turns it into the bound on the real sum when `0 ≤ denom`. The
theorems hold for all trees: `CoefficientTree.sumMap_eq_sum_lookup` and `CoefficientTree.sum_lookup`
by induction on the tree, and `CoefficientTree.sum_le_sumMap` from the first. No module of SymLean
imports this one; it serves certificates built on the library.
-/

@[expose] public section

namespace CAS.Numerics

/-- Packing a natural coefficient table at base one is its exact coefficient sum. -/
theorem CoefficientTree.sum_lookup {depth : ℕ} (a : CoefficientTree depth) :
    (∑ i ∈ Finset.range (2 ^ depth), a.lookup i) = a.pack 1 := by
  induction a with
  | leaf value => simp [lookup, pack]
  | @branch depth left right ihl ihr =>
    rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
    have hl :
        (∑ i ∈ Finset.range (2 ^ depth), (branch left right).lookup i) =
          ∑ i ∈ Finset.range (2 ^ depth), left.lookup i := Finset.sum_congr rfl fun i hi ↦ by
      simp only [lookup, Finset.mem_range.mp hi, ↓reduceIte]
    have hr :
        (∑ i ∈ Finset.range (2 ^ depth), (branch left right).lookup (2 ^ depth + i)) =
          ∑ i ∈ Finset.range (2 ^ depth), right.lookup i := Finset.sum_congr rfl fun i _ ↦ by
      simp only [lookup, Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte,
        Nat.add_sub_cancel_left]
    rw [hl, hr, ihl, ihr]
    simp only [pack, one_pow, one_mul]

/-- Sum an indexed function over a coefficient tree without a linear lookup traversal. -/
def CoefficientTree.sumMap {depth : ℕ} (a : CoefficientTree depth)
    (f : ℕ → ℕ → ℕ) (offset : ℕ) : ℕ :=
  match a with
  | .leaf value => f offset value
  | @CoefficientTree.branch n left right =>
    left.sumMap f offset + right.sumMap f (offset + 2 ^ n)

/-- Balanced evaluation agrees with the ordinary finite sum at the same addresses. -/
theorem CoefficientTree.sumMap_eq_sum_lookup {depth : ℕ} (a : CoefficientTree depth)
    (f : ℕ → ℕ → ℕ) (offset : ℕ) :
    a.sumMap f offset =
      ∑ i ∈ Finset.range (2 ^ depth), f (offset + i) (a.lookup i) := by
  induction a generalizing offset with
  | leaf value => simp [sumMap, lookup]
  | @branch depth left right ihl ihr =>
    rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
    simp only [sumMap, ihl, ihr]
    congr 1
    · exact Finset.sum_congr rfl fun i hi ↦ by
        simp only [lookup, Finset.mem_range.mp hi, ↓reduceIte]
    · exact Finset.sum_congr rfl fun i _ ↦ by simp only [lookup,
        Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte, Nat.add_sub_cancel_left, Nat.add_assoc]

/-- A balanced integer sum bounds any finite collection of real row values.
Padding rows are harmless because their proposed upper bounds are natural numbers. -/
theorem CoefficientTree.sum_le_sumMap {depth n : ℕ} (a : CoefficientTree depth)
    (hn : n ≤ 2 ^ depth) (f : Fin n → ℝ) (upper : ℕ → ℕ → ℕ) (denom : ℝ)
    (hdenom : 0 ≤ denom)
    (hrow : ∀ i : Fin n, f i ≤ (upper i.val (a.lookup i.val) : ℝ) / denom) :
    (∑ i : Fin n, f i) ≤ (a.sumMap upper 0 : ℝ) / denom := by
  have hsum : (∑ i : Fin n, upper i.val (a.lookup i.val)) ≤ a.sumMap upper 0 := by
    rw [a.sumMap_eq_sum_lookup,
      Fin.sum_univ_eq_sum_range (fun i ↦ upper i (a.lookup i))]
    simp only [zero_add]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
      (by intros; exact Nat.zero_le _)
  calc
    _ ≤ ∑ i : Fin n, (upper i.val (a.lookup i.val) : ℝ) / denom :=
      Finset.sum_le_sum fun i _ ↦ hrow i
    _ = (∑ i : Fin n, upper i.val (a.lookup i.val) : ℕ) / denom := by
      simp only [Nat.cast_sum, Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right (Nat.cast_le.mpr hsum) hdenom

end CAS.Numerics

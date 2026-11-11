/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedLinearAlgebra
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# Weighted sums of absolute coefficients from packed rows

`weightedAbsSum M L w row wβ wθ = Σ_{m<M} wβ m Σ_{l<L} |x m l| wθ l` for the signed slots
`x m l` of width `w` of the rows `row m`, as a natural number (`weightedAbsSum_eq`). When the
coefficients are the slots over `2^p` and the weights natural numbers over `1` and `2^d`, the
weighted sum of the absolute coefficients is the computed sum over `2^(p + d)`
(`sum_abs_mul_eq_weightedAbsSum`), the form of the `ℓ¹` bounds of separable tables.

## Implementation notes

`weightedAbsSum` is two nested `natSum` loops, the `Nat.rec` sums of
[PackedSlots](PackedSlots.lean), with `Nat.mul` for the weights. It reads `|x m l|` as
`slotAbs w l (row m)` of [PackedLinearAlgebra](PackedLinearAlgebra.lean), the sum of the two
truncated differences of the slot and its bias, one of which is zero, so no integer is formed.
`weightedAbsSum_eq` holds for all rows, by `natSum_eq_sum` and `cast_slotAbs`, and
`sum_abs_mul_eq_weightedAbsSum` follows term by term with `abs_div`, `pow_add` and `field_simp`;
a bound on the real weighted sum thus comes down to one natural number computed from the data
rows and the weights. No module of SymLean imports this one; it serves certificates built on the
library.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- `Σ_{m<M} wβ m Σ_{l<L} |signedSlot w l (row m)| wθ l` in natural numbers. -/
def weightedAbsSum (M L w : ℕ) (row wβ wθ : ℕ → ℕ) : ℕ :=
  natSum M fun m ↦ Nat.mul (wβ m) (natSum L fun l ↦ Nat.mul (slotAbs w l (row m)) (wθ l))

/-- For all rows and weights, `weightedAbsSum M L w row wβ wθ` is the real double sum of
`|signedSlot w l (row m)| * (wβ m * wθ l)` over `m < M` and `l < L`. -/
theorem weightedAbsSum_eq (M L w : ℕ) (row wβ wθ : ℕ → ℕ) :
    (weightedAbsSum M L w row wβ wθ : ℝ) =
      ∑ m ∈ range M, ∑ l ∈ range L, |(signedSlot w l (row m) : ℝ)| * ((wβ m : ℝ) * wθ l) := by
  rw [weightedAbsSum, natSum_eq_sum]
  push_cast
  refine sum_congr rfl fun m _ ↦ ?_
  rw [Nat.mul_eq, Nat.cast_mul, natSum_eq_sum, Nat.cast_sum, mul_sum]
  refine sum_congr rfl fun l _ ↦ ?_
  rw [Nat.mul_eq, Nat.cast_mul]
  rw [show ((slotAbs w l (row m) : ℕ) : ℝ) = |((signedSlot w l (row m) : ℤ) : ℝ)| by
    exact_mod_cast cast_slotAbs w l (row m)]
  ring

/-- The weighted sum of absolute coefficients given by slots over `2 ^ p`, with weights `wβ m`
and `wθ l / 2 ^ d`. -/
theorem sum_abs_mul_eq_weightedAbsSum {M L w p d : ℕ} (row : ℕ → ℕ) (a : Fin M → Fin L → ℝ)
    (ha : ∀ m l, a m l = (signedSlot w l (row m) : ℝ) / 2 ^ p) (wβ wθ : ℕ → ℕ)
    (WB WT : ℕ → ℝ) (hB : ∀ m, WB m = wβ m) (hT : ∀ l, WT l = (wθ l : ℝ) / 2 ^ d) :
    ∑ m : Fin M, ∑ l : Fin L, |a m l| * (WB m * WT l) =
      (weightedAbsSum M L w row wβ wθ : ℝ) / 2 ^ (p + d) := by
  rw [weightedAbsSum_eq, sum_div, ← Fin.sum_univ_eq_sum_range (fun m ↦ (∑ l ∈ range L,
    |(signedSlot w l (row m) : ℝ)| * ((wβ m : ℝ) * wθ l)) / 2 ^ (p + d)) M]
  refine sum_congr rfl fun m _ ↦ ?_
  rw [sum_div, ← Fin.sum_univ_eq_sum_range (fun l ↦
    |(signedSlot w l (row m) : ℝ)| * ((wβ m : ℝ) * wθ l) / 2 ^ (p + d)) L]
  refine sum_congr rfl fun l _ ↦ ?_
  rw [ha, hB, hT, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ p), pow_add]
  field_simp

end CAS.Numerics

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PairForms
public import CAS.Numerics.MatrixPositivity

/-!
# Sign tests on pairs of natural numbers

Integer checks on pairs `(p, q)` of natural numbers, standing for `p - q` (`pairValue`): a
natural constant is `pairOfNat c`, negation swaps the pair (`pairNeg`), `pairAbsPair a` is
`(|a|, 0)`, and `pairNonneg`, `pairLe` and `pairLt` decide `0 ≤ a`, `a ≤ b` and `a < b`
(`pairNonneg_iff`, `pairLe_iff`, `pairLt_iff`). `natAll_range_spec` reads a passing `natAll`
loop over the indices `start, …, start + count - 1` back as the test at each index.

## Implementation notes

Each test is one `Nat.ble` or `Nat.blt` on sums of entries: `pairLe a b` compares `a.1 + b.2`
with `b.1 + a.2`, moving the subtracted entries across the inequality, so the kernel evaluates
it on literals with its arbitrary-precision arithmetic (see [PackedSlots](PackedSlots.lean));
`pairLe_iff` and `pairLt_iff` follow by `omega`. A certificate over a range of indices is one
closed statement `natAll count (fun k ↦ p (start + k)) = true`, with `natAll` the `Nat.rec` loop
of [MatrixPositivity](MatrixPositivity.lean), which `cega [fast]` decides in one evaluation; the
statement at each index then comes from `natAll_range_spec`, proved for all loops. Inside
SymLean, [GridBall](GridBall.lean) builds on these pairs, and the cell certificates described in
[IntervalBalls](IntervalBalls.lean) end with `natAll_range_spec`.
-/

@[expose] public section

namespace CAS.Numerics

/-- The natural number `c` as a pair. -/
def pairOfNat (c : ℕ) : ℕ × ℕ := (c, 0)

/-- The negation of a pair. -/
def pairNeg (a : ℕ × ℕ) : ℕ × ℕ := (a.2, a.1)

/-- The pair `(|a|, 0)`. -/
def pairAbsPair (a : ℕ × ℕ) : ℕ × ℕ := (pairAbs a, 0)

/-- `0 ≤ pairValue a`, by one natural comparison. -/
def pairNonneg (a : ℕ × ℕ) : Bool := Nat.ble a.2 a.1

/-- `pairValue a ≤ pairValue b`, by one natural comparison. -/
def pairLe (a b : ℕ × ℕ) : Bool := Nat.ble (Nat.add a.1 b.2) (Nat.add b.1 a.2)

/-- `pairValue a < pairValue b`, by one natural comparison. -/
def pairLt (a b : ℕ × ℕ) : Bool := Nat.blt (Nat.add a.1 b.2) (Nat.add b.1 a.2)

/-- The pair `pairOfNat c` has the value `c`. -/
@[simp] theorem pairValue_pairOfNat (c : ℕ) : pairValue (pairOfNat c) = c := by
  simp [pairValue, pairOfNat]

/-- The value of `pairNeg a` is `-pairValue a`. -/
@[simp] theorem pairValue_pairNeg (a : ℕ × ℕ) : pairValue (pairNeg a) = -pairValue a := by
  simp [pairValue, pairNeg]

/-- The value of `pairAbsPair a` is `|pairValue a|`. -/
@[simp] theorem pairValue_pairAbsPair (a : ℕ × ℕ) : pairValue (pairAbsPair a) = |pairValue a| := by
  simp [pairAbsPair, pairValue, cast_pairAbs]

/-- `pairNonneg a` holds exactly when `0 ≤ pairValue a`. -/
theorem pairNonneg_iff (a : ℕ × ℕ) : pairNonneg a = true ↔ 0 ≤ pairValue a := by
  simp only [pairNonneg, Nat.ble_eq, pairValue, sub_nonneg, Nat.cast_le]

/-- `pairLe a b` holds exactly when `pairValue a ≤ pairValue b`. -/
theorem pairLe_iff (a b : ℕ × ℕ) : pairLe a b = true ↔ pairValue a ≤ pairValue b := by
  simp only [pairLe, Nat.ble_eq, Nat.add_eq, pairValue]
  omega

/-- `pairLt a b` holds exactly when `pairValue a < pairValue b`. -/
theorem pairLt_iff (a b : ℕ × ℕ) : pairLt a b = true ↔ pairValue a < pairValue b := by
  simp only [pairLt, Nat.blt_eq, Nat.add_eq, pairValue]
  omega

/-- `natAll` over the indices `start, …, start + count - 1`. -/
theorem natAll_range_spec {start count : ℕ} {p : ℕ → Bool}
    (h : natAll count (fun k ↦ p (start + k)) = true) {i : ℕ}
    (hlo : start ≤ i) (hhi : i < start + count) : p i = true := by
  simpa only [Nat.add_sub_cancel' hlo] using natAll_spec h (j := i - start) (by omega)

end CAS.Numerics

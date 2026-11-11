/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PairPolynomial
public import CAS.Numerics.PackedSlots
import Mathlib.Tactic.Ring.RingNF

/-!
# Linear forms on pairs of natural numbers

A pair `(p, q)` stands for `p - q` (`pairValue`). Linear combinations with natural
coefficients and differences stay in natural numbers: `pairSmul c` multiplies both entries by
`c` and `pairSub` adds the entries crosswise. A biased slot read as a pair, `slotPair w k x`,
has the signed slot as its value, and `pairAbs a` is the `natAbs` of the value of `a`
(`pairAbs_eq_natAbs`).

## Implementation notes

The forms keep the representation of [PairPolynomial](PairPolynomial.lean): `pairSmul` and
`pairSub` call `Nat.mul` and `Nat.add` directly, and a difference adds crosswise instead of
subtracting, so the kernel evaluates a form with natural-number arithmetic only and no truncated
subtraction occurs before `pairAbs`. `slotPair` keeps the bias as the second entry instead of
subtracting it, so a signed combination of packed slots needs no integer either, and
`pairValue_slotPair` holds by `rfl`. [PairChecks](PairChecks.lean) builds its sign tests on these
forms.
-/

@[expose] public section

namespace CAS.Numerics

/-- The pair `c • a`. -/
def pairSmul (c : ℕ) (a : ℕ × ℕ) : ℕ × ℕ := (Nat.mul c a.1, Nat.mul c a.2)

/-- The difference of two pairs. -/
def pairSub (a b : ℕ × ℕ) : ℕ × ℕ := (Nat.add a.1 b.2, Nat.add a.2 b.1)

/-- Slot `k` of width `w` of `x` with its bias, as a pair. -/
def slotPair (w k x : ℕ) : ℕ × ℕ := (slot w k x, slotBias w)

/-- The value of `pairSmul c a` is `c * pairValue a`. -/
@[simp] theorem pairValue_pairSmul (c : ℕ) (a : ℕ × ℕ) :
    pairValue (pairSmul c a) = c * pairValue a := by
  simp only [pairValue, pairSmul, Nat.mul_eq]
  push_cast
  ring

/-- The value of `pairSub a b` is `pairValue a - pairValue b`. -/
@[simp] theorem pairValue_pairSub (a b : ℕ × ℕ) :
    pairValue (pairSub a b) = pairValue a - pairValue b := by
  simp only [pairValue, pairSub, Nat.add_eq]
  push_cast
  ring

/-- The value of `slotPair w k x` is the signed slot `signedSlot w k x`. -/
@[simp] theorem pairValue_slotPair (w k x : ℕ) : pairValue (slotPair w k x) = signedSlot w k x :=
  rfl

/-- `pairAbs a` is the `natAbs` of `pairValue a`. -/
theorem pairAbs_eq_natAbs (a : ℕ × ℕ) : pairAbs a = (pairValue a).natAbs := by
  exact_mod_cast (cast_pairAbs a).trans (Int.abs_eq_natAbs _)

end CAS.Numerics

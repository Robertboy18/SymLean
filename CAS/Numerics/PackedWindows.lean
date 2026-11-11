/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedLinearAlgebra
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# Windows, slot-wise sums and two-sided bounds of packed rows

A window `Nat.land (x >>> (w o)) (slotMask (w n))` of a packed row holds the slots `o` to
`o + n - 1` of `x` (`slot_window`). Two packed rows whose slot sums stay below `2 ^ w` add slot by
slot (`slot_add_of_lt`), and the complement `slotMask (w n) - y` of a row has the complementary
slots (`slot_slotMask_sub`, with `packSlots_slotMask`: the mask is the row of slots `2 ^ w - 1`).
`slot_constBlocks` reads the slots of a row of `n` blocks of `b` equal slots followed by one
more slot.

A passing guard check bounds every signed slot by `2 ^ (g - 1) - 1` from above
(`signedSlot_lt_of_signedGuardCheck`). `offsetBoundCheck w g n off y` checks the two-sided bound
`|signedSlot w j y| ≤ 2 ^ (g - 1) - 1 - slot w j off` for every `j < n` with two guard checks,
of `y + off` and of `off - y`; the offsets may differ from slot to slot, so one check bounds the
slots of a row by bounds that are not powers of two (`abs_signedSlot_le_of_offsetBoundCheck`).

## Implementation notes

A window, a complement and `offsetBoundCheck` are a fixed number of shifts, masks, additions and
subtractions of whole rows, all among the operations the kernel evaluates on literals (see
[PackedSlots](PackedSlots.lean)), so each costs a few big-number operations whatever the number of
slots. The lower bound comes from the complement: `slotMask (w n) - y + constSlots w n 1` has the
slots `2 ^ w - slot w j y`, whose signed values are the negated signed slots of `y`, so the second
guard check bounds `slot w j off - signedSlot w j y` from above as the first bounds
`signedSlot w j y + slot w j off`. A row of `n` blocks of `b` equal slots is packed at width
`w b` from the `n` blocks `constSlots w b (F q)`, and `slot_constBlocks` reads it back through
`slot_slot_mul`.

Besides `1 ≤ g < w` for the guard checks and `off < 2 ^ (w * n)`, the hypotheses of
`abs_signedSlot_le_of_offsetBoundCheck` exclude carries between slots: a prior bound `b` on the
signed slots of `y` with `slot w j off + b < slotBias w` keeps every slot sum of the
additions below `2 ^ w`, so `slot_add_of_lt` adds them slot by slot and `slot_slotMask_sub` reads
the complement. The proof applies `signedSlot_lt_of_signedGuardCheck` to both checks and closes
with `omega`. It holds for all rows; the kernel only evaluates `offsetBoundCheck` on the literals
of a certificate. Inside SymLean, [SuffixSlots](SuffixSlots.lean) reads its windows through
`slot_window`, while `offsetBoundCheck` and `slot_constBlocks` serve certificates built on the
library.
-/

@[expose] public section

namespace CAS.Numerics

/-- The slots `o` to `o + n - 1` of `x` are the slots of its window. -/
theorem slot_window {w o n j : ℕ} (hj : j < n) (x : ℕ) :
    slot w j (Nat.land (Nat.shiftRight x (Nat.mul w o)) (slotMask (Nat.mul w n))) =
      slot w (j + o) x := by
  change slot w j ((x >>> (w * o)) &&& slotMask (w * n)) = _
  rw [slotMask_eq, Nat.and_two_pow_sub_one_eq_mod, slot_mod_two_pow hj,
    Nat.shiftRight_eq_div_pow, slot_div_two_pow]

/-- A window of `n` slots is below `2 ^ (w n)`. -/
theorem window_lt (w o n x : ℕ) :
    Nat.land (Nat.shiftRight x (Nat.mul w o)) (slotMask (Nat.mul w n)) < 2 ^ (w * n) := by
  change (x >>> (w * o)) &&& slotMask (w * n) < _
  rw [slotMask_eq, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by positivity)

/-- Rows whose slot sums stay below `2 ^ w` add slot by slot. -/
theorem slot_add_of_lt {w n x z : ℕ} (hx : x < 2 ^ (w * n)) (hz : z < 2 ^ (w * n))
    (h : ∀ j < n, slot w j x + slot w j z < 2 ^ w) :
    (∀ j < n, slot w j (x + z) = slot w j x + slot w j z) ∧ x + z < 2 ^ (w * n) := by
  have hsum : x + z = packSlots w n (fun j ↦ slot w j x + slot w j z) := by
    conv_lhs => rw [← packSlots_slot hx, ← packSlots_slot hz]
    exact packSlots_add w n _ _
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · rw [hsum, slot_packed_eq h, ite_eq_left hj]
  · rw [hsum]
    exact packSlots_lt h

/-- The constant row of the largest slot value is the mask of the row. -/
theorem packSlots_slotMask (w n : ℕ) :
    packSlots w n (fun _ ↦ 2 ^ w - 1) = 2 ^ (w * n) - 1 := by
  induction n with
  | zero => simp [packSlots, natSum]
  | succ n ih =>
    rw [packSlots_succ, ih, Nat.mul_succ, pow_add]
    have h1 : 1 ≤ 2 ^ (w * n) := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    zify [h1, h2, Nat.one_le_iff_ne_zero.mpr (by positivity : 2 ^ (w * n) * 2 ^ w ≠ 0)]
    ring

/-- Packing depends only on the first `n` values. -/
theorem packSlots_congr {w n : ℕ} {f g : ℕ → ℕ} (h : ∀ k < n, f k = g k) :
    packSlots w n f = packSlots w n g := by
  rw [packSlots_eq_sum, packSlots_eq_sum]
  exact Finset.sum_congr rfl fun k hk ↦ by rw [h k (Finset.mem_range.mp hk)]

/-- The complement of a row in its mask has the complementary slots. -/
theorem slot_slotMask_sub {w n y : ℕ} (hy : y < 2 ^ (w * n)) {j : ℕ} (hj : j < n) :
    slot w j (Nat.sub (slotMask (Nat.mul w n)) y) = 2 ^ w - 1 - slot w j y := by
  have hsum : packSlots w n (fun k ↦ 2 ^ w - 1 - slot w k y) + y = slotMask (Nat.mul w n) := by
    have e : packSlots w n (fun k ↦ 2 ^ w - 1 - slot w k y) + packSlots w n (fun k ↦ slot w k y) =
        packSlots w n (fun k ↦ 2 ^ w - 1 - slot w k y) + y := by rw [packSlots_slot hy]
    rw [← e, packSlots_add]
    change _ = slotMask (w * n)
    rw [slotMask_eq, ← packSlots_slotMask]
    exact packSlots_congr fun k _ ↦ Nat.sub_add_cancel (Nat.le_sub_one_of_lt (slot_lt w k y))
  rw [Nat.sub_eq, ← hsum, Nat.add_sub_cancel, slot_packed_eq (fun k _ ↦ lt_of_le_of_lt
    (Nat.sub_le _ _) (Nat.sub_lt (Nat.one_le_two_pow) (by norm_num))), ite_eq_left hj]

/-- The complement of a row in its mask is below `2 ^ (w n)`. -/
theorem slotMask_sub_lt {w n y : ℕ} : Nat.sub (slotMask (Nat.mul w n)) y < 2 ^ (w * n) := by
  change slotMask (w * n) - y < _
  rw [slotMask_eq]
  have : 1 ≤ 2 ^ (w * n) := Nat.one_le_two_pow
  omega

/-- A passing guard check bounds every signed slot above by `2 ^ (g - 1) - 1`. -/
theorem signedSlot_lt_of_signedGuardCheck {w g n x : ℕ} (hg : g < w) (hg1 : 1 ≤ g)
    (h : signedGuardCheck w g n x = true) {k : ℕ} (hk : k < n) :
    signedSlot w k x < 2 ^ (g - 1) := by
  have hfit := (fitsSlot_of_signedGuardCheck hg h hk).2
  rw [show g = (g - 1) + 1 by omega, slotBias_succ, pow_succ] at hfit
  push_cast at hfit
  linarith

/-- Two guard checks bound every signed slot `y j` of a row by `2 ^ (g - 1) - 1 - off j`, for an
offset row `off` of slots below the margin to the bias. -/
def offsetBoundCheck (w g n off y : ℕ) : Bool :=
  signedGuardCheck w g n (Nat.add y off) &&
    signedGuardCheck w g n
      (Nat.add (Nat.add (Nat.sub (slotMask (Nat.mul w n)) y) off) (constSlots w n 1))

/-- **Two-sided bounds.** If every signed slot of `y` is at most `b` in absolute value and every
offset slot is below `slotBias w - b`, a passing `offsetBoundCheck` gives
`|signedSlot w j y| ≤ 2 ^ (g - 1) - 1 - slot w j off`. -/
theorem abs_signedSlot_le_of_offsetBoundCheck {w g n off y b : ℕ} (hg : g < w) (hg1 : 1 ≤ g)
    (h : offsetBoundCheck w g n off y = true)
    (hoff : off < 2 ^ (w * n))
    (hy : ∀ j < n, (signedSlot w j y).natAbs ≤ b)
    (hmargin : ∀ j < n, slot w j off + b < slotBias w) {j : ℕ} (hj : j < n) :
    |signedSlot w j y| ≤ 2 ^ (g - 1) - 1 - (slot w j off : ℤ) := by
  simp only [offsetBoundCheck, Bool.and_eq_true] at h
  obtain ⟨h₁, h₂⟩ := h
  have hw0 : 0 < w := by omega
  have hβ : slotBias w * 2 = 2 ^ w := by
    rw [show w = (w - 1) + 1 by omega, slotBias_succ, pow_succ]
  have hyl : y < 2 ^ (w * n) := (Nat.le_add_right y off).trans_lt (lt_of_signedGuardCheck h₁)
  -- the slots of `y` lie within `b` of the bias
  have hyslot : ∀ k < n, slotBias w ≤ slot w k y + b ∧ slot w k y ≤ slotBias w + b := by
    intro k hk
    have := hy k hk
    rw [signedSlot] at this
    omega
  -- upper bound from `y + off`
  have hsum₁ := slot_add_of_lt hyl hoff (fun k hk ↦ by
    have := hyslot k hk; have := hmargin k hk; omega)
  have hup := signedSlot_lt_of_signedGuardCheck hg hg1 h₁ hj
  rw [show Nat.add y off = y + off from rfl, signedSlot, hsum₁.1 j hj] at hup
  -- lower bound from `mask - y + off + 1`
  have hones : constSlots w n 1 < 2 ^ (w * n) := by
    rw [constSlots_eq hw0]
    exact packSlots_lt fun _ _ ↦ Nat.one_lt_two_pow (by omega)
  have hcomp : ∀ k < n, slot w k (Nat.sub (slotMask (Nat.mul w n)) y) = 2 ^ w - 1 - slot w k y :=
    fun k hk ↦ slot_slotMask_sub hyl hk
  have hsum₂ := slot_add_of_lt slotMask_sub_lt hoff (fun k hk ↦ by
    rw [hcomp k hk]; have := hyslot k hk; have := hmargin k hk; omega)
  have hone : ∀ k < n, slot w k (constSlots w n 1) = 1 := fun k hk ↦ by
    rw [constSlots_eq hw0, slot_packed_eq (fun _ _ ↦ Nat.one_lt_two_pow (by omega)), ite_eq_left hk]
  have hsum₃ := slot_add_of_lt hsum₂.2 hones (fun k hk ↦ by
    rw [hsum₂.1 k hk, hcomp k hk, hone k hk]
    have := hyslot k hk; have := hmargin k hk; omega)
  have hdown := signedSlot_lt_of_signedGuardCheck hg hg1 h₂ hj
  rw [show Nat.add (Nat.add (Nat.sub (slotMask (Nat.mul w n)) y) off) (constSlots w n 1) =
      Nat.sub (slotMask (Nat.mul w n)) y + off + constSlots w n 1 from rfl, signedSlot,
    hsum₃.1 j hj, hsum₂.1 j hj, hcomp j hj, hone j hj] at hdown
  have hyj := hyslot j hj
  have hmj := hmargin j hj
  have hlt := slot_lt w j y
  rw [abs_le, signedSlot]
  omega

/-- A row of `n` blocks of `b` equal slots `F q`, followed by one more slot `top`: slot `j` is
`F (j / b)` below `b n` and `top` at `b n`. -/
theorem slot_constBlocks {w b n top : ℕ} {F : ℕ → ℕ}
    (hF : ∀ q, F q < 2 ^ w) (htop : top < 2 ^ w) {j : ℕ} (hj : j ≤ b * n) :
    slot w j (Nat.add (packSlots (Nat.mul w b) n fun q ↦ constSlots w b (F q))
        (Nat.shiftLeft top (Nat.mul w (Nat.mul b n)))) = (if j < b * n then F (j / b) else top) ∧
      Nat.add (packSlots (Nat.mul w b) n fun q ↦ constSlots w b (F q))
        (Nat.shiftLeft top (Nat.mul w (Nat.mul b n))) < 2 ^ (w * (b * n + 1)) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · have hF0 : ∀ q, F q = 0 := fun q ↦ by simpa using hF q
    obtain rfl : top = 0 := by simpa using htop
    simp [hF0, slot_eq, constSlots, packSlots_eq_sum, Nat.add_eq]
  set A := packSlots (Nat.mul w b) n fun q ↦ constSlots w b (F q)
  have hblock : ∀ q, constSlots w b (F q) < 2 ^ (w * b) := fun q ↦ by
    rw [constSlots_eq hw]
    exact packSlots_lt fun _ _ ↦ hF q
  have hA : A < 2 ^ (w * (b * n)) := by
    have := packSlots_lt (w := w * b) (n := n) (f := fun q ↦ constSlots w b (F q))
      (fun q _ ↦ hblock q)
    rwa [← Nat.mul_assoc]
  have hrow : Nat.add A (Nat.shiftLeft top (Nat.mul w (Nat.mul b n))) =
      A + top * 2 ^ (w * (b * n)) := congrArg (A + ·) (Nat.shiftLeft_eq top _)
  refine ⟨?_, ?_⟩
  · rw [hrow, slot_add_mul_pow hA]
    split_ifs with hj'
    · have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hj')
      have hq : j / b < n := (Nat.div_lt_iff_lt_mul hb).2 (by linarith)
      have e := slot_slot_mul (w := w) (q := b) (k := j % b) (i := j / b)
        (Nat.mod_lt _ hb) A
      rw [Nat.div_add_mod] at e
      rw [← e]
      have hs : slot (w * b) (j / b) A = constSlots w b (F (j / b)) := by
        simp only [A]
        rw [show Nat.mul w b = w * b from rfl, slot_packed_eq (fun q _ ↦ hblock q),
          ite_eq_left hq]
      rw [hs, constSlots_eq hw, slot_packed_eq (fun _ _ ↦ hF _),
        ite_eq_left (Nat.mod_lt _ hb)]
    · rw [show j = b * n by omega, Nat.sub_self, slot_of_lt htop]
      simp
  · rw [hrow, Nat.mul_add, Nat.mul_one, pow_add]
    nlinarith [Nat.mul_le_mul_left (2 ^ (w * (b * n))) (Nat.succ_le_of_lt htop)]

end CAS.Numerics

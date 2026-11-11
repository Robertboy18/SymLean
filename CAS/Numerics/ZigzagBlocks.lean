/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.SignedPolynomial
public import CAS.Numerics.SlotBlocks
public import CAS.Numerics.PackedSpreadSteps
public import CAS.Numerics.PackedAppend
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity.Finset
import CAS.Numerics.PackedSignedRows

/-!
# Signed products of slot-block tables in natural arithmetic

A table read by `blockSlot w (2 ^ l) blocks` stores zigzag codes of signed coefficients
(`signedCoefficient`). `spreadBlocks w W l blocks D 0` holds its first `2 ^ (l + D)` codes in
the slots of width `W ≥ w` of one natural number (`spreadBlocks_eq`): every block is spread from
width `w` to width `W` in `l` steps (`spread`, with masks in closed form), and the spread blocks
are joined by a balanced sum of shifts. A few operations on the whole number then split the
codes into the packed magnitudes of the nonnegative entries and of the negative entries
(`zigzagPositive`, `zigzagNegative`), and pack all magnitudes (`zigzagMagnitudes`).

The integer packing `packSignedBinary W` of the balanced tree read from such a table is the
difference of the two parts (`packSignedBinary_ofBlocks`). A signed product of three tables is
therefore certified by the natural identity `P_a P_b + N_a N_b + N_c = P_c + P_a N_b + N_a P_b`
(`packSignedBinary_mul_of_zigzag`), and the mass condition of `signedProductCheck` follows from
the slot widths (`signedProductCheck_of_zigzag`). The absolute mass of a table is one remainder
of its packed magnitudes modulo `2 ^ W - 1` (`signedMass_ofBlocks`). A kernel evaluation of
`spreadBlocks` takes `l` spread steps of a few operations on whole numbers for each of the
`2 ^ D` blocks, and `2 ^ D - 1` joins, where the tree packing needs integer operations at each of
its `2 ^ (l + D)` leaves and at every inner node.

## Implementation notes

The product check is Kronecker substitution: the packed numbers are the values at `2 ^ W` of the
coefficient polynomials, one integer product stands for the whole convolution, and
`signedProductCheck_sound` recovers the polynomial identity from the integer identity under the
mass condition. All three tables are stored data; the kernel only spreads, multiplies and
compares. We stay in natural numbers because the kernel evaluates natural-number literals with
its arbitrary-precision arithmetic but has no such extension for `Int`, so
`zigzagProductCheck` is the product of the two differences with the negative terms moved across:
four multiplications and one comparison. The zigzag codes make the split cheap, since the low bit
of a code is its sign: one conjunction reads all signs, one subtraction and one halving give all
magnitudes, and a conjunction with the signs times `2 ^ W - 1` keeps the negative entries. The
masks of `spread` come from `constSlots` with one multiplication and one division
(`spreadMaskConst`) instead of a sum over their slots.

## References

* David Harvey, "Faster polynomial multiplication via multipoint Kronecker substitution",
  *Journal of Symbolic Computation* 44 (2009), pp. 1502-1510,
  <https://doi.org/10.1016/j.jsc.2009.05.004>. Section 1 for the substitution: evaluate at a
  power of two and multiply the integers.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-! ### Spreading with closed-form masks -/

/-- `spreadMask` computed by `constSlots`, with one multiplication and one division. -/
def spreadMaskConst (w W p d : ℕ) : ℕ :=
  constSlots (2 ^ (p - d) * W) (2 ^ d) (2 ^ (2 ^ (p - d - 1) * w) - 1)

/-- For `0 < W`, the closed-form mask `spreadMaskConst w W p d` is `spreadMask w W p d`. -/
theorem spreadMaskConst_eq {w W p d : ℕ} (hW : 0 < W) :
    spreadMaskConst w W p d = spreadMask w W p d :=
  constSlots_eq (Nat.mul_pos (by positivity) hW) _ _

/-- `spreadStep` with the closed-form mask. -/
def spreadStepConst (w W p d x : ℕ) : ℕ :=
  Nat.add (Nat.land x (spreadMaskConst w W p d))
    (Nat.mul (Nat.sub x (Nat.land x (spreadMaskConst w W p d)))
      (2 ^ (2 ^ (p - d - 1) * (W - w))))

/-- `spread` with the closed-form masks. -/
def spreadConst (w W p x : ℕ) : ℕ :=
  Nat.rec (motive := fun _ ↦ ℕ) x (fun d y ↦ spreadStepConst w W p d y) p

/-- `spreadConst w W p x` is `spread w W p x`, for every `x` and all widths. -/
theorem spreadConst_eq {w W p : ℕ} (x : ℕ) :
    spreadConst w W p x = spread w W p x := by
  have hstep : ∀ d y, spreadStepConst w W p d y = spreadStep w W p d y := fun d y ↦ by
    rcases Nat.eq_zero_or_pos W with rfl | hW
    · have h1 := Nat.and_le_left (n := y) (m := spreadMaskConst w 0 p d)
      have h2 := Nat.and_le_left (n := y) (m := spreadMask w 0 p d)
      change (y &&& spreadMaskConst w 0 p d) + (y - (y &&& spreadMaskConst w 0 p d)) *
          2 ^ (2 ^ (p - d - 1) * (0 - w)) =
        (y &&& spreadMask w 0 p d) + (y - (y &&& spreadMask w 0 p d)) *
          2 ^ (2 ^ (p - d - 1) * (0 - w))
      simp only [Nat.zero_sub, Nat.mul_zero, pow_zero, Nat.mul_one]
      omega
    · rw [spreadStepConst, spreadStep, spreadMaskConst_eq hW]
  have h : ∀ n, (Nat.rec (motive := fun _ ↦ ℕ) x (fun d y ↦ spreadStepConst w W p d y) n : ℕ) =
      spreadUpTo w W p x n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change spreadStepConst w W p n (Nat.rec (motive := fun _ ↦ ℕ) x
        (fun d y ↦ spreadStepConst w W p d y) n) = spreadStep w W p n (spreadUpTo w W p x n)
      rw [ih, hstep]
  exact h p

/-! ### Joining spread blocks -/

/-- Block `b` of a table with `2 ^ l` slots of width `w` per block, in slots of width `W`. -/
def spreadBlock (w W l : ℕ) (blocks : ℕ → ℕ) (b : ℕ) : ℕ :=
  spreadConst w W l (Nat.mod (blocks b) (2 ^ (w * 2 ^ l)))

/-- The blocks `first` to `first + 2 ^ D - 1` in slots of width `W`, joined by a balanced sum of
shifts. -/
def spreadBlocks (w W l : ℕ) (blocks : ℕ → ℕ) (D : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ ↦ ℕ → ℕ) (spreadBlock w W l blocks)
    (fun d pack first ↦ Nat.add (pack first)
      (Nat.shiftLeft (pack (Nat.add first (2 ^ d))) (W * 2 ^ (l + d))))
    D

/-- For `w ≤ W`, `spreadBlock w W l blocks b` is the packing in slots of width `W` of the `2 ^ l`
entries `2 ^ l * b + j` of the table read by `blockSlot w (2 ^ l) blocks`. -/
theorem spreadBlock_eq {w W l : ℕ} (hW : w ≤ W) (blocks : ℕ → ℕ) (b : ℕ) :
    spreadBlock w W l blocks b =
      packSlots W (2 ^ l) (fun j ↦ blockSlot w (2 ^ l) blocks (2 ^ l * b + j)) := by
  set x := blocks b % 2 ^ (w * 2 ^ l)
  have hx : packSlots w (2 ^ l) (fun k ↦ slot w k x) = x :=
    packSlots_slot (Nat.mod_lt _ (by positivity))
  unfold spreadBlock
  rw [spreadConst_eq, show Nat.mod (blocks b) (2 ^ (w * 2 ^ l)) = x from rfl, ← hx,
    spread_packSlots hW (fun k ↦ slot_lt w k x)]
  refine packSlots_congr fun k hk ↦ ?_
  change slot w k x = slot w ((2 ^ l * b + k) % 2 ^ l) (blocks ((2 ^ l * b + k) / 2 ^ l))
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hk, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hk,
    Nat.add_zero]
  exact slot_mod_two_pow hk _

/-- For `w ≤ W`, `spreadBlocks w W l blocks D first` is the packing in slots of width `W` of the
`2 ^ (l + D)` entries from `2 ^ l * first` on of the table read by `blockSlot w (2 ^ l) blocks`. -/
theorem spreadBlocks_eq {w W l : ℕ} (hW : w ≤ W) (blocks : ℕ → ℕ) (D : ℕ) :
    ∀ first, spreadBlocks w W l blocks D first =
      packSlots W (2 ^ (l + D)) (fun j ↦ blockSlot w (2 ^ l) blocks (2 ^ l * first + j)) := by
  induction D with
  | zero => exact spreadBlock_eq hW blocks
  | succ D ih =>
    intro first
    have hstep : spreadBlocks w W l blocks (D + 1) first =
        spreadBlocks w W l blocks D first +
          spreadBlocks w W l blocks D (first + 2 ^ D) * 2 ^ (W * 2 ^ (l + D)) := by
      rw [← Nat.shiftLeft_eq]
      rfl
    have hsize : 2 ^ (l + (D + 1)) = 2 ^ (l + D) + 2 ^ (l + D) := by
      rw [← Nat.add_assoc, pow_succ, Nat.mul_two]
    rw [hstep, ih, ih, hsize, packSlots_append]
    congr 2
    exact packSlots_congr fun j _ ↦ by ring_nf

/-! ### Zigzag codes in packed slots -/

/-- The low bits of the codes in the first `n` slots of width `W` of `Z`. -/
def zigzagSigns (W n Z : ℕ) : ℕ := Nat.land Z (constSlots W n 1)

/-- The magnitudes `c / 2` of the codes `c` in the first `n` slots of width `W` of `Z`. -/
def zigzagMagnitudes (W n Z : ℕ) : ℕ := Nat.div (Nat.sub Z (zigzagSigns W n Z)) 2

/-- The magnitudes of the odd codes (the negative entries), with zero at the even codes. -/
def zigzagNegative (W n Z : ℕ) : ℕ :=
  Nat.land (zigzagMagnitudes W n Z) (Nat.mul (zigzagSigns W n Z) (2 ^ W - 1))

/-- The magnitudes of the even codes (the nonnegative entries), with zero at the odd codes. -/
def zigzagPositive (W n Z : ℕ) : ℕ := Nat.sub (zigzagMagnitudes W n Z) (zigzagNegative W n Z)

section Codes

variable {W n : ℕ} {z : ℕ → ℕ}

/-- For codes `z j < 2 ^ W`, `zigzagSigns` of their packing is the packing of their low bits
`z j % 2`. -/
theorem zigzagSigns_packSlots (hz : ∀ j < n, z j < 2 ^ W) :
    zigzagSigns W n (packSlots W n z) = packSlots W n (fun j ↦ z j % 2) := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · have hz0 : ∀ j < n, z j = 0 := fun j hj ↦ by simpa using hz j hj
    have h0 : packSlots 0 n z = 0 := by
      rw [packSlots_eq_sum]
      exact sum_eq_zero fun j hj ↦ by simp [hz0 j (mem_range.mp hj)]
    have h1 : packSlots 0 n (fun j ↦ z j % 2) = 0 := by
      rw [packSlots_eq_sum]
      exact sum_eq_zero fun j hj ↦ by simp [hz0 j (mem_range.mp hj)]
    rw [h0, h1]
    exact Nat.zero_and _
  unfold zigzagSigns
  rw [constSlots_eq hW, land_packSlots hz (fun _ _ ↦ Nat.one_lt_two_pow hW.ne')]
  exact packSlots_congr fun j _ ↦ Nat.and_one_is_mod (z j)

/-- For codes `z j < 2 ^ W`, `zigzagMagnitudes` of their packing is the packing of `z j / 2`. -/
theorem zigzagMagnitudes_packSlots (hz : ∀ j < n, z j < 2 ^ W) :
    zigzagMagnitudes W n (packSlots W n z) = packSlots W n (fun j ↦ z j / 2) := by
  have hsplit : packSlots W n z =
      2 * packSlots W n (fun j ↦ z j / 2) + packSlots W n (fun j ↦ z j % 2) := by
    rw [mul_packSlots, packSlots_add]
    exact packSlots_congr fun j _ ↦ (Nat.div_add_mod (z j) 2).symm
  unfold zigzagMagnitudes
  rw [zigzagSigns_packSlots hz]
  change (packSlots W n z - packSlots W n (fun j ↦ z j % 2)) / 2 = _
  rw [hsplit]
  omega

/-- For codes `z j < 2 ^ W`, `zigzagNegative` of their packing is the packing of `z j / 2` at the
odd codes and `0` at the even codes. -/
theorem zigzagNegative_packSlots (hz : ∀ j < n, z j < 2 ^ W) :
    zigzagNegative W n (packSlots W n z) =
      packSlots W n (fun j ↦ if z j % 2 = 1 then z j / 2 else 0) := by
  have hmask : Nat.mul (packSlots W n fun j ↦ z j % 2) (2 ^ W - 1) =
      packSlots W n fun j ↦ if z j % 2 = 1 then 2 ^ W - 1 else 0 := by
    change packSlots W n (fun j ↦ z j % 2) * (2 ^ W - 1) = _
    rw [Nat.mul_comm, mul_packSlots]
    refine packSlots_congr fun j _ ↦ ?_
    rcases Nat.mod_two_eq_zero_or_one (z j) with h | h <;> simp [h]
  unfold zigzagNegative
  rw [zigzagMagnitudes_packSlots hz, zigzagSigns_packSlots hz, hmask,
    land_packSlots_mask (fun j hj ↦ lt_of_le_of_lt (Nat.div_le_self _ _) (hz j hj))
      (fun j ↦ z j % 2 = 1)]

/-- For codes `z j < 2 ^ W`, `zigzagPositive` of their packing is the packing of `z j / 2` at the
even codes and `0` at the odd codes. -/
theorem zigzagPositive_packSlots (hz : ∀ j < n, z j < 2 ^ W) :
    zigzagPositive W n (packSlots W n z) =
      packSlots W n (fun j ↦ if z j % 2 = 1 then 0 else z j / 2) := by
  unfold zigzagPositive
  rw [zigzagMagnitudes_packSlots hz, zigzagNegative_packSlots hz]
  change packSlots W n _ - packSlots W n _ = _
  rw [packSlots_sub (fun j _ ↦ by split_ifs <;> omega)]
  exact packSlots_congr fun j _ ↦ by split_ifs <;> omega

/-- The two parts of packed codes differ by the signed packing of the coded entries. -/
theorem zigzag_parts_eq (hz : ∀ j < n, z j < 2 ^ W) :
    (zigzagPositive W n (packSlots W n z) : ℤ) - zigzagNegative W n (packSlots W n z) =
      ∑ j ∈ range n, signedCoefficient (z j) * 2 ^ (W * j) := by
  rw [zigzagPositive_packSlots hz, zigzagNegative_packSlots hz, packSlots_eq_sum,
    packSlots_eq_sum, Nat.cast_sum, Nat.cast_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  unfold signedCoefficient
  rcases Nat.mod_two_eq_zero_or_one (z j) with h | h <;> simp [h]

end Codes

/-! ### Balanced trees read from slot-block tables -/

/-- The absolute value of a decoded entry is half its code. -/
theorem abs_signedCoefficient (v : ℕ) : |signedCoefficient v| = ((v / 2 : ℕ) : ℤ) := by
  unfold signedCoefficient
  split_ifs <;> simp only [abs_neg, Nat.abs_cast]

/-- The signed packing of a balanced tree read from a function sums its decoded entries. -/
theorem packSignedBinary_ofFnBlock (bits : ℕ) (f : ℕ → ℕ) (D : ℕ) : ∀ off,
    packSignedBinary bits (CoefficientTree.ofFnBlock f D off) =
      ∑ j ∈ range (2 ^ D), signedCoefficient (f (off + j)) * 2 ^ (bits * j) := by
  induction D with
  | zero => intro off; simp [CoefficientTree.ofFnBlock, packSignedBinary]
  | succ D ih =>
    intro off
    rw [CoefficientTree.ofFnBlock, packSignedBinary, ih, ih, Int.shiftLeft_eq, pow_succ,
      Nat.mul_two, sum_range_add, sum_mul]
    congr 1
    exact sum_congr rfl fun j _ ↦ by rw [Nat.add_assoc]; ring

/-- The absolute mass of a balanced tree read from a function sums the halved codes. -/
theorem signedMass_ofFnBlock (f : ℕ → ℕ) (D : ℕ) : ∀ off,
    signedMass (CoefficientTree.ofFnBlock f D off) =
      ∑ j ∈ range (2 ^ D), ((f (off + j) / 2 : ℕ) : ℤ) := by
  induction D with
  | zero => intro off; simp [CoefficientTree.ofFnBlock, signedMass, abs_signedCoefficient]
  | succ D ih =>
    intro off
    rw [CoefficientTree.ofFnBlock, signedMass, ih, ih, pow_succ, Nat.mul_two, sum_range_add]
    simp only [Nat.add_assoc]

/-- Codes below `2 ^ w` bound the mass of `2 ^ D` entries by `2 ^ (D + w)`. -/
theorem signedMass_ofFnBlock_le {w : ℕ} {f : ℕ → ℕ} (hf : ∀ j, f j < 2 ^ w) (D off : ℕ) :
    signedMass (CoefficientTree.ofFnBlock f D off) ≤ 2 ^ (D + w) := by
  rw [signedMass_ofFnBlock]
  refine (sum_le_card_nsmul _ _ ((2 : ℤ) ^ w) fun j _ ↦ ?_).trans_eq ?_
  · have := hf (off + j)
    exact_mod_cast (show f (off + j) / 2 ≤ 2 ^ w by omega)
  · rw [card_range, nsmul_eq_mul, pow_add]
    push_cast
    ring

/-- The tree of a slot-block table has the signed packing of its spread codes. -/
theorem packSignedBinary_ofBlocks {w W l q depth D : ℕ} (hW : w ≤ W)
    (hq : q = 2 ^ l) (hD : depth = l + D) (blocks : ℕ → ℕ) :
    packSignedBinary W (CoefficientTree.ofFnBlock (blockSlot w q blocks) depth 0) =
      (zigzagPositive W (2 ^ (l + D)) (spreadBlocks w W l blocks D 0) : ℤ) -
        zigzagNegative W (2 ^ (l + D)) (spreadBlocks w W l blocks D 0) := by
  subst hq hD
  have hz : ∀ j < 2 ^ (l + D), blockSlot w (2 ^ l) blocks j < 2 ^ W := fun j _ ↦
    lt_of_lt_of_le (slot_lt _ _ _) (Nat.pow_le_pow_right (by norm_num) hW)
  rw [spreadBlocks_eq hW]
  simp only [Nat.mul_zero, Nat.zero_add]
  rw [zigzag_parts_eq hz, packSignedBinary_ofFnBlock]
  simp only [Nat.zero_add]

/-- The absolute mass of a slot-block table is one remainder of its packed magnitudes. -/
theorem signedMass_ofBlocks {w W l q depth D : ℕ}
    (hq : q = 2 ^ l) (hD : depth = l + D) (hfit : l + D + w < W) (blocks : ℕ → ℕ) :
    signedMass (CoefficientTree.ofFnBlock (blockSlot w q blocks) depth 0) =
      ((zigzagMagnitudes W (2 ^ (l + D)) (spreadBlocks w W l blocks D 0) % (2 ^ W - 1) : ℕ) :
        ℤ) := by
  have hW : w ≤ W := by omega
  subst hq hD
  have hz : ∀ j < 2 ^ (l + D), blockSlot w (2 ^ l) blocks j < 2 ^ W := fun j _ ↦
    lt_of_lt_of_le (slot_lt _ _ _) (Nat.pow_le_pow_right (by norm_num) hW)
  have hsum : ∑ j ∈ range (2 ^ (l + D)), blockSlot w (2 ^ l) blocks j / 2 < 2 ^ W - 1 := by
    have hlt : ∑ j ∈ range (2 ^ (l + D)), blockSlot w (2 ^ l) blocks j / 2 <
        ∑ _j ∈ range (2 ^ (l + D)), 2 ^ w :=
      sum_lt_sum_of_nonempty (nonempty_range_iff.mpr (by positivity)) fun j _ ↦
        lt_of_le_of_lt (Nat.div_le_self _ _) (slot_lt _ _ _)
    rw [sum_const, card_range, smul_eq_mul, ← pow_add] at hlt
    have hle : 2 * 2 ^ (l + D + w) ≤ 2 ^ W := by
      rw [← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) hfit
    omega
  rw [spreadBlocks_eq hW]
  simp only [Nat.mul_zero, Nat.zero_add]
  rw [zigzagMagnitudes_packSlots hz, packSlots_mod,
    Nat.mod_eq_of_lt hsum, signedMass_ofFnBlock, Nat.cast_sum]
  simp only [Nat.zero_add]

/-! ### Products -/

/-- The natural identity `P_a P_b + N_a N_b + N_c = P_c + P_a N_b + N_a P_b` between the parts
of three packed code tables with `na`, `nb` and `nc` slots of width `W`. -/
def zigzagProductCheck (W na nb nc A B C : ℕ) : Bool :=
  Nat.beq
    (Nat.add (Nat.add (Nat.mul (zigzagPositive W na A) (zigzagPositive W nb B))
      (Nat.mul (zigzagNegative W na A) (zigzagNegative W nb B))) (zigzagNegative W nc C))
    (Nat.add (Nat.add (zigzagPositive W nc C)
      (Nat.mul (zigzagPositive W na A) (zigzagNegative W nb B)))
      (Nat.mul (zigzagNegative W na A) (zigzagPositive W nb B)))

/-- A successful natural check multiplies the signed parts. -/
theorem zigzagProductCheck_sound {W na nb nc A B C : ℕ}
    (h : zigzagProductCheck W na nb nc A B C = true) :
    ((zigzagPositive W na A : ℤ) - zigzagNegative W na A) *
        ((zigzagPositive W nb B : ℤ) - zigzagNegative W nb B) =
      (zigzagPositive W nc C : ℤ) - zigzagNegative W nc C := by
  have hz := congrArg (Nat.cast : ℕ → ℤ) (Nat.eq_of_beq_eq_true h)
  push_cast [Nat.add_eq, Nat.mul_eq] at hz
  linear_combination hz

/-- **Packed products of slot-block tables.** The natural check of the spread codes multiplies
the signed packings of the three trees. -/
theorem packSignedBinary_mul_of_zigzag {bits l q wa wb wc da db dc Da Db Dc : ℕ}
    {ba bb bc : ℕ → ℕ} (hq : q = 2 ^ l) (hda : da = l + Da) (hdb : db = l + Db)
    (hdc : dc = l + Dc) (hwa : wa ≤ bits) (hwb : wb ≤ bits) (hwc : wc ≤ bits)
    (h : zigzagProductCheck bits (2 ^ (l + Da)) (2 ^ (l + Db)) (2 ^ (l + Dc))
      (spreadBlocks wa bits l ba Da 0) (spreadBlocks wb bits l bb Db 0)
      (spreadBlocks wc bits l bc Dc 0) = true) :
    packSignedBinary bits (CoefficientTree.ofFnBlock (blockSlot wa q ba) da 0) *
        packSignedBinary bits (CoefficientTree.ofFnBlock (blockSlot wb q bb) db 0) =
      packSignedBinary bits (CoefficientTree.ofFnBlock (blockSlot wc q bc) dc 0) := by
  rw [packSignedBinary_ofBlocks hwa hq hda, packSignedBinary_ofBlocks hwb hq hdb,
    packSignedBinary_ofBlocks hwc hq hdc]
  exact zigzagProductCheck_sound h

/-- **Signed products of slot-block tables.** With codes below `2 ^ wa`, `2 ^ wb` and `2 ^ wc`
fitting the packing digit, the natural check of the spread codes passes `signedProductCheck`. -/
theorem signedProductCheck_of_zigzag {bits l q wa wb wc da db dc Da Db Dc : ℕ}
    {ba bb bc : ℕ → ℕ} (hq : q = 2 ^ l) (hda : da = l + Da) (hdb : db = l + Db)
    (hdc : dc = l + Dc) (hmass : 2 ^ (da + wa) * 2 ^ (db + wb) + 2 ^ (dc + wc) < 2 ^ bits)
    (h : zigzagProductCheck bits (2 ^ (l + Da)) (2 ^ (l + Db)) (2 ^ (l + Dc))
      (spreadBlocks wa bits l ba Da 0) (spreadBlocks wb bits l bb Db 0)
      (spreadBlocks wc bits l bc Dc 0) = true) :
    signedProductCheck bits (CoefficientTree.ofFnBlock (blockSlot wa q ba) da 0)
      (CoefficientTree.ofFnBlock (blockSlot wb q bb) db 0)
      (CoefficientTree.ofFnBlock (blockSlot wc q bc) dc 0) = true := by
  have hwa : wa ≤ bits := by
    by_contra hlt
    have h1 : 2 ^ bits ≤ 2 ^ (da + wa) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (da + wa) ≤ 2 ^ (da + wa) * 2 ^ (db + wb) :=
      Nat.le_mul_of_pos_right _ (by positivity)
    exact absurd hmass (not_lt.mpr (h1.trans (h2.trans (Nat.le_add_right _ _))))
  have hwb : wb ≤ bits := by
    by_contra hlt
    have h1 : 2 ^ bits ≤ 2 ^ (db + wb) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (db + wb) ≤ 2 ^ (da + wa) * 2 ^ (db + wb) :=
      Nat.le_mul_of_pos_left _ (by positivity)
    exact absurd hmass (not_lt.mpr (h1.trans (h2.trans (Nat.le_add_right _ _))))
  have hwc : wc ≤ bits := by
    by_contra hlt
    have h1 : 2 ^ bits ≤ 2 ^ (dc + wc) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact absurd hmass (not_lt.mpr (h1.trans (Nat.le_add_left _ _)))
  unfold signedProductCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, packSignedBinary_mul_of_zigzag hq hda hdb hdc hwa hwb hwc h⟩
  have ha := signedMass_ofFnBlock_le (f := blockSlot wa q ba) (fun _ ↦ slot_lt wa _ _) da 0
  have hb := signedMass_ofFnBlock_le (f := blockSlot wb q bb) (fun _ ↦ slot_lt wb _ _) db 0
  have hc := signedMass_ofFnBlock_le (f := blockSlot wc q bc) (fun _ ↦ slot_lt wc _ _) dc 0
  have hmass' : (2 : ℤ) ^ (da + wa) * 2 ^ (db + wb) + 2 ^ (dc + wc) < 2 ^ bits := by
    exact_mod_cast hmass
  have hab := mul_le_mul ha hb (signedMass_nonneg _) (by positivity)
  linarith

end CAS.Numerics

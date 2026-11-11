/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedSlots
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

/-!
# Integer linear algebra on packed rows

A row of `q` signed integers is one natural number with `q` biased slots of width `w`
(`biasedPack`). `packedRowCombination w q n α s rows` forms the integer combination
`∑ j, (s j - α) • row j` of `n` packed rows, each coefficient given by a natural number `s j`
and the common offset `α`; when every entry of the result fits its slot, the slots of the
result are the entries (`signedSlot_packedRowCombination`). The coefficients are slots of
another packed row (`signedSlot_packedRowCombination_slots`), or biased integers.

On finite matrices, `packedMatMul` evaluates one packed row combination per output row.
`packedMatMul_eq` needs only the entry bounds `|A i j| ≤ a`, `|B j k| ≤ b` and
`2 * n * a * b < 2 ^ w`, which make every output entry fit.

The entry bounds come from the packed rows themselves: a passing `signedGuardCheck w g n x`
places every signed slot of `x` within `slotBias g` (`fitsSlot_of_signedGuardCheck`), and
`signedSlot_eq_zero_of_land` reads zero entries below a slot from one conjunction. `slotAbs`
is the absolute value of one signed slot.

## Implementation notes

We stay in natural numbers for the reasons given in [PackedSlots](PackedSlots.lean). With
`S = ∑ rows j`, `σ = ∑ s j` and the bias row `H = biasRow w q`, the combination is
`(∑ s j * rows j + (n α + 1) H) - (α S + σ H)`. Every row is its signed row plus `H`, so the
subtracted terms remove the bias of every row and the offset `α` of every coefficient, and one
`H` remains as the bias of the result. Intermediate values carry between slots, since a slot
of `s j * rows j` can reach `s j (2 ^ w - 1)`. `cast_packedRowCombination` proves the identity
in the integers, where the truncated subtraction is exact once the entries fit, and
`signedSlot_eq_of_cast_eq` reads the entries back; the only hypotheses are that every row is
below `2 ^ (w q)` and that every entry of the result fits. The sums are `natSum`, a `Nat.rec`
over `Nat.add`, so a combination of `n` rows costs `n` products of a coefficient with a row,
`2 n` additions of rows and `n` additions of coefficients, plus a few operations for the bias
terms. Compiled code evaluates the same definitions.

`signedGuardCheck` compares `x` with `2 ^ (w n)`, adds `signedGuardOffset` (`slotBias g` in
every slot) and takes two conjunctions of the sum, with `signedGuardMask` and with `biasRow`;
the offset and both masks are `constSlots` rows. A signed slot `c` that fits `g` bits becomes
`2 ^ (w - 1) + c + slotBias g`: its top bit is set and its bits `g` through `w - 2` are clear.
Conversely, the top bits exclude carries: an entry that overflowed its slot would leave the
lowest such slot below the bias, with its top bit clear (`lt_two_pow_of_slotBias_le_slot`).
Certificates evaluate the checks in the kernel, as the row checks of [PackedLDL](PackedLDL.lean)
are evaluated by `decide` in [MatrixPositivity](../Examples/Numerics/MatrixPositivity.lean);
`fitsSlot_of_signedGuardCheck` is proved once for all inputs with `g < w`. `slotAbs` adds the
two truncated differences of the slot and the bias, one of which is zero.

`packedRowCombination` is the common step of the packed certificates: it is used by
[PackedLDL](PackedLDL.lean), [LowRankLDL](LowRankLDL.lean), [TwoStageRows](TwoStageRows.lean),
[RowStages](RowStages.lean), [SeparableRows](SeparableRows.lean),
[PackedListComb](PackedListComb.lean) and six other modules. `zGuard` of
[PackedSignedRows](PackedSignedRows.lean) is `signedGuardCheck` on a biased integer, and
[WeightedAbsSums](WeightedAbsSums.lean) uses `slotAbs`. `packedMatMul` has no other user in the
library: it states the method for finite matrices.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- The row of `q` slots of width `w`, each holding the bias `slotBias w`. -/
def biasRow (w q : ℕ) : ℕ := constSlots w q (slotBias w)

/-- The bias row is the packing of `q` copies of `slotBias w`, for every width `w`. -/
theorem biasRow_eq_packSlots (w q : ℕ) : biasRow w q = packSlots w q (fun _ ↦ slotBias w) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · have h0 : slotBias 0 = 0 := rfl
    simp [biasRow, constSlots, h0, packSlots_eq_sum]
  · exact constSlots_eq hw q _

/-- The integer value of the bias row is `∑ k ∈ range q, slotBias w * 2 ^ (w * k)`. -/
theorem cast_biasRow (w q : ℕ) :
    (biasRow w q : ℤ) = ∑ k ∈ range q, (slotBias w : ℤ) * 2 ^ (w * k) := by
  rw [biasRow_eq_packSlots, packSlots_eq_sum]
  push_cast
  rfl

/-- The biased packed row `∑ j < n, (s j - α) • Z j`, where `Z j` is the signed row stored in
`rows j` with `q` slots of width `w`. -/
def packedRowCombination (w q n α : ℕ) (s rows : ℕ → ℕ) : ℕ :=
  Nat.sub
    (Nat.add (natSum n (fun j ↦ Nat.mul (s j) (rows j)))
      (Nat.mul (Nat.add (Nat.mul n α) 1) (biasRow w q)))
    (Nat.add (Nat.mul α (natSum n rows)) (Nat.mul (natSum n s) (biasRow w q)))

/-- When every entry of the combination fits its slot, the packed combination is the biased
expansion of its entries. -/
theorem cast_packedRowCombination {w q n α : ℕ} {s rows : ℕ → ℕ}
    (hrows : ∀ j < n, rows j < 2 ^ (w * q))
    (hfit : ∀ k < q,
      FitsSlot w (∑ j ∈ range n, ((s j : ℤ) - α) * signedSlot w k (rows j))) :
    (packedRowCombination w q n α s rows : ℤ) = ∑ k ∈ range q,
      (∑ j ∈ range n, ((s j : ℤ) - α) * signedSlot w k (rows j) + slotBias w) * 2 ^ (w * k) := by
  set c : ℕ → ℤ := fun k ↦ ∑ j ∈ range n, ((s j : ℤ) - α) * signedSlot w k (rows j)
  set H := biasRow w q
  set Z : ℕ → ℤ := fun j ↦ ∑ k ∈ range q, signedSlot w k (rows j) * 2 ^ (w * k)
  have hrowsZ : ∀ j ∈ range n, (rows j : ℤ) = Z j + H := by
    intro j hj
    rw [cast_eq_sum_signedSlot (hrows j (mem_range.mp hj)), cast_biasRow, ← sum_add_distrib]
    exact sum_congr rfl fun k _ ↦ by ring
  have hV : ∑ k ∈ range q, (c k + slotBias w) * 2 ^ (w * k) =
      ∑ j ∈ range n, ((s j : ℤ) - α) * Z j + H := by
    rw [cast_biasRow]
    simp only [c, Z, add_mul, sum_add_distrib, sum_mul, mul_sum]
    congr 1
    rw [sum_comm]
    exact sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ by ring
  have hU : (natSum n (fun j ↦ s j * rows j) : ℤ) = ∑ j ∈ range n, (s j : ℤ) * (Z j + H) := by
    rw [natSum_eq_sum, Nat.cast_sum]
    exact sum_congr rfl fun j hj ↦ by rw [Nat.cast_mul, hrowsZ j hj]
  have hS : (natSum n rows : ℤ) = ∑ j ∈ range n, (Z j + H) := by
    rw [natSum_eq_sum, Nat.cast_sum]
    exact sum_congr rfl hrowsZ
  have hσ : (natSum n s : ℤ) = ∑ j ∈ range n, (s j : ℤ) := by rw [natSum_eq_sum, Nat.cast_sum]
  have key : ((natSum n (fun j ↦ s j * rows j) + (n * α + 1) * H : ℕ) : ℤ) -
      ((α * natSum n rows + natSum n s * H : ℕ) : ℤ) =
      ∑ k ∈ range q, (c k + slotBias w) * 2 ^ (w * k) := by
    push_cast
    rw [hU, hS, hσ, hV]
    simp only [mul_add, sum_add_distrib, sub_mul, sum_sub_distrib, mul_sum, sum_mul,
      sum_const, card_range, nsmul_eq_mul]
    ring
  have hnonneg : 0 ≤ ∑ k ∈ range q, (c k + slotBias w) * 2 ^ (w * k) :=
    sum_nonneg fun k hk' ↦ mul_nonneg (hfit k (mem_range.mp hk')).1 (by positivity)
  have hle : α * natSum n rows + natSum n s * H ≤
      natSum n (fun j ↦ s j * rows j) + (n * α + 1) * H := Int.ofNat_le.1 (by linarith)
  change (((natSum n (fun j ↦ s j * rows j) + (n * α + 1) * H) -
    (α * natSum n rows + natSum n s * H) : ℕ) : ℤ) = _
  rw [Nat.cast_sub hle, key]

/-- When every entry of the combination fits its slot, the slots of the packed combination
are its entries. -/
theorem signedSlot_packedRowCombination {w q n α : ℕ} {s rows : ℕ → ℕ}
    (hrows : ∀ j < n, rows j < 2 ^ (w * q))
    (hfit : ∀ k < q,
      FitsSlot w (∑ j ∈ range n, ((s j : ℤ) - α) * signedSlot w k (rows j)))
    {k : ℕ} (hk : k < q) :
    signedSlot w k (packedRowCombination w q n α s rows) =
      ∑ j ∈ range n, ((s j : ℤ) - α) * signedSlot w k (rows j) :=
  signedSlot_eq_of_cast_eq hfit (cast_packedRowCombination hrows hfit) hk

/-- The combination with coefficients read from the slots of a packed row `coefficients` of
width `wc`. -/
theorem signedSlot_packedRowCombination_slots {wc w q n coefficients : ℕ} {rows : ℕ → ℕ}
    (hrows : ∀ j < n, rows j < 2 ^ (w * q))
    (hfit : ∀ k < q,
      FitsSlot w (∑ j ∈ range n, signedSlot wc j coefficients * signedSlot w k (rows j)))
    {k : ℕ} (hk : k < q) :
    signedSlot w k (packedRowCombination w q n (slotBias wc)
        (fun j ↦ slot wc j coefficients) rows) =
      ∑ j ∈ range n, signedSlot wc j coefficients * signedSlot w k (rows j) :=
  signedSlot_packedRowCombination hrows hfit hk

/-- A sum of `n` products of entries bounded by `a` and `b` fits when `2 * n * a * b < 2 ^ w`. -/
theorem fitsSlot_sum_mul {w n a b : ℕ} {x y : ℕ → ℤ} (hx : ∀ j < n, (x j).natAbs ≤ a)
    (hy : ∀ j < n, (y j).natAbs ≤ b) (hw : 2 * n * a * b < 2 ^ w) :
    FitsSlot w (∑ j ∈ range n, x j * y j) := by
  apply fitsSlot_of_natAbs_le (m := n * a * b) _ (by linarith)
  have h : |∑ j ∈ range n, x j * y j| ≤ (n * a * b : ℕ) := by
    refine (abs_sum_le_sum_abs _ _).trans
      ((sum_le_card_nsmul _ _ ((a * b : ℕ) : ℤ) fun j hj ↦ ?_).trans_eq ?_)
    · rw [abs_mul]
      push_cast
      exact mul_le_mul ((Int.abs_eq_natAbs _).trans_le (by exact_mod_cast hx j (mem_range.mp hj)))
        ((Int.abs_eq_natAbs _).trans_le (by exact_mod_cast hy j (mem_range.mp hj)))
        (abs_nonneg _) (by positivity)
    · rw [card_range, nsmul_eq_mul]
      push_cast
      ring
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

/-! ### Absolute values of slots -/

/-- The absolute value of a signed slot, by truncated subtraction of the bias. -/
def slotAbs (w k x : ℕ) : ℕ :=
  Nat.add (Nat.sub (slot w k x) (slotBias w)) (Nat.sub (slotBias w) (slot w k x))

/-- `slotAbs w k x` is the absolute value of the signed slot `signedSlot w k x`. -/
theorem cast_slotAbs (w k x : ℕ) : (slotAbs w k x : ℤ) = |signedSlot w k x| := by
  change ((slot w k x - slotBias w + (slotBias w - slot w k x) : ℕ) : ℤ) = _
  rw [signedSlot, Int.abs_eq_natAbs]
  omega

/-! ### Entry bounds of packed rows -/

/-- The offset `slotBias g` in each of the first `n` slots of width `w`. -/
def signedGuardOffset (w g n : ℕ) : ℕ := constSlots w n (slotBias g)

/-- The bits `g` through `w - 2` of each of the first `n` slots of width `w`. -/
def signedGuardMask (w g n : ℕ) : ℕ := constSlots w n (guardSlot (Nat.sub w 1) g)

/-- `x < 2 ^ (w n)` and every one of the first `n` signed slots of `x` fits a slot of width `g`,
checked with one comparison, one addition and two conjunctions: after adding `slotBias g` to
every slot, each slot has its top bit `w - 1` set and the bits `g` through `w - 2` clear. -/
def signedGuardCheck (w g n x : ℕ) : Bool :=
  Nat.blt x (Nat.shiftLeft 1 (Nat.mul w n)) &&
    Nat.beq (Nat.land (Nat.add x (signedGuardOffset w g n)) (signedGuardMask w g n)) 0 &&
    Nat.beq (Nat.land (Nat.add x (signedGuardOffset w g n)) (biasRow w n)) (biasRow w n)

/-- A passing guard check makes every signed slot fit `g` bits; the added offset never carries
between slots, since a carry would leave the top bit of its slot clear. -/
theorem fitsSlot_of_signedGuardCheck {w g n x : ℕ} (hg : g < w)
    (h : signedGuardCheck w g n x = true) {k : ℕ} (hk : k < n) :
    FitsSlot g (signedSlot w k x) := by
  simp only [signedGuardCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hx, hmid⟩, htop⟩ := h
  have hx' : x < 2 ^ (w * n) := by
    have := Nat.blt_eq.mp hx
    change x < 1 <<< (w * n) at this
    rwa [Nat.one_shiftLeft] at this
  have hmid' := Nat.eq_of_beq_eq_true hmid
  have htop' := Nat.eq_of_beq_eq_true htop
  have hw : w = (w - 1) + 1 := by omega
  have hbias : slotBias w = 2 ^ (w - 1) := by rw [hw, slotBias_succ, Nat.add_sub_cancel]
  set y := x + signedGuardOffset w g n
  have hw0 : 0 < w := by omega
  have hy : y = packSlots w n (fun k ↦ slot w k x + slotBias g) := by
    change x + signedGuardOffset w g n = _
    rw [signedGuardOffset, constSlots_eq hw0]
    conv_lhs => rw [← packSlots_slot hx']
    exact packSlots_add w n _ _
  -- the top bit of every slot of `y` is set
  have htopbit : ∀ k < n, (slot w k y).testBit (w - 1) = true := by
    intro k hk
    have hslotT : slot w k (biasRow w n) = 2 ^ (w - 1) := by
      rw [biasRow_eq_packSlots, slot_packed_eq (fun _ _ ↦ slotBias_lt w), ite_eq_left hk,
        hbias]
    have hT : (biasRow w n).testBit (w * k + (w - 1)) = true := by
      have := testBit_slot w k (biasRow w n) (w - 1)
      rw [hslotT, Nat.testBit_two_pow_self] at this
      simpa [show w - 1 < w by omega] using this.symm
    have hand := congrArg (fun z ↦ z.testBit (w * k + (w - 1))) htop'
    change (y &&& biasRow w n).testBit _ = _ at hand
    rw [Nat.testBit_and, hT, Bool.and_true] at hand
    rw [testBit_slot]
    simp [show w - 1 < w by omega, hand]
  have hge : ∀ k < n,
      slotBias w ≤ slot w k (packSlots w n (fun k ↦ slot w k x + slotBias g)) := by
    intro k hk
    rw [← hy, hbias]
    exact Nat.ge_two_pow_of_testBit (htopbit k hk)
  have hu : ∀ k < n, slot w k x + slotBias g < 2 ^ w + slotBias w := by
    intro k _
    have := slot_lt w k x
    have := slotBias_le_slotBias hg.le
    omega
  have hfit := lt_two_pow_of_slotBias_le_slot hu hge
  have hslot : slot w k y = slot w k x + slotBias g := by
    rw [hy, slot_packed_eq hfit, ite_eq_left hk]
  -- the bits `g` through `w - 2` of slot `k` of `y` are clear
  have hlow : slot w k y % 2 ^ (w - 1) < 2 ^ g := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [Nat.testBit_mod_two_pow]
    by_cases hiw : i < w - 1
    · have hgs : guardSlot (Nat.sub w 1) g < 2 ^ w :=
        (guardSlot_lt _ _).trans_le (Nat.pow_le_pow_right two_pos (Nat.sub_le w 1))
      have hslotM : slot w k (signedGuardMask w g n) = guardSlot (Nat.sub w 1) g := by
        rw [signedGuardMask, constSlots_eq hw0,
          slot_packed_eq (f := fun _ ↦ guardSlot (Nat.sub w 1) g) (fun _ _ ↦ hgs),
          ite_eq_left hk]
      have hM : (signedGuardMask w g n).testBit (w * k + i) = true := by
        have := testBit_slot w k (signedGuardMask w g n) i
        rw [hslotM, testBit_guardSlot] at this
        simpa [show g ≤ i from hi, show i < w - 1 from hiw, show i < w by omega] using
          this.symm
      have hand := congrArg (fun z ↦ z.testBit (w * k + i)) hmid'
      change (y &&& signedGuardMask w g n).testBit _ = (0 : ℕ).testBit _ at hand
      rw [Nat.testBit_and, hM, Bool.and_true, Nat.zero_testBit] at hand
      rw [testBit_slot]
      simp [hiw, hand]
    · simp [hiw]
  have hsplit : slot w k y = slot w k y % 2 ^ (w - 1) + 2 ^ (w - 1) := by
    have hlt : slot w k y < 2 ^ (w - 1) * 2 := by
      rw [← pow_succ, ← hw]
      exact slot_lt w k y
    have hge' : 2 ^ (w - 1) ≤ slot w k y := Nat.ge_two_pow_of_testBit (htopbit k hk)
    rw [Nat.mod_eq_sub_mod hge', Nat.mod_eq_of_lt (by omega)]
    omega
  have hval : signedSlot w k x + slotBias g = ((slot w k y % 2 ^ (w - 1) : ℕ) : ℤ) := by
    rw [signedSlot]
    omega
  rw [FitsSlot, hval]
  exact ⟨by positivity, by exact_mod_cast hlow⟩

/-- A passing guard check bounds every signed slot by `slotBias g = 2 ^ (g - 1)`. -/
theorem natAbs_signedSlot_le_of_signedGuardCheck {w g n x : ℕ} (hg : g < w)
    (h : signedGuardCheck w g n x = true) {k : ℕ} (hk : k < n) :
    (signedSlot w k x).natAbs ≤ slotBias g :=
  natAbs_le_of_fitsSlot (fitsSlot_of_signedGuardCheck hg h hk)

/-- A passing guard check bounds the packed number by `2 ^ (w * n)`. -/
theorem lt_of_signedGuardCheck {w g n x : ℕ} (h : signedGuardCheck w g n x = true) :
    x < 2 ^ (w * n) := by
  simp only [signedGuardCheck, Bool.and_eq_true] at h
  have := Nat.blt_eq.mp h.1.1
  change x < 1 <<< (w * n) at this
  rwa [Nat.one_shiftLeft] at this

/-- Slots below `m` equal to the bias are zero entries. -/
theorem signedSlot_eq_zero_of_land {w m x : ℕ}
    (h : Nat.land x (slotMask (Nat.mul w m)) = biasRow w m) {j : ℕ} (hj : j < m) :
    signedSlot w j x = 0 := by
  have hmod : x % 2 ^ (w * m) = biasRow w m := by
    rw [← Nat.and_two_pow_sub_one_eq_mod, ← slotMask_eq]
    exact h
  rw [signedSlot, ← slot_mod_two_pow hj x, hmod, biasRow_eq_packSlots,
    slot_packed_eq (fun _ _ ↦ slotBias_lt w), ite_eq_left hj, sub_self]

/-! ### Finite matrices -/

/-- A finite matrix read at natural indices, with zero outside its range. -/
def extendMatrix {n q : ℕ} (B : Fin n → Fin q → ℤ) (j k : ℕ) : ℤ :=
  if hj : j < n then (if hk : k < q then B ⟨j, hj⟩ ⟨k, hk⟩ else 0) else 0

/-- At indices in range, the extended matrix reads the matrix: `extendMatrix B j k = B j k`. -/
theorem extendMatrix_of_lt {n q : ℕ} (B : Fin n → Fin q → ℤ) (j : Fin n) (k : Fin q) :
    extendMatrix B j.val k.val = B j k := by
  simp [extendMatrix]

/-- Row `i` of the product `A B`, packed with bias in `q` slots of width `w`. -/
def packedMatMulRow (w : ℕ) {p n q : ℕ} (A : Fin p → Fin n → ℤ) (B : Fin n → Fin q → ℤ)
    (i : Fin p) : ℕ :=
  packedRowCombination w q n (slotBias w)
    (fun j ↦ encodeSlot w (extendMatrix A i.val j))
    (fun j ↦ biasedPack w q (extendMatrix B j))

/-- The product `A B` of integer matrices by packed row combinations in slots of width `w`. -/
def packedMatMul (w : ℕ) {p n q : ℕ} (A : Fin p → Fin n → ℤ) (B : Fin n → Fin q → ℤ) :
    Fin p → Fin q → ℤ :=
  fun i k ↦ signedSlot w k.val (packedMatMulRow w A B i)

/-- With the bounds of `packedMatMul_eq`, the clamped encodings of both factors give the
exact products. -/
private theorem encoded_products {w p n q a b : ℕ} {A : Fin p → Fin n → ℤ}
    {B : Fin n → Fin q → ℤ} (ha : ∀ i j, (A i j).natAbs ≤ a) (hb : ∀ j k, (B j k).natAbs ≤ b)
    (hw : 2 * n * a * b < 2 ^ w) (i : Fin p) (j : Fin n) (k : Fin q) :
    ((encodeSlot w (A i j) : ℤ) - slotBias w) * (encodeSlot w (B j k) - slotBias w) =
      A i j * B j k := by
  have hzero : FitsSlot w 0 :=
    ⟨by positivity, by simpa using (by exact_mod_cast slotBias_lt w : (slotBias w : ℤ) < 2 ^ w)⟩
  by_cases ha0 : a = 0
  · have hA : A i j = 0 := Int.natAbs_eq_zero.mp (Nat.le_zero.mp (ha0 ▸ ha i j))
    rw [hA, encodeSlot_of_fits hzero]
    ring
  by_cases hb0 : b = 0
  · have hB : B j k = 0 := Int.natAbs_eq_zero.mp (Nat.le_zero.mp (hb0 ▸ hb j k))
    rw [hB, encodeSlot_of_fits hzero]
    ring
  have hn : 0 < n := Fin.pos j
  have hA : FitsSlot w (A i j) := fitsSlot_of_natAbs_le (ha i j) (by
    linarith [(Nat.le_mul_of_pos_left a hn).trans
      (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hb0))])
  have hB : FitsSlot w (B j k) := fitsSlot_of_natAbs_le (hb j k) (by
    linarith [Nat.le_mul_of_pos_left b (Nat.mul_pos hn (Nat.pos_of_ne_zero ha0))])
  rw [encodeSlot_of_fits hA, encodeSlot_of_fits hB]
  ring

/-- The signed slots of a packed product row are the entries of the product. -/
theorem signedSlot_packedMatMulRow (w : ℕ) {p n q : ℕ} (A : Fin p → Fin n → ℤ)
    (B : Fin n → Fin q → ℤ) {a b : ℕ} (ha : ∀ i j, (A i j).natAbs ≤ a)
    (hb : ∀ j k, (B j k).natAbs ≤ b) (hw : 2 * n * a * b < 2 ^ w) (i : Fin p) (k : Fin q) :
    signedSlot w k.val (packedMatMulRow w A B i) = ∑ j, A i j * B j k := by
  have hterm : ∀ (k : Fin q), ∀ j ∈ range n,
      ((encodeSlot w (extendMatrix A i.val j) : ℤ) - slotBias w) *
        signedSlot w k.val (biasedPack w q (extendMatrix B j)) =
      extendMatrix A i.val j * extendMatrix B j k.val := by
    intro k j hj
    have hj' := mem_range.mp hj
    rw [signedSlot, biasedPack, slot_packed_eq (fun k _ ↦ encodeSlot_lt w _), ite_eq_left k.isLt]
    have h := encoded_products ha hb hw i ⟨j, hj'⟩ k
    rw [extendMatrix_of_lt A i ⟨j, hj'⟩] at *
    rw [show extendMatrix B j k.val = B ⟨j, hj'⟩ k from extendMatrix_of_lt B ⟨j, hj'⟩ k]
    exact h
  have hsum0 : ∀ k : Fin q, ∑ j ∈ range n, extendMatrix A i.val j * extendMatrix B j k.val =
      ∑ j, A i j * B j k := fun k ↦ by
    rw [← Fin.sum_univ_eq_sum_range (fun j ↦ extendMatrix A i.val j * extendMatrix B j k.val)]
    exact sum_congr rfl fun j _ ↦ by rw [extendMatrix_of_lt, extendMatrix_of_lt]
  have hsum : ∀ k : Fin q, ∑ j ∈ range n,
      ((encodeSlot w (extendMatrix A i.val j) : ℤ) - slotBias w) *
        signedSlot w k.val (biasedPack w q (extendMatrix B j)) = ∑ j, A i j * B j k := fun k ↦ by
    rw [sum_congr rfl (hterm k), hsum0]
  have hfit : ∀ k : Fin q, FitsSlot w (∑ j, A i j * B j k) := fun k ↦ hsum0 k ▸ fitsSlot_sum_mul
    (fun j hj ↦ (congrArg Int.natAbs (extendMatrix_of_lt A i ⟨j, hj⟩)).trans_le (ha _ _))
    (fun j hj ↦ (congrArg Int.natAbs (extendMatrix_of_lt B ⟨j, hj⟩ k)).trans_le (hb _ _)) hw
  rw [packedMatMulRow, signedSlot_packedRowCombination (fun j _ ↦ biasedPack_lt w q _)
    (fun k hk ↦ by rw [hsum ⟨k, hk⟩]; exact hfit ⟨k, hk⟩) k.isLt, hsum k]

/-- **Packed matrix products.** If `|A i j| ≤ a` and `|B j k| ≤ b` for all indices and
`2 * n * a * b < 2 ^ w`, then `packedMatMul w A B` is the matrix product
`fun i k ↦ ∑ j, A i j * B j k`. -/
theorem packedMatMul_eq (w : ℕ) {p n q : ℕ} (A : Fin p → Fin n → ℤ) (B : Fin n → Fin q → ℤ)
    {a b : ℕ} (ha : ∀ i j, (A i j).natAbs ≤ a) (hb : ∀ j k, (B j k).natAbs ≤ b)
    (hw : 2 * n * a * b < 2 ^ w) :
    packedMatMul w A B = fun i k ↦ ∑ j, A i j * B j k :=
  funext fun i ↦ funext fun k ↦ signedSlot_packedMatMulRow w A B ha hb hw i k

end CAS.Numerics

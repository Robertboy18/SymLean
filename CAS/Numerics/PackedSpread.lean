/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedSignedWindows
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# Spreading packed slots by one multiplication

`spreadSlots w S n x` moves the slots `0, …, n - 1` (width `w`) of `x` to the slots of width
`w S`, for a stride `S > n` (`spreadSlots_eq`).

For products of packed rows, `packSlots_mul_spread` places all products `a x * b y` of a row of
`n ≤ S` slots and a row of stride `S` at the slots `x + S y`, the Kronecker product of the two
vectors in one multiplication. `land_packSlots_mask` keeps the slots selected by a mask,
`shiftRight_packSlots` moves a row down by whole slots, `packSlots_regroup` regroups the slots
at multiples of `S` into slots of width `w S`, and `le_of_sub_constSlots` reads from one
subtraction of a constant row that every slot is at least `c`, provided the row is at least the
constant row and no slot of the difference reaches `2 ^ w - c`.

## Implementation notes

The multiplier `constSlots (w (S - 1)) n 1` is `∑_{r < n} 2 ^ (w (S - 1) r)`, so the product
with `x` is the sum of `n` copies of `x`, the copy `r` shifted by `w (S - 1) r`. It holds the
entry `k` of `x` at slot `k + (S - 1) r` of width `w` for every `r`. For `k, r < n < S` these
positions are pairwise distinct, so the product has no carries and every slot holds at most one
entry (`slot_sum_distinct`); a position is a multiple of `S` exactly when `r = k`, and then it
is `S k`, the low `w` bits of slot `k` of width `w S`. The mask `constSlots (w S) n (2 ^ w - 1)`
keeps these bits and clears the other copies (`slot_land`). So we spread a row with one
multiplication and one `and`, both constants being `constSlots` rows as in
[PackedSlots](PackedSlots.lean), instead of reading and placing the `n` slots one by one. The
hypotheses of `spreadSlots_eq` are `n < S`, which keeps the positions distinct, and
`x < 2 ^ (w n)`, which makes `x` the pack of its first `n` slots.

`packSlots_mul_spread` rests on the same argument for two rows, whose products land at the
distinct slots `x + S y`; it is an identity of sums with no bound on the entries, and reading a
product from its slot needs the product below `2 ^ w`. `le_of_sub_constSlots` replaces `N`
comparisons by one subtraction: if some slot were below `c`, the lowest such slot would borrow
and leave at least `2 ^ w - c` in the difference.
[PackedSignedRows](PackedSignedRows.lean) spreads biased rows with `spreadSlots_eq`
(`spreadSlots_biased`, for factors at a stride) and shifts rows with `shiftRight_packSlots`,
[ZigzagBlocks](ZigzagBlocks.lean) masks rows with `land_packSlots_mask`,
[PackedAppend](PackedAppend.lean) reads its lower bounds with `le_of_sub_constSlots`, and
[PackedRoundComb](PackedRoundComb.lean) uses `slot_land`. `packSlots_mul_spread` and
`packSlots_regroup` have no user in the library; certificates outside it use them.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- The slots `0, …, n - 1` of `x` spread to slots of width `w * S`. -/
def spreadSlots (w S n x : ℕ) : ℕ :=
  Nat.land (Nat.mul x (constSlots (w * (S - 1)) n 1)) (constSlots (w * S) n (2 ^ w - 1))

/-- Slot `k` of `Nat.land x y` is the conjunction of slot `k` of `x` and slot `k` of `y`. -/
theorem slot_land (w k x y : ℕ) : slot w k (Nat.land x y) = Nat.land (slot w k x) (slot w k y) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (slot w k (x &&& y)).testBit i = (slot w k x &&& slot w k y).testBit i
  rw [Nat.testBit_and, testBit_slot, testBit_slot, testBit_slot, Nat.testBit_and]
  cases decide (i < w) <;> simp

/-- A slot of a sum of entries below `2 ^ w` at pairwise distinct slots is the entry placed
there, if any. -/
theorem slot_sum_distinct {ι : Type*} {w : ℕ} (T : Finset ι) (pos : ι → ℕ)
    (v : ι → ℕ)
    (hinj : ∀ a ∈ T, ∀ b ∈ T, pos a = pos b → a = b) (hv : ∀ a ∈ T, v a < 2 ^ w) (P : ℕ) :
    slot w P (∑ a ∈ T, v a * 2 ^ (w * pos a)) =
      ∑ a ∈ T.filter (fun a ↦ pos a = P), v a := by
  set N := T.sup pos + 1
  have hN : ∀ a ∈ T, pos a < N := fun a ha ↦ Nat.lt_succ_of_le (Finset.le_sup ha)
  have hfib : ∑ a ∈ T, v a * 2 ^ (w * pos a) =
      packSlots w N fun p ↦ ∑ a ∈ T.filter (fun a ↦ pos a = p), v a := by
    rw [packSlots_eq_sum]
    simp only [sum_mul]
    rw [← sum_fiberwise_of_maps_to (s := T) (t := range N) (g := pos)
      (fun a ha ↦ mem_range.mpr (hN a ha))]
    refine sum_congr rfl fun p _ ↦ sum_congr rfl fun a ha ↦ ?_
    rw [(mem_filter.mp ha).2]
  have hle : ∀ p, ∑ a ∈ T.filter (fun a ↦ pos a = p), v a < 2 ^ w := by
    intro p
    rcases (T.filter (fun a ↦ pos a = p)).eq_empty_or_nonempty with h | ⟨a, ha⟩
    · rw [h, sum_empty]
      positivity
    · rw [mem_filter] at ha
      rw [sum_eq_single_of_mem a (mem_filter.2 ha) fun b hb hba ↦ absurd
        (hinj b (mem_filter.1 hb).1 a ha.1 ((mem_filter.1 hb).2.trans ha.2.symm)) hba]
      exact hv a ha.1
  rw [hfib, slot_packed_eq (fun p _ ↦ hle p)]
  split_ifs with hP
  · rfl
  · refine (sum_eq_zero fun a ha ↦ absurd ?_ hP).symm
    exact (mem_filter.mp ha).2 ▸ hN a (mem_filter.mp ha).1

/-- For `n < S` and `x < 2 ^ (w * n)`, `spreadSlots w S n x` is the packing in slots of width
`w * S` of the first `n` slots of width `w` of `x`. -/
theorem spreadSlots_eq {w S n x : ℕ} (hS : n < S) (hx : x < 2 ^ (w * n)) :
    spreadSlots w S n x = packSlots (w * S) n fun k ↦ slot w k x := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · obtain rfl : x = 0 := by simpa using hx
    simp [spreadSlots, packSlots_eq_sum, slot_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : x = 0 := by simpa using hx
    simp [spreadSlots, packSlots_eq_sum]
  have hS1 : 0 < w * (S - 1) := Nat.mul_pos hw (by omega)
  have hwS : 0 < w * S := Nat.mul_pos hw (by omega)
  set f : ℕ → ℕ := fun k ↦ slot w k x
  have hxf : x = packSlots w n f := (packSlots_slot hx).symm
  -- the product as a sum over pairs
  have hprod : Nat.mul x (constSlots (w * (S - 1)) n 1) =
      ∑ a ∈ range n ×ˢ range n, f a.1 * 2 ^ (w * (a.1 + (S - 1) * a.2)) := by
    rw [Nat.mul_eq, constSlots_eq hS1, hxf, packSlots_eq_sum, packSlots_eq_sum, sum_mul_sum,
      sum_product]
    refine sum_congr rfl fun k _ ↦ sum_congr rfl fun r _ ↦ ?_
    simp only
    rw [Nat.mul_add, pow_add, show w * (S - 1) * r = w * ((S - 1) * r) by ring]
    ring
  have hpos : ∀ a ∈ range n ×ˢ range n, ∀ b ∈ range n ×ˢ range n,
      a.1 + (S - 1) * a.2 = b.1 + (S - 1) * b.2 → a = b := by
    intro a ha b hb h
    simp only [mem_product, mem_range] at ha hb
    have key : a.2 = b.2 := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hl | hl
      · have := Nat.mul_le_mul_left (S - 1) (show a.2 + 1 ≤ b.2 from hl)
        rw [Nat.mul_add_one] at this
        omega
      · have := Nat.mul_le_mul_left (S - 1) (show b.2 + 1 ≤ a.2 from hl)
        rw [Nat.mul_add_one] at this
        omega
    exact Prod.ext (by rw [key] at h; omega) key
  have hSk : ∀ k, k + (S - 1) * k = S * k := fun k ↦ by
    rw [Nat.sub_one_mul]
    have := Nat.le_mul_of_pos_left k (show 0 < S by omega)
    omega
  have hfw : ∀ a ∈ range n ×ˢ range n, f a.1 < 2 ^ w := fun a _ ↦ slot_lt w _ x
  set y := Nat.mul x (constSlots (w * (S - 1)) n 1)
  have hpw : 2 ^ w ≤ 2 ^ (w * S) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right w (by omega))
  have hres : spreadSlots w S n x < 2 ^ (w * S * n) := by
    refine Nat.and_le_right.trans_lt ?_
    rw [constSlots_eq hwS]
    exact packSlots_lt fun _ _ ↦ by have := Nat.one_le_two_pow (n := w); omega
  rw [← packSlots_slot hres]
  refine packSlots_congr fun k hk ↦ ?_
  unfold spreadSlots
  rw [slot_land, constSlots_eq hwS, slot_packed_eq (fun _ _ ↦ by
      have := Nat.one_le_two_pow (n := w); omega), ite_eq_left hk]
  change (slot (w * S) k y &&& 2 ^ w - 1) = f k
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have h0 (z : ℕ) : slot w 0 z = z % 2 ^ w := by rw [slot_eq]; simp
  rw [← h0, slot_slot_mul (by omega : 0 < S), Nat.add_zero]
  change slot w (S * k) y = f k
  rw [hprod, slot_sum_distinct _ _ _ hpos hfw]
  have : (range n ×ˢ range n).filter (fun a ↦ a.1 + (S - 1) * a.2 = S * k) = {(k, k)} := by
    ext a
    simp only [mem_filter, mem_product, mem_range, mem_singleton]
    constructor
    · rintro ⟨⟨ha1, ha2⟩, h⟩
      exact hpos a (by simp [ha1, ha2]) (k, k) (by simp [hk]) (h.trans (hSk k).symm)
    · rintro rfl
      exact ⟨⟨hk, hk⟩, hSk k⟩
  rw [this, sum_singleton]

/-! ### Kronecker products and masks -/

/-- In an additive commutative monoid, a sum over `q ∈ range (S * m)` is the sum over `y < m` of
the sums over `x < S` of the terms at `q = x + S * y`. -/
theorem sum_range_mul_eq {M : Type*} [AddCommMonoid M] (S m : ℕ) (f : ℕ → M) :
    ∑ q ∈ range (S * m), f q = ∑ y ∈ range m, ∑ x ∈ range S, f (x + S * y) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]
    congr 1
    refine sum_congr rfl fun x _ ↦ ?_
    rw [Nat.add_comm]

/-- The product of a row of `n ≤ S` slots with a row spread to stride `S` holds all products
`a x * b y` at the slots `x + S y`. -/
theorem packSlots_mul_spread {w n S m : ℕ} (hn : n ≤ S) (a b : ℕ → ℕ) :
    packSlots w n a * packSlots (w * S) m b =
      packSlots w (S * m) fun q ↦ if q % S < n then a (q % S) * b (q / S) else 0 := by
  have hS : 0 < S ∨ n = 0 := by omega
  rw [packSlots_eq_sum, packSlots_eq_sum, packSlots_eq_sum, sum_mul_sum, sum_comm,
    sum_range_mul_eq]
  refine sum_congr rfl fun y hy ↦ ?_
  rw [← sum_subset (range_subset_range.2 hn) fun x hx hxn ↦ ?_]
  · refine sum_congr rfl fun x hx ↦ ?_
    rw [mem_range] at hx
    have hxS : x < S := by omega
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hxS, Nat.add_mul_div_left _ _
      (show 0 < S by omega), Nat.div_eq_of_lt hxS, zero_add, hx, ↓reduceIte]
    rw [Nat.mul_add, pow_add, ← mul_assoc w S y, pow_mul]
    ring
  · rw [mem_range] at hx hxn
    simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx, hxn]

/-- `and` with a mask of full and empty slots keeps the full slots. -/
theorem land_packSlots_mask {w N : ℕ} {f : ℕ → ℕ} (hf : ∀ q < N, f q < 2 ^ w) (P : ℕ → Prop)
    [DecidablePred P] :
    Nat.land (packSlots w N f) (packSlots w N fun q ↦ if P q then 2 ^ w - 1 else 0) =
      packSlots w N fun q ↦ if P q then f q else 0 := by
  have hlt₁ : packSlots w N f < 2 ^ (w * N) := packSlots_lt hf
  have hm : ∀ q < N, (if P q then 2 ^ w - 1 else 0) < 2 ^ w := fun q _ ↦ by
    have := Nat.one_le_two_pow (n := w)
    split_ifs <;> omega
  have hr : ∀ q < N, (if P q then f q else 0) < 2 ^ w := fun q hq ↦ by
    split_ifs <;> [exact hf q hq; positivity]
  have hlt₂ : Nat.land (packSlots w N f) (packSlots w N fun q ↦ if P q then 2 ^ w - 1 else 0) <
      2 ^ (w * N) := Nat.and_le_left.trans_lt hlt₁
  refine eq_of_slot_eq hlt₂ (packSlots_lt hr) fun q hq ↦ ?_
  rw [slot_land, slot_packed_eq hf, slot_packed_eq hm, slot_packed_eq hr]
  simp only [hq, ↓reduceIte]
  split_ifs
  · exact Nat.and_two_pow_sub_one_of_lt_two_pow (hf q hq)
  · exact Nat.and_zero _

/-- Shifting a packed row down by `j` slots. -/
theorem shiftRight_packSlots (w N j : ℕ) (f : ℕ → ℕ) (hf : ∀ q < N, f q < 2 ^ w) :
    Nat.shiftRight (packSlots w N f) (w * j) = packSlots w (N - j) fun q ↦ f (q + j) := by
  have hlt : packSlots w N f < 2 ^ (w * N) := packSlots_lt hf
  have hlt' : Nat.shiftRight (packSlots w N f) (w * j) < 2 ^ (w * (N - j)) := by
    change packSlots w N f >>> (w * j) < _
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)))
  have hr : ∀ q < N - j, f (q + j) < 2 ^ w := fun q hq ↦ hf _ (by omega)
  apply eq_of_slot_eq hlt' (packSlots_lt hr)
  intro q hq
  change slot w q (packSlots w N f >>> (w * j)) = _
  rw [Nat.shiftRight_eq_div_pow, slot_div_two_pow, slot_packed_eq hf, slot_packed_eq hr]
  simp only [show q + j < N by omega, hq, ↓reduceIte]

/-- Slots that are multiples of `S` regroup into slots of width `w S`. -/
theorem packSlots_regroup {w S : ℕ} (hS : 0 < S) (n : ℕ) (h : ℕ → ℕ) :
    (packSlots w (S * n) fun q ↦ if q % S = 0 then h (q / S) else 0) = packSlots (w * S) n h := by
  rw [packSlots_eq_sum, packSlots_eq_sum, sum_range_mul_eq]
  refine sum_congr rfl fun y _ ↦ ?_
  rw [sum_eq_single_of_mem 0 (mem_range.2 hS) fun x hx hx0 ↦ ?_]
  · simp [Nat.mul_div_cancel_left _ hS, mul_assoc]
  · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.1 hx), hx0]

/-- Subtracting a constant from every slot does not borrow when the row is at least the
constant row and every slot of the difference stays below `2 ^ w - c`: a borrow would leave a
slot at least `2 ^ w - c`. -/
theorem le_of_sub_constSlots {w c : ℕ} (N : ℕ) {r : ℕ → ℕ}
    (hr : ∀ k < N, r k < 2 ^ w)
    (h0 : packSlots w N (fun _ ↦ c) ≤ packSlots w N r)
    (hX : ∀ k < N, slot w k (packSlots w N r - packSlots w N fun _ ↦ c) < 2 ^ w - c) :
    ∀ k < N, c ≤ r k := by
  induction N generalizing r with
  | zero => intro k hk; omega
  | succ N ih =>
    have hc : c < 2 ^ w := by have := hX 0 (by omega); omega
    rw [packSlots_succ_low, packSlots_succ_low] at h0 hX
    set R' := packSlots w N fun k ↦ r (k + 1)
    set C' := packSlots w N fun _ : ℕ ↦ c
    have hr0 := hr 0 (by omega)
    by_cases hc0 : c ≤ r 0
    · have hRC : C' ≤ R' := by
        by_contra hlt
        push Not at hlt
        have := Nat.mul_le_mul_right (2 ^ w) (show R' + 1 ≤ C' from hlt)
        rw [Nat.add_one_mul] at this
        omega
      have hsplit : r 0 + R' * 2 ^ w - (c + C' * 2 ^ w) = (r 0 - c) + (R' - C') * 2 ^ (w * 1) := by
        rw [Nat.mul_one, Nat.sub_mul]
        have : C' * 2 ^ w ≤ R' * 2 ^ w := Nat.mul_le_mul_right _ hRC
        omega
      rw [hsplit] at hX
      have hlo : r 0 - c < 2 ^ (w * 1) := by rw [Nat.mul_one]; omega
      rintro (_ | k) hk
      · exact hc0
      · exact ih (r := fun k ↦ r (k + 1)) (fun k hk ↦ hr _ (by omega)) hRC (fun k hk ↦ by
          have := hX (k + 1) (by omega)
          rwa [slot_add_mul_pow hlo, ite_eq_right (by omega), show k + 1 - 1 = k by omega] at this)
          k (by omega)
    · exfalso
      push Not at hc0
      have hRC : C' + 1 ≤ R' := by
        by_contra hlt
        have := Nat.mul_le_mul_right (2 ^ w) (show R' ≤ C' by omega)
        omega
      have hsplit : r 0 + R' * 2 ^ w - (c + C' * 2 ^ w) =
          (r 0 + 2 ^ w - c) + (R' - C' - 1) * 2 ^ (w * 1) := by
        rw [Nat.mul_one, Nat.sub_mul, Nat.sub_mul, one_mul]
        have : (C' + 1) * 2 ^ w ≤ R' * 2 ^ w := Nat.mul_le_mul_right _ hRC
        rw [add_mul, one_mul] at this
        omega
      rw [hsplit] at hX
      have hlo : r 0 + 2 ^ w - c < 2 ^ (w * 1) := by rw [Nat.mul_one]; omega
      have := hX 0 (by omega)
      rw [slot_add_mul_pow hlo, ite_eq_left (by omega)] at this
      rw [Nat.mul_one] at hlo
      rw [slot_of_lt hlo, ite_eq_left rfl] at this
      omega

end CAS.Numerics

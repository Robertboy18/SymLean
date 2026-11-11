/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.Binary64
public import CAS.IncludeStr
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# Packed slots in natural numbers

A natural number `x` holds slots of `w` bits: slot `k` is `x / 2 ^ (w * k) % 2 ^ w`, read by one
shift and one mask. Packing natural entries smaller than `2 ^ w` and reading a slot back returns
the entry (`slot_packed_eq`), and a natural number below `2 ^ (w * n)` is determined by its
first `n` slots (`eq_of_slot_eq`). One conjunction with a guard mask bounds every slot at once
(`allSlots_lt_of_guardMask`).

A signed entry `c` is stored as `c + slotBias w`, where `slotBias w = 2 ^ w / 2`; it fits when
the biased value lies in `[0, 2 ^ w)` (`FitsSlot`). A natural number whose integer value is the
biased slot expansion of entries that fit has those entries as its signed slots
(`signedSlot_eq_of_cast_eq`). This identification is what makes integer linear algebra on
packed natural numbers exact: the computation may carry between slots in intermediate values,
and only the final value needs entries that fit.

The definitions use `Nat.rec`, `Nat.add`, `Nat.mul`, `Nat.shiftLeft`, `Nat.shiftRight` and
`Nat.land` directly, so kernel reduction applies the natural-number literal extensions without
unfolding typeclass instances, and compiled code evaluates the same terms.
`Binary64WordTree.ofPackedSlots` (in `Binary64`) stores slots of any width in the balanced tree
used for binary64 words; a lookup returns the slot of the packed literal (`get_ofPackedSlots`).
A `binary64_words%` table is `ofPackedSlots 64`, so its words are the 64-bit slots of its literal
(`get_ofPacked`), and read as signed slots they are the words minus `slotBias 64 = 2 ^ 63`.

## Implementation notes

We pack because the kernel computes with natural-number literals itself: `Nat.add`, `Nat.sub`,
`Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.pow`, `Nat.gcd`, `Nat.beq`, `Nat.ble`, `Nat.land`,
`Nat.lor`, `Nat.xor`, `Nat.shiftLeft` and `Nat.shiftRight` on literals are evaluated by an
arbitrary-precision library, GMP in standard builds, instead of by unfolding their definitions
(`type_checker::reduce_nat` in the Lean kernel). One addition or multiplication of packed rows
thus replaces one operation per slot by a single big-number operation, and the product of two
packed rows is a Kronecker substitution ([PackedConvolution](PackedConvolution.lean)). The
kernel has no such extension for `Int`, so the bias, the carries allowed in intermediate values
and `signedSlot_eq_of_cast_eq` let signed arithmetic run on natural numbers.

## Kernel rules

The packed definitions of `CAS.Numerics` follow rules measured with Lean 4.35:

* loops are `Nat.rec` over the operations above, with `cond` and `Nat.beq`, `Nat.blt`,
  `Nat.ble` for branches; a linear `Nat.rec` sum of 100,000 terms checks in about one second;
* integers stay out of loops: kernel `Int` operations unfold their definitions and instances (a
  balanced sum of 131,072 integer products took 14 s, and a linear `Int` recursion of 5,000
  steps exceeded the kernel recursion depth), so signed entries are biased natural slots and
  integers appear only in the statements of the soundness theorems;
* sums recurse on the partial result, since accumulator-passing recursion also exceeds the
  kernel recursion depth;
* strides are shifts, never `Nat.pow`, whose results above `2 ^ 2 ^ 24` the kernel refuses;
* constant rows and masks are `constSlots`, since compiled code does not share them between
  calls and a loop over the slots would be repeated for every row;
* large literals come from `include_str` through the importers, never from numerals in source,
  whose parsing is quadratic in the number of digits;
* one kernel declaration stays within about one million reduction steps, 60 seconds and 3 GB;
  `cega [batch := b]` or `forall_of_batchAll` joins such leaves.

## References

* *The Lean Language Reference*, section "Natural Numbers",
  <https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/>. The subsection
  "Run-Time Representation" on the kernel's arbitrary-precision natural-number literals.
* Lean 4, release v4.35.0, <https://github.com/leanprover/lean4>. `type_checker::reduce_nat` in
  `src/kernel/type_checker.cpp` lists the operations the kernel evaluates on literals.
-/

@[expose] public section

namespace CAS.Numerics

open scoped BigOperators

/-! ### Slots -/

/-- The mask `slotMask w` is `2 ^ w - 1`. -/
theorem slotMask_eq (w : ℕ) : slotMask w = 2 ^ w - 1 := by
  change 1 <<< w - 1 = _
  rw [Nat.one_shiftLeft]

/-- Slot `k` of width `w` of `x` is `x / 2 ^ (w * k) % 2 ^ w`. -/
theorem slot_eq (w k x : ℕ) : slot w k x = x / 2 ^ (w * k) % 2 ^ w := by
  change (x >>> (w * k)) &&& slotMask w = _
  rw [slotMask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

/-- Every slot of width `w` is below `2 ^ w`. -/
theorem slot_lt (w k x : ℕ) : slot w k x < 2 ^ w :=
  slot_eq w k x ▸ Nat.mod_lt _ (Nat.two_pow_pos w)

/-- Bit `i` of slot `k` of width `w` of `x` is bit `w * k + i` of `x` when `i < w`, and `false`
otherwise. -/
theorem testBit_slot (w k x i : ℕ) :
    (slot w k x).testBit i = (decide (i < w) && x.testBit (w * k + i)) := by
  change ((x >>> (w * k)) &&& slotMask w).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, slotMask_eq, Nat.testBit_two_pow_sub_one,
    Bool.and_comm]

/-- A value below `2 ^ w` is its own slot zero and has no other nonzero slot. -/
theorem slot_of_lt {w v : ℕ} (hv : v < 2 ^ w) (k : ℕ) :
    slot w k v = if k = 0 then v else 0 := by
  rw [slot_eq]
  split_ifs with hk
  · simp [hk, Nat.mod_eq_of_lt hv]
  · rw [Nat.div_eq_of_lt (hv.trans_le (Nat.pow_le_pow_right two_pos
      (Nat.le_mul_of_pos_right w (Nat.pos_of_ne_zero hk)))), Nat.zero_mod]

/-- Slots of a sum whose low part fits below slot `m`: the low slots come from `lo` and the
slots from `m` on are those of `hi`. -/
theorem slot_add_mul_pow {w m lo : ℕ} (hlo : lo < 2 ^ (w * m)) (hi k : ℕ) :
    slot w k (lo + hi * 2 ^ (w * m)) = if k < m then slot w k lo else slot w (k - m) hi := by
  simp only [slot_eq]
  split_ifs with hk
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hk
    rw [show hi * 2 ^ (w * (k + d + 1)) = hi * 2 ^ (w * d) * 2 ^ w * 2 ^ (w * k) by ring,
      Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_right]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hk)
    rw [Nat.add_sub_cancel_left, Nat.mul_add, pow_add, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlo, zero_add]

/-- Reducing modulo `2 ^ (w * m)` keeps the slots below `m`. -/
theorem slot_mod_two_pow {w m k : ℕ} (hk : k < m) (x : ℕ) :
    slot w k (x % 2 ^ (w * m)) = slot w k x := by
  have h := slot_add_mul_pow (Nat.mod_lt x (Nat.two_pow_pos (w * m))) (x / 2 ^ (w * m)) k
  rw [Nat.mul_comm (x / _), Nat.mod_add_div, ite_eq_left hk] at h
  exact h.symm

/-- Dividing by `2 ^ (w * m)` shifts the slots down by `m`. -/
theorem slot_div_two_pow {w m : ℕ} (k x : ℕ) :
    slot w k (x / 2 ^ (w * m)) = slot w (k + m) x := by
  rw [slot_eq, slot_eq, Nat.div_div_eq_div_mul, ← pow_add, ← Nat.mul_add, Nat.add_comm m k]

/-- Two numbers below `2 ^ (w * n)` with the same first `n` slots are equal. -/
theorem eq_of_slot_eq {w n x y : ℕ} (hx : x < 2 ^ (w * n)) (hy : y < 2 ^ (w * n))
    (h : ∀ k < n, slot w k x = slot w k y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < w * n
  · have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
    have hk : i / w < n := (Nat.div_lt_iff_lt_mul hw).mpr (by rwa [Nat.mul_comm])
    simpa only [testBit_slot, Nat.mod_lt i hw, decide_true, Bool.true_and, Nat.div_add_mod]
      using congrArg (fun z ↦ z.testBit (i % w)) (h (i / w) hk)
  · have hle := Nat.pow_le_pow_right two_pos (not_lt.mp hi)
    rw [Nat.testBit_lt_two_pow (hx.trans_le hle), Nat.testBit_lt_two_pow (hy.trans_le hle)]

/-! ### Kernel loops and packing -/

/-- The sum `f 0 + ⋯ + f (n - 1)`, computed by `Nat.rec` with natural addition. -/
def natSum (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  Nat.rec (motive := fun _ ↦ ℕ) 0 (fun j s ↦ Nat.add s (f j)) n

/-- `natSum` of no terms is `0`. -/
@[simp] theorem natSum_zero (f : ℕ → ℕ) : natSum 0 f = 0 := rfl

/-- `natSum (n + 1) f` is `natSum n f + f n`. -/
theorem natSum_succ (n : ℕ) (f : ℕ → ℕ) : natSum (n + 1) f = natSum n f + f n := rfl

/-- `natSum n f` is the sum of `f j` over `j ∈ Finset.range n`. -/
theorem natSum_eq_sum (n : ℕ) (f : ℕ → ℕ) : natSum n f = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [natSum_succ, ih, Finset.sum_range_succ]

/-- The entries `f 0, …, f (n - 1)` in slots of width `w`, the first slot least significant. -/
def packSlots (w n : ℕ) (f : ℕ → ℕ) : ℕ :=
  natSum n (fun k ↦ Nat.shiftLeft (f k) (Nat.mul w k))

/-- Packing `n + 1` entries adds `f n * 2 ^ (w * n)` to the packing of the first `n`. -/
theorem packSlots_succ (w n : ℕ) (f : ℕ → ℕ) :
    packSlots w (n + 1) f = packSlots w n f + f n * 2 ^ (w * n) := by
  change natSum n _ + (f n <<< (w * n)) = _
  rw [Nat.shiftLeft_eq]
  rfl

/-- `packSlots w n f` is `∑ k ∈ Finset.range n, f k * 2 ^ (w * k)`, for entries of any size. -/
theorem packSlots_eq_sum (w n : ℕ) (f : ℕ → ℕ) :
    packSlots w n f = ∑ k ∈ Finset.range n, f k * 2 ^ (w * k) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [packSlots_succ, ih, Finset.sum_range_succ]

/-- The slots of a number below `2 ^ (w * n)` vanish from index `n` on. -/
theorem slot_eq_zero_of_lt {w n x i : ℕ} (hx : x < 2 ^ (w * n)) (hi : n ≤ i) : slot w i x = 0 := by
  rw [slot_eq, Nat.div_eq_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right Nat.zero_lt_two
    (Nat.mul_le_mul_left w hi))), Nat.zero_mod]

/-- Packing stops at the last nonzero entry. -/
theorem packSlots_of_zero {w n N : ℕ} (hnN : n ≤ N) {f : ℕ → ℕ}
    (hf : ∀ i, n ≤ i → i < N → f i = 0) : packSlots w N f = packSlots w n f := by
  simp only [packSlots_eq_sum]
  refine (Finset.sum_subset (Finset.range_subset_range.2 hnN) fun i hi hi' ↦ ?_).symm
  simp [hf i (by simpa using hi') (by simpa using hi)]

/-- If the first `n` entries are below `2 ^ w`, their packing is below `2 ^ (w * n)`. -/
theorem packSlots_lt {w n : ℕ} {f : ℕ → ℕ} (hf : ∀ k < n, f k < 2 ^ w) :
    packSlots w n f < 2 ^ (w * n) := by
  induction n with
  | zero => simp [packSlots]
  | succ n ih =>
    rw [packSlots_succ, Nat.mul_succ, pow_add]
    have := Nat.mul_le_mul_right (2 ^ (w * n)) (show f n + 1 ≤ 2 ^ w from hf n (by omega))
    linarith [ih fun k hk ↦ hf k (by omega)]

/-- Packing is additive in the entries, with no bound on them: the packings of `f` and `g` add up
to the packing of `fun k ↦ f k + g k`. -/
theorem packSlots_add (w n : ℕ) (f g : ℕ → ℕ) :
    packSlots w n f + packSlots w n g = packSlots w n (fun k ↦ f k + g k) := by
  simp only [packSlots_eq_sum, ← Finset.sum_add_distrib, add_mul]

/-- Packing splits off its lowest slot. -/
theorem packSlots_succ_low (w n : ℕ) (f : ℕ → ℕ) :
    packSlots w (n + 1) f = f 0 + packSlots w n (fun k ↦ f (k + 1)) * 2 ^ w := by
  simp only [packSlots_eq_sum, Finset.sum_range_succ', Finset.sum_mul, mul_add_one, pow_add,
    Nat.mul_zero, pow_zero, mul_one, mul_assoc]
  ring

/-- The constant `c` in each of the first `n` slots of width `w`, by one multiplication and one
division: `c * ((2 ^ (w * n) - 1) / (2 ^ w - 1))`. Compiled code and the kernel compute it in
a few big-number operations, without a loop over the slots. -/
def constSlots (w n c : ℕ) : ℕ := Nat.mul c (Nat.div (slotMask (Nat.mul w n)) (slotMask w))

/-- For `0 < w`, `constSlots w n c` is the packing of `n` copies of `c`. -/
theorem constSlots_eq {w : ℕ} (hw : 0 < w) (n c : ℕ) :
    constSlots w n c = packSlots w n (fun _ ↦ c) := by
  change c * (slotMask (w * n) / slotMask w) = _
  rw [slotMask_eq, slotMask_eq, pow_mul, ← Nat.geomSum_eq (Nat.le_self_pow hw.ne' 2) n,
    packSlots_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [pow_mul]

/-- Reading a slot of packed entries below `2 ^ w` returns the entry, and zero past the end. -/
theorem slot_packed_eq {w n : ℕ} {f : ℕ → ℕ} (hf : ∀ k < n, f k < 2 ^ w) (k : ℕ) :
    slot w k (packSlots w n f) = if k < n then f k else 0 := by
  induction n generalizing k with
  | zero => simp [packSlots, natSum, slot_eq]
  | succ n ih =>
    have hf' : ∀ j < n, f j < 2 ^ w := fun j hj ↦ hf j (by omega)
    rw [packSlots_succ, slot_add_mul_pow (packSlots_lt hf'), slot_of_lt (hf n (by omega)), ih hf']
    split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- A number below `2 ^ (w * n)` is the packing of its own first `n` slots. -/
theorem packSlots_slot {w n x : ℕ} (hx : x < 2 ^ (w * n)) :
    packSlots w n (fun k ↦ slot w k x) = x :=
  eq_of_slot_eq (packSlots_lt fun k _ ↦ slot_lt w k x) hx fun k hk ↦ by
    rw [slot_packed_eq fun k _ ↦ slot_lt w k x, ite_eq_left hk]

/-- Slots of width `w * q` hold `q` consecutive slots of width `w` each. -/
theorem slot_slot_mul {w q k i : ℕ} (hk : k < q) (x : ℕ) :
    slot w k (slot (w * q) i x) = slot w (q * i + k) x := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [testBit_slot]
  by_cases hj : j < w
  · have hlt : w * k + j < w * q := by
      linarith [Nat.mul_le_mul_left w (show k + 1 ≤ q from hk)]
    simp [hj, hlt, show w * q * i + (w * k + j) = w * (q * i + k) + j by ring]
  · simp [hj]

/-- Slot `i` of `x`, located by `depth` halvings into blocks of `2 ^ leaf` slots. Kernel
reduction shares the halved literals between lookups of one declaration, so random access into
a large literal costs a few steps per level. Compiled code recomputes the halvings at every
call; it reads large tables faster through `Binary64WordTree`. -/
def slotLookup (w leaf depth : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ) (fun x i ↦ slot w i x)
    (fun d lookup x i ↦
      cond (Nat.blt i (Nat.shiftLeft 1 (Nat.add leaf d)))
        (lookup (Nat.land x (slotMask (Nat.mul w (Nat.shiftLeft 1 (Nat.add leaf d))))) i)
        (lookup (Nat.shiftRight x (Nat.mul w (Nat.shiftLeft 1 (Nat.add leaf d))))
          (Nat.sub i (Nat.shiftLeft 1 (Nat.add leaf d)))))
    depth

/-- The lookup reads the slot itself, at every index. -/
theorem slotLookup_eq (w leaf depth x i : ℕ) : slotLookup w leaf depth x i = slot w i x := by
  induction depth generalizing x i with
  | zero => rfl
  | succ d ih =>
    change cond (Nat.blt i (1 <<< (leaf + d)))
      (slotLookup w leaf d (x &&& slotMask (w * (1 <<< (leaf + d)))) i)
      (slotLookup w leaf d (x >>> (w * (1 <<< (leaf + d)))) (i - (1 <<< (leaf + d)))) = _
    rw [ih, ih, slotMask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
      Nat.one_shiftLeft]
    cases h : Nat.blt i (2 ^ (leaf + d))
    · have hi : ¬i < 2 ^ (leaf + d) := fun hi ↦ by rw [Nat.blt_eq.mpr hi] at h; cases h
      rw [Bool.cond_false, slot_div_two_pow, Nat.sub_add_cancel (not_lt.mp hi)]
    · rw [Bool.cond_true, slot_mod_two_pow (Nat.blt_eq.mp h)]

/-! ### Guard masks -/

/-- The bits `g` through `w - 1` of one slot of width `w`. -/
def guardSlot (w g : ℕ) : ℕ := Nat.shiftLeft (slotMask (Nat.sub w g)) g

/-- Bit `i` of `guardSlot w g` is set exactly when `g ≤ i` and `i < w`. -/
theorem testBit_guardSlot (w g i : ℕ) :
    (guardSlot w g).testBit i = (decide (g ≤ i) && decide (i < w)) := by
  change ((slotMask (w - g)) <<< g).testBit i = _
  rw [Nat.testBit_shiftLeft, slotMask_eq, Nat.testBit_two_pow_sub_one]
  by_cases hi : g ≤ i <;> by_cases hiw : i < w <;> simp [hi, hiw] <;> omega

/-- `guardSlot w g` is below `2 ^ w`, so it fits one slot of width `w`. -/
theorem guardSlot_lt (w g : ℕ) : guardSlot w g < 2 ^ w :=
  Nat.lt_pow_two_of_testBit _ fun i hi ↦ by simp [testBit_guardSlot, not_lt.2 hi]

/-- The guard bits `g` through `w - 1` of each of the first `n` slots of width `w`. -/
def guardMask (w g n : ℕ) : ℕ := packSlots w n (fun _ ↦ guardSlot w g)

/-- If a number has no guard bit set, every one of its first `n` slots is below `2 ^ g`. -/
theorem allSlots_lt_of_guardMask {w g n x : ℕ} (h : Nat.land x (guardMask w g n) = 0)
    {k : ℕ} (hk : k < n) : slot w k x < 2 ^ g := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_slot]
  by_cases hiw : i < w
  · have hmask : (guardMask w g n).testBit (w * k + i) = true := by
      have := testBit_slot w k (guardMask w g n) i
      rw [guardMask, slot_packed_eq (fun _ _ ↦ guardSlot_lt w g), ite_eq_left hk,
        testBit_guardSlot] at this
      simpa [hi, hiw, guardMask] using this.symm
    have hzero := congrArg (fun z ↦ z.testBit (w * k + i)) h
    change (x &&& guardMask w g n).testBit (w * k + i) = (0 : ℕ).testBit (w * k + i) at hzero
    rw [Nat.testBit_and, hmask, Nat.zero_testBit, Bool.and_true] at hzero
    simp [hzero]
  · simp [hiw]

/-! ### Signed entries with bias -/

/-- The bias `2 ^ w / 2` added to a signed entry stored in a slot of width `w`. -/
def slotBias (w : ℕ) : ℕ := Nat.shiftRight (Nat.shiftLeft 1 w) 1

/-- The bias `slotBias w` is `2 ^ w / 2`. -/
theorem slotBias_eq (w : ℕ) : slotBias w = 2 ^ w / 2 := by
  change (1 <<< w) >>> 1 = _
  rw [Nat.one_shiftLeft, Nat.shiftRight_eq_div_pow, pow_one]

/-- The bias `slotBias w` is below `2 ^ w`. -/
theorem slotBias_lt (w : ℕ) : slotBias w < 2 ^ w := by
  rw [slotBias_eq]
  exact Nat.div_lt_self (by positivity) (by norm_num)

/-- The bias `slotBias (w + 1)` is `2 ^ w`. -/
theorem slotBias_succ (w : ℕ) : slotBias (w + 1) = 2 ^ w := by
  rw [slotBias_eq, pow_succ, Nat.mul_div_cancel _ (by norm_num)]

/-- The bias grows with the width: `g ≤ w` gives `slotBias g ≤ slotBias w`. -/
theorem slotBias_le_slotBias {g w : ℕ} (h : g ≤ w) : slotBias g ≤ slotBias w := by
  rw [slotBias_eq, slotBias_eq]
  exact Nat.div_le_div_right (Nat.pow_le_pow_right (by norm_num) h)

/-- The signed entry stored with bias in slot `k`. -/
def signedSlot (w k x : ℕ) : ℤ := (slot w k x : ℤ) - slotBias w

/-- A signed entry is at most the bias in absolute value. -/
theorem natAbs_signedSlot_le_slotBias (w k x : ℕ) : (signedSlot w k x).natAbs ≤ slotBias w := by
  have h := slot_lt w k x
  rw [signedSlot, slotBias_eq]
  omega

/-- A signed entry fits a slot of width `w` when its biased value lies in `[0, 2 ^ w)`. -/
def FitsSlot (w : ℕ) (c : ℤ) : Prop := 0 ≤ c + slotBias w ∧ c + slotBias w < 2 ^ w

/-- Every signed entry of absolute value at most `m` fits when `2 * m < 2 ^ w`. -/
theorem fitsSlot_of_natAbs_le {w m : ℕ} {c : ℤ} (hc : c.natAbs ≤ m) (hm : 2 * m < 2 ^ w) :
    FitsSlot w c := by
  have h2 : ((2 ^ w : ℕ) : ℤ) = 2 ^ w := by norm_num
  rw [FitsSlot, slotBias_eq]
  omega

/-- A signed entry that fits a slot of width `g` has absolute value at most `slotBias g`. -/
theorem natAbs_le_of_fitsSlot {g : ℕ} {c : ℤ} (hc : FitsSlot g c) : c.natAbs ≤ slotBias g := by
  have h2 : ((2 ^ g : ℕ) : ℤ) = (2 : ℤ) ^ g := by norm_num
  rw [FitsSlot, slotBias_eq] at hc
  rw [slotBias_eq]
  omega

/-- The biased slot value of a signed entry, clamped to the slot. Entries that fit are stored
exactly (`encodeSlot_of_fits`). -/
def encodeSlot (w : ℕ) (c : ℤ) : ℕ := min (c + slotBias w).toNat (slotMask w)

/-- Every encoded value `encodeSlot w c` is below `2 ^ w`. -/
theorem encodeSlot_lt (w : ℕ) (c : ℤ) : encodeSlot w c < 2 ^ w :=
  (min_le_right _ _).trans_lt (slotMask_eq w ▸ Nat.sub_lt (Nat.two_pow_pos w) one_pos)

/-- A signed entry `c` that fits a slot of width `w` is encoded as `c + slotBias w`, without
clamping. -/
theorem encodeSlot_of_fits {w : ℕ} {c : ℤ} (hc : FitsSlot w c) :
    (encodeSlot w c : ℤ) = c + slotBias w := by
  have h1 := hc.2
  have h2 : ((2 ^ w : ℕ) : ℤ) = (2 : ℤ) ^ w := by norm_num
  rw [encodeSlot, slotMask_eq, min_eq_left (by omega), Int.toNat_of_nonneg hc.1]

/-- The signed vector `f 0, …, f (n - 1)` packed with bias in slots of width `w`. -/
def biasedPack (w n : ℕ) (f : ℕ → ℤ) : ℕ := packSlots w n (fun k ↦ encodeSlot w (f k))

/-- `biasedPack w n f` is below `2 ^ (w * n)` for every `f`. -/
theorem biasedPack_lt (w n : ℕ) (f : ℕ → ℤ) : biasedPack w n f < 2 ^ (w * n) :=
  packSlots_lt (fun k _ ↦ encodeSlot_lt w (f k))

/-- For `k < n` and `f k` fitting a slot of width `w`, signed slot `k` of `biasedPack w n f` is
`f k`. -/
theorem signedSlot_biasedPack {w n : ℕ} {f : ℕ → ℤ} {k : ℕ} (hk : k < n)
    (hf : FitsSlot w (f k)) : signedSlot w k (biasedPack w n f) = f k := by
  rw [signedSlot, biasedPack, slot_packed_eq (fun k _ ↦ encodeSlot_lt w (f k)), ite_eq_left hk,
    encodeSlot_of_fits hf]
  ring

/-- A natural number whose integer value is the biased slot expansion of entries that fit has
those entries as its signed slots. -/
theorem signedSlot_eq_of_cast_eq {w n x : ℕ} {c : ℕ → ℤ} (hc : ∀ k < n, FitsSlot w (c k))
    (hx : (x : ℤ) = ∑ k ∈ Finset.range n, (c k + slotBias w) * 2 ^ (w * k))
    {k : ℕ} (hk : k < n) : signedSlot w k x = c k := by
  have hpack : (x : ℤ) = (biasedPack w n c : ℤ) := by
    rw [hx, biasedPack, packSlots_eq_sum]
    push_cast
    exact Finset.sum_congr rfl fun j hj ↦ by
      rw [encodeSlot_of_fits (hc j (Finset.mem_range.mp hj))]
  rw [Int.ofNat_inj.1 hpack, signedSlot_biasedPack hk (hc k hk)]

/-- The integer value of a number below `2 ^ (w * n)` is the biased expansion of its signed
slots. -/
theorem cast_eq_sum_signedSlot {w n x : ℕ} (hx : x < 2 ^ (w * n)) :
    (x : ℤ) = ∑ k ∈ Finset.range n, (signedSlot w k x + slotBias w) * 2 ^ (w * k) := by
  conv_lhs => rw [← packSlots_slot hx, packSlots_eq_sum]
  push_cast
  simp [signedSlot]

/-- Entries below `2 ^ w + slotBias w` whose packed slots all reach the bias fit their slots:
an entry of `2 ^ w` or more would leave a slot below the bias in the lowest such position. -/
theorem lt_two_pow_of_slotBias_le_slot {w n : ℕ} {u : ℕ → ℕ}
    (hu : ∀ k < n, u k < 2 ^ w + slotBias w)
    (h : ∀ k < n, slotBias w ≤ slot w k (packSlots w n u)) : ∀ k < n, u k < 2 ^ w := by
  induction n generalizing u with
  | zero => intro k hk; omega
  | succ n ih =>
    have h0 : u 0 < 2 ^ w := by
      by_contra hge
      have h0' := h 0 (by omega)
      have hlt := hu 0 (by omega)
      have hb := slotBias_lt w
      rw [packSlots_succ_low, slot_eq, Nat.mul_zero, pow_zero, Nat.div_one,
        Nat.add_mul_mod_self_right, Nat.mod_eq_sub_mod (not_lt.mp hge),
        Nat.mod_eq_of_lt (by omega)] at h0'
      omega
    have hslot : ∀ k, slot w (k + 1) (packSlots w (n + 1) u) =
        slot w k (packSlots w n (fun k ↦ u (k + 1))) := by
      intro k
      rw [packSlots_succ_low, show 2 ^ w = 2 ^ (w * 1) by rw [Nat.mul_one],
        slot_add_mul_pow (by rwa [Nat.mul_one]), ite_eq_right (by omega), Nat.add_sub_cancel]
    have hrest := ih (u := fun k ↦ u (k + 1)) (fun k hk ↦ hu (k + 1) (by omega))
      (fun k hk ↦ by rw [← hslot]; exact h (k + 1) (by omega))
    rintro (_ | k) hk
    exacts [h0, hrest k (by omega)]

/-! ### Balanced word trees of slots -/

namespace Binary64WordTree

/-- A lookup at an index `i` with `i < m` in `append left right` reads `left` at `i`. -/
theorem get_append_left {m n : ℕ} (left : Binary64WordTree m) (right : Binary64WordTree n)
    (i : Fin (m + n)) (hi : i.val < m) :
    (Binary64WordTree.append left right).get i = left.get ⟨i.val, hi⟩ := by
  simp [get, hi]

/-- A lookup at an index `i` with `¬i < m` in `append left right` reads `right` at `i - m`. -/
theorem get_append_right {m n : ℕ} (left : Binary64WordTree m) (right : Binary64WordTree n)
    (i : Fin (m + n)) (hi : ¬i.val < m) :
    (Binary64WordTree.append left right).get i =
      right.get ⟨i.val - m, by have := i.isLt; omega⟩ := by
  simp [get, hi]

/-- A lookup at `i` in `ofPackedSlotsLinear w n packed` returns slot `i` of width `w` of
`packed`. -/
theorem get_ofPackedSlotsLinear (w : ℕ) {n : ℕ} (packed : ℕ) (i : Fin n) :
    (ofPackedSlotsLinear w n packed).get i = slot w i.val packed := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [ofPackedSlotsLinear]
    by_cases hi : i.val < n
    · rw [get_append_left _ _ i hi, ih]
    · rw [get_append_right _ _ i hi]
      have : i.val = n := by have := i.isLt; omega
      simp [get, this]

/-- Transporting a tree along `e : m = n` keeps its words: index `i` reads `t` at the same
value. -/
theorem get_cast {m n : ℕ} (e : m = n) (t : Binary64WordTree m) (i : Fin n) :
    (e ▸ t).get i = t.get ⟨i.val, e ▸ i.isLt⟩ := by
  subst e
  rfl

/-- A lookup in the balanced tree returns the slot of the packed number. -/
theorem get_ofPackedSlots (w depth : ℕ) {n : ℕ} (packed : ℕ) (i : Fin n) :
    (ofPackedSlots w depth n packed).get i = slot w i.val packed := by
  induction depth generalizing n packed with
  | zero => exact get_ofPackedSlotsLinear w packed i
  | succ depth ih =>
    rw [ofPackedSlots]
    split_ifs with h
    · rw [get_cast]
      by_cases hi : i.val < n / 2
      · rw [get_append_left _ _ _ hi, ih]
        change slot w i.val (packed &&& slotMask (w * (n / 2))) = _
        rw [slotMask_eq, Nat.and_two_pow_sub_one_eq_mod, slot_mod_two_pow hi]
      · rw [get_append_right _ _ _ hi, ih]
        change slot w (i.val - n / 2) (packed >>> (w * (n / 2))) = _
        rw [Nat.shiftRight_eq_div_pow, slot_div_two_pow, Nat.sub_add_cancel (not_lt.mp hi)]
    · exact get_ofPackedSlotsLinear w packed i

/-- Read a word at a natural index, for loops over natural numbers. Indices past the end read
the last word of their branch; `getNat_eq_get` covers indices in range. -/
def getNat {n : ℕ} : Binary64WordTree n → ℕ → ℕ
  | .empty, _ => 0
  | .singleton word, _ => word
  | @append m _ left right, i => cond (Nat.blt i m) (left.getNat i) (right.getNat (Nat.sub i m))

/-- For an index in range, `getNat` reads the same word as `get`. -/
theorem getNat_eq_get {n : ℕ} (t : Binary64WordTree n) (i : Fin n) : t.getNat i.val = t.get i := by
  induction t with
  | empty => exact i.elim0
  | singleton word => rfl
  | @append m k left right ihl ihr =>
    by_cases hi : i.val < m
    · rw [get_append_left _ _ i hi, ← ihl]
      simp [getNat, hi]
    · rw [get_append_right _ _ i hi, ← ihr]
      simp [getNat, hi]

/-- A lookup in an imported binary64 table returns the corresponding 64-bit slot. -/
theorem get_ofPacked (depth : ℕ) {n : ℕ} (packed : ℕ) (i : Fin n) :
    (ofPacked depth n packed).get i = slot 64 i.val packed :=
  get_ofPackedSlots 64 depth packed i

end Binary64WordTree

end CAS.Numerics

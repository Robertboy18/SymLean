/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
module

public import CAS.Numerics.PackedSignedWindows
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# Spreading packed slots to a wider width in logarithmically many steps

`spread w W p x` moves the `2^p` slots of width `w` of `x` to slots of width `W ≥ w` in `p`
steps (`spread_packSlots`). At depth `d` the slots form blocks of `2^(p-d)` contiguous slots at
the stride `2^(p-d) W` (`spreadLayout`), and one step `spreadStep` splits every block, moving its
upper half up by `2^(p-d-1) (W - w)` bits (`spreadStep_layout`). `land_packSlots` takes the
conjunction of two packed rows slot by slot.

## Implementation notes

A step keeps the lower half of every block with an `and` against `spreadMask`, which holds the
low `2^(p-d-1) w` bits of every slot of width `2^(p-d) W`, subtracts this from `x` to get the
upper halves, multiplies them by `2 ^ (2^(p-d-1) (W - w))` and adds the two. Nothing crosses a
block: the subtracted bits are bits of `x`, and since `w ≤ W` the moved upper half ends at bit
`2^(p-d-1) (W + w) ≤ 2^(p-d) W` of its block. `spreadStep_layout` proves one step from depth `d`
to depth `d + 1`, `spreadUpTo_layout` iterates it along the `Nat.rec` of `spreadUpTo`, and
`spread_packSlots` reads the two ends, depth `0` being the packed input and depth `p` the spread
row. The only hypotheses are `w ≤ W` and that every entry is below `2 ^ w`.

So `p` steps of a few operations on numbers of at most `2^p W` bits replace the `2^p` slot reads
of a rebuild slot by slot, provided the masks are constants. `spreadMask` is a `packSlots` sum
over the `2^d` blocks, the form the proofs read; [ZigzagBlocks](ZigzagBlocks.lean), which
spreads in the kernel, takes the masks from `constSlots` instead (`spreadConst`, equal to
`spread` by `spreadConst_eq`). Certificates outside the library use `spread_packSlots` too.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-! ### Packing lemmas -/

/-- Packing `2 * h` entries is the packing of the first `h` plus `2 ^ (w * h)` times the packing of
the next `h`, for entries of any size. -/
theorem packSlots_two_mul (w h : ℕ) (g : ℕ → ℕ) :
    packSlots w (2 * h) g =
      packSlots w h g + 2 ^ (w * h) * packSlots w h (fun r ↦ g (h + r)) := by
  simp only [packSlots_eq_sum, two_mul, sum_range_add, mul_sum]
  congr 1
  refine sum_congr rfl fun r _ ↦ ?_
  rw [mul_add, pow_add]
  ring

/-- If the first `n` entries are below `2 ^ v`, bit `i` of their packing is bit `i % v` of entry
`i / v` when `i < v * n`, and `false` otherwise. -/
theorem testBit_packSlots {v n : ℕ} {G : ℕ → ℕ} (hG : ∀ q < n, G q < 2 ^ v) (i : ℕ) :
    (packSlots v n G).testBit i = (decide (i < v * n) && (G (i / v)).testBit (i % v)) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · have h0 : packSlots 0 n G = 0 := by
      rw [packSlots_eq_sum]
      exact sum_eq_zero fun q hq ↦ by simp [show G q = 0 by simpa using hG q (mem_range.mp hq)]
    simp [h0]
  have hslot := testBit_slot v (i / v) (packSlots v n G) (i % v)
  rw [slot_packed_eq hG, Nat.div_add_mod] at hslot
  simp only [Nat.mod_lt i hv, decide_true, Bool.true_and] at hslot
  rw [← hslot]
  have hk : i / v < n ↔ i < v * n := by
    rw [Nat.div_lt_iff_lt_mul hv, Nat.mul_comm]
  by_cases h : i / v < n
  · rw [ite_eq_left h, decide_eq_true (hk.mp h), Bool.true_and]
  · rw [ite_eq_right h, decide_eq_false (fun h' ↦ h (hk.mpr h')), Bool.false_and,
      Nat.zero_testBit]

/-- If the first `n` entries of `G` and `H` are below `2 ^ v`, the conjunction of their packings
is the packing of the entrywise conjunctions `Nat.land (G q) (H q)`. -/
theorem land_packSlots {v n : ℕ} {G H : ℕ → ℕ} (hG : ∀ q < n, G q < 2 ^ v)
    (hH : ∀ q < n, H q < 2 ^ v) :
    Nat.land (packSlots v n G) (packSlots v n H) =
      packSlots v n (fun q ↦ Nat.land (G q) (H q)) := by
  have hGH : ∀ q < n, Nat.land (G q) (H q) < 2 ^ v :=
    fun q hq ↦ lt_of_le_of_lt Nat.and_le_left (hG q hq)
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  change (packSlots v n G &&& packSlots v n H).testBit i = _
  rw [Nat.testBit_and, testBit_packSlots hG, testBit_packSlots hH, testBit_packSlots hGH]
  change _ = (decide (i < v * n) && (G (i / v) &&& H (i / v)).testBit (i % v))
  rw [Nat.testBit_and]
  cases decide (i < v * n) <;> simp

/-- The packing of the `n` entries `A q + 2 ^ u * B q` in slots of width `2 * u` is the packing of
the `2 * n` entries `A 0, B 0, A 1, B 1, …` in slots of width `u`, for entries of any size. -/
theorem packSlots_pairs (u n : ℕ) (A B : ℕ → ℕ) :
    packSlots (2 * u) n (fun q ↦ A q + 2 ^ u * B q) =
      packSlots u (2 * n) (fun k ↦ if k % 2 = 0 then A (k / 2) else B (k / 2)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [packSlots_succ, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, packSlots_succ,
      packSlots_succ]
    rw [ite_eq_left (by omega), ite_eq_right (by omega), show 2 * n / 2 = n by omega,
      show (2 * n + 1) / 2 = n by omega, show u * (2 * n + 1) = u + 2 * u * n by ring,
      show u * (2 * n) = 2 * u * n by ring, pow_add]
    ring

/-! ### The spreading steps -/

/-- The mask of the lower halves of the blocks at depth `d`. -/
def spreadMask (w W p d : ℕ) : ℕ :=
  packSlots (2 ^ (p - d) * W) (2 ^ d) fun _ ↦ 2 ^ (2 ^ (p - d - 1) * w) - 1

/-- One step: the upper half of every block moves up by `2^(p-d-1) (W - w)` bits. -/
def spreadStep (w W p d x : ℕ) : ℕ :=
  Nat.add (Nat.land x (spreadMask w W p d))
    (Nat.mul (Nat.sub x (Nat.land x (spreadMask w W p d))) (2 ^ (2 ^ (p - d - 1) * (W - w))))

/-- The first `n` steps. -/
def spreadUpTo (w W p : ℕ) (x : ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ ↦ ℕ) x (fun d y ↦ spreadStep w W p d y) n

/-- The slots of width `w` of `x` spread to width `W`. -/
def spread (w W p x : ℕ) : ℕ := spreadUpTo w W p x p

/-- The layout at depth `d`: blocks of `2^(p-d)` contiguous slots at the stride `2^(p-d) W`. -/
def spreadLayout (w W p : ℕ) (f : ℕ → ℕ) (d : ℕ) : ℕ :=
  packSlots (2 ^ (p - d) * W) (2 ^ d) fun q ↦
    packSlots w (2 ^ (p - d)) fun r ↦ f (q * 2 ^ (p - d) + r)

/-- For `w ≤ W`, `d < p` and `f k < 2 ^ w` for every `k`, one `spreadStep` at depth `d` takes the
layout at depth `d` to the layout at depth `d + 1`. -/
theorem spreadStep_layout {w W p d : ℕ} (hW : w ≤ W) (hd : d < p) {f : ℕ → ℕ}
    (hf : ∀ k, f k < 2 ^ w) :
    spreadStep w W p d (spreadLayout w W p f d) = spreadLayout w W p f (d + 1) := by
  set h := 2 ^ (p - d - 1)
  have hb : 2 ^ (p - d) = 2 * h := by
    rw [show p - d = p - d - 1 + 1 by omega, pow_succ]; ring
  have hpd : p - (d + 1) = p - d - 1 := by omega
  set lo : ℕ → ℕ := fun q ↦ packSlots w h fun r ↦ f (q * (2 * h) + r)
  set up : ℕ → ℕ := fun q ↦ packSlots w h fun r ↦ f (q * (2 * h) + h + r)
  have hlo : ∀ q, lo q < 2 ^ (w * h) := fun q ↦ packSlots_lt fun r _ ↦ hf _
  have hup : ∀ q, up q < 2 ^ (w * h) := fun q ↦ packSlots_lt fun r _ ↦ hf _
  have hblock : ∀ q, (packSlots w (2 ^ (p - d)) fun r ↦ f (q * 2 ^ (p - d) + r)) =
      lo q + 2 ^ (w * h) * up q := fun q ↦ by
    rw [hb, packSlots_two_mul]
    simp only [lo, up, Nat.add_assoc]
  have hGlt : ∀ q, lo q + 2 ^ (w * h) * up q < 2 ^ (2 ^ (p - d) * W) := fun q ↦ by
    have : lo q + 2 ^ (w * h) * up q < 2 ^ (w * h) * 2 ^ (w * h) := by
      nlinarith [hlo q, Nat.mul_le_mul_left (2 ^ (w * h)) (hup q)]
    refine this.trans_le ?_
    rw [← pow_add, hb]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hmask : 2 ^ (h * w) - 1 < 2 ^ (2 ^ (p - d) * W) := Nat.sub_one_lt_of_le (by positivity)
    (Nat.pow_le_pow_right (by norm_num) (by rw [hb]; nlinarith))
  have hx : spreadLayout w W p f d =
      packSlots (2 ^ (p - d) * W) (2 ^ d) fun q ↦ lo q + 2 ^ (w * h) * up q := by
    unfold spreadLayout
    exact congrArg _ (funext hblock)
  have hland : Nat.land (spreadLayout w W p f d) (spreadMask w W p d) =
      packSlots (2 ^ (p - d) * W) (2 ^ d) lo := by
    rw [hx, spreadMask, land_packSlots (fun q _ ↦ hGlt q) (fun q _ ↦ hmask)]
    refine congrArg _ (funext fun q ↦ ?_)
    change (lo q + 2 ^ (w * h) * up q) &&& (2 ^ (h * w) - 1) = lo q
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mul_comm h w, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hlo q)]
  simp only [spreadStep, Nat.add_eq, Nat.sub_eq, Nat.mul_eq]
  rw [hland, hx, packSlots_sub (fun q _ ↦ Nat.le_add_right _ _)]
  simp only [Nat.add_sub_cancel_left]
  change packSlots _ _ lo + packSlots _ _ (fun q ↦ 2 ^ (w * h) * up q) * 2 ^ (h * (W - w)) = _
  rw [Nat.mul_comm (packSlots _ _ _), mul_packSlots, packSlots_add]
  have hpow : ∀ q, 2 ^ (h * (W - w)) * (2 ^ (w * h) * up q) = 2 ^ (h * W) * up q := fun q ↦ by
    rw [← Nat.mul_assoc, ← pow_add, Nat.mul_comm w h, ← Nat.mul_add, Nat.sub_add_cancel hW]
  simp only [hpow]
  rw [show 2 ^ (p - d) * W = 2 * (h * W) by rw [hb]; ring, packSlots_pairs]
  unfold spreadLayout
  rw [hpd, pow_succ, Nat.mul_comm (2 ^ d) 2]
  refine congrArg _ (funext fun k ↦ ?_)
  split_ifs with hk
  · simp only [lo]
    refine congrArg _ (funext fun r ↦ congrArg f ?_)
    nth_rewrite 2 [show k = 2 * (k / 2) by omega]
    ring
  · simp only [up]
    refine congrArg _ (funext fun r ↦ congrArg f ?_)
    nth_rewrite 2 [show k = 2 * (k / 2) + 1 by omega]
    ring

/-- For `w ≤ W`, `f k < 2 ^ w` for every `k` and `n ≤ p`, the first `n` steps take the layout at
depth `0` to the layout at depth `n`. -/
theorem spreadUpTo_layout {w W p : ℕ} (hW : w ≤ W) {f : ℕ → ℕ}
    (hf : ∀ k, f k < 2 ^ w) {n : ℕ} (hn : n ≤ p) :
    spreadUpTo w W p (spreadLayout w W p f 0) n = spreadLayout w W p f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change spreadStep w W p n (spreadUpTo w W p (spreadLayout w W p f 0) n) = _
    rw [ih (by omega), spreadStep_layout hW (by omega) hf]

/-- **Spreading.** The `2^p` slots of width `w` of a packed number become slots of width `W`. -/
theorem spread_packSlots {w W p : ℕ} (hW : w ≤ W) {f : ℕ → ℕ}
    (hf : ∀ k, f k < 2 ^ w) : spread w W p (packSlots w (2 ^ p) f) = packSlots W (2 ^ p) f := by
  have h0 : spreadLayout w W p f 0 = packSlots w (2 ^ p) f := by
    simp [spreadLayout, packSlots_eq_sum]
  have hp : spreadLayout w W p f p = packSlots W (2 ^ p) f := by
    simp [spreadLayout, packSlots_eq_sum]
  rw [spread, ← h0, spreadUpTo_layout hW hf le_rfl, hp]

end CAS.Numerics

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedSlots
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# Rounding every slot of a packed row

`roundSlotBiased w o s x` takes a biased slot value `x = z + slotBias w` to the biased value
`⌊(z + 2 ^ (s - 1)) / 2 ^ s⌋ + slotBias o` of `z / 2 ^ s` rounded to the nearest integer, with
natural-number operations only (`abs_roundSlotBiased_sub_le`), and fits a slot of width `o` when
the signed value is small (`roundSlotBiased_fits'`). `mapRowByHalving f w o d x` applies a map `f`
to the `2 ^ d` slots of `x` and repacks the results in slots of width `o`
(`slot_mapRowByHalving`); `roundRowByHalving` is its instance for `roundSlotBiased`
(`slot_roundRowByHalving`).

## Implementation notes

For `1 ≤ s < w` the power `2 ^ s` divides `slotBias w`, so `(x + 2 ^ (s - 1)) >>> s` is the
rounded value `⌊(z + 2 ^ (s - 1)) / 2 ^ s⌋` plus `slotBias w >>> s`; we subtract that and add
`slotBias o` to rebias the result to width `o`. The truncated subtraction is exact unless the
rounded value is below `-slotBias o`. `abs_roundSlotBiased_sub_le` takes this as its hypothesis,
and `roundSlotBiased_fits` derives it, together with the fit in `o` bits, from
`|z| < 2 ^ (s + b)` and `b + 1 < o`.

`mapRowByHalving f w o (d + 1) x` cuts `x` after slot `2 ^ d - 1` with one `Nat.mod` and one
`Nat.div` by `2 ^ (w 2 ^ d)`, maps both halves by recursion on `d`, and joins the results with
one multiplication by `2 ^ (o 2 ^ d)` and one addition. For a row of `2 ^ d` slots the parts at
each depth together hold its `2 ^ d w` bits, so each of the `d` levels splits numbers of
`2 ^ d w` bits in total and joins results of `2 ^ d o` bits, while reading every slot from the
whole row would divide a number of `2 ^ d w` bits once for each of the `2 ^ d` slots. Since
every mapped slot is below `2 ^ o`, the joined halves do not overlap (`slot_mapRowByHalving`,
by induction on `d` with `slot_add_mul_pow`). `roundRowByHalving` repeats the recursion with
`roundSlotBiased` in place of `f`, written out for kernel evaluation, and
`slot_roundRowByHalving` shows by induction that the two agree.
[PackedRowMaps](PackedRowMaps.lean) rebiases rows with `mapRowByHalving`, and certificates
outside the library use both maps.
-/

@[expose] public section

namespace CAS.Numerics

/-- The rounded and rebiased value of one biased slot. -/
def roundSlotBiased (w o s x : ℕ) : ℕ :=
  Nat.sub (Nat.add (Nat.shiftRight (Nat.add x (Nat.shiftLeft 1 (s - 1))) s) (slotBias o))
    (Nat.shiftRight (slotBias w) s)

/-- The rounded value is within one half of `z / 2 ^ s` when no subtraction truncates. -/
theorem abs_roundSlotBiased_sub_le {w o s x : ℕ} (hs : 1 ≤ s) (hsw : s < w)
    (hlo : (slotBias w) >>> s ≤ (x + 2 ^ (s - 1)) / 2 ^ s + slotBias o) :
    |((roundSlotBiased w o s x : ℤ) - slotBias o : ℝ) - ((x : ℤ) - slotBias w : ℝ) / 2 ^ s| ≤
      1 / 2 := by
  set q := (x + 2 ^ (s - 1)) / 2 ^ s with hq
  set M := slotBias w / 2 ^ s with hMdef
  have hlo' : M ≤ q + slotBias o := by rwa [Nat.shiftRight_eq_div_pow] at hlo
  have hbw : slotBias w = 2 ^ (w - 1) := by rw [← slotBias_succ, Nat.sub_add_cancel (by omega)]
  have hM : M * 2 ^ s = slotBias w := by
    rw [hMdef, hbw, Nat.div_mul_cancel (pow_dvd_pow 2 (by omega))]
  have hout : roundSlotBiased w o s x = q + slotBias o - M := by
    change (x + 1 <<< (s - 1)) >>> s + slotBias o - slotBias w >>> s = _
    rw [Nat.one_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have hD : (0 : ℝ) < 2 ^ s := by positivity
  have hq1 : ((q * 2 ^ s : ℕ) : ℝ) ≤ x + 2 ^ (s - 1) := by
    exact_mod_cast Nat.div_mul_le_self (x + 2 ^ (s - 1)) (2 ^ s)
  have hq2 : (x : ℝ) + 2 ^ (s - 1) < ((q * 2 ^ s + 2 ^ s : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_div_mul_add (a := x + 2 ^ (s - 1)) (b := 2 ^ s) (by positivity)
  have hhalf : (2 : ℝ) ^ s = 2 * 2 ^ (s - 1) := by
    rw [← pow_succ', show s - 1 + 1 = s by omega]
  have hMR : (M : ℝ) * 2 ^ s = slotBias w := by exact_mod_cast hM
  rw [hout, Nat.cast_sub hlo']
  push_cast at hq1 hq2 ⊢
  have key : (q : ℝ) + slotBias o - M - slotBias o - ((x : ℝ) - slotBias w) / 2 ^ s =
      ((q : ℝ) * 2 ^ s - x) / 2 ^ s := by
    rw [← hMR]; field_simp; ring
  rw [key, abs_div, abs_of_pos hD, div_le_iff₀ hD, abs_le]
  constructor <;> linarith

/-- A slot whose signed value lies in `[-2 ^ (s + b), 2 ^ (s + b))` rounds into a slot of width
`o > b + 1` without truncation. -/
theorem roundSlotBiased_fits' {w o s b x : ℕ} (hsw : s < w) (hb : b + 1 < o)
    (hz₁ : -(2 : ℝ) ^ (s + b) ≤ (x : ℝ) - slotBias w) (hz₂ : (x : ℝ) - slotBias w < 2 ^ (s + b)) :
    (slotBias w) >>> s ≤ (x + 2 ^ (s - 1)) / 2 ^ s + slotBias o ∧
      roundSlotBiased w o s x < 2 ^ o := by
  set q := (x + 2 ^ (s - 1)) / 2 ^ s with hq
  set M := slotBias w / 2 ^ s with hMdef
  have hbw : slotBias w = 2 ^ (w - 1) := by rw [← slotBias_succ, Nat.sub_add_cancel (by omega)]
  have hM : M * 2 ^ s = slotBias w := by
    rw [hMdef, hbw, Nat.div_mul_cancel (pow_dvd_pow 2 (by omega))]
  have hMR : (M : ℝ) * 2 ^ s = slotBias w := by exact_mod_cast hM
  have hD : (0 : ℝ) < 2 ^ s := by positivity
  have hq1 : ((q * 2 ^ s : ℕ) : ℝ) ≤ x + 2 ^ (s - 1) := by
    exact_mod_cast Nat.div_mul_le_self (x + 2 ^ (s - 1)) (2 ^ s)
  have hq2 : (x : ℝ) + 2 ^ (s - 1) < ((q * 2 ^ s + 2 ^ s : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_div_mul_add (a := x + 2 ^ (s - 1)) (b := 2 ^ s) (by positivity)
  push_cast at hq1 hq2
  have hhalf : (2 : ℝ) ^ (s - 1) ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) (by omega)
  have hhalf' : (0 : ℝ) < 2 ^ (s - 1) := by positivity
  have hsb : (2 : ℝ) ^ (s + b) = 2 ^ b * 2 ^ s := by rw [pow_add, mul_comm]
  have hup : (q : ℝ) < M + 2 ^ b + 1 := lt_of_mul_lt_mul_right (by nlinarith) hD.le
  have hdown : (M : ℝ) < q + 2 ^ b + 1 := lt_of_mul_lt_mul_right (by nlinarith) hD.le
  have hup' : q < M + 2 ^ b + 1 := by exact_mod_cast hup
  have hdown' : M < q + 2 ^ b + 1 := by exact_mod_cast hdown
  have ho : slotBias o = 2 ^ (o - 1) := by rw [← slotBias_succ, Nat.sub_add_cancel (by omega)]
  have ho2 : 2 ^ o = 2 * 2 ^ (o - 1) := by rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  have hbo : 2 ^ b < 2 ^ (o - 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hshift : (slotBias w) >>> s = M := Nat.shiftRight_eq_div_pow _ _
  refine ⟨by rw [hshift]; omega, ?_⟩
  have hout : roundSlotBiased w o s x = q + slotBias o - M := by
    change (x + 1 <<< (s - 1)) >>> s + slotBias o - slotBias w >>> s = _
    rw [Nat.one_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  rw [hout]
  omega

/-- A slot whose signed value is below `2 ^ (s + b)` in absolute value rounds into a slot of width
`o > b + 1` without truncation. -/
theorem roundSlotBiased_fits {w o s b x : ℕ} (hsw : s < w) (hb : b + 1 < o)
    (hz : |(x : ℝ) - slotBias w| < 2 ^ (s + b)) :
    (slotBias w) >>> s ≤ (x + 2 ^ (s - 1)) / 2 ^ s + slotBias o ∧
      roundSlotBiased w o s x < 2 ^ o :=
  roundSlotBiased_fits' hsw hb (abs_lt.mp hz).1.le (abs_lt.mp hz).2

/-- The slots `0, …, 2 ^ d - 1` of `x`, each rounded by `roundSlotBiased`, in slots of width
`o`, by halving. -/
def roundRowByHalving (w o s : ℕ) : ℕ → ℕ → ℕ
  | 0, x => roundSlotBiased w o s (Nat.mod x (Nat.pow 2 w))
  | d + 1, x =>
    Nat.add (roundRowByHalving w o s d (Nat.mod x (Nat.pow 2 (w * 2 ^ d))))
      (Nat.mul (roundRowByHalving w o s d (Nat.div x (Nat.pow 2 (w * 2 ^ d))))
        (Nat.pow 2 (o * 2 ^ d)))

/-- The slots `0, …, 2 ^ d - 1` of `x`, each mapped by `f`, in slots of width `o`, by halving. -/
def mapRowByHalving (f : ℕ → ℕ) (w o : ℕ) : ℕ → ℕ → ℕ
  | 0, x => f (Nat.mod x (Nat.pow 2 w))
  | d + 1, x =>
    Nat.add (mapRowByHalving f w o d (Nat.mod x (Nat.pow 2 (w * 2 ^ d))))
      (Nat.mul (mapRowByHalving f w o d (Nat.div x (Nat.pow 2 (w * 2 ^ d))))
        (Nat.pow 2 (o * 2 ^ d)))

/-- When every mapped slot is below `2 ^ o`, the mapped row is below `2 ^ (o 2 ^ d)` and its
slots are the mapped slots. -/
theorem slot_mapRowByHalving {f : ℕ → ℕ} {w o : ℕ} (d : ℕ) {x : ℕ}
    (h : ∀ k < 2 ^ d, f (slot w k x) < 2 ^ o) :
    mapRowByHalving f w o d x < 2 ^ (o * 2 ^ d) ∧
      ∀ k < 2 ^ d, slot o k (mapRowByHalving f w o d x) = f (slot w k x) := by
  induction d generalizing x with
  | zero =>
    have h0 : slot w 0 x = x % 2 ^ w := by rw [slot_eq]; simp
    have hlt := h 0 (by norm_num)
    rw [h0] at hlt
    have hdef : mapRowByHalving f w o 0 x = f (x % 2 ^ w) := rfl
    rw [hdef]
    refine ⟨by simpa using hlt, fun k hk ↦ ?_⟩
    obtain rfl : k = 0 := by simpa using hk
    rw [h0, slot_eq]
    simp [Nat.mod_eq_of_lt hlt]
  | succ d ih =>
    set m := 2 ^ d with hm
    have hlo := ih (x := x % 2 ^ (w * m)) fun k hk ↦ by
      rw [slot_mod_two_pow hk]; exact h k (by rw [pow_succ]; omega)
    have hhi := ih (x := x / 2 ^ (w * m)) fun k hk ↦ by
      rw [slot_div_two_pow]; exact h (k + m) (by rw [pow_succ]; omega)
    have hdef : mapRowByHalving f w o (d + 1) x = mapRowByHalving f w o d (x % 2 ^ (w * m)) +
        mapRowByHalving f w o d (x / 2 ^ (w * m)) * 2 ^ (o * m) := rfl
    rw [hdef]
    refine ⟨?_, fun k hk ↦ ?_⟩
    · have e : 2 ^ (o * 2 ^ (d + 1)) = 2 ^ (o * m) * 2 ^ (o * m) := by
        rw [← pow_add, pow_succ, ← hm]
        ring_nf
      have := Nat.mul_le_mul_right (2 ^ (o * m)) hhi.1
      rw [Nat.succ_mul] at this
      rw [e]
      omega
    · rw [slot_add_mul_pow hlo.1]
      split_ifs with hkm
      · rw [hlo.2 k hkm, slot_mod_two_pow hkm]
      · have hkm' : k - m < 2 ^ d := by rw [pow_succ] at hk; omega
        rw [hhi.2 (k - m) hkm', slot_div_two_pow, (by omega : k - m + m = k)]

/-- When every rounded slot is below `2 ^ o`, the rounded row is below `2 ^ (o 2 ^ d)` and its
slots are the rounded slots. -/
theorem slot_roundRowByHalving {w o s : ℕ} (d : ℕ) {x : ℕ}
    (h : ∀ k < 2 ^ d, roundSlotBiased w o s (slot w k x) < 2 ^ o) :
    roundRowByHalving w o s d x < 2 ^ (o * 2 ^ d) ∧
      ∀ k < 2 ^ d, slot o k (roundRowByHalving w o s d x) = roundSlotBiased w o s (slot w k x) := by
  have e : ∀ d x,
      roundRowByHalving w o s d x = mapRowByHalving (roundSlotBiased w o s) w o d x := by
    intro d
    induction d with
    | zero => intro x; rfl
    | succ d ih => intro x; simp only [roundRowByHalving, mapRowByHalving, ih]
  simpa only [e] using slot_mapRowByHalving d h

end CAS.Numerics

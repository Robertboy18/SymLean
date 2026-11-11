/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedSpread
public import CAS.Numerics.PackedSpreadSteps
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# Signed packed rows

A row of integers `c 0, …, c (n - 1)` is stored as the integer `zPack W n c = ∑_q c q 2 ^ (W q)`.
Sums and products of rows are then integer sums and products (`zPack_mul`: the product of two
rows is the row of their convolution), with no condition on the entries. Reading slots, cutting
out a window and rounding every entry go through the biased natural number
`zPack W n c + ∑_q 2 ^ (W - 1) 2 ^ (W q)`, whose slots are `c q + 2 ^ (W - 1)` as long as every
entry lies in `[-2 ^ (W - 1), 2 ^ (W - 1))` (`zPack_add_zBias`): `zRestrict_zPack`,
`zRound_zPack`. `zGuard` checks on the biased row that every entry fits `g` bits
(`abs_le_of_zGuard`), and `zPosSum`, `zAbsSum` give the sum of the nonnegative entries and the
sum of the absolute values with a few operations on the whole row and one remainder modulo
`2 ^ W - 1` (`zPosSum_zPack`, `zAbsSum_zPack`, from `packSlots_mod`). `zPack_sparse`,
`zConv_sparse_left` and `spreadSlots_biased` treat factors whose entries sit at a stride, and
`abs_zConv_le` bounds the convolution by `n A B`.

## Implementation notes

`zPack_mul` is Kronecker substitution: `zPack W` evaluates the polynomial of a row at `2 ^ W`,
so one integer product gives the whole convolution, and its entries can be read back once they
fit their slots. We keep a signed row as one integer rather than a biased natural number, so sums
and products need no correction terms; the bias appears only where slots are read. The
remainder modulo `2 ^ W - 1` casts out the base: `2 ^ W` is `1` modulo `2 ^ W - 1`, so a packed
row is congruent to the sum of its slots, which is the sum itself when it is below `2 ^ W - 1`.
The operations call `Int.add`, `Int.mul`, `Nat.rec` and the other primitive operations
directly, which the kernel evaluates several times faster than the instance-based notation.

## References

* David Harvey, "Faster polynomial multiplication via multipoint Kronecker substitution",
  *Journal of Symbolic Computation* 44 (2009), pp. 1502-1510,
  <https://doi.org/10.1016/j.jsc.2009.05.004>. Section 1 for the substitution: evaluate at a
  power of two and multiply the integers.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-! ### Operations -/

/-- `∑_{j < n} f j` over the integers, by `Nat.rec`. -/
def zSum (n : ℕ) (f : ℕ → ℤ) : ℤ := Nat.rec (motive := fun _ ↦ ℤ) 0 (fun j s ↦ Int.add s (f j)) n

/-- The bias row `∑_{q < n} 2 ^ (W - 1) 2 ^ (W q)`. -/
def zBias (W n : ℕ) : ℤ := Int.ofNat (constSlots W n (Nat.pow 2 (Nat.sub W 1)))

/-- The slots `a, …, a + L - 1` of a signed row of `n` slots of width `W`. -/
def zRestrict (W n a L : ℕ) (x : ℤ) : ℤ :=
  Int.sub (Int.ofNat (Nat.land (Nat.shiftRight (Int.toNat (Int.add x (zBias W n))) (Nat.mul W a))
    (slotMask (Nat.mul W L)))) (zBias W L)

/-- The offset row of `zRound`: bias plus half a unit of `2 ^ s`. -/
def zRoundOffset (W n s : ℕ) : ℤ :=
  Int.ofNat (constSlots W n (Nat.add (Nat.pow 2 (Nat.sub W 1)) (Nat.pow 2 (Nat.sub s 1))))

/-- The entries of a signed row of `n` slots of width `W` rounded from `2 ^ s` to `1` (half
up). -/
def zRound (W n s : ℕ) (x : ℤ) : ℤ :=
  let y := Int.toNat (Int.add x (zRoundOffset W n s))
  Int.sub (Int.ofNat (Nat.shiftRight (Nat.sub y (Nat.land y (constSlots W n
    (Nat.sub (Nat.pow 2 s) 1)))) s))
    (Int.ofNat (constSlots W n (Nat.pow 2 (Nat.sub (Nat.sub W 1) s))))

/-- Slot `k` of a signed row of `n` slots of width `W`. -/
def zSlot (W n k : ℕ) (x : ℤ) : ℤ :=
  Int.subNatNat (slot W k (Int.toNat (Int.add x (zBias W n)))) (Nat.pow 2 (Nat.sub W 1))

/-- `c` rounded from `2 ^ g` to `1` (half up). -/
def zShift (g : ℕ) (c : ℤ) : ℤ :=
  Int.ediv (Int.add c (Int.ofNat (Nat.pow 2 (Nat.sub g 1)))) (Int.ofNat (Nat.pow 2 g))

/-- `x · 2 ^ (W k)`. -/
def zUp (W k : ℕ) (x : ℤ) : ℤ := Int.mul x (Int.ofNat (Nat.shiftLeft 1 (Nat.mul W k)))

/-- Every one of the first `n` entries of a signed row fits `g` bits, checked on the biased
form. -/
def zGuard (W n g : ℕ) (x : ℤ) : Bool := signedGuardCheck W g n (Int.toNat (Int.add x (zBias W n)))

/-! ### Rows -/


/-- The signed packed row `∑_{q < n} c q 2 ^ (W q)`. -/
def zPack (W n : ℕ) (c : ℕ → ℤ) : ℤ := ∑ q ∈ range n, c q * 2 ^ (W * q)

/-- Every one of the first `n` entries lies in `[-2 ^ (W - 1), 2 ^ (W - 1))`. -/
def ZFits (W n : ℕ) (c : ℕ → ℤ) : Prop := ∀ q < n, -2 ^ (W - 1) ≤ c q ∧ c q < 2 ^ (W - 1)

/-- `zSum n f` is the sum of `f j` over `j ∈ range n`. -/
theorem zSum_eq (n : ℕ) (f : ℕ → ℤ) : zSum n f = ∑ j ∈ range n, f j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_range_succ, ← ih]; rfl

/-- `zShift g c` is `(c + 2 ^ (g - 1)) / 2 ^ g`, in integer division. -/
theorem zShift_eq (g : ℕ) (c : ℤ) : zShift g c = (c + 2 ^ (g - 1)) / 2 ^ g := by
  simp [zShift, ← Int.div_def]

/-- `zUp W k x` is `x * 2 ^ (W * k)`. -/
theorem zUp_eq (W k : ℕ) (x : ℤ) : zUp W k x = x * 2 ^ (W * k) := by
  simp [zUp, Nat.shiftLeft_eq]

/-- For `0 < W`, the bias row `zBias W n` is `∑ q ∈ range n, 2 ^ (W - 1) * 2 ^ (W * q)`. -/
theorem zBias_eq {W : ℕ} (hW : 0 < W) (n : ℕ) :
    zBias W n = ∑ q ∈ range n, (2 : ℤ) ^ (W - 1) * 2 ^ (W * q) := by
  simp only [zBias, Int.ofNat_eq_natCast, Nat.pow_eq, Nat.sub_eq]
  rw [constSlots_eq hW, packSlots_eq_sum]
  push_cast
  rfl

/-- For `0 < W` and entries with `ZFits W n c`, the biased row `zPack W n c + zBias W n` is the
natural packing of the biased entries `(c q + 2 ^ (W - 1)).toNat`. -/
theorem zPack_add_zBias {W n : ℕ} (hW : 0 < W) {c : ℕ → ℤ} (h : ZFits W n c) :
    zPack W n c + zBias W n =
      ((packSlots W n fun q ↦ (c q + 2 ^ (W - 1)).toNat : ℕ) : ℤ) := by
  rw [zBias_eq hW, zPack, ← sum_add_distrib, packSlots_eq_sum]
  push_cast
  refine sum_congr rfl fun q hq ↦ ?_
  rw [Int.toNat_of_nonneg (by linarith [(h q (mem_range.mp hq)).1])]
  ring

/-- For `0 < W` and `ZFits W n c`, every biased entry `(c q + 2 ^ (W - 1)).toNat` with `q < n`
is below `2 ^ W`. -/
theorem toNat_slots_lt {W n : ℕ} (hW : 0 < W) {c : ℕ → ℤ} (h : ZFits W n c) :
    ∀ q < n, (c q + 2 ^ (W - 1)).toNat < 2 ^ W := by
  intro q hq
  have := h q hq
  have h2 := pow_sub_one_mul hW.ne' (2 : ℤ)
  exact (Int.toNat_lt (by linarith)).2 (by push_cast; linarith)

/-- For `0 < W` and `ZFits W n c`, the natural number `(zPack W n c + zBias W n).toNat` that
`zSlot`, `zRestrict`, `zGuard` and `zPosSum` read is the packing of the biased entries
`(c q + 2 ^ (W - 1)).toNat`. -/
theorem zPack_biased_toNat {W n : ℕ} (hW : 0 < W) {c : ℕ → ℤ} (h : ZFits W n c) :
    Int.toNat (Int.add (zPack W n c) (zBias W n)) =
      packSlots W n fun q ↦ (c q + 2 ^ (W - 1)).toNat := by
  change (zPack W n c + zBias W n).toNat = _
  rw [zPack_add_zBias hW h, Int.toNat_natCast]

/-- For `L ≤ N` and entries `f q < 2 ^ W` for `q < N`, masking the packing of `N` entries with
`slotMask (W * L)` leaves the packing of the first `L`. -/
theorem packSlots_land_slotMask {W N L : ℕ} (hL : L ≤ N) {f : ℕ → ℕ}
    (hf : ∀ q < N, f q < 2 ^ W) :
    Nat.land (packSlots W N f) (slotMask (W * L)) = packSlots W L f := by
  change packSlots W N f &&& slotMask (W * L) = _
  rw [slotMask_eq, Nat.and_two_pow_sub_one_eq_mod]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hL
  have hsplit : packSlots W (L + d) f =
      packSlots W L f + 2 ^ (W * L) * packSlots W d (fun r ↦ f (L + r)) := by
    simp only [packSlots_eq_sum, sum_range_add, mul_sum]
    congr 1
    refine sum_congr rfl fun r _ ↦ ?_
    rw [Nat.mul_add, pow_add]; ring
  rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt
    (packSlots_lt fun q hq ↦ hf q (by omega))]

/-- **A window of slots.** -/
theorem zRestrict_zPack {W n a L : ℕ} (hW : 0 < W) {c : ℕ → ℤ} (h : ZFits W n c)
    (haL : a + L ≤ n) :
    zRestrict W n a L (zPack W n c) = zPack W L fun q ↦ c (a + q) := by
  unfold zRestrict
  rw [zPack_biased_toNat hW h, Nat.mul_eq, shiftRight_packSlots W n a _ (toNat_slots_lt hW h),
    Nat.mul_eq, packSlots_land_slotMask (by omega) fun q hq ↦ toNat_slots_lt hW h _ (by omega)]
  simp_rw [Nat.add_comm _ a]
  exact sub_eq_of_eq_add (zPack_add_zBias hW fun q hq ↦ h (a + q) (by omega)).symm

/-- **Rounding every entry in place.** -/
theorem zRound_zPack {W n s : ℕ} (hsW : s + 1 ≤ W) {c : ℕ → ℤ}
    (h : ∀ q < n, -2 ^ (W - 1) ≤ c q ∧ c q + 2 ^ (s - 1) < 2 ^ (W - 1)) :
    zRound W n s (zPack W n c) = zPack W n fun q ↦ (c q + 2 ^ (s - 1)) / 2 ^ s := by
  have hW : 0 < W := by omega
  have hpowW := pow_sub_one_mul hW.ne' (2 : ℤ)
  have hpowS : (2 : ℤ) ^ (W - 1) = 2 ^ (W - 1 - s) * 2 ^ s := by rw [← pow_add]; congr 1; omega
  set Y : ℕ → ℕ := fun q ↦ (c q + 2 ^ (W - 1) + 2 ^ (s - 1)).toNat
  have hY : ∀ q < n, (Y q : ℤ) = c q + 2 ^ (W - 1) + 2 ^ (s - 1) := fun q hq ↦
    Int.toNat_of_nonneg (by linarith [(h q hq).1, pow_pos (two_pos (α := ℤ)) (s - 1)])
  have hYlt : ∀ q < n, Y q < 2 ^ W := fun q hq ↦
    Int.ofNat_lt.1 (by push_cast; linarith [hY q hq, (h q hq).2])
  have hy : Int.toNat (Int.add (zPack W n c) (zRoundOffset W n s)) = packSlots W n Y := by
    rw [← Int.toNat_natCast (packSlots W n Y), packSlots_eq_sum]
    simp only [zRoundOffset, Int.ofNat_eq_natCast, Nat.pow_eq, Nat.sub_eq, Nat.add_eq, Int.add_def]
    rw [constSlots_eq hW, packSlots_eq_sum, zPack]
    push_cast
    rw [← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun q hq ↦ ?_
    rw [hY q (mem_range.mp hq)]
    ring
  have hmask : constSlots W n (Nat.sub (Nat.pow 2 s) 1) = packSlots W n fun _ ↦ 2 ^ s - 1 :=
    constSlots_eq hW n _
  have hm1 : ∀ q < n, 2 ^ s - 1 < 2 ^ W := fun _ _ ↦
    (Nat.sub_le _ _).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hland : Nat.land (packSlots W n Y) (packSlots W n fun _ ↦ 2 ^ s - 1) =
      packSlots W n fun q ↦ Y q % 2 ^ s := by
    rw [land_packSlots hYlt hm1]
    exact packSlots_congr fun q _ ↦ Nat.and_two_pow_sub_one_eq_mod (Y q) s
  have hsub : Nat.sub (packSlots W n Y) (packSlots W n fun q ↦ Y q % 2 ^ s) =
      2 ^ s * packSlots W n (fun q ↦ Y q / 2 ^ s) := by
    rw [mul_packSlots]
    refine Nat.sub_eq_of_eq_add ?_
    rw [packSlots_add]
    exact packSlots_congr fun q _ ↦ (Nat.div_add_mod _ _).symm
  have hshr : Nat.shiftRight (2 ^ s * packSlots W n (fun q ↦ Y q / 2 ^ s)) s =
      packSlots W n (fun q ↦ Y q / 2 ^ s) := by
    change _ >>> s = _
    rw [Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ (by positivity)]
  unfold zRound
  simp only
  rw [hy, hmask, hland, hsub, hshr]
  simp only [Int.ofNat_eq_natCast, Nat.pow_eq, Nat.sub_eq]
  rw [constSlots_eq hW, packSlots_eq_sum, packSlots_eq_sum, zPack]
  change ((∑ k ∈ range n, Y k / 2 ^ s * 2 ^ (W * k) : ℕ) : ℤ) -
    ((∑ k ∈ range n, 2 ^ (W - 1 - s) * 2 ^ (W * k) : ℕ) : ℤ) = _
  push_cast
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun q hq ↦ ?_
  rw [hY q (mem_range.mp hq), hpowS, add_right_comm, Int.add_mul_ediv_right _ _ (by positivity)]
  ring

/-! ### Sums, shifts and products of rows -/

/-- The sum of two rows is the row of the entrywise sums. -/
theorem zPack_add (W n : ℕ) (c d : ℕ → ℤ) :
    zPack W n c + zPack W n d = zPack W n fun q ↦ c q + d q := by
  simp only [zPack, ← sum_add_distrib, add_mul]

/-- The difference of two rows is the row of the entrywise differences. -/
theorem zPack_sub (W n : ℕ) (c d : ℕ → ℤ) :
    zPack W n c - zPack W n d = zPack W n fun q ↦ c q - d q := by
  simp only [zPack, ← sum_sub_distrib, sub_mul]

/-- The negation of a row is the row of the negated entries. -/
theorem zPack_neg (W n : ℕ) (c : ℕ → ℤ) : -zPack W n c = zPack W n fun q ↦ -c q := by
  simp only [zPack, ← sum_neg_distrib, neg_mul]

/-- An integer multiple `x * zPack W n c` is the row of the entries `x * c q`. -/
theorem zPack_smul (W n : ℕ) (x : ℤ) (c : ℕ → ℤ) :
    x * zPack W n c = zPack W n fun q ↦ x * c q := by
  simp only [zPack, mul_sum, mul_assoc]

/-- Entries past `n` that vanish do not change the row. -/
theorem zPack_extend {W n N : ℕ} (hn : n ≤ N) {c : ℕ → ℤ} (hc : ∀ q, n ≤ q → q < N → c q = 0) :
    zPack W N c = zPack W n c := by
  refine (sum_subset (range_subset_range.2 hn) fun q hq hq' ↦ ?_).symm
  simp [hc q (by simpa using hq') (by simpa using hq)]

/-- Multiplying by `2 ^ (W k)` moves every entry up by `k` slots. -/
theorem zUp_zPack (W k n : ℕ) (c : ℕ → ℤ) :
    zUp W k (zPack W n c) = zPack W (n + k) fun q ↦ if k ≤ q then c (q - k) else 0 := by
  rw [zUp_eq, zPack, zPack, Nat.add_comm n k, sum_range_add, sum_mul,
    sum_eq_zero (s := range k) fun q hq ↦ by simp [not_le.2 (mem_range.1 hq)], zero_add]
  refine sum_congr rfl fun q _ ↦ ?_
  simp only [Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left, Nat.mul_add, pow_add]
  ring

/-- The convolution of two rows of `n` and `m` entries. -/
def zConv (n m : ℕ) (c d : ℕ → ℤ) (q : ℕ) : ℤ :=
  ∑ i ∈ range n, ∑ j ∈ range m, if i + j = q then c i * d j else 0

/-- **Products.** The product of two rows is the row of their convolution. -/
theorem zPack_mul (W n m : ℕ) (c d : ℕ → ℤ) :
    zPack W n c * zPack W m d = zPack W (n + m) (zConv n m c d) := by
  rw [zPack, zPack, sum_mul_sum]
  simp only [zPack, zConv, sum_mul, ite_mul, zero_mul]
  rw [eq_comm, sum_comm]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [mem_range] at hi hj
  rw [sum_ite_eq, ite_eq_left (mem_range.2 (by omega)), Nat.mul_add, pow_add]
  ring

/-- Every entry of the convolution is at most `n A B`. -/
theorem abs_zConv_le {n m : ℕ} {c d : ℕ → ℤ} {A B : ℤ} (hB : 0 ≤ B)
    (hc : ∀ i < n, |c i| ≤ A) (hd : ∀ j < m, |d j| ≤ B) (q : ℕ) :
    |zConv n m c d q| ≤ n * (A * B) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [zConv]
  have hA : 0 ≤ A := (abs_nonneg _).trans (hc 0 hn)
  unfold zConv
  have hinner : ∀ i ∈ range n, |∑ j ∈ range m, if i + j = q then c i * d j else 0| ≤ A * B := by
    intro i hi
    rw [mem_range] at hi
    by_cases hiq : i ≤ q
    · have hcond : ∀ j, (i + j = q) ↔ (q - i = j) := fun j ↦ by omega
      simp_rw [hcond]
      rw [sum_ite_eq]
      split_ifs with hm
      · rw [abs_mul]
        exact mul_le_mul (hc i hi) (hd _ (mem_range.mp hm)) (abs_nonneg _) hA
      · simp [mul_nonneg hA hB]
    · rw [sum_eq_zero fun j _ ↦ by rw [ite_eq_right_iff]; intro h; omega]
      simp [mul_nonneg hA hB]
  calc |∑ i ∈ range n, ∑ j ∈ range m, if i + j = q then c i * d j else 0|
      ≤ ∑ i ∈ range n, |∑ j ∈ range m, if i + j = q then c i * d j else 0| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range n, A * B := sum_le_sum hinner
    _ = n * (A * B) := by simp

/-! ### Guards and spreading -/

/-- A passing guard bounds every entry by `2 ^ (g - 1)`. -/
theorem abs_le_of_zGuard {W n g : ℕ} {c : ℕ → ℤ} (h : ZFits W n c)
    (hG : zGuard W n g (zPack W n c) = true) {q : ℕ} (hq : q < n) : |c q| ≤ 2 ^ (g - 1) := by
  rcases lt_or_ge g W with hg | hg
  swap
  · have hpow : (2 : ℤ) ^ (W - 1) ≤ 2 ^ (g - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [abs_le]
    constructor <;> linarith [(h q hq).1, (h q hq).2]
  have hW : 0 < W := by omega
  unfold zGuard at hG
  rw [zPack_biased_toNat hW h] at hG
  have hfit := fitsSlot_of_signedGuardCheck hg hG hq
  have hslot : signedSlot W q (packSlots W n fun q ↦ (c q + 2 ^ (W - 1)).toNat) = c q := by
    rw [signedSlot, slot_packed_eq (toNat_slots_lt hW h), ite_eq_left hq,
      Int.toNat_of_nonneg (by linarith [(h q hq).1]), slotBias_eq, ← pow_sub_one_mul hW.ne',
      Nat.mul_div_cancel _ two_pos]
    push_cast
    ring
  rw [hslot] at hfit
  have hle := natAbs_le_of_fitsSlot hfit
  rw [slotBias_eq] at hle
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hle.trans (Nat.div_le_of_le_mul (by
    rw [← pow_succ']
    exact Nat.pow_le_pow_right two_pos (by omega)))

/-- Sparse rows: entries `u k` at the slots `T k`. -/
theorem zPack_sparse (W T n : ℕ) (hT : 0 < T) (u : ℕ → ℤ) :
    zPack W (T * n) (fun x ↦ if x % T = 0 then u (x / T) else 0) =
      ∑ k ∈ range n, u k * 2 ^ (W * T * k) := by
  rw [zPack, sum_range_mul_eq]
  refine sum_congr rfl fun y _ ↦ ?_
  rw [sum_eq_single_of_mem 0 (mem_range.2 hT) fun x hx hx0 ↦ ?_]
  · simp [Nat.mul_div_cancel_left _ hT, mul_assoc]
  · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.1 hx), hx0]

/-- **Spreading a biased row.** Spreading the slots of a biased row to the stride `S` and
removing the bias leaves the entries at the slots of width `w S`. -/
theorem spreadSlots_biased {w S n : ℕ} (hS : n < S) (hw : 0 < w) {u : ℕ → ℤ} (β : ℕ)
    (hu : ∀ k < n, 0 ≤ u k + β ∧ u k + β < 2 ^ w) :
    Int.sub (Int.ofNat (spreadSlots w S n (packSlots w n fun k ↦ (u k + β).toNat)))
        (Int.ofNat (constSlots (w * S) n β)) = ∑ k ∈ range n, u k * 2 ^ (w * S * k) := by
  have hlt : ∀ k < n, (u k + β).toNat < 2 ^ w := fun k hk ↦
    (Int.toNat_lt (hu k hk).1).2 (by exact_mod_cast (hu k hk).2)
  rw [spreadSlots_eq hS (packSlots_lt hlt), constSlots_eq (Nat.mul_pos hw (by omega))]
  change ((_ : ℕ) : ℤ) - ((_ : ℕ) : ℤ) = _
  rw [packSlots_eq_sum (w * S), packSlots_eq_sum (w * S)]
  push_cast
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [slot_packed_eq hlt, ite_eq_left (mem_range.mp hk),
    Int.toNat_of_nonneg (hu k (mem_range.mp hk)).1]
  ring

/-! ### Biases and sparse factors -/

/-- A row whose entries plus `β` lie in `[0, 2 ^ W)`, plus the constant row `β`, is the packing
of the biased entries. -/
theorem zPack_add_const {W n : ℕ} (hW : 0 < W) {c : ℕ → ℤ} (β : ℕ)
    (h : ∀ q < n, 0 ≤ c q + β ∧ c q + β < 2 ^ W) :
    zPack W n c + (constSlots W n β : ℤ) = ((packSlots W n fun q ↦ (c q + β).toNat : ℕ) : ℤ) := by
  rw [constSlots_eq hW, packSlots_eq_sum, packSlots_eq_sum, zPack]
  push_cast
  rw [← sum_add_distrib]
  refine sum_congr rfl fun q hq ↦ ?_
  rw [Int.toNat_of_nonneg (h q (mem_range.mp hq)).1]
  ring

/-- The convolution with a factor that is sparse at the stride `T`. -/
theorem zConv_sparse_left (T n m : ℕ) (hT : 0 < T) (u d : ℕ → ℤ) (y : ℕ) :
    zConv (T * n) m (fun x ↦ if x % T = 0 then u (x / T) else 0) d y =
      ∑ k ∈ range n, if T * k ≤ y ∧ y - T * k < m then u k * d (y - T * k) else 0 := by
  rw [zConv, sum_range_mul_eq]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [sum_eq_single_of_mem 0 (mem_range.2 hT) fun x hx hx0 ↦ sum_eq_zero fun j _ ↦ ?_]
  · simp only [zero_add, Nat.mul_mod_right, ↓reduceIte, Nat.mul_div_cancel_left _ hT]
    split_ifs with hk
    · rw [sum_eq_single (y - T * k) (fun j _ hj ↦ ite_eq_right (by omega))
        fun hj ↦ absurd (mem_range.2 hk.2) hj, ite_eq_left (by omega)]
    · exact sum_eq_zero fun j hj ↦ ite_eq_right (by simp at hj; omega)
  · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.1 hx), hx0]

/-- Rows whose first `n` entries agree are equal. -/
theorem zPack_congr {W n : ℕ} {c d : ℕ → ℤ} (h : ∀ q < n, c q = d q) : zPack W n c = zPack W n d :=
  sum_congr rfl fun q hq ↦ by rw [h q (mem_range.mp hq)]

/-- Entries bounded by `2 ^ g` with `g + 1 < W` fit the slots. -/
theorem zFits_of_abs_le {W n g : ℕ} (hg : g + 1 < W) {c : ℕ → ℤ}
    (h : ∀ q < n, |c q| ≤ 2 ^ g) : ZFits W n c := by
  intro q hq
  obtain ⟨h1, h2⟩ := abs_le.1 (h q hq)
  have h3 : (2 : ℤ) ^ g < 2 ^ (W - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  constructor <;> linarith

/-- The row of zero entries is `0`. -/
@[simp] theorem zPack_zero (W n : ℕ) : zPack W n (fun _ ↦ 0) = 0 := by simp [zPack]

/-- The convolution of rows of `n` and `m` entries vanishes from slot `n + m - 1` on. -/
theorem zConv_eq_zero_of_le {n m q : ℕ} (c d : ℕ → ℤ) (hq : n + m ≤ q + 1) :
    zConv n m c d q = 0 := by
  unfold zConv
  refine sum_eq_zero fun i hi ↦ sum_eq_zero fun j hj ↦ ?_
  rw [mem_range] at hi hj
  rw [ite_eq_right (by omega)]

/-- The product of two rows, as a row of `n + m - 1` entries. -/
theorem zPack_mul' (W n m : ℕ) (c d : ℕ → ℤ) :
    zPack W n c * zPack W m d = zPack W (n + m - 1) (zConv n m c d) := by
  rw [zPack_mul, zPack_extend (n := n + m - 1) (N := n + m) (by omega)
    fun q hq _ ↦ zConv_eq_zero_of_le c d (by omega)]

/-- `abs_zConv_le` with the bounds on `c` and `d` assumed at every index: for `0 ≤ B`,
`|c i| ≤ A` and `|d j| ≤ B`, every entry of `zConv n m c d` is at most `n * (A * B)` in absolute
value. -/
theorem abs_zConv_le' {n m : ℕ} {c d : ℕ → ℤ} {A B : ℤ} (hB : 0 ≤ B)
    (hc : ∀ i, |c i| ≤ A) (hd : ∀ j, |d j| ≤ B) (q : ℕ) :
    |zConv n m c d q| ≤ n * (A * B) :=
  abs_zConv_le hB (fun i _ ↦ hc i) (fun j _ ↦ hd j) q

/-- A row of `n` entries as a row of `N ≥ n` entries, zero past `n`. -/
theorem zPack_truncate {W n N : ℕ} (hn : n ≤ N) (c : ℕ → ℤ) :
    zPack W n c = zPack W N fun q ↦ if q < n then c q else 0 := by
  rw [zPack_extend hn fun q hq _ ↦ by rw [ite_eq_right (by omega)]]
  exact zPack_congr fun q hq ↦ by rw [ite_eq_left hq]

/-! ### Sums of absolute values -/

/-- The sum of the nonnegative entries of a signed row of `n` slots of width `W`: the top bit of
every biased slot marks a nonnegative entry, these bits times `2 ^ (W - 1) - 1` form the mask of
the entries without the bias, and one remainder modulo `2 ^ W - 1` sums the masked slots. -/
def zPosSum (W n : ℕ) (x : ℤ) : ℕ :=
  let b := Int.toNat (Int.add x (zBias W n))
  Nat.mod (Nat.land b (Nat.mul (Nat.shiftRight (Nat.land b (constSlots W n (Nat.pow 2
    (Nat.sub W 1)))) (Nat.sub W 1)) (Nat.sub (Nat.pow 2 (Nat.sub W 1)) 1)))
    (Nat.sub (Nat.pow 2 W) 1)

/-- The sum of the absolute values of the entries of a signed row of `n` slots of width `W`. -/
def zAbsSum (W n : ℕ) (x : ℤ) : ℕ := Nat.add (zPosSum W n x) (zPosSum W n (Int.neg x))

/-- A packed row modulo `2 ^ W - 1` is the sum of its slots modulo `2 ^ W - 1`. -/
theorem packSlots_mod (W n : ℕ) (f : ℕ → ℕ) :
    packSlots W n f % (2 ^ W - 1) = (∑ k ∈ range n, f k) % (2 ^ W - 1) := by
  set M := 2 ^ W - 1 with hM
  have hW : 2 ^ W = M + 1 := by have := Nat.one_le_two_pow (n := W); omega
  have hp : ∀ k, 2 ^ (W * k) % M = 1 % M := fun k ↦ by
    rw [pow_mul, Nat.pow_mod, hW, Nat.add_mod_left, ← Nat.pow_mod, one_pow]
  induction n with
  | zero => simp [packSlots, natSum]
  | succ n ih =>
    rw [packSlots_succ, sum_range_succ, Nat.add_mod, ih, Nat.mul_mod, hp, ← Nat.mul_mod,
      Nat.mul_one, ← Nat.add_mod]

/-- For `v < 2 ^ W`, `Nat.land v (2 ^ (W - 1))` is `v / 2 ^ (W - 1) * 2 ^ (W - 1)`: it keeps bit
`W - 1` of `v`. -/
theorem land_two_pow_pred {v W : ℕ} (hv : v < 2 ^ W) :
    Nat.land v (2 ^ (W - 1)) = v / 2 ^ (W - 1) * 2 ^ (W - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  change (v &&& 2 ^ (W - 1)).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : W - 1 = j
  · subst hj; simp
  · rw [decide_eq_false hj, Bool.and_false]
    by_cases hj' : W - 1 ≤ j
    · have : W ≤ j := by omega
      rw [show j - (W - 1) + (W - 1) = j by omega,
        Nat.testBit_lt_two_pow (hv.trans_le (Nat.pow_le_pow_right (by norm_num) this))]
      simp
    · simp [hj']

/-- **The sum of the nonnegative entries.** -/
theorem zPosSum_zPack {W n g : ℕ} (hg : g + 1 < W) {c : ℕ → ℤ} (hc : ∀ q < n, |c q| ≤ 2 ^ g)
    (hn : n * 2 ^ g < 2 ^ W - 1) :
    zPosSum W n (zPack W n c) = ∑ q ∈ range n, (max (c q) 0).toNat := by
  have hW : 0 < W := by omega
  have hfit := zFits_of_abs_le hg hc
  set B : ℕ → ℕ := fun q ↦ (c q + 2 ^ (W - 1)).toNat with hB
  have hBlt : ∀ q < n, B q < 2 ^ W := toNat_slots_lt hW hfit
  have hpow : 2 ^ W = 2 * 2 ^ (W - 1) := by rw [← pow_succ']; congr 1; omega
  have hcB : ∀ q < n, (B q : ℤ) = c q + 2 ^ (W - 1) := fun q hq ↦
    Int.toNat_of_nonneg (by have := (hfit q hq).1; linarith)
  -- the top bits
  have hH : Nat.land (packSlots W n B) (constSlots W n (Nat.pow 2 (Nat.sub W 1))) =
      packSlots W n fun q ↦ B q / 2 ^ (W - 1) * 2 ^ (W - 1) := by
    rw [constSlots_eq hW, land_packSlots hBlt (fun _ _ ↦ by
      change 2 ^ (W - 1) < 2 ^ W; exact Nat.pow_lt_pow_right (by norm_num) (by omega))]
    exact packSlots_congr fun q hq ↦ land_two_pow_pred (hBlt q hq)
  have hS : Nat.shiftRight (packSlots W n fun q ↦ B q / 2 ^ (W - 1) * 2 ^ (W - 1))
      (Nat.sub W 1) = packSlots W n fun q ↦ B q / 2 ^ (W - 1) := by
    rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.sub_eq]
    simp_rw [Nat.mul_comm _ (2 ^ (W - 1))]
    rw [← mul_packSlots, Nat.mul_div_cancel_left _ (by positivity)]
  have hM : Nat.mul (packSlots W n fun q ↦ B q / 2 ^ (W - 1)) (Nat.sub (Nat.pow 2 (Nat.sub W 1)) 1)
      = packSlots W n fun q ↦ (2 ^ (W - 1) - 1) * (B q / 2 ^ (W - 1)) := by
    rw [Nat.mul_eq, Nat.mul_comm, ← mul_packSlots]; rfl
  have hle1 : ∀ q < n, B q / 2 ^ (W - 1) ≤ 1 := fun q hq ↦
    Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by have := hBlt q hq; omega))
  have hval : ∀ q < n, Nat.land (B q) ((2 ^ (W - 1) - 1) * (B q / 2 ^ (W - 1))) =
      (max (c q) 0).toNat := by
    intro q hq
    have hcq := hcB q hq
    have hBq := hBlt q hq
    have hP : ((2 ^ (W - 1) : ℕ) : ℤ) = 2 ^ (W - 1) := by norm_num
    rcases Nat.lt_or_ge (B q) (2 ^ (W - 1)) with hlt | hge
    · rw [Nat.div_eq_of_lt hlt, Nat.mul_zero, max_eq_right (by omega)]
      simp
    · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega), Nat.mul_one, max_eq_left (by omega)]
      change B q &&& 2 ^ (W - 1) - 1 = _
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      omega
  have hsum : ∑ q ∈ range n, (max (c q) 0).toNat < 2 ^ W - 1 := by
    refine lt_of_le_of_lt ?_ hn
    simpa using sum_le_card_nsmul (range n) _ (2 ^ g) fun q hq ↦ Int.toNat_le.2 (by
      push_cast
      exact max_le ((le_abs_self _).trans (hc q (mem_range.mp hq))) (by positivity))
  unfold zPosSum
  simp only []
  rw [zPack_biased_toNat hW hfit, hH, hS, hM, land_packSlots hBlt (fun q hq ↦
      (mul_le_of_le_one_right (Nat.zero_le _) (hle1 q hq)).trans_lt (by omega)),
    packSlots_congr hval]
  change packSlots W n _ % (2 ^ W - 1) = _
  rw [packSlots_mod, Nat.mod_eq_of_lt hsum]

/-- **The sum of the absolute values.** -/
theorem zAbsSum_zPack {W n g : ℕ} (hg : g + 1 < W) {c : ℕ → ℤ} (hc : ∀ q < n, |c q| ≤ 2 ^ g)
    (hn : n * 2 ^ g < 2 ^ W - 1) :
    (zAbsSum W n (zPack W n c) : ℤ) = ∑ q ∈ range n, |c q| := by
  have hneg : Int.neg (zPack W n c) = zPack W n fun q ↦ -c q := zPack_neg W n c
  unfold zAbsSum
  rw [hneg, Nat.add_eq, zPosSum_zPack hg hc hn,
    zPosSum_zPack hg (fun q hq ↦ by rw [abs_neg]; exact hc q hq) hn]
  push_cast
  rw [← sum_add_distrib]
  refine sum_congr rfl fun q _ ↦ ?_
  rw [Int.toNat_of_nonneg (le_max_right _ _), Int.toNat_of_nonneg (le_max_right _ _),
    max_zero_add_max_neg_zero_eq_abs_self]

end CAS.Numerics

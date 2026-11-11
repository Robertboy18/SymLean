/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
module

public import CAS.Numerics.PackedSpread
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# Rounded combinations of packed rows in natural numbers

A signed slot of width `w` is stored as `x = v + 2^(w-1)`. For terms `(p, n, x)`, the coefficient
`p - n` given by its natural parts and `x` a packed row of such slots held in slots of width
`W > w`, `packedRoundComb W w m k β` computes `⌊(∑ (p - n) v + 2^(k-1)) / 2^k⌋ + β` (the rounding
`roundShift k` of [IntegerRounding](IntegerRounding.lean)) in every one of the `m` slots at once
(`slot_packedRoundComb`). `land_shiftRight_packSlots` divides every slot of a packed row by `2^k`
with one shift and one mask.

## Implementation notes

We never form the signed values. The positive part `∑ p x + 2^(k-1) + β 2^k + (∑ n) 2^(w-1)` and
the negative part `∑ n x + (∑ p) 2^(w-1)` are packed rows of natural numbers whose difference is
`∑ (p - n) v + 2^(k-1) + β 2^k` in every slot. We subtract them, shift the difference right by
`k`, and the mask `constSlots W m (2^(W-k) - 1)` clears the `k` bits that every slot received
from the slot above; the offset `β 2^k` comes out of the division as `+ β`. The hypotheses of
`slot_packedRoundComb` exclude carries and borrows between slots. With every slot of every row
below `2 ^ w`, the bound `2^(k-1) + β 2^k + (∑ p + ∑ n) 2^w < 2^W` keeps each slot of the
positive part below `2 ^ W`, and `(∑ p + ∑ n) 2^(w-1) ≤ β 2^k` keeps each slot of the negative
part at most the matching slot of the positive part. So neither part carries and the
subtraction works slot by slot (`packSlots_sub`).

For `t` terms the four `List.rec` folds cost `2 t` products of a coefficient with a row, `2 t`
additions of rows and `2 t` additions of coefficients. The rest is three `constSlots` rows
(see [PackedSlots](PackedSlots.lean)), two additions, one subtraction, one shift and one `and`,
whatever the number `m` of slots. No module of the library imports this one; certificates
outside the library use it.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- The signed value `∑ (p - n) (x - 2^(w-1))` of the terms `(p, n, x)`. -/
def combValueN (w : ℕ) (cs : List (ℕ × ℕ × ℕ)) : ℤ :=
  (cs.map fun c ↦ ((c.1 : ℤ) - c.2.1) * ((c.2.2 : ℤ) - ((2 ^ (w - 1) : ℕ) : ℤ))).sum


/-- `∑ p x` over the terms. -/
def packPosFold (cs : List (ℕ × ℕ × ℕ)) : ℕ :=
  List.rec (motive := fun _ ↦ ℕ) 0 (fun c _ s ↦ Nat.add (Nat.mul c.1 c.2.2) s) cs

/-- `∑ n x` over the terms. -/
def packNegFold (cs : List (ℕ × ℕ × ℕ)) : ℕ :=
  List.rec (motive := fun _ ↦ ℕ) 0 (fun c _ s ↦ Nat.add (Nat.mul c.2.1 c.2.2) s) cs

/-- `∑ p` over the terms. -/
def coefPosSum (cs : List (ℕ × ℕ × ℕ)) : ℕ :=
  List.rec (motive := fun _ ↦ ℕ) 0 (fun c _ s ↦ Nat.add c.1 s) cs

/-- `∑ n` over the terms. -/
def coefNegSum (cs : List (ℕ × ℕ × ℕ)) : ℕ :=
  List.rec (motive := fun _ ↦ ℕ) 0 (fun c _ s ↦ Nat.add c.2.1 s) cs

/-- The rounded combination `⌊(∑ (p - n) (x - 2^(w-1)) + 2^(k-1)) / 2^k⌋ + β` of every slot. -/
def packedRoundComb (W w m k β : ℕ) (cs : List (ℕ × ℕ × ℕ)) : ℕ :=
  Nat.land (Nat.shiftRight (Nat.sub
    (Nat.add (packPosFold cs) (constSlots W m (Nat.add (Nat.add (2 ^ (k - 1)) (Nat.mul β (2 ^ k)))
      (Nat.mul (coefNegSum cs) (2 ^ (w - 1))))))
    (Nat.add (packNegFold cs) (constSlots W m (Nat.mul (coefPosSum cs) (2 ^ (w - 1)))))) k)
    (constSlots W m (Nat.sub (2 ^ (W - k)) 1))

/-- Shifting every slot of a packed row down by `k ≤ W` bits. -/
theorem land_shiftRight_packSlots {W m k : ℕ} (hW : 0 < W) (hk : k ≤ W) {f : ℕ → ℕ}
    (hf : ∀ q < m, f q < 2 ^ W) :
    Nat.land (Nat.shiftRight (packSlots W m f) k) (constSlots W m (Nat.sub (2 ^ (W - k)) 1)) =
      packSlots W m fun q ↦ f q / 2 ^ k := by
  have hc : 2 ^ (W - k) - 1 < 2 ^ W :=
    lt_of_lt_of_le (Nat.sub_lt (by positivity) one_pos) (Nat.pow_le_pow_right (by norm_num)
      (Nat.sub_le W k))
  have hg : ∀ q < m, f q / 2 ^ k < 2 ^ W := fun q hq ↦
    lt_of_le_of_lt (Nat.div_le_self _ _) (hf q hq)
  have hlt : Nat.land (Nat.shiftRight (packSlots W m f) k)
      (constSlots W m (Nat.sub (2 ^ (W - k)) 1)) < 2 ^ (W * m) := by
    rw [constSlots_eq hW]
    exact lt_of_le_of_lt Nat.and_le_right (packSlots_lt fun _ _ ↦ hc)
  refine eq_of_slot_eq hlt (packSlots_lt hg) fun q hq ↦ ?_
  have hfq := slot_packed_eq hf q
  rw [ite_eq_left hq, slot_eq] at hfq
  simp only [Nat.sub_eq]
  rw [slot_land, constSlots_eq hW, slot_packed_eq (fun _ _ ↦ hc), ite_eq_left hq,
    slot_packed_eq hg, ite_eq_left hq, slot_eq, ← hfq]
  change (packSlots W m f >>> k) / 2 ^ (W * q) % 2 ^ W &&& 2 ^ (W - k) - 1 = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    mul_comm (2 ^ k), ← Nat.div_div_eq_div_mul, Nat.mod_mod_of_dvd _
      (Nat.pow_dvd_pow 2 (Nat.sub_le W k)), ← Nat.mod_mul_right_div_self, ← pow_add,
    Nat.add_sub_cancel' hk]

section PackedRoundComb

variable {W : ℕ}

/-- If the row `x` of every term `(p, n, x)` is below `2 ^ (W * m)`, `packPosFold cs` is the
packing in `m` slots of width `W` of the sums of `p * slot W l x` over the terms. The sums may
exceed `2 ^ W`. -/
theorem packPosFold_eq {m : ℕ} {cs : List (ℕ × ℕ × ℕ)} (hx : ∀ c ∈ cs, c.2.2 < 2 ^ (W * m)) :
    packPosFold cs = packSlots W m fun l ↦ (cs.map fun c ↦ c.1 * slot W l c.2.2).sum := by
  induction cs with
  | nil => exact (packSlots_zero W m).symm
  | cons c cs ih =>
    change c.1 * c.2.2 + packPosFold cs = _
    rw [ih fun c' hc' ↦ hx c' (List.mem_cons_of_mem _ hc'),
      ← packSlots_slot (hx c (List.mem_cons_self ..)), mul_packSlots, packSlots_add]
    simp only [List.map_cons, List.sum_cons]

/-- If the row `x` of every term `(p, n, x)` is below `2 ^ (W * m)`, `packNegFold cs` is the
packing in `m` slots of width `W` of the sums of `n * slot W l x` over the terms. The sums may
exceed `2 ^ W`. -/
theorem packNegFold_eq {m : ℕ} {cs : List (ℕ × ℕ × ℕ)} (hx : ∀ c ∈ cs, c.2.2 < 2 ^ (W * m)) :
    packNegFold cs = packSlots W m fun l ↦ (cs.map fun c ↦ c.2.1 * slot W l c.2.2).sum := by
  induction cs with
  | nil => exact (packSlots_zero W m).symm
  | cons c cs ih =>
    change c.2.1 * c.2.2 + packNegFold cs = _
    rw [ih fun c' hc' ↦ hx c' (List.mem_cons_of_mem _ hc'),
      ← packSlots_slot (hx c (List.mem_cons_self ..)), mul_packSlots, packSlots_add]
    simp only [List.map_cons, List.sum_cons]

private theorem sum_mul_slot_le {w l : ℕ} (cs : List (ℕ × ℕ × ℕ)) (g : ℕ × ℕ × ℕ → ℕ)
    (hy : ∀ c ∈ cs, slot W l c.2.2 < 2 ^ w) :
    (cs.map fun c ↦ g c * slot W l c.2.2).sum ≤ (cs.map g).sum * 2 ^ w := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (hy c (List.mem_cons_self ..)).le)
      (ih fun c' hc' ↦ hy c' (List.mem_cons_of_mem _ hc'))

private theorem coefPosSum_eq (cs : List (ℕ × ℕ × ℕ)) : coefPosSum cs = (cs.map (·.1)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => change c.1 + coefPosSum cs = _; rw [ih]; simp

private theorem coefNegSum_eq (cs : List (ℕ × ℕ × ℕ)) :
    coefNegSum cs = (cs.map (·.2.1)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => change c.2.1 + coefNegSum cs = _; rw [ih]; simp

private theorem combValueN_map (w l : ℕ) (cs : List (ℕ × ℕ × ℕ)) :
    combValueN w (cs.map fun c ↦ (c.1, c.2.1, slot W l c.2.2)) =
      ((cs.map fun c ↦ c.1 * slot W l c.2.2).sum : ℕ) -
        ((cs.map fun c ↦ c.2.1 * slot W l c.2.2).sum : ℕ) -
        (((cs.map (·.1)).sum : ℕ) - ((cs.map (·.2.1)).sum : ℕ)) * ((2 ^ (w - 1) : ℕ) : ℤ) := by
  induction cs with
  | nil => simp [combValueN]
  | cons c cs ih =>
    simp only [combValueN, List.map_cons, List.sum_cons, List.map_map] at ih ⊢
    rw [ih]
    push_cast
    ring

/-- **Rounding every slot.** Slot `l` of `packedRoundComb` is the rounded combination of the
slots `l` of the terms, when the offsets keep every slot nonnegative and below `2^W`. -/
theorem slot_packedRoundComb {w m k β : ℕ} (hw : 0 < w) (hk : 0 < k) (hkW : k ≤ W)
    {cs : List (ℕ × ℕ × ℕ)} (hx : ∀ c ∈ cs, c.2.2 < 2 ^ (W * m))
    (hy : ∀ c ∈ cs, ∀ l < m, slot W l c.2.2 < 2 ^ w)
    (hβ : (coefPosSum cs + coefNegSum cs) * 2 ^ (w - 1) ≤ β * 2 ^ k)
    (hfit : 2 ^ (k - 1) + β * 2 ^ k + (coefPosSum cs + coefNegSum cs) * 2 ^ w < 2 ^ W)
    {l : ℕ} (hl : l < m) :
    (slot W l (packedRoundComb W w m k β cs) : ℤ) =
      (combValueN w (cs.map fun c ↦ (c.1, c.2.1, slot W l c.2.2)) + ((2 ^ (k - 1) : ℕ) : ℤ)) /
        ((2 ^ k : ℕ) : ℤ) + β := by
  have hW : 0 < W := lt_of_lt_of_le hk hkW
  have h2w : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
  set sp := coefPosSum cs
  set sn := coefNegSum cs
  set Pf : ℕ → ℕ := fun q ↦ (cs.map fun c ↦ c.1 * slot W q c.2.2).sum +
    (2 ^ (k - 1) + β * 2 ^ k + sn * 2 ^ (w - 1)) with hPf
  set Nf : ℕ → ℕ := fun q ↦ (cs.map fun c ↦ c.2.1 * slot W q c.2.2).sum + sp * 2 ^ (w - 1)
    with hNf
  have hsp : sp = (cs.map (·.1)).sum := coefPosSum_eq cs
  have hsn : sn = (cs.map (·.2.1)).sum := coefNegSum_eq cs
  have hpos : ∀ q < m, (cs.map fun c ↦ c.1 * slot W q c.2.2).sum ≤ sp * 2 ^ w := fun q hq ↦ by
    rw [hsp]; exact sum_mul_slot_le cs (·.1) fun c hc ↦ hy c hc q hq
  have hneg : ∀ q < m, (cs.map fun c ↦ c.2.1 * slot W q c.2.2).sum ≤ sn * 2 ^ w := fun q hq ↦ by
    rw [hsn]; exact sum_mul_slot_le cs (·.2.1) fun c hc ↦ hy c hc q hq
  have hle : ∀ q < m, Nf q ≤ Pf q := fun q hq ↦ by
    have := hneg q hq
    rw [h2w] at this
    have h4 : 0 < 2 ^ (k - 1) := by positivity
    have h2 : (sp + sn) * 2 ^ (w - 1) = sp * 2 ^ (w - 1) + sn * 2 ^ (w - 1) := add_mul _ _ _
    have h3 : sn * (2 * 2 ^ (w - 1)) = sn * 2 ^ (w - 1) + sn * 2 ^ (w - 1) := by ring
    simp only [hPf, hNf]
    omega
  have hPlt : ∀ q < m, Pf q < 2 ^ W := fun q hq ↦ by
    have := hpos q hq
    have h2 : sn * 2 ^ (w - 1) ≤ sn * 2 ^ w := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right
      (by norm_num) (Nat.sub_le w 1))
    have h3 : (sp + sn) * 2 ^ w = sp * 2 ^ w + sn * 2 ^ w := add_mul _ _ _
    simp only [hPf]
    omega
  have hZlt : ∀ q < m, Pf q - Nf q < 2 ^ W := fun q hq ↦
    lt_of_le_of_lt (Nat.sub_le _ _) (hPlt q hq)
  have hP : packPosFold cs + constSlots W m (2 ^ (k - 1) + β * 2 ^ k + sn * 2 ^ (w - 1)) =
      packSlots W m Pf := by
    rw [packPosFold_eq hx, constSlots_eq hW, packSlots_add]
  have hN : packNegFold cs + constSlots W m (sp * 2 ^ (w - 1)) = packSlots W m Nf := by
    rw [packNegFold_eq hx, constSlots_eq hW, packSlots_add]
  have hdef : packedRoundComb W w m k β cs = Nat.land (Nat.shiftRight
      ((packPosFold cs + constSlots W m (2 ^ (k - 1) + β * 2 ^ k + sn * 2 ^ (w - 1))) -
        (packNegFold cs + constSlots W m (sp * 2 ^ (w - 1)))) k)
      (constSlots W m (Nat.sub (2 ^ (W - k)) 1)) := rfl
  have hdiv : ∀ q < m, (Pf q - Nf q) / 2 ^ k < 2 ^ W := fun q hq ↦
    lt_of_le_of_lt (Nat.div_le_self _ _) (hZlt q hq)
  rw [hdef, hP, hN, packSlots_sub hle, land_shiftRight_packSlots hW hkW hZlt,
    slot_packed_eq hdiv, ite_eq_left hl, Int.natCast_div, Nat.cast_sub (hle l hl)]
  have hval : ((Pf l : ℕ) : ℤ) - (Nf l : ℕ) =
      combValueN w (cs.map fun c ↦ (c.1, c.2.1, slot W l c.2.2)) + 2 ^ (k - 1) + β * 2 ^ k := by
    rw [combValueN_map, ← hsp, ← hsn]
    simp only [hPf, hNf]
    push_cast
    ring
  rw [hval, show combValueN w (cs.map fun c ↦ (c.1, c.2.1, slot W l c.2.2)) +
    2 ^ (k - 1) + β * 2 ^ k = (combValueN w (cs.map fun c ↦ (c.1, c.2.1, slot W l c.2.2)) +
      ((2 ^ (k - 1) : ℕ) : ℤ)) + β * ((2 ^ k : ℕ) : ℤ) by push_cast; ring,
    Int.add_mul_ediv_right _ _ (by positivity)]

end PackedRoundComb

end CAS.Numerics

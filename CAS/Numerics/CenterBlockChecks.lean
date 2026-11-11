/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.SuffixSlots

/-!
# Rounded centers of a tiled matrix

A certified matrix stored in blocks of mode groups (slots of `64` bits holding `E + 2 ^ 63`, the
block of the groups `(gA, gB)` at position `locPos gA gB` of tile `locTile gA gB`, stored as
`(gB, gA)` when `locSwap gA gB ≠ 0`) is compared entrywise with the rows of a center in slots of
`cw` bits. For modes `a`, `b` with multipliers `m_a`, `m_b`, the check `centerEntryOk` states
`|m_a m_b E_ab + D_ab - c_ab W| ≤ H` in integers, with `c_ab` the signed slot `a` of row `b` and
`D_ab` the slot bias times `W` plus a diagonal term; `W = 2 ^ K`, `H = 2 ^ (K - 1)` make it the
statement that `c_ab` rounds `m_a m_b E_ab / 2 ^ K` plus the diagonal term to the nearest integer.
`centerBlockCheck` runs over the entries of one pair of groups, reading the entries of a column of
the block and of the center row through windows, and `centerEntryOk_of_blockCheck` gives the
check of every entry from the checks of all pairs of groups.

## Implementation notes

`centerRowSlots` runs only during elaboration: `computed_rows%` evaluates it with compiled code
(rounding half up with `Int.fdiv`) and stores the center rows as data, which establish nothing
by themselves. The kernel evaluates `centerBlockCheck` for every pair of groups; an entry costs a
few products and two comparisons of natural numbers (`centerEntryOk`), and `centerEntryOk_spec`
turns a passing check into the integer inequality. The check accepts any `c_ab` within `H` of
the scaled value, so ties may be rounded either way. `slotWindow` cuts the multipliers and the
center row (and, for an unswapped block, its column) down to the slots of group `gA` before the
inner loop, so the inner loop reads its slots from short numbers rather than from the full
literals.
-/

@[expose] public section

namespace CAS.Numerics

/-- The biased stored entry of the modes at columns `i` of group `gA` and `j` of group `gB`. -/
def tileEntryBiased (locTile locPos locSwap : ℕ → ℕ → ℕ) (tileW tileS lit : ℕ → ℕ)
    (gA gB i j : ℕ) : ℕ :=
  slot 64 (3 + if locSwap gA gB = 0 then i + tileS (locTile gA gB) * j
      else j + tileS (locTile gA gB) * i)
    (slot (tileW (locTile gA gB)) (locPos gA gB) (lit (locTile gA gB)))

/-- The entry check `|U (Eb - 2 ^ 63) + D - cb W| ≤ H` in natural numbers. -/
def centerEntryOk (U Eb cb D W H : ℕ) : Bool :=
  Nat.ble (U * Eb + D) (U * 2 ^ 63 + cb * W + H) &&
    Nat.ble (U * 2 ^ 63 + cb * W) (U * Eb + D + H)

/-- A passing `centerEntryOk U Eb cb D W H` gives the integer bound
`|U * (Eb - 2 ^ 63) + D - cb * W| ≤ H`. -/
theorem centerEntryOk_spec {U Eb cb D W H : ℕ} (h : centerEntryOk U Eb cb D W H = true) :
    |(U : ℤ) * ((Eb : ℤ) - 2 ^ 63) + (D : ℤ) - (cb : ℤ) * (W : ℤ)| ≤ (H : ℤ) := by
  simp only [centerEntryOk, Bool.and_eq_true, Nat.ble_eq] at h
  zify at h
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- The checks of the entries of the groups `(gA, gB)`: group `g` holds the modes
`start g, …, start g + size g - 1`, `m` the multipliers in slots of `mw` bits, `crow b` the
center row of mode `b`, `dg` the diagonal terms in slots of `dw` bits. -/
def centerBlockCheck (locTile locPos locSwap : ℕ → ℕ → ℕ) (tileW tileS lit : ℕ → ℕ)
    (start size : ℕ → ℕ) (mw m cw : ℕ) (crow : ℕ → ℕ) (dw dg W H D0 : ℕ) (gA gB : ℕ) : Bool :=
  let n := locTile gA gB
  let blk := slot (tileW n) (locPos gA gB) (lit n)
  let S := tileS n
  let sw := locSwap gA gB
  let sA := start gA
  let nA := size gA
  let Mw := slotWindow mw sA nA m
  natAll (size gB) fun j ↦
    let b := start gB + j
    let mb := slot mw b m
    let Cw := slotWindow cw sA nA (crow b)
    let Ew := slotWindow 64 (3 + S * j) nA blk
    natAll nA fun i ↦
      centerEntryOk (slot mw i Mw * mb)
        (if sw = 0 then slot 64 i Ew else slot 64 (3 + (j + S * i)) blk) (slot cw i Cw)
        (if sA + i = b then D0 + slot dw b dg * W else D0) W H

/-- The checks of all pairs of groups give the check of the entry of the modes `a`, `b` at
columns `i`, `j` of their groups. -/
theorem centerEntryOk_of_blockCheck {locTile locPos locSwap : ℕ → ℕ → ℕ} {tileW tileS lit : ℕ → ℕ}
    {start size : ℕ → ℕ} {mw m cw : ℕ} {crow : ℕ → ℕ} {dw dg W H D0 gA gB : ℕ}
    (hchk : centerBlockCheck locTile locPos locSwap tileW tileS lit start size mw m cw crow dw dg W
      H D0 gA gB = true)
    {a b i j : ℕ} (ha : start gA + i = a) (hi : i < size gA) (hb : start gB + j = b)
    (hj : j < size gB) :
    centerEntryOk (slot mw a m * slot mw b m)
      (tileEntryBiased locTile locPos locSwap tileW tileS lit gA gB i j) (slot cw a (crow b))
      (if a = b then D0 + slot dw b dg * W else D0) W H = true := by
  unfold centerBlockCheck at hchk
  have h := natAll_spec (natAll_spec hchk hj) hi
  simp only [slot_slotWindow hi] at h
  rw [Nat.add_comm i (start gA), ha, hb] at h
  unfold tileEntryBiased
  by_cases hsw : locSwap gA gB = 0
  · simp only [hsw, ite_true] at h ⊢
    rwa [show 3 + (i + tileS (locTile gA gB) * j) = i + (3 + tileS (locTile gA gB) * j) by
      omega]
  · simp only [hsw, ite_false] at h ⊢
    exact h

/-- The biased slots of row `b` of a rounded center: entry `a` is
`⌊(m_a m_b E_ab + 2 ^ (K - 1)) / 2 ^ K⌋ + [a = b] dg_a` plus `2 ^ (cw - 1)`, for the groups
`0, …, G - 1` in mode order and `b` at column `b - start (group b)` of its group. Used during
elaboration (`computed_rows%`) to store a center that the block checks then verify. -/
def centerRowSlots (locTile locPos locSwap : ℕ → ℕ → ℕ) (tileW tileS lit : ℕ → ℕ)
    (start size : ℕ → ℕ) (G : ℕ) (group : ℕ → ℕ) (mw m dw dg K cw b : ℕ) : Array ℕ := Id.run do
  let gB := group b
  let j := b - start gB
  let mb := slot mw b m
  let mut out : Array ℕ := #[]
  for gA in [0:G] do
    let n := locTile gA gB
    let blk := slot (tileW n) (locPos gA gB) (lit n)
    let S := tileS n
    let sw := locSwap gA gB
    for i in [0:size gA] do
      let a := start gA + i
      let q := if sw = 0 then i + S * j else j + S * i
      let E : ℤ := (slot 64 (3 + q) blk : ℤ) - 2 ^ 63
      let v : ℤ := Int.fdiv ((slot mw a m * mb : ℕ) * E + 2 ^ (K - 1)) (2 ^ K) +
        (if a = b then (slot dw a dg : ℤ) else 0)
      out := out.push (v + 2 ^ (cw - 1)).toNat
  return out

end CAS.Numerics

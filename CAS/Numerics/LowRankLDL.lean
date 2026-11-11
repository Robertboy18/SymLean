/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedLDL
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity.Finset

/-!
# Packed `LDLᵀ` certificates for a matrix plus a low-rank term

A finite-rank capture matrix has the form `-c A + diag(g) + V diag(t) Vᵀ` with `A` dense,
`g ≥ 0` diagonal and `V` of `m` columns. Its rows need not be stored: `lowRankRow` forms row `i`
as one packed row combination of the `m` columns `Vcol j` (coefficients `V i j t j`, read from
slot `i`), the row `Arow i` (coefficient `-c`) and the unit row (coefficient `g i`), and the
row checks of [PackedLDL](PackedLDL.lean) take these rows as the matrix. `productRow` forms
`∑_l b l • Arow l - c • Vj` for integer coefficients `b`, so a guard check on it bounds the
entries of `Aᵀ b - c V_j`: the check that a stored column approximates the product of the
matrix with a coefficient column.

## Main definitions

* `lowRankRow`: row `i` of `-c A + diag(g) + V diag(t) Vᵀ`, packed.
* `productRow`: the packed row `∑_l b l • Arow l - c • Vj`.

## Main results

* `signedSlot_lowRankRow`: under entry bounds on `Arow i` and `Vcol j` and a fitting width,
  the slots of `lowRankRow` are the entries of the matrix.
* `quadForm_ge_of_lowRankRowCheck`: passing row checks give the lower bound `τ |x|²` for the form
  `xᵀ (-c A + diag(g)) x / q + ∑_j (t j / q) (Vᵀ x)_j²`.
* `capture_center_form_of_lowRankRowCheck`: the same bound with the entries read on dyadic grids.
* `signedSlot_productRow`, `abs_product_sub_le_of_guard`: the slots of `productRow` are the
  entries of `Aᵀ b - c V_j`, and a passing guard check bounds the error of a stored column in
  real scales.

## Implementation notes

The certificate stores `A`, the `m` columns of `V` and the factor; the `n²` entries of the
low-rank term are never written down. Each row check recomputes its row with one combination of
`m + 2` packed rows, about `3 (m + 2)` big-number operations, and the entry bounds of `Arow` and
`Vcol`, from guard checks, make every slot of that combination the exact entry
(`signedSlot_lowRankRow`). Untrusted code proposes `V`, `t`, the factor and the coefficients `b`;
the kernel checks the guards, the row checks and the product rows.
`quadForm_ge_of_lowRankRowCheck` rewrites the slots and applies
`quadForm_ge_of_ldltRowCheck_div`, then regroups `∑_j t j (Vᵀ x)_j²`.
-/

@[expose] public section

open Finset

namespace CAS.Numerics

/-- The biased coefficients of row `i`: `V i j t j` for the `m` columns, `-c` for the matrix row
and `g i` for the unit row, each plus `α`. -/
def lowRankCoefficient (w m α c : ℕ) (Vcol t g : ℕ → ℕ) (i j : ℕ) : ℕ :=
  cond (Nat.blt j m)
    (Nat.sub (Nat.add α (Nat.mul (slot w i (Vcol j)) (t j))) (Nat.mul (slotBias w) (t j)))
    (cond (Nat.beq j m) (Nat.sub α c) (Nat.add α (g i)))

/-- The rows combined for row `i`: the `m` columns, the matrix row `i` and the unit row. -/
def lowRankRows (w n m : ℕ) (Arow Vcol : ℕ → ℕ) (i j : ℕ) : ℕ :=
  cond (Nat.blt j m) (Vcol j) (cond (Nat.beq j m) (Arow i) (unitRow w n i))

/-- Row `i` of `-c A + diag(g) + V diag(t) Vᵀ`, packed in `n` biased slots of width `w`. -/
def lowRankRow (w n m α c : ℕ) (Arow Vcol t g : ℕ → ℕ) (i : ℕ) : ℕ :=
  packedRowCombination w n (m + 2) α (lowRankCoefficient w m α c Vcol t g i)
    (lowRankRows w n m Arow Vcol i)

/-- The combination `∑_l (b l) • Arow l - c • Vj` with integer coefficients biased by `α`. -/
def productRow (w n α c : ℕ) (Arow : ℕ → ℕ) (b : ℕ → ℤ) (Vj : ℕ) : ℕ :=
  packedRowCombination w n (n + 1) α
    (fun l ↦ cond (Nat.blt l n) (Int.toNat ((α : ℤ) + b l)) (Nat.sub α c))
    (fun l ↦ cond (Nat.blt l n) (Arow l) Vj)

/-- The slots of `lowRankRow` are the entries `∑_j V i j t j V k j - c A i k + [k = i] g i`. -/
theorem signedSlot_lowRankRow {w n m α c : ℕ} {Arow Vcol t g : ℕ → ℕ} {BA BV T G i k : ℕ}
    (hw : 2 ≤ w) (hi : i < n) (hk : k < n) (hA : Arow i < 2 ^ (w * n))
    (hAb : ∀ l < n, (signedSlot w l (Arow i)).natAbs ≤ BA)
    (hV : ∀ j < m, Vcol j < 2 ^ (w * n))
    (hVb : ∀ j < m, ∀ l < n, (signedSlot w l (Vcol j)).natAbs ≤ BV)
    (ht : ∀ j < m, t j ≤ T) (hg : g i ≤ G) (hαc : c ≤ α) (hαV : BV * T ≤ α)
    (hfit : 2 * (m * (BV * T * BV) + c * BA + G) < 2 ^ w) :
    signedSlot w k (lowRankRow w n m α c Arow Vcol t g i) =
      ∑ j ∈ range m, signedSlot w i (Vcol j) * t j * signedSlot w k (Vcol j) -
        c * signedSlot w k (Arow i) + if k = i then (g i : ℤ) else 0 := by
  have hcoef : ∀ j < m, ((lowRankCoefficient w m α c Vcol t g i j : ℕ) : ℤ) - α =
      signedSlot w i (Vcol j) * t j := by
    intro j hj
    have hb : slotBias w ≤ slot w i (Vcol j) + BV := by
      have := hVb j hj i hi
      rw [signedSlot] at this
      omega
    have hle : slotBias w * t j ≤ α + slot w i (Vcol j) * t j := by
      nlinarith [Nat.mul_le_mul_right (t j) hb, Nat.mul_le_mul_left BV (ht j hj)]
    simp only [lowRankCoefficient, Nat.blt_eq.mpr hj, Bool.cond_true, Nat.sub_eq, Nat.add_eq,
      Nat.mul_eq]
    push_cast [Nat.cast_sub hle, signedSlot]
    ring
  have hmm : Nat.blt m m = false := by simp [Bool.eq_false_iff]
  have hm1 : Nat.blt (m + 1) m = false := by simp [Bool.eq_false_iff]
  have hm2 : Nat.beq (m + 1) m = false := by simp [Bool.eq_false_iff]
  have hcm : ((lowRankCoefficient w m α c Vcol t g i m : ℕ) : ℤ) - α = -c := by
    simp only [lowRankCoefficient, hmm, Bool.cond_false, Nat.beq_refl, Bool.cond_true, Nat.sub_eq]
    omega
  have hcm1 : ((lowRankCoefficient w m α c Vcol t g i (m + 1) : ℕ) : ℤ) - α = g i := by
    simp only [lowRankCoefficient, hm1, hm2, Bool.cond_false, Nat.add_eq]
    omega
  have hrow : ∀ j < m, lowRankRows w n m Arow Vcol i j = Vcol j := fun j hj ↦ by
    simp only [lowRankRows, Nat.blt_eq.mpr hj, Bool.cond_true]
  have hrowm : lowRankRows w n m Arow Vcol i m = Arow i := by
    simp only [lowRankRows, hmm, Bool.cond_false, Nat.beq_refl, Bool.cond_true]
  have hrowm1 : lowRankRows w n m Arow Vcol i (m + 1) = unitRow w n i := by
    simp only [lowRankRows, hm1, hm2, Bool.cond_false]
  have hsum : ∀ k' < n, ∑ j ∈ range (m + 2),
      ((lowRankCoefficient w m α c Vcol t g i j : ℤ) - α) *
        signedSlot w k' (lowRankRows w n m Arow Vcol i j) =
      ∑ j ∈ range m, signedSlot w i (Vcol j) * t j * signedSlot w k' (Vcol j) -
        c * signedSlot w k' (Arow i) + if k' = i then (g i : ℤ) else 0 := by
    intro k' hk'
    rw [show m + 2 = m + 1 + 1 from rfl, sum_range_succ, sum_range_succ, hcm, hcm1, hrowm,
      hrowm1, signedSlot_unitRow hw hk']
    rw [sum_congr rfl fun j hj ↦ by rw [hcoef j (mem_range.mp hj), hrow j (mem_range.mp hj)]]
    split_ifs <;> ring
  have hrows : ∀ j < m + 2, lowRankRows w n m Arow Vcol i j < 2 ^ (w * n) := fun j hj ↦ by
    rcases lt_or_ge j m with hjm | hjm
    · exact hrow j hjm ▸ hV j hjm
    obtain rfl | rfl : j = m ∨ j = m + 1 := by omega
    · exact hrowm ▸ hA
    · exact hrowm1 ▸ unitRow_lt hw hi
  have hfit' : ∀ k' < n, FitsSlot w (∑ j ∈ range (m + 2),
      ((lowRankCoefficient w m α c Vcol t g i j : ℤ) - α) *
        signedSlot w k' (lowRankRows w n m Arow Vcol i j)) := by
    intro k' hk'
    rw [hsum k' hk']
    refine fitsSlot_of_natAbs_le ((Int.natAbs_add_le _ _).trans (add_le_add
      ((Int.natAbs_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)) hfit
    · refine (Int.natAbs_sum_le _ _).trans
        ((sum_le_card_nsmul _ _ (BV * T * BV) fun j hj ↦ ?_).trans_eq (by simp))
      have hj := mem_range.mp hj
      rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.mul_le_mul (Nat.mul_le_mul (hVb j hj i hi) (ht j hj)) (hVb j hj k' hk')
    · rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.mul_le_mul_left c (hAb k' hk')
    · split_ifs <;> simp [hg]
  exact (signedSlot_packedRowCombination hrows hfit' hk).trans (hsum k hk)

/-- **Packed certificate for a matrix plus a low-rank term.** If the `LDLᵀ` row checks pass for
the rows `lowRankRow`, the guard bounds on `Arow` and `Vcol` hold and the sizes fit, then for
`A i k = signedSlot w k (Arow i)` and `V i j = signedSlot w i (Vcol j)`,
`τ |x|² ≤ ∑_i (g i / q) x_i² - ∑_{i,k} (c A i k / q) x_i x_k + ∑_j (t j / q) (∑_i V i j x_i)²`. -/
theorem quadForm_ge_of_lowRankRowCheck (p : PackedLDLParams) {m α c BA BV T G : ℕ}
    {Arow Vcol t g Urow d : ℕ → ℕ} (hp : p.valid = true) (hscale : 0 < p.scale)
    (hrows : ∀ i < p.size,
      ldltRowCheck p (lowRankRow p.width p.size m α c Arow Vcol t g) Urow d i = true)
    (hA : ∀ i < p.size, Arow i < 2 ^ (p.width * p.size))
    (hAb : ∀ i < p.size, ∀ l < p.size, (signedSlot p.width l (Arow i)).natAbs ≤ BA)
    (hV : ∀ j < m, Vcol j < 2 ^ (p.width * p.size))
    (hVb : ∀ j < m, ∀ l < p.size, (signedSlot p.width l (Vcol j)).natAbs ≤ BV)
    (ht : ∀ j < m, t j ≤ T) (hg : ∀ i < p.size, g i ≤ G) (hαc : c ≤ α) (hαV : BV * T ≤ α)
    (hfit : 2 * (m * (BV * T * BV) + c * BA + G) < 2 ^ p.width) {q τ : ℝ} (hq : 0 < q)
    (hτ : p.scale * q * τ + p.size * slotBias p.residualBits ≤ p.shift) (x : Fin p.size → ℝ) :
    τ * ∑ i, x i ^ 2 ≤ ∑ i : Fin p.size, ((g i.val : ℝ) / q) * x i ^ 2 -
      ∑ i : Fin p.size, ∑ k : Fin p.size,
        ((c : ℝ) * signedSlot p.width k.val (Arow i.val) / q) * x i * x k +
      ∑ j : Fin m, ((t j.val : ℝ) / q) *
        (∑ i : Fin p.size, (signedSlot p.width i.val (Vcol j.val) : ℝ) * x i) ^ 2 := by
  have hv := PackedLDLParams.valid_spec hp
  refine (quadForm_ge_of_ldltRowCheck_div p _ Urow d hp hrows hscale hq hτ x).trans_eq ?_
  have hslot : ∀ i k : Fin p.size,
      (signedSlot p.width k.val (lowRankRow p.width p.size m α c Arow Vcol t g i.val) : ℝ) =
        ∑ j : Fin m, (signedSlot p.width i.val (Vcol j.val) : ℝ) * t j.val *
          signedSlot p.width k.val (Vcol j.val) -
          c * signedSlot p.width k.val (Arow i.val) + if k = i then (g i.val : ℝ) else 0 := by
    intro i k
    rw [signedSlot_lowRankRow hv.1 i.isLt k.isLt (hA i i.isLt) (hAb i i.isLt) hV hVb ht
      (hg i i.isLt) hαc hαV hfit, ← Fin.sum_univ_eq_sum_range (fun j ↦
      signedSlot p.width i (Vcol j) * t j * signedSlot p.width k (Vcol j)) m]
    push_cast [Fin.val_inj]
    congr
  have hdiag : ∀ i : Fin p.size, (g i.val : ℝ) / q * x i ^ 2 =
      ∑ k : Fin p.size, if k = i then (g i.val : ℝ) / q * x i * x k else 0 := by
    intro i
    rw [sum_ite_eq']
    simp [sq, mul_assoc]
  have hlow : ∑ j : Fin m, (t j.val : ℝ) / q *
        (∑ i : Fin p.size, (signedSlot p.width i.val (Vcol j.val) : ℝ) * x i) ^ 2 =
      ∑ i : Fin p.size, ∑ k : Fin p.size, (∑ j : Fin m,
        (signedSlot p.width i.val (Vcol j.val) : ℝ) * t j.val *
          signedSlot p.width k.val (Vcol j.val)) / q * x i * x k := by
    simp only [sum_div, sum_mul, sq, mul_sum]
    rw [sum_comm (γ := Fin m)]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [sum_comm (γ := Fin m)]
    exact sum_congr rfl fun k _ ↦ sum_congr rfl fun j _ ↦ by ring
  simp only [hslot, hdiag, hlow, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun k _ ↦ ?_
  split_ifs <;> ring

/-- The slots of `productRow` are the entries of `Aᵀ b - c V_j`. -/
theorem signedSlot_productRow {w n α c : ℕ} {Arow : ℕ → ℕ} {b : ℕ → ℤ} {Vj BA BB BV k : ℕ}
    (hk : k < n) (hA : ∀ l < n, Arow l < 2 ^ (w * n))
    (hAb : ∀ l < n, ∀ k' < n, (signedSlot w k' (Arow l)).natAbs ≤ BA) (hVj : Vj < 2 ^ (w * n))
    (hVb : ∀ k' < n, (signedSlot w k' Vj).natAbs ≤ BV) (hb : ∀ l < n, (b l).natAbs ≤ BB)
    (hαb : BB ≤ α) (hαc : c ≤ α) (hfit : 2 * (n * (BB * BA) + c * BV) < 2 ^ w) :
    signedSlot w k (productRow w n α c Arow b Vj) =
      ∑ l ∈ range n, b l * signedSlot w k (Arow l) - c * signedSlot w k Vj := by
  have hnn : Nat.blt n n = false := by simp [Bool.eq_false_iff]
  have hcoef : ∀ l < n, ((cond (Nat.blt l n) (Int.toNat ((α : ℤ) + b l)) (Nat.sub α c) : ℕ) : ℤ) -
      α = b l := by
    intro l hl
    have := hb l hl
    simp only [Nat.blt_eq.mpr hl, Bool.cond_true]
    omega
  have hcn : ((cond (Nat.blt n n) (Int.toNat ((α : ℤ) + b n)) (Nat.sub α c) : ℕ) : ℤ) - α = -c := by
    simp only [hnn, Bool.cond_false, Nat.sub_eq]
    omega
  have hrows : ∀ l < n + 1, (cond (Nat.blt l n) (Arow l) Vj) < 2 ^ (w * n) := fun l hl ↦ by
    rcases lt_or_ge l n with hln | hln
    · simpa [Nat.blt_eq.mpr hln] using hA l hln
    · obtain rfl : l = n := by omega
      simpa [hnn] using hVj
  have hsum : ∀ k' < n, ∑ l ∈ range (n + 1),
      ((cond (Nat.blt l n) (Int.toNat ((α : ℤ) + b l)) (Nat.sub α c) : ℕ) - (α : ℤ)) *
        signedSlot w k' (cond (Nat.blt l n) (Arow l) Vj) =
      ∑ l ∈ range n, b l * signedSlot w k' (Arow l) - c * signedSlot w k' Vj := by
    intro k' _
    rw [sum_range_succ, hcn]
    simp only [hnn, Bool.cond_false]
    rw [sum_congr rfl fun l hl ↦ by
      rw [hcoef l (mem_range.mp hl), show Nat.blt l n = true from Nat.blt_eq.mpr (mem_range.mp hl),
        Bool.cond_true]]
    ring
  have hfit' : ∀ k' < n, FitsSlot w (∑ l ∈ range (n + 1),
      ((cond (Nat.blt l n) (Int.toNat ((α : ℤ) + b l)) (Nat.sub α c) : ℕ) - (α : ℤ)) *
        signedSlot w k' (cond (Nat.blt l n) (Arow l) Vj)) := by
    intro k' hk'
    rw [hsum k' hk']
    refine fitsSlot_of_natAbs_le ((Int.natAbs_sub_le _ _).trans (add_le_add ?_ ?_)) hfit
    · refine (Int.natAbs_sum_le _ _).trans
        ((sum_le_card_nsmul _ _ (BB * BA) fun l hl ↦ ?_).trans_eq (by simp))
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hb l (mem_range.mp hl)) (hAb l (mem_range.mp hl) k' hk')
    · rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.mul_le_mul_left c (hVb k' hk')
  exact (signedSlot_packedRowCombination hrows hfit' hk).trans (hsum k hk)

/-- The certified lower bound of `quadForm_ge_of_lowRankRowCheck` in real scales: the matrix row
coefficient is `2 ^ (P - s_A)` with `P = 2 t_V + t_W`, the matrix entries are read on the grid
`2 ^ (-s_A)` (transposed: `ã k l = A l k`), the columns on `2 ^ (-t_V)`, the weights on
`2 ^ (-t_W)` and the diagonal as `K` times `g k / (K 2 ^ P)`. -/
theorem capture_center_form_of_lowRankRowCheck (p : PackedLDLParams) {m α BA BV T G sA tV tW : ℕ}
    {Arow Vcol t g Urow d : ℕ → ℕ} (hp : p.valid = true) (hscale : 0 < p.scale)
    (hsA : sA ≤ 2 * tV + tW)
    (hrows : ∀ i < p.size, ldltRowCheck p
      (lowRankRow p.width p.size m α (2 ^ (2 * tV + tW - sA)) Arow Vcol t g) Urow d i = true)
    (hA : ∀ i < p.size, Arow i < 2 ^ (p.width * p.size))
    (hAb : ∀ i < p.size, ∀ l < p.size, (signedSlot p.width l (Arow i)).natAbs ≤ BA)
    (hV : ∀ j < m, Vcol j < 2 ^ (p.width * p.size))
    (hVb : ∀ j < m, ∀ l < p.size, (signedSlot p.width l (Vcol j)).natAbs ≤ BV)
    (ht : ∀ j < m, t j ≤ T) (hg : ∀ i < p.size, g i ≤ G) (hαc : 2 ^ (2 * tV + tW - sA) ≤ α)
    (hαV : BV * T ≤ α)
    (hfit : 2 * (m * (BV * T * BV) + 2 ^ (2 * tV + tW - sA) * BA + G) < 2 ^ p.width)
    {τ K : ℝ} (hK : 0 < K)
    (hτ : p.scale * 2 ^ (2 * tV + tW) * τ + p.size * slotBias p.residualBits ≤ p.shift)
    (x : Fin p.size → ℝ) :
    τ * ∑ k, x k ^ 2 ≤ K * ∑ k : Fin p.size, ((g k.val : ℝ) / 2 ^ (2 * tV + tW) / K) * x k ^ 2 -
      ∑ k : Fin p.size, ∑ l : Fin p.size,
        ((signedSlot p.width k.val (Arow l.val) : ℝ) / 2 ^ sA) * x k * x l +
      ∑ j : Fin m, ((t j.val : ℝ) / 2 ^ tW) *
        (∑ k : Fin p.size, x k * ((signedSlot p.width k.val (Vcol j.val) : ℝ) / 2 ^ tV)) ^ 2 := by
  refine (quadForm_ge_of_lowRankRowCheck p hp hscale hrows hA hAb hV hVb ht hg hαc hαV hfit
    (q := 2 ^ (2 * tV + tW)) (by positivity) hτ x).trans_eq ?_
  have hc : ((2 ^ (2 * tV + tW - sA) : ℕ) : ℝ) / 2 ^ (2 * tV + tW) = 1 / 2 ^ sA := by
    rw [Nat.cast_pow, Nat.cast_ofNat, div_eq_div_iff (by positivity) (by positivity), one_mul,
      ← pow_add, Nat.sub_add_cancel hsA]
  congr 1
  · congr 1
    · rw [mul_sum]
      exact sum_congr rfl fun k _ ↦ by field_simp
    · rw [sum_comm]
      refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_
      rw [mul_comm (((2 ^ (2 * tV + tW - sA) : ℕ) : ℝ)), mul_div_assoc, hc]
      ring
  · refine sum_congr rfl fun j _ ↦ ?_
    have hs : ∑ k : Fin p.size, x k * ((signedSlot p.width k.val (Vcol j.val) : ℝ) / 2 ^ tV) =
        (∑ i : Fin p.size, (signedSlot p.width i.val (Vcol j.val) : ℝ) * x i) / 2 ^ tV := by
      rw [sum_div]; exact sum_congr rfl fun k _ ↦ by ring
    rw [hs, pow_add, pow_mul']
    field_simp

/-- **Product check.** If `productRow` with coefficients `b l` passes the guard `2 ^ (g - 1)`, then
every entry of `Aᵀ b / 2 ^ (s_A + s_C) - V_j / 2 ^ t_V` (with `c = 2 ^ (s_A + s_C - t_V)`) is at
most `2 ^ (g - 1) / 2 ^ (s_A + s_C)`. -/
theorem abs_product_sub_le_of_guard {w n α sA sC tV gb BA BB BV : ℕ} {Arow : ℕ → ℕ}
    {b : ℕ → ℤ} {Vj : ℕ} (hgb : gb < w) (htV : tV ≤ sA + sC)
    (hguard : signedGuardCheck w gb n (productRow w n α (2 ^ (sA + sC - tV)) Arow b Vj) = true)
    (hA : ∀ l < n, Arow l < 2 ^ (w * n))
    (hAb : ∀ l < n, ∀ k' < n, (signedSlot w k' (Arow l)).natAbs ≤ BA) (hVj : Vj < 2 ^ (w * n))
    (hVb : ∀ k' < n, (signedSlot w k' Vj).natAbs ≤ BV) (hb : ∀ l < n, (b l).natAbs ≤ BB)
    (hαb : BB ≤ α) (hαc : 2 ^ (sA + sC - tV) ≤ α)
    (hfit : 2 * (n * (BB * BA) + 2 ^ (sA + sC - tV) * BV) < 2 ^ w) {k : ℕ} (hk : k < n) :
    |∑ l ∈ range n, ((signedSlot w k (Arow l) : ℝ) / 2 ^ sA) * ((b l : ℝ) / 2 ^ sC) -
        (signedSlot w k Vj : ℝ) / 2 ^ tV| ≤ (slotBias gb : ℝ) / 2 ^ (sA + sC) := by
  have hg := natAbs_signedSlot_le_of_signedGuardCheck hgb hguard hk
  rw [signedSlot_productRow hk hA hAb hVj hVb hb hαb hαc hfit] at hg
  have hgr := (Nat.cast_le (α := ℝ)).mpr hg
  rw [Nat.cast_natAbs, Int.cast_abs] at hgr
  push_cast at hgr
  have h2 : (2 : ℝ) ^ (sA + sC) = 2 ^ (sA + sC - tV) * 2 ^ tV := by
    rw [← pow_add, Nat.sub_add_cancel htV]
  have hP : (0 : ℝ) < 2 ^ (sA + sC) := by positivity
  rw [le_div_iff₀ hP, ← abs_of_pos hP, ← abs_mul]
  convert hgr using 2
  rw [sub_mul, sum_mul]
  congr 1
  · exact sum_congr rfl fun l _ ↦ by rw [pow_add]; field_simp
  · rw [h2]; field_simp

end CAS.Numerics

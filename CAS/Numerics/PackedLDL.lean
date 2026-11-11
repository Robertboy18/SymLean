/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedLinearAlgebra
public import CAS.Analysis.Matrix.QuadraticFormBounds
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity.Finset

/-!
# Packed `LDLᵀ` certificates for large matrices

An integer matrix `M` of size `n` is stored as packed rows `Mrow i` of `n` biased slots of
width `w`, and an untrusted lower triangular factor by its columns: `Urow k` holds the entries
`L j k` in slot `j`, zero below slot `k`, for the first `r` columns, with diagonal weights `d k`.
For row `i` the check forms, as one packed row combination of `min (i + 1, r) + 2` rows,
`R i = a M i - b e i - ∑ k ≤ i, L i k d k (column k)`,
reading `L i k` from slot `i` of `Urow k`, and asks with `signedGuardCheck` that every entry
of `R i` lies within `ε = slotBias g`. Then `a M = L D Lᵀ + b I + R` with `|R i j| ≤ ε`, so
`a xᵀ M x ≥ (b - n ε) |x|²` (`quadForm_ge_of_ldltRowCheck`).

## Main definitions

* `PackedLDLParams`: slot width, sizes, entry and residual bounds, the scale `a` of `M` and the
  shift `b`; `PackedLDLParams.valid` checks that every entry of every combination fits its slot.
* `ldltResidualRow`: the packed residual row `R i`.
* `ldltRowCheck`: the entry bounds of row `i` of `M` and of factor column `i`, the zero slots of
  that column below `i`, the bound on its weight, and the residual bound for row `i`.

## Main results

* `quadForm_ge_of_ldltRowCheck`: valid sizes and passing row checks give
  `(b - n ε) |x|² ≤ a xᵀ M x` for every real `x`.
* `quadForm_ge_of_ldltRowCheck_div`: `τ |x|² ≤ xᵀ (M / q) x` whenever `a q τ + n ε ≤ b`.
* `forall_lt_of_forall_fin`, `forall_lt_add_of_forall_fin`: join row ranges checked apart.

## Implementation notes

Untrusted code computes the factor, for `a M - b I`, that is `a (M - (τ + n ε / a) I)` when
`b = a τ + n ε`, so `R` holds only rounding. The kernel evaluates only `PackedLDLParams.valid`
and the row checks; `quadForm_ge_of_ldltRowCheck` turns them into the bound through
`quadForm_ge_of_ldlt_abs_le`, since `L D Lᵀ ⪰ 0` and an entrywise bound `ε` on `R` costs at most
`n ε |x|²`. This is the classical route of a factor of a shifted matrix with a rigorous bound on
its residual (Rump, (10.54)); we bound the residual exactly, in integers. The sizes are fixed in
advance, so that the entry bounds `slotBias matrixBits` and `slotBias factorBits` that the row
checks verify make every entry of every combination fit its slot. Each row check is
independent, so `cega` batches cover any range of rows.

We pack because the kernel evaluates `Nat.add`, `Nat.sub`, `Nat.mul` and the bitwise operations
on natural-number literals with an arbitrary-precision library, GMP in standard builds (see
[PackedSlots](PackedSlots.lean)): the product of a coefficient with a packed row replaces `n`
small products, each of which would cost its own reduction steps, and a row costs about
`3 min (i + 1, r)` big-number operations on numbers of `n w` bits. The packed residual rows and
the split into ranges of rows are ours.

A large check is split into ranges of rows proved in separate modules, of about equal work, and
`forall_lt_of_forall_fin` and `forall_lt_add_of_forall_fin` join the ranges into the hypothesis
of `quadForm_ge_of_ldltRowCheck`. A matrix whose entries span many orders of magnitude, such as
the Gram matrix of modes of very different norms, is certified after scaling its diagonal to
about one, so that the factor stays bounded and one `ε` serves every row.

## References

* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Section 10.8, (10.54): a lower bound for the smallest eigenvalue from an approximate Cholesky
  factor of a shifted matrix and a bound on the residual.
* Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th ed., The Johns Hopkins
  University Press, Baltimore, 2013, <https://doi.org/10.56021/9781421407944>. For the `LDLᵀ`
  and Cholesky factorizations.
-/

@[expose] public section

open Finset

namespace CAS.Numerics

/-- The sizes of a packed `LDLᵀ` check: slot width `width`, matrix size `size`, number of
factor columns `rank`, entry bounds `slotBias matrixBits` for `M` and `slotBias factorBits` for
the factor, residual bound `slotBias residualBits`, the multiplier `scale` of `M`, the diagonal
shift `shift` and a bound `diagonalBound` for the weights. -/
structure PackedLDLParams where
  /-- The slot width `w` of the packed rows, in bits. -/
  width : ℕ
  /-- The matrix size `n`, the number of slots of each row. -/
  size : ℕ
  /-- The number `r` of factor columns. -/
  rank : ℕ
  /-- The bound `slotBias matrixBits` that the row checks verify for the entries of `M`. -/
  matrixBits : ℕ
  /-- The bound `slotBias factorBits` that the row checks verify for the factor entries. -/
  factorBits : ℕ
  /-- The residual bound `ε = slotBias residualBits` that the row checks verify. -/
  residualBits : ℕ
  /-- The multiplier `a` of `M`. -/
  scale : ℕ
  /-- The diagonal shift `b`. -/
  shift : ℕ
  /-- The bound on the diagonal weights `d k`. -/
  diagonalBound : ℕ

namespace PackedLDLParams

variable (p : PackedLDLParams)

/-- The coefficient offset, at least the shift and every factor coefficient. -/
def offset : ℕ := Nat.max p.shift (Nat.mul (slotBias p.factorBits) p.diagonalBound)

/-- The number `min (i + 1, rank)` of factor columns entering row `i`. -/
def columns (i : ℕ) : ℕ := Nat.min (Nat.add i 1) p.rank

/-- The largest absolute entry of a combination, `a BM + b + n BU² D`. -/
def entryBound : ℕ :=
  Nat.add (Nat.add (Nat.mul p.scale (slotBias p.matrixBits)) p.shift)
    (Nat.mul p.size (Nat.mul (Nat.mul (slotBias p.factorBits) (slotBias p.factorBits))
      p.diagonalBound))

/-- The sizes fit: every combination entry fits a slot of the chosen width. -/
def valid : Bool :=
  Nat.ble 2 p.width && Nat.blt p.matrixBits p.width && Nat.blt p.factorBits p.width &&
    Nat.blt p.residualBits p.width && Nat.ble p.rank p.size &&
    Nat.blt (Nat.mul 2 p.entryBound) (Nat.shiftLeft 1 p.width)

end PackedLDLParams

/-- The biased unit row `e i`: `slotBias w + [k = i]` in slot `k`. -/
def unitRow (w n i : ℕ) : ℕ := Nat.add (biasRow w n) (Nat.shiftLeft 1 (Nat.mul w i))

/-- The biased coefficients of row `i`: `-(L i j d j)` for the `m` factor columns, then the
multiplier of `M` and the negated shift. -/
def ldltCoefficient (p : PackedLDLParams) (Urow d : ℕ → ℕ) (i m j : ℕ) : ℕ :=
  cond (Nat.blt j m)
    (Nat.sub (Nat.add p.offset (Nat.mul (slotBias p.width) (d j)))
      (Nat.mul (slot p.width i (Urow j)) (d j)))
    (cond (Nat.beq j m) (Nat.add p.offset p.scale) (Nat.sub p.offset p.shift))

/-- The rows combined for row `i`: the `m` factor columns, row `i` of `M`, the unit row. -/
def ldltRow (p : PackedLDLParams) (Mrow Urow : ℕ → ℕ) (i m j : ℕ) : ℕ :=
  cond (Nat.blt j m) (Urow j) (cond (Nat.beq j m) (Mrow i) (unitRow p.width p.size i))

/-- The packed residual row `a M i - b e i - ∑ k < m, L i k d k (column k)`. -/
def ldltResidualRow (p : PackedLDLParams) (Mrow Urow d : ℕ → ℕ) (i : ℕ) : ℕ :=
  packedRowCombination p.width p.size (Nat.add (p.columns i) 2) p.offset
    (ldltCoefficient p Urow d i (p.columns i)) (ldltRow p Mrow Urow i (p.columns i))

/-- The check of row `i`: entry bounds of row `i` of `M`, of factor column `i` (with its zero
slots below `i`) and of its weight, and the residual bound for row `i`. -/
def ldltRowCheck (p : PackedLDLParams) (Mrow Urow d : ℕ → ℕ) (i : ℕ) : Bool :=
  signedGuardCheck p.width p.matrixBits p.size (Mrow i) &&
    cond (Nat.blt i p.rank)
      (signedGuardCheck p.width p.factorBits p.size (Urow i) &&
        Nat.beq (Nat.land (Urow i) (slotMask (Nat.mul p.width i))) (biasRow p.width i) &&
        Nat.ble (d i) p.diagonalBound)
      true &&
    signedGuardCheck p.width p.residualBits p.size (ldltResidualRow p Mrow Urow d i)

/-! ### Soundness -/

/-- For `i < n`, the unit row `unitRow w n i` is the packing of `slotBias w + 1` in slot `i` and
`slotBias w` in the other `n - 1` slots. -/
theorem unitRow_eq_packSlots {w n i : ℕ} (hi : i < n) :
    unitRow w n i = packSlots w n (fun k ↦ slotBias w + if k = i then 1 else 0) := by
  rw [← packSlots_add, ← biasRow_eq_packSlots]
  change biasRow w n + 1 <<< (w * i) = _
  rw [Nat.one_shiftLeft]
  congr 1
  rw [packSlots_eq_sum]
  simp [hi]

private theorem slotBias_add_one_lt {w : ℕ} (hw : 2 ≤ w) : slotBias w + 1 < 2 ^ w := by
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  rw [slotBias_succ, pow_succ]
  have : 2 ≤ 2 ^ v := Nat.le_self_pow (by omega) 2
  omega

/-- For `2 ≤ w` and `i < n`, the unit row `unitRow w n i` is below `2 ^ (w * n)`. -/
theorem unitRow_lt {w n i : ℕ} (hw : 2 ≤ w) (hi : i < n) : unitRow w n i < 2 ^ (w * n) := by
  rw [unitRow_eq_packSlots hi]
  have := slotBias_add_one_lt hw
  exact packSlots_lt fun k _ ↦ by split_ifs <;> omega

/-- For `2 ≤ w` and `k < n`, signed slot `k` of `unitRow w n i` is `1` when `k = i` and `0`
otherwise, for every `i`, also `n ≤ i`. -/
theorem signedSlot_unitRow {w n i k : ℕ} (hw : 2 ≤ w) (hk : k < n) :
    signedSlot w k (unitRow w n i) = if k = i then 1 else 0 := by
  have := slotBias_add_one_lt hw
  rcases lt_or_ge i n with hi | hi
  · rw [unitRow_eq_packSlots hi, signedSlot, slot_packed_eq (fun j _ ↦ by split_ifs <;> omega),
      ite_eq_left hk]
    split_ifs <;> simp
  -- Past the row, the unit sits above the slots of the bias row.
  have hB : biasRow w n < 2 ^ (w * i) := by
    rw [biasRow_eq_packSlots]
    exact (packSlots_lt fun _ _ ↦ by omega).trans_le
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hi))
  have hrow : unitRow w n i = biasRow w n + 1 * 2 ^ (w * i) := by
    change biasRow w n + 1 <<< (w * i) = _
    rw [Nat.one_shiftLeft, one_mul]
  rw [hrow, signedSlot, slot_add_mul_pow hB, ite_eq_left (by omega), biasRow_eq_packSlots,
    slot_packed_eq (fun _ _ ↦ by omega), ite_eq_left hk, ite_eq_right (by omega)]
  simp

namespace PackedLDLParams

variable {p : PackedLDLParams}

/-- A passing `p.valid` gives `2 ≤ p.width`, `p.matrixBits`, `p.factorBits` and `p.residualBits`
below `p.width`, `p.rank ≤ p.size` and `2 * p.entryBound < 2 ^ p.width`. -/
theorem valid_spec (hp : p.valid = true) :
    2 ≤ p.width ∧ p.matrixBits < p.width ∧ p.factorBits < p.width ∧
      p.residualBits < p.width ∧ p.rank ≤ p.size ∧ 2 * p.entryBound < 2 ^ p.width := by
  simp only [valid, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hp
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hp
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  change 2 * p.entryBound < 1 <<< p.width at h6
  rwa [Nat.one_shiftLeft] at h6

/-- Row `i` uses at most `p.rank` factor columns. -/
theorem columns_le_rank (i : ℕ) : p.columns i ≤ p.rank := Nat.min_le_right _ _

/-- Column `j` enters row `i` exactly when `j ≤ i` and `j < p.rank`. -/
theorem lt_columns_iff {i j : ℕ} : j < p.columns i ↔ j ≤ i ∧ j < p.rank := by
  change j < min (i + 1) p.rank ↔ _
  rw [Nat.lt_min]
  omega

/-- `p.entryBound` is `scale * slotBias matrixBits + shift` plus
`size * (slotBias factorBits * slotBias factorBits * diagonalBound)`. -/
theorem entryBound_eq : p.entryBound = p.scale * slotBias p.matrixBits + p.shift +
    p.size * (slotBias p.factorBits * slotBias p.factorBits * p.diagonalBound) := rfl

end PackedLDLParams

/-- What the row checks give for one column of the factor. -/
structure FactorColumnSpec (p : PackedLDLParams) (Urow d : ℕ → ℕ) (k : ℕ) : Prop where
  /-- Column `k` is a packed row of `size` slots of width `width`. -/
  lt : Urow k < 2 ^ (p.width * p.size)
  /-- Every entry of column `k` is at most `slotBias factorBits` in absolute value. -/
  bound : ∀ j < p.size, (signedSlot p.width j (Urow k)).natAbs ≤ slotBias p.factorBits
  /-- The slots `j < k` of column `k` are zero. -/
  low : ∀ j < k, signedSlot p.width j (Urow k) = 0
  /-- The weight `d k` is at most `diagonalBound`. -/
  weight : d k ≤ p.diagonalBound

/-- For valid sizes and `k < p.rank`, a passing check of row `k` gives `FactorColumnSpec` for
column `k`: it is a packed row of `p.size` slots with entries at most `slotBias p.factorBits` in
absolute value, its slots below `k` are zero, and `d k ≤ p.diagonalBound`. -/
theorem factorColumnSpec_of_rowCheck {p : PackedLDLParams} {Mrow Urow d : ℕ → ℕ} {k : ℕ}
    (hp : p.valid = true) (hk : k < p.rank) (h : ldltRowCheck p Mrow Urow d k = true) :
    FactorColumnSpec p Urow d k := by
  have hv := PackedLDLParams.valid_spec hp
  have hkr : Nat.blt k p.rank = true := Nat.blt_eq.mpr hk
  simp only [ldltRowCheck, hkr, Bool.cond_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  obtain ⟨⟨_, ⟨hg, hlow⟩, hd⟩, _⟩ := h
  exact ⟨lt_of_signedGuardCheck hg, fun j hj ↦ natAbs_signedSlot_le_of_signedGuardCheck hv.2.2.1
    hg hj, fun j hj ↦ signedSlot_eq_zero_of_land hlow hj, hd⟩

/-- The integer entries of the combination for row `i`. -/
theorem sum_ldltCombination {p : PackedLDLParams} {Mrow Urow d : ℕ → ℕ} {i k : ℕ}
    (hp : p.valid = true) (hi : i < p.size) (hk : k < p.size)
    (hU : ∀ j < p.rank, FactorColumnSpec p Urow d j) :
    ∑ j ∈ range (Nat.add (p.columns i) 2),
        ((ldltCoefficient p Urow d i (p.columns i) j : ℤ) - p.offset) *
          signedSlot p.width k (ldltRow p Mrow Urow i (p.columns i) j) =
      p.scale * signedSlot p.width k (Mrow i) - (if k = i then (p.shift : ℤ) else 0) -
        ∑ j ∈ range (p.columns i),
          signedSlot p.width i (Urow j) * d j * signedSlot p.width k (Urow j) := by
  have hv := PackedLDLParams.valid_spec hp
  set m := p.columns i
  have hm : Nat.add m 2 = m + 1 + 1 := rfl
  rw [hm, sum_range_succ, sum_range_succ]
  have hcm : ldltCoefficient p Urow d i m m = p.offset + p.scale := by
    simp [ldltCoefficient]
  have hcm1 : ldltCoefficient p Urow d i m (m + 1) = p.offset - p.shift := by
    simp [ldltCoefficient]
  have hrm : ldltRow p Mrow Urow i m m = Mrow i := by simp [ldltRow]
  have hrm1 : ldltRow p Mrow Urow i m (m + 1) = unitRow p.width p.size i := by
    simp [ldltRow]
  have hshift : p.shift ≤ p.offset := Nat.le_max_left _ _
  rw [hcm, hcm1, hrm, hrm1, signedSlot_unitRow hv.1 hk]
  have hfactor : ∀ j ∈ range m,
      ((ldltCoefficient p Urow d i m j : ℤ) - p.offset) *
          signedSlot p.width k (ldltRow p Mrow Urow i m j) =
        -(signedSlot p.width i (Urow j) * d j * signedSlot p.width k (Urow j)) := by
    intro j hj
    have hjm : j < m := mem_range.mp hj
    have hjm' : Nat.blt j m = true := Nat.blt_eq.mpr hjm
    have hspec := hU j (lt_of_lt_of_le hjm (PackedLDLParams.columns_le_rank i))
    have hbound := hspec.bound i hi
    have hle : slot p.width i (Urow j) * d j ≤ p.offset + slotBias p.width * d j := by
      have h1 : slot p.width i (Urow j) ≤ slotBias p.factorBits + slotBias p.width := by
        unfold signedSlot at hbound
        omega
      have h2 : slotBias p.factorBits * d j ≤ p.offset :=
        (Nat.mul_le_mul_left _ hspec.weight).trans (Nat.le_max_right _ _)
      nlinarith [Nat.mul_le_mul_right (d j) h1]
    simp only [ldltCoefficient, ldltRow, hjm', Bool.cond_true]
    change (((p.offset + slotBias p.width * d j - slot p.width i (Urow j) * d j : ℕ) : ℤ) -
      p.offset) * signedSlot p.width k (Urow j) = _
    rw [Nat.cast_sub hle]
    simp only [signedSlot]
    push_cast
    ring
  rw [sum_congr rfl hfactor, sum_neg_distrib, Nat.cast_sub hshift]
  push_cast
  split_ifs <;> ring

/-- The slots of the residual row of row `i` are the entries
`a M i k - b [k = i] - ∑ j < min (i + 1, r), L i j d j L k j`. -/
theorem signedSlot_ldltResidualRow {p : PackedLDLParams} {Mrow Urow d : ℕ → ℕ} {i k : ℕ}
    (hp : p.valid = true) (hi : i < p.size) (hk : k < p.size)
    (hM : Mrow i < 2 ^ (p.width * p.size))
    (hMb : ∀ j < p.size, (signedSlot p.width j (Mrow i)).natAbs ≤ slotBias p.matrixBits)
    (hU : ∀ j < p.rank, FactorColumnSpec p Urow d j) :
    signedSlot p.width k (ldltResidualRow p Mrow Urow d i) =
      p.scale * signedSlot p.width k (Mrow i) - (if k = i then (p.shift : ℤ) else 0) -
        ∑ j ∈ range (p.columns i),
          signedSlot p.width i (Urow j) * d j * signedSlot p.width k (Urow j) := by
  have hv := PackedLDLParams.valid_spec hp
  set m := p.columns i
  have hrows : ∀ j < Nat.add m 2, ldltRow p Mrow Urow i m j < 2 ^ (p.width * p.size) := by
    intro j _
    unfold ldltRow
    cases hjm : Nat.blt j m
    · cases Nat.beq j m
      · exact unitRow_lt hv.1 hi
      · exact hM
    · exact (hU j ((Nat.blt_eq.mp hjm).trans_le (PackedLDLParams.columns_le_rank i))).lt
  have hfit : ∀ k' < p.size, FitsSlot p.width (∑ j ∈ range (Nat.add m 2),
      ((ldltCoefficient p Urow d i m j : ℤ) - p.offset) *
        signedSlot p.width k' (ldltRow p Mrow Urow i m j)) := by
    intro k' hk'
    rw [sum_ldltCombination hp hi hk' hU]
    apply fitsSlot_of_natAbs_le (m := p.entryBound) _ hv.2.2.2.2.2
    have hMk : |(signedSlot p.width k' (Mrow i) : ℤ)| ≤ slotBias p.matrixBits :=
      (Int.abs_eq_natAbs _).trans_le (by exact_mod_cast hMb k' hk')
    have hsum : |∑ j ∈ range m, signedSlot p.width i (Urow j) * d j *
        signedSlot p.width k' (Urow j)| ≤
        ((p.size * (slotBias p.factorBits * slotBias p.factorBits * p.diagonalBound) : ℕ) :
          ℤ) := by
      refine (abs_sum_le_sum_abs _ _).trans ((sum_le_card_nsmul _ _
        ((slotBias p.factorBits * slotBias p.factorBits * p.diagonalBound : ℕ) : ℤ)
          fun j hj ↦ ?_).trans ?_)
      · have hspec := hU j ((mem_range.mp hj).trans_le (PackedLDLParams.columns_le_rank i))
        have h1 : |(signedSlot p.width i (Urow j) : ℤ)| ≤ slotBias p.factorBits :=
          (Int.abs_eq_natAbs _).trans_le (by exact_mod_cast hspec.bound i hi)
        have h2 : |(signedSlot p.width k' (Urow j) : ℤ)| ≤ slotBias p.factorBits :=
          (Int.abs_eq_natAbs _).trans_le (by exact_mod_cast hspec.bound k' hk')
        have h3 : ((d j : ℕ) : ℤ) ≤ p.diagonalBound := by exact_mod_cast hspec.weight
        rw [abs_mul, abs_mul, Nat.abs_cast]
        push_cast
        calc _ ≤ (slotBias p.factorBits : ℤ) * p.diagonalBound * slotBias p.factorBits := by
              gcongr
          _ = _ := by ring
      · rw [card_range, nsmul_eq_mul]
        exact_mod_cast Nat.mul_le_mul_right _
          ((PackedLDLParams.columns_le_rank i).trans hv.2.2.2.2.1)
    have htot : |(p.scale : ℤ) * signedSlot p.width k' (Mrow i) -
        (if k' = i then (p.shift : ℤ) else 0) - ∑ j ∈ range m,
          signedSlot p.width i (Urow j) * d j * signedSlot p.width k' (Urow j)| ≤
        (p.entryBound : ℤ) := by
      have hite : |(if k' = i then (p.shift : ℤ) else 0)| ≤ p.shift := by
        split_ifs <;> simp
      have hscale : |(p.scale : ℤ) * signedSlot p.width k' (Mrow i)| ≤
          (p.scale : ℤ) * slotBias p.matrixBits := by
        rw [abs_mul, Nat.abs_cast]
        exact mul_le_mul_of_nonneg_left hMk (by positivity)
      refine ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add hscale hite))
        hsum)).trans_eq ?_
      rw [PackedLDLParams.entryBound_eq]
      push_cast
      ring
    rw [Int.abs_eq_natAbs] at htot
    exact_mod_cast htot
  unfold ldltResidualRow
  rw [signedSlot_packedRowCombination hrows hfit hk, sum_ldltCombination hp hi hk hU]

/-- The sum over factor columns `j < min (i + 1, r)` is the `L D Lᵀ` entry of the lower
triangular factor, since column `j` vanishes above row `j`. -/
private theorem sum_columns_eq {p : PackedLDLParams} {Urow d : ℕ → ℕ} (hp : p.valid = true)
    (hU : ∀ j < p.rank, FactorColumnSpec p Urow d j) (i k : Fin p.size) :
    (∑ j ∈ range (p.columns i), (signedSlot p.width i (Urow j) : ℝ) * d j *
        signedSlot p.width k (Urow j)) =
      ∑ j : Fin p.size,
        (if j.val ≤ i.val ∧ j.val < p.rank then (signedSlot p.width i (Urow j) : ℝ) else 0) *
        (if j.val < p.rank then (d j : ℝ) else 0) *
        (if j.val ≤ k.val ∧ j.val < p.rank then (signedSlot p.width k (Urow j) : ℝ) else 0) := by
  have hv := PackedLDLParams.valid_spec hp
  have hmn : p.columns i ≤ p.size := (PackedLDLParams.columns_le_rank i).trans hv.2.2.2.2.1
  rw [Fin.sum_univ_eq_sum_range (fun j ↦
      (if j ≤ i.val ∧ j < p.rank then (signedSlot p.width i (Urow j) : ℝ) else 0) *
      (if j < p.rank then (d j : ℝ) else 0) *
      (if j ≤ k.val ∧ j < p.rank then (signedSlot p.width k (Urow j) : ℝ) else 0)) p.size,
    ← sum_range_add_sum_Ico _ hmn]
  rw [sum_eq_zero (s := Ico (p.columns i) p.size) fun j hj ↦ by
      simp [← PackedLDLParams.lt_columns_iff, not_lt.mpr (mem_Ico.mp hj).1], add_zero]
  refine sum_congr rfl fun j hj ↦ ?_
  have hjc := PackedLDLParams.lt_columns_iff.mp (mem_range.mp hj)
  by_cases hjk : j ≤ k.val
  · simp [hjc, hjk]
  · simp [hjc, hjk, (hU j hjc.2).low k (by omega)]

/-- **Packed `LDLᵀ` certificate.** If the sizes are valid and every row check passes, then
`(b - n ε) |x|² ≤ a xᵀ M x` for the matrix `M i j = signedSlot w j (Mrow i)`, where `a` is the
scale, `b` the shift and `ε = slotBias residualBits`. -/
theorem quadForm_ge_of_ldltRowCheck (p : PackedLDLParams) (Mrow Urow d : ℕ → ℕ)
    (hp : p.valid = true) (hrows : ∀ i < p.size, ldltRowCheck p Mrow Urow d i = true)
    (x : Fin p.size → ℝ) :
    ((p.shift : ℝ) - p.size * slotBias p.residualBits) * ∑ i, x i ^ 2 ≤
      p.scale * ∑ i, ∑ j, (signedSlot p.width j.val (Mrow i.val) : ℝ) * x i * x j := by
  have hv := PackedLDLParams.valid_spec hp
  have hU : ∀ j < p.rank, FactorColumnSpec p Urow d j := fun j hj ↦
    factorColumnSpec_of_rowCheck hp hj (hrows j (lt_of_lt_of_le hj hv.2.2.2.2.1))
  have hrow : ∀ i : Fin p.size, signedGuardCheck p.width p.matrixBits p.size (Mrow i) = true ∧
      signedGuardCheck p.width p.residualBits p.size (ldltResidualRow p Mrow Urow d i) =
        true := fun i ↦ by
    have h := hrows i i.isLt
    simp only [ldltRowCheck, Bool.and_eq_true] at h
    exact ⟨h.1.1, h.2⟩
  set L : Fin p.size → Fin p.size → ℝ := fun i j ↦
    if j.val ≤ i.val ∧ j.val < p.rank then (signedSlot p.width i (Urow j) : ℝ) else 0
  set D : Fin p.size → ℝ := fun j ↦ if j.val < p.rank then (d j : ℝ) else 0
  set R : Fin p.size → Fin p.size → ℝ := fun i k ↦
    (signedSlot p.width k (ldltResidualRow p Mrow Urow d i) : ℝ)
  have hA : ∀ i k : Fin p.size, (p.scale : ℝ) * signedSlot p.width k (Mrow i) =
      ∑ j, L i j * D j * L k j + (if i = k then (p.shift : ℝ) else 0) + R i k := by
    intro i k
    have h := signedSlot_ldltResidualRow (k := k) hp i.isLt k.isLt
      (lt_of_signedGuardCheck (hrow i).1)
      (fun j hj ↦ natAbs_signedSlot_le_of_signedGuardCheck hv.2.1 (hrow i).1 hj) hU
    have hR : R i k = (p.scale : ℝ) * signedSlot p.width k (Mrow i) -
        (if k.val = i.val then (p.shift : ℝ) else 0) - ∑ j ∈ range (p.columns i),
          (signedSlot p.width i (Urow j) : ℝ) * d j * signedSlot p.width k (Urow j) := by
      simp only [R, h]
      push_cast
      rfl
    rw [hR, sum_columns_eq hp hU i k]
    simp only [← Fin.ext_iff, @eq_comm _ k, L, D]
    ring
  have hRb : ∀ i k : Fin p.size, |R i k| ≤ slotBias p.residualBits := fun i k ↦ by
    have h := natAbs_signedSlot_le_of_signedGuardCheck hv.2.2.2.1 (hrow i).2 k.isLt
    simp only [R]
    exact_mod_cast (Int.abs_eq_natAbs _).trans_le (Int.ofNat_le.2 h)
  have hD : ∀ j, 0 ≤ D j := fun j ↦ by simp only [D]; split_ifs <;> positivity
  have hmain := CAS.Analysis.Matrix.quadForm_ge_of_ldlt_abs_le
    (A := fun (i k : Fin p.size) ↦ (p.scale : ℝ) * signedSlot p.width k (Mrow i)) L hD hA hRb x
  simpa only [Fintype.card_fin, mul_sum, mul_assoc] using hmain

/-- The certificate for the real matrix `M / q`: `τ |x|² ≤ xᵀ (M / q) x` for every `τ` with
`a q τ + n ε ≤ b`. -/
theorem quadForm_ge_of_ldltRowCheck_div (p : PackedLDLParams) (Mrow Urow d : ℕ → ℕ)
    (hp : p.valid = true) (hrows : ∀ i < p.size, ldltRowCheck p Mrow Urow d i = true)
    {q τ : ℝ} (hscale : 0 < p.scale) (hq : 0 < q)
    (hτ : p.scale * q * τ + p.size * slotBias p.residualBits ≤ p.shift) (x : Fin p.size → ℝ) :
    τ * ∑ i, x i ^ 2 ≤
      ∑ i, ∑ j, ((signedSlot p.width j.val (Mrow i.val) : ℝ) / q) * x i * x j := by
  have h := quadForm_ge_of_ldltRowCheck p Mrow Urow d hp hrows x
  have ha : (0 : ℝ) < p.scale := by exact_mod_cast hscale
  have hS : 0 ≤ ∑ i, x i ^ 2 := sum_nonneg fun i _ ↦ sq_nonneg _
  have hsum : ∑ i, ∑ j, ((signedSlot p.width j.val (Mrow i.val) : ℝ) / q) * x i * x j =
      (∑ i, ∑ j, (signedSlot p.width j.val (Mrow i.val) : ℝ) * x i * x j) / q := by
    simp only [sum_div, div_mul_eq_mul_div]
  rw [hsum, le_div_iff₀ hq]
  have := mul_le_mul_of_nonneg_right (show (p.scale : ℝ) * q * τ ≤
    (p.shift : ℝ) - p.size * slotBias p.residualBits by linarith) hS
  exact le_of_mul_le_mul_left (by linarith) ha

/-! ### Row ranges checked in separate modules -/

/-- A family checked on `Fin n` holds below `n`. -/
theorem forall_lt_of_forall_fin {P : ℕ → Prop} {n : ℕ} (h : ∀ i : Fin n, P i.val) :
    ∀ i < n, P i :=
  fun i hi ↦ h ⟨i, hi⟩

/-- Joining checked row ranges: the rows below `m` and the `k` rows from `m` on give the rows
below `m + k`. Shards proving `∀ i : Fin k, P (m + i.val)` join in order. -/
theorem forall_lt_add_of_forall_fin {P : ℕ → Prop} {m k : ℕ} (h₁ : ∀ i < m, P i)
    (h₂ : ∀ i : Fin k, P (m + i.val)) : ∀ i < m + k, P i := by
  intro i hi
  by_cases him : i < m
  · exact h₁ i him
  · simpa [show m + (i - m) = i by omega] using h₂ ⟨i - m, by omega⟩

end CAS.Numerics

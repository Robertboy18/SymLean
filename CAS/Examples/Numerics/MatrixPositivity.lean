/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.MatrixPositivity
public import CAS.Numerics.PackedLDL

/-!
# Positivity certificates for a tridiagonal matrix

The matrix `A = tridiag(1, 2, 1)` of size three has eigenvalues `2 - √2`, `2` and `2 + √2`, so
`A ⪰ (1/2) I` but not `A ⪰ (3/5) I`. Each check below is decided by kernel reduction.

* Sylvester's test of `A - m I` accepts `m = 1/2` and rejects `m = 3/5`
  (`tridiagonal_quadForm_ge`); the natural-number test on biased entries accepts a positive
  definite matrix and rejects an indefinite one.
* The dense check `ldltCheck` certifies `A ⪰ (9/20) I` from the rounded factor of `A - (1/2) I`
  with ten fractional bits (`tridiagonal_quadForm_ge_ldlt`).
* The packed check certifies `A ⪰ (509/1024) I` from the same factor stored as packed rows of
  37-bit slots (`tridiagonal_quadForm_ge_packed`): the residual entries stay below `2 ^ 20`
  against the shift `2 ^ 29`.
-/

@[expose] public section

namespace CAS.Examples.Numerics.MatrixPositivity

open CAS.Numerics

/-- The tridiagonal matrix `tridiag(1, 2, 1)` of size three. -/
def tridiagonal : Matrix (Fin 3) (Fin 3) ℚ := !![2, 1, 0; 1, 2, 1; 0, 1, 2]

theorem tridiagonal_isSymm : tridiagonal.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem sylvester3Check_half : sylvester3Check tridiagonal (1 / 2) = true := by
  decide +kernel

theorem sylvester3Check_three_fifths : sylvester3Check tridiagonal (3 / 5) = false := by
  decide +kernel

/-- Sylvester's test gives the lower bound `1/2` for the quadratic form. -/
theorem tridiagonal_quadForm_ge (v : Fin 3 → ℝ) :
    ((1 / 2 : ℚ) : ℝ) * ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, (tridiagonal i j : ℝ) * v i * v j :=
  quadForm_ge_of_sylvester3 tridiagonal tridiagonal_isSymm (1 / 2) sylvester3Check_half v

/-- The biased test accepts `!![3, -1, 1; -1, 3, -1; 1, -1, 3]` with bias `2 ^ 63`. -/
theorem sylvester3SlotCheck_positive :
    sylvester3SlotCheck (2 ^ 63) (2 ^ 63 + 3) (2 ^ 63 - 1) (2 ^ 63 + 1) (2 ^ 63 + 3)
      (2 ^ 63 - 1) (2 ^ 63 + 3) = true := by decide

/-- The biased test rejects the indefinite `!![1, 2, 0; 2, 1, 0; 0, 0, 1]`. -/
theorem sylvester3SlotCheck_indefinite :
    sylvester3SlotCheck (2 ^ 63) (2 ^ 63 + 1) (2 ^ 63 + 2) (2 ^ 63) (2 ^ 63 + 1) (2 ^ 63)
      (2 ^ 63 + 1) = false := by decide

/-- `1024 A`, the numerators of `A` with ten fractional bits. -/
def tridiagonalNumerators : Fin 3 → Fin 3 → ℤ := fun i j ↦ 1024 * (tridiagonal i j).num

/-- The rounded unit lower triangular factor of `A - (1/2) I`, ten fractional bits. -/
def factor : Fin 3 → Fin 3 → ℤ := ![![1024, 0, 0], ![683, 1024, 0], ![0, 1229, 1024]]

/-- The rounded weights `3/2, 5/6, 3/10` with ten fractional bits. -/
def weights : Fin 3 → ℕ := ![1536, 853, 307]

theorem ldltCheck_tridiagonal : ldltCheck tridiagonalNumerators factor weights 10 (9 / 20) =
    true := by decide +kernel

/-- The dense `LDLᵀ` certificate gives `A ⪰ (9/20) I`. -/
theorem tridiagonal_quadForm_ge_ldlt (x : Fin 3 → ℝ) :
    ((9 / 20 : ℚ) : ℝ) * ∑ i, x i ^ 2 ≤
      ∑ i, ∑ j, ((tridiagonalNumerators i j : ℝ) / 2 ^ 10) * x i * x j :=
  quadForm_ge_of_ldltCheck _ _ _ _ _ ldltCheck_tridiagonal x

/-- The sizes of the packed check: 37-bit slots, residual within `2 ^ 20`, scale `2 ^ 20`,
shift `2 ^ 29`. -/
def packedParams : PackedLDLParams where
  width := 37
  size := 3
  rank := 3
  matrixBits := 13
  factorBits := 12
  residualBits := 21
  scale := 1048576
  shift := 536870912
  diagonalBound := 1536

/-- The rows of `1024 A` in biased 37-bit slots. -/
def packedMatrix (i : ℕ) : ℕ :=
  [1298074214643151640239169580566528, 1298074233985964754213973864219648,
    1298074253328777867907303171162112].getD i 0

/-- The columns of the factor in biased 37-bit slots. -/
def packedFactor (k : ℕ) : ℕ :=
  [1298074214643151640192302897431552, 1298074237858305270026345451094016,
    1298074233985964753932498887507968].getD k 0

/-- The weights of the factor. -/
def packedWeights (k : ℕ) : ℕ := [1536, 853, 307].getD k 0

theorem packedParams_valid : packedParams.valid = true := by decide

theorem packed_rows : ∀ i < packedParams.size,
    ldltRowCheck packedParams packedMatrix packedFactor packedWeights i = true := by decide

/-- The packed rows hold `1024 A`. -/
theorem signedSlot_packedMatrix (i j : Fin 3) :
    signedSlot 37 j.val (packedMatrix i.val) = tridiagonalNumerators i j := by
  fin_cases i <;> fin_cases j <;> decide

/-- The packed `LDLᵀ` certificate gives `A ⪰ (509/1024) I`. -/
theorem tridiagonal_quadForm_ge_packed (x : Fin 3 → ℝ) :
    (509 / 1024 : ℝ) * ∑ i, x i ^ 2 ≤
      ∑ i, ∑ j, ((tridiagonalNumerators i j : ℝ) / 2 ^ 10) * x i * x j := by
  have h := quadForm_ge_of_ldltRowCheck_div packedParams packedMatrix packedFactor packedWeights
    packedParams_valid packed_rows (q := 2 ^ 10) (τ := 509 / 1024) (by decide) (by positivity)
    (by norm_num [packedParams, slotBias]) x
  refine h.trans_eq (Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_)
  have hij := signedSlot_packedMatrix i j
  change ((signedSlot 37 j.val (packedMatrix i.val) : ℤ) : ℝ) / 2 ^ 10 * x i * x j = _
  rw [hij]

end CAS.Examples.Numerics.MatrixPositivity

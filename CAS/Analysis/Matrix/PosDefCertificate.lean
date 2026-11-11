/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.Matrix.QuadraticFormBounds
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Positive definiteness and Rayleigh bounds of rational matrices

`ldlIdentity A l D` checks `A = L D Lᵀ` entry by entry over `ℚ`, where `L = unitLower l` is the
unit lower triangular matrix with strict lower part `l` and `D` is diagonal. The real matrix of `A`
is then positive definite when every pivot of `D` is positive (`posDef_of_ldlCheck`) and positive
semidefinite when every pivot is nonnegative (`posSemidef_of_ldlCheck`).

The same check on `A - c I` and on `μ I - A` gives the Rayleigh bounds
`c ∑ xᵢ² ≤ ∑ᵢ ∑ⱼ A i j xᵢ xⱼ ≤ μ ∑ xᵢ²` for every real vector `x` (`quadForm_ge_of_ldlCheck`,
`quadForm_le_of_ldlCheck`). A rational vector whose quadratic form is evaluated exactly shows that
such a bound fails for a larger `c` or a smaller `μ` (`exists_quadForm_lt`, `exists_quadForm_gt`),
or that a matrix is not positive definite (`not_posDef_of_quadFormCheck`).

## Implementation notes

The factorization and the vectors are found outside the kernel, by exact symmetric elimination
over `ℚ` (`QMatrix.ldl`, called by `#cas [positiveDefinite]` and `#cas [eigenvalueBounds]` in
`CAS.Command.Matrix`); the kernel only decides `ldlIdentity`, the signs of the pivots and the
quadratic forms. The soundness proof is a congruence. `L` is lower triangular with ones on the
diagonal, so its determinant is `1` (`Matrix.det_of_isLowerTriangular`) and multiplication by it
is injective (`Matrix.vecMul_injective_iff_isUnit`); Mathlib's
`Matrix.PosDef.mul_mul_conjTranspose_same` and `Matrix.PosSemidef.mul_mul_conjTranspose_same`
then carry the sign of the diagonal `D` (`Matrix.posDef_diagonal_iff`,
`Matrix.posSemidef_diagonal_iff`) over to `L D Lᴴ`. We check `L D Lᵀ` rather than a Cholesky
factor because its pivots stay rational: no square root enters the certificate.

## References

* Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th ed., The Johns Hopkins
  University Press, Baltimore, 2013, <https://doi.org/10.56021/9781421407944>. For the `LDLᵀ`
  and Cholesky factorizations.
-/

@[expose] public section

open Finset Matrix

namespace CAS.Analysis.Matrix

/-- The unit lower triangular matrix whose entries below the diagonal are those of `l`. -/
def unitLower {n : ℕ} (l : Fin n → Fin n → ℚ) (i j : Fin n) : ℚ :=
  if j < i then l i j else if i = j then 1 else 0

/-- Whether `A = L D Lᵀ` entry by entry, for `L = unitLower l` and the diagonal matrix `D`. -/
def ldlIdentity {n : ℕ} (A l : Fin n → Fin n → ℚ) (D : Fin n → ℚ) : Bool :=
  decide (∀ i j, A i j = ∑ k, unitLower l i k * D k * unitLower l j k)

/-- The entrywise identity over `ℚ` as a factorization of the real matrix. -/
private theorem of_eq_unitLower_mul_diagonal {n : ℕ} {A l : Fin n → Fin n → ℚ}
    {D : Fin n → ℚ} (h : ∀ i j, A i j = ∑ k, unitLower l i k * D k * unitLower l j k) :
    (_root_.Matrix.of fun i j ↦ (A i j : ℝ)) =
      _root_.Matrix.of (fun i j ↦ (unitLower l i j : ℝ)) * diagonal (fun k ↦ (D k : ℝ)) *
        (_root_.Matrix.of fun i j ↦ (unitLower l i j : ℝ))ᴴ := by
  ext i j
  rw [mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, star_trivial, of_apply, h i j]
  push_cast
  rfl

/-- `unitLower l` is invertible: it is triangular with ones on the diagonal. -/
private theorem vecMul_unitLower_injective {n : ℕ} (l : Fin n → Fin n → ℚ) :
    Function.Injective (_root_.Matrix.of fun i j ↦ (unitLower l i j : ℝ)).vecMul := by
  have hLow : (_root_.Matrix.of fun i j ↦ (unitLower l i j : ℝ)).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    simp only [of_apply, unitLower, lt_asymm hij', hij'.ne, ite_false, Rat.cast_zero]
  have hdet : (_root_.Matrix.of fun i j ↦ (unitLower l i j : ℝ)).det = 1 := by
    rw [det_of_isLowerTriangular _ hLow]
    simp [unitLower]
  exact vecMul_injective_iff_isUnit.mpr
    ((isUnit_iff_isUnit_det _).mpr (by rw [hdet]; exact isUnit_one))

/-- `A = L D Lᵀ` with positive pivots: `A` is positive definite. -/
theorem posDef_of_ldlCheck {n : ℕ} {A l : Fin n → Fin n → ℚ} {D : Fin n → ℚ}
    (h : (ldlIdentity A l D && decide (∀ i, 0 < D i)) = true) :
    (_root_.Matrix.of fun i j ↦ (A i j : ℝ)).PosDef := by
  simp only [ldlIdentity, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [of_eq_unitLower_mul_diagonal h.1]
  exact (posDef_diagonal_iff.mpr fun k ↦ by exact_mod_cast h.2 k).mul_mul_conjTranspose_same
    (vecMul_unitLower_injective l)

/-- `A = L D Lᵀ` with nonnegative pivots: `A` is positive semidefinite. -/
theorem posSemidef_of_ldlCheck {n : ℕ} {A l : Fin n → Fin n → ℚ} {D : Fin n → ℚ}
    (h : (ldlIdentity A l D && decide (∀ i, 0 ≤ D i)) = true) :
    (_root_.Matrix.of fun i j ↦ (A i j : ℝ)).PosSemidef := by
  simp only [ldlIdentity, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [of_eq_unitLower_mul_diagonal h.1]
  exact (posSemidef_diagonal_iff.mpr fun k ↦ by exact_mod_cast h.2 k).mul_mul_conjTranspose_same _

/-- The quadratic form of a matrix with a nonnegative `LDLᵀ` factorization is nonnegative. -/
private theorem quadForm_nonneg_of_ldlCheck {n : ℕ} {A l : Fin n → Fin n → ℚ} {D : Fin n → ℚ}
    (h : (ldlIdentity A l D && decide (∀ i, 0 ≤ D i)) = true) (x : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, (A i j : ℝ) * x i * x j := by
  have := (posSemidef_of_ldlCheck h).dotProduct_mulVec_nonneg x
  simp only [star_trivial] at this
  rw [← sum_sum_mul_mul_eq_dotProduct_mulVec] at this
  simpa using this

/-- `A - c I = L D Lᵀ` with nonnegative pivots: `c ∑ xᵢ² ≤ ∑ᵢ ∑ⱼ A i j xᵢ xⱼ`. -/
theorem quadForm_ge_of_ldlCheck {n : ℕ} {A l : Fin n → Fin n → ℚ} {D : Fin n → ℚ} {c : ℚ}
    (h : (ldlIdentity (fun i j ↦ A i j - if i = j then c else 0) l D &&
      decide (∀ i, 0 ≤ D i)) = true) (x : Fin n → ℝ) :
    (c : ℝ) * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, (A i j : ℝ) * x i * x j := by
  have h0 := quadForm_nonneg_of_ldlCheck h x
  have hsplit : ∑ i, ∑ j, (((A i j - if i = j then c else 0 : ℚ)) : ℝ) * x i * x j =
      ∑ i, ∑ j, (A i j : ℝ) * x i * x j - (c : ℝ) * ∑ i, x i ^ 2 := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [Rat.cast_sub, sub_mul, sum_sub_distrib]
    congr 1
    rw [sum_eq_single i (fun j _ hj ↦ by simp [Ne.symm hj]) (by simp)]
    simp only [↓reduceIte]
    ring
  linarith

/-- `μ I - A = L D Lᵀ` with nonnegative pivots: `∑ᵢ ∑ⱼ A i j xᵢ xⱼ ≤ μ ∑ xᵢ²`. -/
theorem quadForm_le_of_ldlCheck {n : ℕ} {A l : Fin n → Fin n → ℚ} {D : Fin n → ℚ} {μ : ℚ}
    (h : (ldlIdentity (fun i j ↦ (if i = j then μ else 0) - A i j) l D &&
      decide (∀ i, 0 ≤ D i)) = true) (x : Fin n → ℝ) :
    ∑ i, ∑ j, (A i j : ℝ) * x i * x j ≤ (μ : ℝ) * ∑ i, x i ^ 2 := by
  have h0 := quadForm_nonneg_of_ldlCheck h x
  have hsplit : ∑ i, ∑ j, ((((if i = j then μ else 0) - A i j : ℚ)) : ℝ) * x i * x j =
      (μ : ℝ) * ∑ i, x i ^ 2 - ∑ i, ∑ j, (A i j : ℝ) * x i * x j := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [Rat.cast_sub, sub_mul, sum_sub_distrib]
    congr 1
    rw [sum_eq_single i (fun j _ hj ↦ by simp [Ne.symm hj]) (by simp)]
    simp only [↓reduceIte]
    ring
  linarith

/-- A rational vector `x` with `xᵀ A x < t |x|²`, checked over `ℚ`, gives a real one. -/
theorem exists_quadForm_lt {n : ℕ} {A : Fin n → Fin n → ℚ} {t : ℚ} (x : Fin n → ℚ)
    (h : decide (∑ i, ∑ j, A i j * x i * x j < t * ∑ i, x i ^ 2) = true) :
    ∃ y : Fin n → ℝ, ∑ i, ∑ j, (A i j : ℝ) * y i * y j < (t : ℝ) * ∑ i, y i ^ 2 :=
  ⟨fun i ↦ (x i : ℝ), by
    change ∑ i, ∑ j, (A i j : ℝ) * (x i : ℝ) * (x j : ℝ) < (t : ℝ) * ∑ i, (x i : ℝ) ^ 2
    exact_mod_cast of_decide_eq_true h⟩

/-- A rational vector `x` with `t |x|² < xᵀ A x`, checked over `ℚ`, gives a real one. -/
theorem exists_quadForm_gt {n : ℕ} {A : Fin n → Fin n → ℚ} {t : ℚ} (x : Fin n → ℚ)
    (h : decide (t * ∑ i, x i ^ 2 < ∑ i, ∑ j, A i j * x i * x j) = true) :
    ∃ y : Fin n → ℝ, (t : ℝ) * ∑ i, y i ^ 2 < ∑ i, ∑ j, (A i j : ℝ) * y i * y j :=
  ⟨fun i ↦ (x i : ℝ), by
    change (t : ℝ) * ∑ i, (x i : ℝ) ^ 2 < ∑ i, ∑ j, (A i j : ℝ) * (x i : ℝ) * (x j : ℝ)
    exact_mod_cast of_decide_eq_true h⟩

/-- A vector with a nonpositive quadratic form shows that a matrix is not positive definite. -/
theorem not_posDef_of_quadForm_nonpos {n : ℕ} {A : _root_.Matrix (Fin n) (Fin n) ℝ}
    (x : Fin n → ℝ) (hx : x ≠ 0) (h : ∑ i, ∑ j, A i j * x i * x j ≤ 0) : ¬ A.PosDef := by
  intro hA
  have hpos := hA.dotProduct_mulVec_pos hx
  rw [sum_sum_mul_mul_eq_dotProduct_mulVec] at h
  simp only [star_trivial] at hpos
  linarith

/-- A nonzero rational vector with a nonpositive quadratic form, both checked over `ℚ`, shows
that a rational matrix is not positive definite. -/
theorem not_posDef_of_quadFormCheck {n : ℕ} {A : Fin n → Fin n → ℚ} (x : Fin n → ℚ)
    (h : (decide (∃ i, x i ≠ 0) && decide (∑ i, ∑ j, A i j * x i * x j ≤ 0)) = true) :
    ¬ (_root_.Matrix.of fun i j ↦ (A i j : ℝ)).PosDef := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨i, hi⟩, hq⟩ := h
  refine not_posDef_of_quadForm_nonpos (fun i ↦ (x i : ℝ))
    (fun h0 ↦ hi (by simpa using congrFun h0 i)) ?_
  simp only [of_apply]
  exact_mod_cast hq

end CAS.Analysis.Matrix

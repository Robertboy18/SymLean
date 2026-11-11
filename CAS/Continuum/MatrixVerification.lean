/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Approximate inverse verification for finite matrices

The analytic kernel for checked finite-dimensional matrix inversion. A candidate consists only of
a square matrix `A`, a proposed inverse `B`, and a proposed residual bound `r`; it contains no
proof. `ApproximateInverseCandidate.IsCertified` says that the Euclidean operator norm of the
left residual `1 - B * A` is at most `r` and that `r < 1`. From it we prove that `A` and `B` are
units, that `A` acts bijectively on Euclidean space, and an a posteriori bound for `A⁻¹ - B`.

## Main definitions

* `ApproximateInverseCandidate`: the proof-free data `A`, `B` and `r`.
* `ApproximateInverseCandidate.IsCertified`: `‖1 - B * A‖ ≤ r` and `r < 1`.

## Main results

* `ApproximateInverseCandidate.matrix_isUnit`, `proposedInverse_isUnit`: if
  `‖1 - B * A‖ ≤ r < 1`, then `A` and `B` are invertible.
* `toEuclideanCLM_bijective`: `A` acts bijectively on Euclidean space.
* `inverse_sub_proposedInverse_norm_le`: `‖A⁻¹ - B‖ ≤ r * ‖A⁻¹‖`.

## Implementation notes

The test is the classical residual verification of an approximate inverse (Theorem 10.2 in
Rump's survey). We prove it with Mathlib's Neumann-series lemma `isUnit_one_sub_of_norm_lt_one`,
which makes `B * A` a unit. Square matrix rings are directly finite, so `IsUnit.mul_iff` makes
both `A` and `B` units: a one-sided approximate inverse gives invertibility. The error bound
comes from the identity `(1 - B * A) * A⁻¹ = A⁻¹ - B`; Rump's bound (10.9) for the solution of a
linear system is not proved here.

The caller computes `B` numerically, and `B` need not be exact. Only a proof of `IsCertified`
enters the theorems, so the kernel checks the residual inequality and the strict threshold and
never the computation that produced `B`.

## References

* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Theorem 10.2 is the test `‖I - R A‖ < 1`, there for any matrix norm.
-/

@[expose] public section

namespace CAS.Continuum.MatrixVerification

open scoped Matrix.Norms.L2Operator

/-- Proof-free data proposed by a finite-dimensional approximate-inverse computation. -/
structure ApproximateInverseCandidate (n 𝕜 : Type*) where
  /-- Square matrix whose invertibility is to be certified. -/
  matrix : Matrix n n 𝕜
  /-- Numerically proposed inverse. It is not assumed to be exact. -/
  proposedInverse : Matrix n n 𝕜
  /-- Proposed nonnegative upper bound for the operator norm of the left residual. -/
  residualBound : NNReal

namespace ApproximateInverseCandidate

variable {n 𝕜 : Type*}

/-- Left residual `1 - B * A` of an approximate inverse `B` for a matrix `A`. -/
def leftResidual [Fintype n] [DecidableEq n] [Ring 𝕜]
    (candidate : ApproximateInverseCandidate n 𝕜) : Matrix n n 𝕜 :=
  1 - candidate.proposedInverse * candidate.matrix

section RCLike

variable [Fintype n] [DecidableEq n] [RCLike 𝕜]

/--
The mathematical obligations for an approximate-inverse certificate.

The norm is Mathlib's Euclidean operator norm on matrices. This proposition is kept
separate from `ApproximateInverseCandidate`: untrusted numerical code may propose the data, but
the residual inequality and strict threshold must be proved in Lean.
-/
def IsCertified (candidate : ApproximateInverseCandidate n 𝕜) : Prop :=
  ‖candidate.leftResidual‖ ≤ (candidate.residualBound : ℝ) ∧
    (candidate.residualBound : ℝ) < 1

/-- A certified residual has operator norm strictly below one. -/
theorem residual_norm_lt_one {candidate : ApproximateInverseCandidate n 𝕜}
    (hcert : candidate.IsCertified) : ‖candidate.leftResidual‖ < 1 :=
  lt_of_le_of_lt hcert.1 hcert.2

/-- Neumann verification makes the product of the proposal and target matrix a unit. -/
theorem proposedInverse_mul_matrix_isUnit
    {candidate : ApproximateInverseCandidate n 𝕜}
    (hcert : candidate.IsCertified) :
    IsUnit (candidate.proposedInverse * candidate.matrix) := by
  simpa [leftResidual] using isUnit_one_sub_of_norm_lt_one (candidate.residual_norm_lt_one hcert)

/-- A certified one-sided approximate inverse proves that the target square matrix is a unit. -/
theorem matrix_isUnit {candidate : ApproximateInverseCandidate n 𝕜}
    (hcert : candidate.IsCertified) : IsUnit candidate.matrix :=
  (IsUnit.mul_iff.mp (candidate.proposedInverse_mul_matrix_isUnit hcert)).2

/-- A certified one-sided approximate inverse is itself invertible. -/
theorem proposedInverse_isUnit {candidate : ApproximateInverseCandidate n 𝕜}
    (hcert : candidate.IsCertified) : IsUnit candidate.proposedInverse :=
  (IsUnit.mul_iff.mp (candidate.proposedInverse_mul_matrix_isUnit hcert)).1

/-- An invertible matrix acts bijectively on Euclidean space. -/
theorem toEuclideanCLM_bijective_of_isUnit
    (candidate : ApproximateInverseCandidate n 𝕜)
    (hmatrix : IsUnit candidate.matrix) :
    Function.Bijective
      ((Matrix.toEuclideanCLM (n := n) (𝕜 := 𝕜)) candidate.matrix) :=
  ContinuousLinearMap.isUnit_iff_bijective.mp (hmatrix.map Matrix.toEuclideanCLM)

/-- The matrix associated to a certified candidate acts bijectively on Euclidean space. -/
theorem toEuclideanCLM_bijective
    {candidate : ApproximateInverseCandidate n 𝕜}
    (hcert : candidate.IsCertified) :
    Function.Bijective
      ((Matrix.toEuclideanCLM (n := n) (𝕜 := 𝕜)) candidate.matrix) :=
  candidate.toEuclideanCLM_bijective_of_isUnit (candidate.matrix_isUnit hcert)

/--
A posteriori error bound for the proposed inverse.

The right side uses the certified residual bound and the norm of the ring inverse, which the
certificate itself does not bound.
-/
theorem inverse_sub_proposedInverse_norm_le
    {candidate : ApproximateInverseCandidate n 𝕜}
    (hcert : candidate.IsCertified) :
    ‖Ring.inverse candidate.matrix - candidate.proposedInverse‖ ≤
      (candidate.residualBound : ℝ) * ‖Ring.inverse candidate.matrix‖ := by
  have hmatrix := candidate.matrix_isUnit hcert
  have hidentity :
      candidate.leftResidual * Ring.inverse candidate.matrix =
        Ring.inverse candidate.matrix - candidate.proposedInverse := by
    rw [leftResidual, sub_mul, one_mul, mul_assoc,
      Ring.mul_inverse_cancel candidate.matrix hmatrix, mul_one]
  rw [← hidentity]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hcert.1 (norm_nonneg _))

end RCLike

end ApproximateInverseCandidate

end CAS.Continuum.MatrixVerification

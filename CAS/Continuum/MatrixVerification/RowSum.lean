/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.MatrixVerification

/-!
# Row-sum certificates for approximate matrix inverses

Entrywise bounds on `I - B A` give an approximate-inverse theorem. `ResidualEntryBounds` is an
exact rational matrix of proposed entry bounds and contains no proof.
`ResidualEntryBounds.IsCertified` checks each proposed entry bound, every resulting row sum
against the candidate's residual bound, and the strict Neumann threshold.
`ResidualEntryBounds.matrix_isUnit` is the resulting invertibility theorem.

## Implementation notes

The checker uses Mathlib's matrix infinity operator norm, whose value is the maximum absolute row
sum (`Matrix.linfty_opNorm_def`), and then the Neumann-series lemma as in `MatrixVerification`.
Row sums of exact rationals are cheap to check, while the Euclidean operator norm used by
`ApproximateInverseCandidate.IsCertified` has no such formula. The result is algebraic
invertibility, so clients using the Euclidean operator norm may use it without identifying the
two matrix norms. The proposed inverse and the entry bounds come from the caller, for example a
numerical backend; only a proof of `IsCertified` reaches the theorems.

## References

* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Theorem 10.2 is the test `‖I - R A‖ < 1` for any matrix norm; the remark after it notes that
  the infinity norm is easy to calculate.
-/

@[expose] public section

namespace CAS.Continuum.MatrixVerification

open scoped Matrix.Norms.Operator

/-- Exact rational upper bounds proposed for the entries of an approximate-inverse residual. -/
abbrev ResidualEntryBounds (n : Type*) :=
  Matrix n n ℚ

namespace ResidualEntryBounds

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/--
Semantic obligations for exact entry bounds and their induced row-sum bound.

The first conjunct checks every entry. The second checks that every exact rational row sum fits
under the candidate's intrinsically nonnegative residual bound. The final inequality is the
Neumann threshold.
-/
def IsCertified (bounds : ResidualEntryBounds n)
    (candidate : ApproximateInverseCandidate n 𝕜) : Prop :=
  (∀ i j, ‖candidate.leftResidual i j‖ ≤ (bounds i j : ℝ)) ∧
    (∀ i, ((∑ j, bounds i j : ℚ) : ℝ) ≤ (candidate.residualBound : ℝ)) ∧
    (candidate.residualBound : ℝ) < 1

/-- Certified entry bounds imply the corresponding absolute row-sum estimates. -/
theorem row_norm_sum_le (bounds : ResidualEntryBounds n)
    (candidate : ApproximateInverseCandidate n 𝕜)
    (hcert : bounds.IsCertified candidate) (i : n) :
    ∑ j, ‖candidate.leftResidual i j‖ ≤ (candidate.residualBound : ℝ) :=
  (Finset.sum_le_sum fun j _ ↦ hcert.1 i j).trans
    ((Rat.cast_sum _ _).symm.trans_le (hcert.2.1 i))

/-- Certified entry bounds put the matrix infinity norm of the residual below one. -/
theorem residual_norm_lt_one (bounds : ResidualEntryBounds n)
    (candidate : ApproximateInverseCandidate n 𝕜)
    (hcert : bounds.IsCertified candidate) :
    ‖candidate.leftResidual‖ < 1 := by
  refine lt_of_le_of_lt ?_ hcert.2.2
  rw [Matrix.linfty_opNorm_def, NNReal.coe_le_coe]
  refine Finset.sup_le fun i _ ↦ ?_
  rw [← NNReal.coe_le_coe]
  simpa only [NNReal.coe_sum, coe_nnnorm] using bounds.row_norm_sum_le candidate hcert i

/-- Entrywise row-sum verification proves that the proposed product `B A` is a unit. -/
theorem proposedInverse_mul_matrix_isUnit
    (bounds : ResidualEntryBounds n)
    (candidate : ApproximateInverseCandidate n 𝕜)
    (hcert : bounds.IsCertified candidate) :
    IsUnit (candidate.proposedInverse * candidate.matrix) := by
  simpa [ApproximateInverseCandidate.leftResidual] using
    isUnit_one_sub_of_norm_lt_one (bounds.residual_norm_lt_one candidate hcert)

/-- Entrywise row-sum verification proves that the target square matrix is invertible. -/
theorem matrix_isUnit
    (bounds : ResidualEntryBounds n)
    (candidate : ApproximateInverseCandidate n 𝕜)
    (hcert : bounds.IsCertified candidate) : IsUnit candidate.matrix :=
  (IsUnit.mul_iff.mp (bounds.proposedInverse_mul_matrix_isUnit candidate hcert)).2

end ResidualEntryBounds

end CAS.Continuum.MatrixVerification

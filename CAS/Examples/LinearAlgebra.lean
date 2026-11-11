/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
meta import CAS.Analysis.Matrix.Spectrum

/-!
# Exact linear algebra over `ℚ`: `det`, `inverse`, `rowReduce`, `nullSpace`, `eigenvectors`, …

The matrix commands of `CAS.Command.LinearAlgebra`. Each command runs in the build inside
`#guard_msgs`, which checks its report; each report's theorem is kernel-checked when the command
runs.

`#cas [inverse]` of a singular matrix proves `A.det = 0` instead of an inverse: Mathlib's
`A⁻¹` is total and is `0` for a singular matrix, as the first example shows, so `A⁻¹ = 0` would be
a true theorem but not an inverse.
-/

namespace CAS.Examples.LinearAlgebra

/-- Mathlib's inverse of the singular matrix `!![1, 2; 2, 4]` is `0`. -/
example : (!![(1 : ℚ), 2; 2, 4])⁻¹ = 0 :=
  Matrix.nonsing_inv_apply_not_isUnit _ (by simp only [norm_det]; norm_num)

end CAS.Examples.LinearAlgebra

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

-- Det, Inverse, Transpose, Tr, MatrixPower, Dot
/--
info: #cas [det]
Domain: ℚ^(3×3)
Input (matrix): !![1, 2, 3; 4, 5, 6; 7, 8, 10]
Output (determinant): -3

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Determinant
        Proposition: !![1, 2, 3; 4, 5, 6; 7, 8, 10].det = -3
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [det] !![1, 2, 3; 4, 5, 6; 7, 8, 10]

set_option linter.style.longLine false in
/--
info: #cas [det]
Domain: ℚ^(5×5)
Input (matrix): !![2, -1, 0, 0, 1; -1, 2, -1, 0, 0; 0, -1, 2, -1, 0; 0, 0, -1, 2, -1; 1, 0, 0, -1, 2]
Output (determinant): 4

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [det] !![2, -1, 0, 0, 1; -1, 2, -1, 0, 0; 0, -1, 2, -1, 0; 0, 0, -1, 2, -1; 1, 0, 0, -1, 2]

/--
info: #cas [inverse]
Domain: ℚ^(2×2)
Input (matrix): !![1, 2; 3, 4]
Output (inverse): !![-2, 1; 3/2, -1/2]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Inverse from the product B * A = 1
        Proposition: !![1, 2; 3, 4]⁻¹ = !![-2, 1; 3 / 2, -(1 / 2)]
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [inverse] !![1, 2; 3, 4]

/--
info: #cas [inverse]
Domain: ℚ^(3×3)
Input (matrix): !![1, 2, 3; 0, 1, 4; 5, 6, 0]
Output (inverse): !![-24, 18, 5; 20, -15, -4; -5, 4, 1]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [inverse] !![1, 2, 3; 0, 1, 4; 5, 6, 0]

/--
info: #cas [inverse]
Domain: ℚ^(2×2)
Input (matrix): !![1, 2; 2, 4]
Output (no inverse): the matrix is singular (determinant 0); Mathlib's A⁻¹ is 0

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The determinant vanishes
        Proposition: !![1, 2; 2, 4].det = 0
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [inverse] !![1, 2; 2, 4]

/--
info: #cas [transpose]
Domain: ℚ^(2×3)
Input (matrix): !![1, 2, 3; 4, 5, 6]
Output (transpose): !![1, 4; 2, 5; 3, 6]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [transpose] !![1, 2, 3; 4, 5, 6]

/--
info: #cas [trace]
Domain: ℚ^(2×2)
Input (matrix): !![1, 2; 3, 4]
Output (trace): 5

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [trace] !![1, 2; 3, 4]

/--
info: #cas [matrixPower 10]
Domain: ℚ^(2×2)
Input (matrix): !![1, 1; 1, 0]
Output (power): !![89, 55; 55, 34]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Decided by kernel evaluation
        Proposition: !![1, 1; 1, 0] ^ 10 = !![89, 55; 55, 34]
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [matrixPower 10] !![1, 1; 1, 0]

/--
info: #cas [dot]
Domain: ℚ^(2×2)
Input (product): !![1, 2; 3, 4] . !![0, 1; 1, 0]
Output (product): !![2, 1; 4, 3]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dot] (!![1, 2; 3, 4], !![0, 1; 1, 0])

/--
info: #cas [dot]
Domain: ℚ^(2×3)
Input (product): !![1, 2, 3; 4, 5, 6] . ![1, 1, 1]
Output (product): ![6, 15]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dot] (!![1, 2, 3; 4, 5, 6], ![1, 1, 1])

/--
error: det: the matrix must be square
-/
#guard_msgs (error, drop info) in
#cas [det] !![1, 2, 3; 4, 5, 6]

/--
error: the rows of the matrix have different lengths
-/
#guard_msgs (error, drop info) in
#cas [inverse] !![1, 2; 3]

-- RowReduce, MatrixRank, NullSpace, LinearSolve
set_option linter.style.longLine false in
/--
info: #cas [rowReduce]
Domain: ℚ^(3×3)
Input (matrix): !![1, 2, 3; 4, 5, 6; 7, 8, 9]
Output (reduced row echelon form, pivot columns [0, 1]): !![1, 0, -1; 0, 1, 2; 0, 0, 0]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Row operations E with E * A = R
        Proposition: !![-(5 / 3), 2 / 3, 0; 4 / 3, -(1 / 3), 0; 1, -2, 1] * !![1, 2, 3; 4, 5, 6; 7, 8, 9] =
            !![1, 0, -1; 0, 1, 2; 0, 0, 0] ∧
          !![-(5 / 3), 2 / 3, 0; 4 / 3, -(1 / 3), 0; 1, -2, 1].det ≠ 0 ∧
            !![1, 0, -1; 0, 1, 2; 0, 0, 0].IsReducedRowEchelon
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [rowReduce] !![1, 2, 3; 4, 5, 6; 7, 8, 9]

/--
info: #cas [rowReduce]
Domain: ℚ^(3×4)
Input (matrix): !![0, 2, 4, 1; 1, 1, 1, 1; 2, 4, 6, 3]
Output (reduced row echelon form, pivot columns [0, 1]): !![1, 0, -1, 1/2; 0, 1, 2, 1/2; 0, 0, 0, 0]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [rowReduce] !![0, 2, 4, 1; 1, 1, 1, 1; 2, 4, 6, 3]

/--
info: #cas [matrixRank]
Domain: ℚ^(3×3)
Input (matrix): !![1, 2, 3; 4, 5, 6; 7, 8, 9]
Output (rank): 2

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Rank from a factorization and a nonsingular minor
        Proposition: !![1, 2, 3; 4, 5, 6; 7, 8, 9].rank = 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [matrixRank] !![1, 2, 3; 4, 5, 6; 7, 8, 9]

/--
info: #cas [matrixRank]
Domain: ℚ^(2×4)
Input (matrix): !![1, 2, 3, 4; 2, 4, 6, 8]
Output (rank): 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [matrixRank] !![1, 2, 3, 4; 2, 4, 6, 8]

/--
info: #cas [matrixRank]
Domain: ℚ^(2×2)
Input (matrix): !![0, 0; 0, 0]
Output (rank): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [matrixRank] !![0, 0; 0, 0]

set_option linter.style.longLine false in
/--
info: #cas [nullSpace]
Domain: ℚ^(2×3)
Input (matrix): !![1, 2, 3; 2, 4, 6]
Output (basis of the null space, dimension 2): [![-2, 1, 0], ![-3, 0, 1]]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Basis of the null space
        Proposition: (∀ (i : Fin (Nat.succ 1)), !![1, 2, 3; 2, 4, 6].mulVec (![![-2, 1, 0], ![-3, 0, 1]] i) = 0) ∧
          LinearIndependent ℚ ![![-2, 1, 0], ![-3, 0, 1]] ∧
            ∀ (x : Fin 3 → ℚ), !![1, 2, 3; 2, 4, 6].mulVec x = 0 → ∃ c, x = ∑ i, c i • ![![-2, 1, 0], ![-3, 0, 1]] i
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [nullSpace] !![1, 2, 3; 2, 4, 6]

/--
info: #cas [nullSpace]
Domain: ℚ^(2×2)
Input (matrix): !![1, 2; 3, 4]
Output (basis of the null space, dimension 0): [] (only the zero vector)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nullSpace] !![1, 2; 3, 4]

set_option linter.style.longLine false in
/--
info: #cas [linearSolve]
Domain: ℚ^(2×3)
Input (linear system): !![1, 2, 3; 2, 4, 6] . x = ![1, 2]
Output (all solutions): ![1, 0, 0] + span of [![-2, 1, 0], ![-3, 0, 1]]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Solution set
        Proposition: !![1, 2, 3; 2, 4, 6].mulVec ![1, 0, 0] = ![1, 2] ∧
          LinearIndependent ℚ ![![-2, 1, 0], ![-3, 0, 1]] ∧
            ∀ (x : Fin 3 → ℚ),
              !![1, 2, 3; 2, 4, 6].mulVec x = ![1, 2] ↔ ∃ c, x = ![1, 0, 0] + ∑ i, c i • ![![-2, 1, 0], ![-3, 0, 1]] i
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [linearSolve] (!![1, 2, 3; 2, 4, 6], ![1, 2])

/--
info: #cas [linearSolve]
Domain: ℚ^(2×2)
Input (linear system): !![1, 2; 3, 4] . x = ![5, 6]
Output (all solutions): ![-4, 9/2]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [linearSolve] (!![1, 2; 3, 4], ![5, 6])

/--
info: #cas [linearSolve]
Domain: ℚ^(2×3)
Input (linear system): !![1, 2, 3; 2, 4, 6] . x = ![1, 3]
Output (all solutions): no solution

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Solution set
        Proposition: ¬∃ x, !![1, 2, 3; 2, 4, 6].mulVec x = ![1, 3]
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [linearSolve] (!![1, 2, 3; 2, 4, 6], ![1, 3])

/--
info: #cas [linearSolve]
Domain: ℚ^(3×3)
Input (linear system): !![1, 1, 1; 1, -1, 2; 2, 0, 3] . x = ![6, 5, 11]
Output (all solutions): ![11/2, 1/2, 0] + span of [![-3/2, 1/2, 1]]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [linearSolve] (!![1, 1, 1; 1, -1, 2; 2, 0, 3], ![6, 5, 11])

/--
error: linearSolve: the right side has 3 entries, the matrix 2 rows
-/
#guard_msgs (error, drop info) in
#cas [linearSolve] (!![1, 2; 3, 4], ![5, 6, 7])

-- CharacteristicPolynomial, Eigenvalues, Eigenvectors
/--
info: #cas [characteristicPolynomial]
Domain: ℚ^(2×2)
Input (matrix): !![1, 2; 3, 4]
Output (det (x I - A)): x^2 - 5*x - 2

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Characteristic polynomial in ℚ[X]
        Proposition: !![1, 2; 3, 4].charpoly = Polynomial.X ^ 2 - 5 * Polynomial.X - 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [characteristicPolynomial] !![1, 2; 3, 4]

/--
info: #cas [characteristicPolynomial]
Domain: ℚ^(4×4)
Input (matrix): !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2]
Output (det (x I - A)): x^4 - 8*x^3 + 21*x^2 - 20*x + 5

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [characteristicPolynomial] !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2]

/--
info: #cas [eigenvalues]
Domain: ℚ^(3×3)
Input (matrix): !![2, 0, 0; 0, 3, 4; 0, 4, 9]
Output (eigenvalues with multiplicity): [1, 2, 11]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Characteristic polynomial factored over ℚ, eigenspaces
        Proposition: !![2, 0, 0; 0, 3, 4; 0, 4, 9].charpoly =
          (Polynomial.X - 1) * (Polynomial.X - 2) * (Polynomial.X - 11)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] core route of eigenvalues: selected
-/
#guard_msgs in
#cas [eigenvalues] !![2, 0, 0; 0, 3, 4; 0, 4, 9]

/--
info: #cas [eigenvalues]
Domain: ℚ^(2×2)
Input (matrix): !![1, 2; 3, 4]
Output (eigenvalues with multiplicity): [5/2 - √33/2, 5/2 + √33/2]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [eigenvalues] !![1, 2; 3, 4]

/--
info: #cas [eigenvalues]
Domain: ℚ^(2×2)
Input (matrix): !![0, 1; 1, 1]
Output (eigenvalues with multiplicity): [1/2 - √5/2, 1/2 + √5/2]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The spectrum with algebraic multiplicities
        Proposition: spectrum ℝ !![0, 1; 1, 1] = {1 / 2 - 1 / 2 * √5, 1 / 2 + 1 / 2 * √5} ∧
          !![0, 1; 1, 1].charpoly.roots = {1 / 2 - 1 / 2 * √5, 1 / 2 + 1 / 2 * √5}
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] core route of eigenvalues: selected
-/
#guard_msgs in
#cas [eigenvalues] !![0, 1; 1, 1]

/--
info: #cas [eigenvalues]
Domain: ℚ^(2×2)
Input (matrix): !![0, -1; 1, 0]
Output (eigenvalues with multiplicity): [i, -i]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The spectrum with algebraic multiplicities
        Proposition: spectrum ℂ !![0, -1; 1, 0] = {Complex.I, -Complex.I} ∧
          !![0, -1; 1, 0].charpoly.roots = {Complex.I, -Complex.I}
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] core route of eigenvalues: selected
-/
#guard_msgs in
#cas [eigenvalues] !![0, -1; 1, 0]

/--
info: #cas [eigenvalues]
Domain: ℚ^(2×2)
Input (matrix): !![1, 2; -2, 1]
Output (eigenvalues with multiplicity): [1 + 2i, 1 - 2i]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [eigenvalues] !![1, 2; -2, 1]

/--
info: #cas [eigenvalues]
Domain: ℚ^(3×3)
Input (matrix): !![2, 0, 0; 0, 0, -1; 0, 1, 0]
Output (eigenvalues with multiplicity): [2, i, -i]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [eigenvalues] !![2, 0, 0; 0, 0, -1; 0, 1, 0]

/--
info: #cas [eigenvalues]
Domain: ℚ^(4×4)
Input (matrix): !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]
Output (eigenvalues with multiplicity): [1/2 - √5/2, 1/2 - √5/2, 1/2 + √5/2, 1/2 + √5/2]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [eigenvalues] !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]

set_option linter.style.longLine false in
/--
info: #cas [eigenvalues]
Domain: ℚ^(3×3)
Input (matrix): !![0, 0, 2; 1, 0, 0; 0, 1, 0]
Output (eigenvalues with multiplicity): [r₁, z₁, conj z₁]; r₁ ∈ (1.25992104, 1.25992106), z₁, conj z₁ = α ± iβ, α ∈ [-0.62996054, -0.62996050], β ∈ [1.09112362, 1.09112366]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The spectrum with algebraic multiplicities
        Proposition: let r₁ := CAS.AlgRoot.real [-2, 0, 0, 1] 1.25992104 1.25992106;
        let z₁ := CAS.AlgRoot.complex [-2, 0, 0, 1] (-0.62996052) 1.09112364 2e-8;
        (r₁ ∈ Set.Ioo 1.25992104 1.25992106 ∧ r₁ ^ 3 - 2 = 0) ∧
          (z₁.re ∈ Set.Icc (-0.62996054) (-0.62996050) ∧ z₁.im ∈ Set.Icc 1.09112362 1.09112366 ∧ z₁ ^ 3 - 2 = 0) ∧
            spectrum ℂ !![0, 0, 2; 1, 0, 0; 0, 1, 0] = {↑r₁, z₁, (starRingEnd ℂ) z₁} ∧
              !![0, 0, 2; 1, 0, 0; 0, 1, 0].charpoly.roots = {↑r₁, z₁, (starRingEnd ℂ) z₁}
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] core route of eigenvalues: selected
-/
#guard_msgs in
#cas [eigenvalues] !![0, 0, 2; 1, 0, 0; 0, 1, 0]

set_option linter.style.longLine false in
/--
info: #cas [eigenvalues]
Domain: ℚ^(9×9)
Input (matrix): !![2, 1, 0, 0, 0, 0, 0, 0, 1; 1, 3, 1, 0, 0, 0, 0, 0, 0; 0, 1, 4, 1, 0, 0, 0, 0, 0; 0, 0, 1, 5, 1, 0, 0, 0, 0; 0, 0, 0, 1, 6, 1, 0, 0, 0; 0, 0, 0, 0, 1, 7, 1, 0, 0; 0, 0, 0, 0, 0, 1, 8, 1, 0; 0, 0, 0, 0, 0, 0, 1, 9, 1; 1, 0, 0, 0, 0, 0, 0, 1, 10]
Output (eigenvalues with multiplicity): [r₁, r₂, r₃, r₄, r₅, r₆, r₇, r₈, r₉]; r₁ ∈ (1.18252751, 1.18252753), r₂ ∈ (2.74970782, 2.74970784), r₃ ∈ (3.94754298, 3.94754300), r₄ ∈ (4.99197855, 4.99197857), r₅ ∈ (6.00191022, 6.00191024), r₆ ∈ (7.00511301, 7.00511303), r₇ ∈ (8.05368598, 8.05368600), r₈ ∈ (9.25004520, 9.25004522), r₉ ∈ (10.81748864, 10.81748866)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [eigenvalues] !![2, 1, 0, 0, 0, 0, 0, 0, 1; 1, 3, 1, 0, 0, 0, 0, 0, 0; 0, 1, 4, 1, 0, 0, 0, 0, 0;
  0, 0, 1, 5, 1, 0, 0, 0, 0; 0, 0, 0, 1, 6, 1, 0, 0, 0; 0, 0, 0, 0, 1, 7, 1, 0, 0;
  0, 0, 0, 0, 0, 1, 8, 1, 0; 0, 0, 0, 0, 0, 0, 1, 9, 1; 1, 0, 0, 0, 0, 0, 0, 1, 10]

set_option linter.style.longLine false in
/--
info: #cas [eigenvectors]
Domain: ℚ^(2×2)
Input (matrix): !![4, 1; 2, 3]
Output (eigenvalue ↦ basis of its eigenspace): [2 ↦ [![-1/2, 1]], 5 ↦ [![1, 1]]]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Characteristic polynomial factored over ℚ, eigenspaces
        Proposition: ((∀ (i : Fin (Nat.succ 0)), (!![4, 1; 2, 3] - 2 • 1).mulVec (![![-(1 / 2), 1]] i) = 0) ∧
            LinearIndependent ℚ ![![-(1 / 2), 1]] ∧
              ∀ (x : Fin 2 → ℚ), (!![4, 1; 2, 3] - 2 • 1).mulVec x = 0 → ∃ c, x = ∑ i, c i • ![![-(1 / 2), 1]] i) ∧
          ((∀ (i : Fin (Nat.succ 0)), (!![4, 1; 2, 3] - 5 • 1).mulVec (![![1, 1]] i) = 0) ∧
              LinearIndependent ℚ ![![1, 1]] ∧
                ∀ (x : Fin 2 → ℚ), (!![4, 1; 2, 3] - 5 • 1).mulVec x = 0 → ∃ c, x = ∑ i, c i • ![![1, 1]] i) ∧
            !![4, 1; 2, 3].charpoly = (Polynomial.X - 2) * (Polynomial.X - 5)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] core route of eigenvectors: selected
-/
#guard_msgs in
#cas [eigenvectors] !![4, 1; 2, 3]

/--
info: #cas [eigenvectors]
Domain: ℚ^(2×2)
Input (matrix): !![1, 1; 0, 1]
Output (eigenvalue ↦ basis of its eigenspace): [1 ↦ [![1, 0]]]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [eigenvectors] !![1, 1; 0, 1]

-- `X ^ 2 - X - 1` remains after the rational roots: the eigenvectors are polynomials in a root `α`,
-- and one statement covers both roots. They are real by the discriminant, so the statement is over
-- `ℝ` and begins with the theorem that `X ^ 2 - X - 1` splits over `ℝ`.
set_option linter.style.longLine false in
/--
info: #cas [eigenvectors]
Domain: ℚ^(2×2)
Input (matrix): !![1, 1; 1, 0]
Output (eigenvalue ↦ basis of its eigenspace): [α ↦ [![α, 1]]] for each α ∈ ℝ with α^2 - α - 1 = 0

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Characteristic polynomial factored over ℚ, eigenspaces
        Proposition: ((Polynomial.map (algebraMap ℚ ℝ) (Polynomial.X ^ 2 - Polynomial.X - 1)).Splits ∧
            ∀ (α : ℝ),
              (Polynomial.aeval α) (Polynomial.X ^ 2 - Polynomial.X - 1) = 0 →
                (∀ (i : Fin 1), (!![1, 1; 1, 0] - α • 1).mulVec (![![α, 1]] i) = 0) ∧
                  LinearIndependent ℝ ![![α, 1]] ∧
                    ∀ (x : Fin 2 → ℝ), (!![1, 1; 1, 0] - α • 1).mulVec x = 0 → ∃ c, x = ∑ i, c i • ![![α, 1]] i) ∧
          !![1, 1; 1, 0].charpoly = Polynomial.X ^ 2 - Polynomial.X - 1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] core route of eigenvectors: selected
-/
#guard_msgs in
#cas [eigenvectors] !![1, 1; 1, 0]

-- A root `α` of `X ^ 2 - X - 1` with an eigenspace of dimension two: the factor appears twice in
-- the characteristic polynomial, and the elimination leaves two free columns.
set_option linter.style.longLine false in
/--
info: #cas [eigenvectors]
Domain: ℚ^(4×4)
Input (matrix): !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0]
Output (eigenvalue ↦ basis of its eigenspace): [α ↦ [![α, 1, 0, 0], ![0, 0, α, 1]]] for each α ∈ ℝ with α^2 - α - 1 = 0

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Characteristic polynomial factored over ℚ, eigenspaces
        Proposition: ((Polynomial.map (algebraMap ℚ ℝ) (Polynomial.X ^ 2 - Polynomial.X - 1)).Splits ∧
            ∀ (α : ℝ),
              (Polynomial.aeval α) (Polynomial.X ^ 2 - Polynomial.X - 1) = 0 →
                (∀ (i : Fin 2),
                    (!![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0] - α • 1).mulVec
                        (![![α, 1, 0, 0], ![0, 0, α, 1]] i) =
                      0) ∧
                  LinearIndependent ℝ ![![α, 1, 0, 0], ![0, 0, α, 1]] ∧
                    ∀ (x : Fin 4 → ℝ),
                      (!![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0] - α • 1).mulVec x = 0 →
                        ∃ c, x = ∑ i, c i • ![![α, 1, 0, 0], ![0, 0, α, 1]] i) ∧
          !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0].charpoly = (Polynomial.X ^ 2 - Polynomial.X - 1) ^ 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] core route of eigenvectors: selected
-/
#guard_msgs in
#cas [eigenvectors] !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0]

-- The cubic `X ^ 3 - 3 * X + 1` has three real roots. Their enclosures in disjoint rational
-- intervals show it, so the statement is over `ℝ`, with the theorem that the cubic splits over `ℝ`.
set_option linter.style.longLine false in
/--
info: #cas [eigenvectors]
Domain: ℚ^(3×3)
Input (matrix): !![0, 0, -1; 1, 0, 3; 0, 1, 0]
Output (eigenvalue ↦ basis of its eigenspace): [α ↦ [![α^2 - 3, α, 1]]] for each α ∈ ℝ with α^3 - 3*α + 1 = 0

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Characteristic polynomial factored over ℚ, eigenspaces
        Proposition: ((Polynomial.map (algebraMap ℚ ℝ) (Polynomial.X ^ 3 - 3 * Polynomial.X + 1)).Splits ∧
            ∀ (α : ℝ),
              (Polynomial.aeval α) (Polynomial.X ^ 3 - 3 * Polynomial.X + 1) = 0 →
                (∀ (i : Fin 1), (!![0, 0, -1; 1, 0, 3; 0, 1, 0] - α • 1).mulVec (![![α ^ 2 - 3, α, 1]] i) = 0) ∧
                  LinearIndependent ℝ ![![α ^ 2 - 3, α, 1]] ∧
                    ∀ (x : Fin 3 → ℝ),
                      (!![0, 0, -1; 1, 0, 3; 0, 1, 0] - α • 1).mulVec x = 0 →
                        ∃ c, x = ∑ i, c i • ![![α ^ 2 - 3, α, 1]] i) ∧
          !![0, 0, -1; 1, 0, 3; 0, 1, 0].charpoly = Polynomial.X ^ 3 - 3 * Polynomial.X + 1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] core route of eigenvectors: selected
-/
#guard_msgs in
#cas [eigenvectors] !![0, 0, -1; 1, 0, 3; 0, 1, 0]

/-- info: 'CAS.Analysis.Matrix.eigenspace_basis' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CAS.Analysis.Matrix.eigenspace_basis

-- A rational eigenvalue, with its statement over `ℚ`, and the two roots of `X ^ 2 - X - 1`.
set_option linter.style.longLine false in
/--
info: #cas [eigenvectors]
Domain: ℚ^(3×3)
Input (matrix): !![2, 0, 0; 0, 1, 1; 0, 1, 0]
Output (eigenvalue ↦ basis of its eigenspace): [2 ↦ [![1, 0, 0]], α ↦ [![0, α, 1]]] for each α ∈ ℝ with α^2 - α - 1 = 0

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Characteristic polynomial factored over ℚ, eigenspaces
        Proposition: ((∀ (i : Fin (Nat.succ 0)), (!![2, 0, 0; 0, 1, 1; 0, 1, 0] - 2 • 1).mulVec (![![1, 0, 0]] i) = 0) ∧
            LinearIndependent ℚ ![![1, 0, 0]] ∧
              ∀ (x : Fin 3 → ℚ),
                (!![2, 0, 0; 0, 1, 1; 0, 1, 0] - 2 • 1).mulVec x = 0 → ∃ c, x = ∑ i, c i • ![![1, 0, 0]] i) ∧
          ((Polynomial.map (algebraMap ℚ ℝ) (Polynomial.X ^ 2 - Polynomial.X - 1)).Splits ∧
              ∀ (α : ℝ),
                (Polynomial.aeval α) (Polynomial.X ^ 2 - Polynomial.X - 1) = 0 →
                  (∀ (i : Fin 1), (!![2, 0, 0; 0, 1, 1; 0, 1, 0] - α • 1).mulVec (![![0, α, 1]] i) = 0) ∧
                    LinearIndependent ℝ ![![0, α, 1]] ∧
                      ∀ (x : Fin 3 → ℝ),
                        (!![2, 0, 0; 0, 1, 1; 0, 1, 0] - α • 1).mulVec x = 0 → ∃ c, x = ∑ i, c i • ![![0, α, 1]] i) ∧
            !![2, 0, 0; 0, 1, 1; 0, 1, 0].charpoly = (Polynomial.X - 2) * (Polynomial.X ^ 2 - Polynomial.X - 1)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] core route of eigenvectors: selected
-/
#guard_msgs in
#cas [eigenvectors] !![2, 0, 0; 0, 1, 1; 0, 1, 0]

-- The cubic `X ^ 3 - 2` has two complex roots, so the statement is over `ℂ`.
/--
info: #cas [eigenvectors]
Domain: ℚ^(3×3)
Input (matrix): !![0, 0, 2; 1, 0, 0; 0, 1, 0]
Output (eigenvalue ↦ basis of its eigenspace): [α ↦ [![α^2, α, 1]]] for each α ∈ ℂ with α^3 - 2 = 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [eigenvectors] !![0, 0, 2; 1, 0, 0; 0, 1, 0]

-- Without Hex the characteristic polynomial `(X ^ 2 - 2) * (X ^ 2 - 3)` stays the one squarefree
-- factor `X ^ 4 - 5 * X ^ 2 + 6`. The elimination over `ℚ[X]/(X ^ 4 - 5 * X ^ 2 + 6)` meets a
-- pivot that is not a unit, splits the factor by a gcd, and proves a statement for each part.
set_option linter.style.longLine false in
/--
info: #cas [eigenvectors]
Domain: ℚ^(4×4)
Input (matrix): !![0, 2, 0, 0; 1, 0, 0, 0; 0, 0, 0, 3; 0, 0, 1, 0]
Output (eigenvalue ↦ basis of its eigenspace): [α₁ ↦ [![α₁, 1, 0, 0]], α₂ ↦ [![0, 0, α₂, 1]]] for each α₁ ∈ ℝ with α₁^2 - 2 = 0 and each α₂ ∈ ℝ with α₂^2 - 3 = 0

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Characteristic polynomial factored over ℚ, eigenspaces
        Proposition: ((Polynomial.map (algebraMap ℚ ℝ) (Polynomial.X ^ 2 - 2)).Splits ∧
            ∀ (α : ℝ),
              (Polynomial.aeval α) (Polynomial.X ^ 2 - 2) = 0 →
                (∀ (i : Fin 1),
                    (!![0, 2, 0, 0; 1, 0, 0, 0; 0, 0, 0, 3; 0, 0, 1, 0] - α • 1).mulVec (![![α, 1, 0, 0]] i) = 0) ∧
                  LinearIndependent ℝ ![![α, 1, 0, 0]] ∧
                    ∀ (x : Fin 4 → ℝ),
                      (!![0, 2, 0, 0; 1, 0, 0, 0; 0, 0, 0, 3; 0, 0, 1, 0] - α • 1).mulVec x = 0 →
                        ∃ c, x = ∑ i, c i • ![![α, 1, 0, 0]] i) ∧
          ((Polynomial.map (algebraMap ℚ ℝ) (Polynomial.X ^ 2 - 3)).Splits ∧
              ∀ (α : ℝ),
                (Polynomial.aeval α) (Polynomial.X ^ 2 - 3) = 0 →
                  (∀ (i : Fin 1),
                      (!![0, 2, 0, 0; 1, 0, 0, 0; 0, 0, 0, 3; 0, 0, 1, 0] - α • 1).mulVec (![![0, 0, α, 1]] i) = 0) ∧
                    LinearIndependent ℝ ![![0, 0, α, 1]] ∧
                      ∀ (x : Fin 4 → ℝ),
                        (!![0, 2, 0, 0; 1, 0, 0, 0; 0, 0, 0, 3; 0, 0, 1, 0] - α • 1).mulVec x = 0 →
                          ∃ c, x = ∑ i, c i • ![![0, 0, α, 1]] i) ∧
            !![0, 2, 0, 0; 1, 0, 0, 0; 0, 0, 0, 3; 0, 0, 1, 0].charpoly =
              (Polynomial.X ^ 2 - 2) * (Polynomial.X ^ 2 - 3)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] core route of eigenvectors: selected
-/
#guard_msgs in
#cas [eigenvectors] !![0, 2, 0, 0; 1, 0, 0, 0; 0, 0, 0, 3; 0, 0, 1, 0]

-- Regressions
/--
info: #cas [eigenvalues]
Domain: ℚ^(1×1)
Input (matrix): !![100000001]
Output (eigenvalues with multiplicity): [100000001]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [eigenvalues] !![100000001]

set_option linter.style.longLine false in
/--
info: #cas [eigenvectors]
Domain: ℚ^(2×2)
Input (matrix): !![2, 0; 0, 2]
Output (eigenvalue ↦ basis of its eigenspace): [2 ↦ [![1, 0], ![0, 1]]]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Characteristic polynomial factored over ℚ, eigenspaces
        Proposition: ((∀ (i : Fin (Nat.succ 1)), (!![2, 0; 0, 2] - 2 • 1).mulVec (![![1, 0], ![0, 1]] i) = 0) ∧
            LinearIndependent ℚ ![![1, 0], ![0, 1]] ∧
              ∀ (x : Fin 2 → ℚ), (!![2, 0; 0, 2] - 2 • 1).mulVec x = 0 → ∃ c, x = ∑ i, c i • ![![1, 0], ![0, 1]] i) ∧
          !![2, 0; 0, 2].charpoly = (Polynomial.X - 2) ^ 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] core route of eigenvectors: selected
-/
#guard_msgs in
#cas [eigenvectors] !![2, 0; 0, 2]

section

open CAS.Command.LinearAlgebra
open CAS.Analysis.Matrix (EigFactor)

-- `eigenbases` when the elimination splits off parts of degree one. For `X ^ 2 - 3 X + 2` of
-- multiplicity two and a matrix with the eigenvalues `1` and `2`, each of multiplicity two, it
-- gives no basis and these two roots, each with multiplicity two.
#guard
  match eigenbases #[#[1, 0, 0, 0], #[0, 1, 0, 0], #[0, 0, 2, 0], #[0, 0, 0, 2]] 3
      (#[2, -3, 1], 2) with
  | .ok (bases, roots) => bases.isEmpty && roots == [(1, 2), (2, 2)]
  | .error _ => false

-- For `(X - 1) (X ^ 2 - 2)` of multiplicity two it gives the root `1` with multiplicity two and a
-- basis of two vectors for the roots of `X ^ 2 - 2`, also with multiplicity two.
#guard
  match eigenbases #[#[1, 0, 0, 0, 0, 0], #[0, 1, 0, 0, 0, 0], #[0, 0, 0, 2, 0, 0],
      #[0, 0, 1, 0, 0, 0], #[0, 0, 0, 0, 0, 2], #[0, 0, 0, 0, 1, 0]] 4 (#[2, -2, -1, 1], 2) with
  | .ok (bases, roots) =>
    bases.map (fun b ↦ (b.factor, b.multiplicity, b.basis.toList.map (polyVectorText "α"))) ==
        [((#[-2, 0, 1] : Array ℚ), 2, ["![0, 0, α, 1, 0, 0]", "![0, 0, 0, 0, α, 1]"])] &&
      roots == [(1, 2)]
  | .error _ => false

-- `mergeRoots` adds the multiplicities of a root in both lists.
#guard mergeRoots [(1, 1), (3, 2)] [(3, 1), (2, 2)] == [(1, 1), (2, 2), (3, 3)]

-- `eigenbasisOf` accepts the elimination of `A - X I` modulo `X ^ 2 - X - 1` for
-- `A = !![1, 1; 1, 0]`. It rejects it for `A`, `R` or `E` of the wrong size, and for pivot
-- columns that are too many, out of range, decreasing or repeated.
#guard
  let A : QMatrix := #[#[1, 1], #[1, 0]]
  let q : Array ℚ := #[-1, -1, 1]
  match eliminateModulo q (shiftedMatrix A) with
  | .split _ => false
  | .reduced R E pivots => (eigenbasisOf A q 1 R E pivots).isOk

#guard
  let A : QMatrix := #[#[1, 1], #[1, 0]]
  let q : Array ℚ := #[-1, -1, 1]
  match eliminateModulo q (shiftedMatrix A) with
  | .split _ => false
  | .reduced R E pivots =>
    [eigenbasisOf #[#[1, 1], #[1]] q 1 R E pivots,
      eigenbasisOf A q 1 (R.set! 0 #[#[1]]) E pivots,
      eigenbasisOf A q 1 R E.pop pivots].all
      (· matches .error "the elimination has the wrong dimensions")

#guard
  let A : QMatrix := #[#[1, 1], #[1, 0]]
  let q : Array ℚ := #[-1, -1, 1]
  match eliminateModulo q (shiftedMatrix A) with
  | .split _ => false
  | .reduced R E _ =>
    [#[0, 1, 1], #[2], #[1, 0], #[0, 0]].all fun pivots ↦ eigenbasisOf A q 1 R E pivots matches
      .error "the pivot columns are not increasing columns of the matrix"

-- `realCheck` accepts two certificates that the roots of `X ^ 2 - X - 1` are real: the roots
-- `1/2 ± √(5/4)`, and enclosures of the roots in `(-1, 0)` and `(1, 2)`.
#guard (EigFactor.char (.realPair (1/2) 1 (5/4))).realCheck [-1, -1, 1]
#guard (EigFactor.enclosed [-1, -1, 1] ⟨[(-1, 0), (1, 2)], []⟩).realCheck [-1, -1, 1]

-- It rejects wrong coefficients, a nonmonic polynomial with the same roots, a negative or zero
-- discriminant, complex roots, and enclosures of a nonmonic polynomial or with a root missing.
#guard !(EigFactor.char (.realPair (1/2) 1 (5/4))).realCheck [-1, 1, 1]
#guard !(EigFactor.char (.realPair (1/2) 1 (5/4))).realCheck [-2, -2, 2]
#guard !(EigFactor.char (.realPair 0 1 (-1))).realCheck [1, 0, 1]
#guard !(EigFactor.char (.realPair 0 1 0)).realCheck [0, 0, 1]
#guard !(EigFactor.char (.pair 0 1 1)).realCheck [1, 0, 1]
#guard !(EigFactor.enclosed [-2, -2, 2] ⟨[(-1, 0), (1, 2)], []⟩).realCheck [-2, -2, 2]
#guard !(EigFactor.enclosed [-1, -1, 1] ⟨[(1, 2)], []⟩).realCheck [-1, -1, 1]

end

/--
info: #cas [det]
Domain: ℚ^(1×1)
Input (matrix): !![0]
Output (determinant): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [det] !![0]

/--
info: #cas [inverse]
Domain: ℚ^(1×1)
Input (matrix): !![5]
Output (inverse): !![1/5]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [inverse] !![5]

/--
info: #cas [rowReduce]
Domain: ℚ^(1×3)
Input (matrix): !![1, 2, 3]
Output (reduced row echelon form, pivot columns [0]): !![1, 2, 3]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [rowReduce] !![1, 2, 3]

/--
info: #cas [nullSpace]
Domain: ℚ^(3×1)
Input (matrix): !![1; 2; 3]
Output (basis of the null space, dimension 0): [] (only the zero vector)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nullSpace] !![1; 2; 3]

/--
info: #cas [characteristicPolynomial]
Domain: ℚ^(3×3)
Input (matrix): !![1, 2, 3; 4, 5, 6; 7, 8, 10]
Output (det (x I - A)): x^3 - 16*x^2 - 12*x + 3

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [characteristicPolynomial] !![1, 2, 3; 4, 5, 6; 7, 8, 10]


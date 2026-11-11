/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Linear algebra

The compiled examples of the docstrings of the LinearAlgebra family: determinants, products,
transposes, traces, inverses and powers of matrices with rational entries, row reduction, rank,
null spaces and linear systems, characteristic polynomials, eigenvalues and eigenvectors,
Rayleigh bounds and positive definiteness. Each section pins the report lines that a docstring
shows and proves its theorem, and checks the axioms of that proof.
-/

@[expose] public section

namespace CAS.Examples.Reference.LinearAlgebra

set_option linter.hashCommand false

/-! ## det -/

/--
Output (determinant): -3
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [det] !![1, 2, 3; 4, 5, 6; 7, 8, 10]

/--
Output (determinant): 4
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [det] !![2, -1, 0, 0, 1; -1, 2, -1, 0, 0; 0, -1, 2, -1, 0; 0, 0, -1, 2, -1; 1, 0, 0, -1, 2]

/--
Output (determinant): -1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [det] !![1/2, 1; 3, 4]

theorem det_three : Matrix.det !![(1 : ℚ), 2, 3; 4, 5, 6; 7, 8, 10] = -3 := by
  cas

/--
info: 'CAS.Examples.Reference.LinearAlgebra.det_three' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms det_three

/--
det: the matrix must be square
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [det] !![1, 2, 3; 4, 5, 6]

/--
expected a rational number, such as -3/2, 0.25 or 1/10^15
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [det] !![x, 1; 1, 1]

/-! ## dot -/

/--
Output (product): !![2, 1; 4, 3]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [dot] (!![1, 2; 3, 4], !![0, 1; 1, 0])

/--
Output (product): ![6, 15]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [dot] (!![1, 2, 3; 4, 5, 6], ![1, 1, 1])

theorem dot_swap : !![(1 : ℚ), 2; 3, 4] * !![0, 1; 1, 0] = !![2, 1; 4, 3] := by
  cas

/--
info: 'CAS.Examples.Reference.LinearAlgebra.dot_swap' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dot_swap

/--
dot: the sizes do not match
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [dot] (!![1, 2; 3, 4], ![1, 2, 3])

/--
expected a matrix `!![a, b; c, d]` or `[[a, b], [c, d]]`
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [dot] (![1, 2], ![3, 4])

/-! ## transpose -/

/--
Output (transpose): !![1, 4; 2, 5; 3, 6]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [transpose] !![1, 2, 3; 4, 5, 6]

/--
Output (transpose): !![1; 2; 3]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [transpose] !![1, 2, 3]

theorem transpose_two : !![(1 : ℚ), 2; 3, 4].transpose = !![1, 3; 2, 4] := by
  cas

/--
info: 'CAS.Examples.Reference.LinearAlgebra.transpose_two' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms transpose_two

/--
the rows of the matrix have different lengths
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [transpose] !![1, 2; 3]

/-! ## trace -/

/--
Output (trace): 5
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [trace] !![1, 2; 3, 4]

/--
Output (trace): 5/6
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [trace] !![1/2, 7; 0, 1/3]

theorem trace_two : Matrix.trace !![(1 : ℚ), 2; 3, 4] = 5 := by
  cas

/--
info: 'CAS.Examples.Reference.LinearAlgebra.trace_two' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms trace_two

/--
trace: the matrix must be square
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [trace] !![1, 2, 3; 4, 5, 6]

/-! ## inverse -/

/--
Output (inverse): !![-2, 1; 3/2, -1/2]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [inverse] !![1, 2; 3, 4]

/--
Output (inverse): !![-24, 18, 5; 20, -15, -4; -5, 4, 1]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [inverse] !![1, 2, 3; 0, 1, 4; 5, 6, 0]

/--
Output (no inverse): the matrix is singular (determinant 0); Mathlib's A⁻¹ is 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [inverse] !![1, 2; 2, 4]

theorem inverse_two : (!![(1 : ℚ), 2; 3, 4])⁻¹ = !![-2, 1; 3 / 2, -1 / 2] := by
  cas

/--
info: 'CAS.Examples.Reference.LinearAlgebra.inverse_two' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms inverse_two

/--
inverse: the matrix must be square
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [inverse] !![1, 2, 3; 4, 5, 6]

/-! ## matrixPower -/

/--
Output (power): !![89, 55; 55, 34]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [matrixPower 10] !![1, 1; 1, 0]

/--
Output (power): !![1/8, 3/4; 0, 1/8]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [matrixPower 3] !![1/2, 1; 0, 1/2]

theorem fibonacci_matrix : !![(1 : ℚ), 1; 1, 0] ^ 10 = !![89, 55; 55, 34] := by
  decide +kernel

/--
info: 'CAS.Examples.Reference.LinearAlgebra.fibonacci_matrix' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fibonacci_matrix

/--
matrixPower 1001: the power is decided by kernel evaluation, up to exponent 1000
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [matrixPower 1001] !![1, 1; 1, 0]

/-! ## matrixRank -/

/--
Output (rank): 2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [matrixRank] !![1, 2, 3; 4, 5, 6; 7, 8, 9]

/--
Output (rank): 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [matrixRank] !![1, 2, 3, 4; 2, 4, 6, 8]

/--
Output (rank): 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [matrixRank] !![0, 0; 0, 0]

theorem rank_three : Matrix.rank !![(1 : ℚ), 2, 3; 4, 5, 6; 7, 8, 9] = 2 := by
  cas

/--
info: 'CAS.Examples.Reference.LinearAlgebra.rank_three' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rank_three

/--
expected a matrix `!![a, b; c, d]` or `[[a, b], [c, d]]`
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [matrixRank] ![1, 2, 3]

/-! ## nullSpace -/

/--
Output (basis of the null space, dimension 2): [![-2, 1, 0], ![-3, 0, 1]]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [nullSpace] !![1, 2, 3; 2, 4, 6]

/--
Output (basis of the null space, dimension 0): [] (only the zero vector)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [nullSpace] !![1, 2; 3, 4]

theorem nullSpace_vector : !![(1 : ℚ), 2, 3; 2, 4, 6].mulVec ![-2, 1, 0] = 0 := by
  cas

/--
info: 'CAS.Examples.Reference.LinearAlgebra.nullSpace_vector' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms nullSpace_vector

/--
expected a matrix `!![a, b; c, d]` or `[[a, b], [c, d]]`
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [nullSpace] (!![1, 2; 3, 4], ![0, 0])

/-! ## rowReduce -/

/--
Output (reduced row echelon form, pivot columns [0, 1]): !![1, 0, -1; 0, 1, 2; 0, 0, 0]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [rowReduce] !![1, 2, 3; 4, 5, 6; 7, 8, 9]

/--
Output (reduced row echelon form, pivot columns [0, 1]):
!![1, 0, -1, 1/2; 0, 1, 2, 1/2; 0, 0, 0, 0]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [rowReduce] !![0, 2, 4, 1; 1, 1, 1, 1; 2, 4, 6, 3]

theorem rowReduce_certificate :
    !![(-(5 / 3) : ℚ), 2 / 3, 0; 4 / 3, -(1 / 3), 0; 1, -2, 1] * !![1, 2, 3; 4, 5, 6; 7, 8, 9] =
      !![1, 0, -1; 0, 1, 2; 0, 0, 0] := by
  decide +kernel

/--
info: 'CAS.Examples.Reference.LinearAlgebra.rowReduce_certificate' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rowReduce_certificate

/--
expected a matrix `!![a, b; c, d]` or `[[a, b], [c, d]]`
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [rowReduce] (!![1, 2; 3, 4], ![5, 6])

/-! ## linearSolve -/

/--
Output (all solutions): ![-4, 9/2]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [linearSolve] (!![1, 2; 3, 4], ![5, 6])

/--
Output (all solutions): ![1, 0, 0] + span of [![-2, 1, 0], ![-3, 0, 1]]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [linearSolve] (!![1, 2, 3; 2, 4, 6], ![1, 2])

/--
Output (all solutions): no solution
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [linearSolve] (!![1, 2, 3; 2, 4, 6], ![1, 3])

theorem linearSolve_check : !![(1 : ℚ), 2; 3, 4].mulVec ![-4, 9 / 2] = ![5, 6] := by
  cas

/--
info: 'CAS.Examples.Reference.LinearAlgebra.linearSolve_check' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms linearSolve_check

/--
linearSolve: the right side has 3 entries, the matrix 2 rows
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [linearSolve] (!![1, 2; 3, 4], ![5, 6, 7])

/--
linearSolve: expected a pair `(A, b)`
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [linearSolve] !![1, 2; 3, 4]

/-! ## characteristicPolynomial -/

/--
Output (det (x I - A)): x^2 - 5*x - 2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [characteristicPolynomial] !![1, 2; 3, 4]

/--
Output (det (x I - A)): x^4 - 8*x^3 + 21*x^2 - 20*x + 5
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [characteristicPolynomial] !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2]

theorem charpoly_two :
    Matrix.charpoly !![(1 : ℚ), 2; 3, 4] = Polynomial.X ^ 2 - 5 * Polynomial.X - 2 := by
  cas

/--
info: 'CAS.Examples.Reference.LinearAlgebra.charpoly_two' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms charpoly_two

/--
characteristicPolynomial: the matrix must be square
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [characteristicPolynomial] !![1, 2, 3; 4, 5, 6]

/-! ## eigenvalues -/

/--
Output (eigenvalues with multiplicity): [1, 2, 11]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [eigenvalues] !![2, 0, 0; 0, 3, 4; 0, 4, 9]

/--
Output (eigenvalues with multiplicity): [1/2 - √5/2, 1/2 + √5/2]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [eigenvalues] !![0, 1; 1, 1]

/--
Output (eigenvalues with multiplicity): [r₁, z₁, conj z₁]; r₁ ∈ (1.25992104, 1.25992106), z₁,
conj z₁ = α ± iβ, α ∈ [-0.62996054, -0.62996050], β ∈ [1.09112362, 1.09112366]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [eigenvalues] !![0, 0, 2; 1, 0, 0; 0, 1, 0]

theorem golden_ratio_mem_spectrum
    (h : spectrum ℝ !![(0 : ℝ), 1; 1, 1] = {1 / 2 - 1 / 2 * √5, 1 / 2 + 1 / 2 * √5}) :
    1 / 2 + 1 / 2 * √5 ∈ spectrum ℝ !![(0 : ℝ), 1; 1, 1] := by
  rw [h]
  exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

/--
info: 'CAS.Examples.Reference.LinearAlgebra.golden_ratio_mem_spectrum' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms golden_ratio_mem_spectrum

/--
eigenvalues: the matrix must be square
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [eigenvalues] !![1, 2, 3; 4, 5, 6]

/-! ## eigenvectors -/

/--
Output (eigenvalue ↦ basis of its eigenspace): [2 ↦ [![-1/2, 1]], 5 ↦ [![1, 1]]]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [eigenvectors] !![4, 1; 2, 3]

/--
Output (eigenvalue ↦ basis of its eigenspace): [1 ↦ [![1, 0]]]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [eigenvectors] !![1, 1; 0, 1]

/--
Output (eigenvalue ↦ basis of its eigenspace): [α ↦ [![α, 1]]] for each α ∈ ℝ with α^2 - α - 1 = 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [eigenvectors] !![1, 1; 1, 0]

/--
Output (eigenvalue ↦ basis of its eigenspace): [α ↦ [![α, 1]]] for each α ∈ ℂ with α^2 + 1 = 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [eigenvectors] !![0, -1; 1, 0]

theorem eigenvector_five : !![(4 : ℚ), 1; 2, 3].mulVec ![1, 1] = (5 : ℚ) • ![1, 1] := by
  cas

/--
info: 'CAS.Examples.Reference.LinearAlgebra.eigenvector_five' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eigenvector_five

/--
eigenvectors: the matrix must be square
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [eigenvectors] !![1, 2, 3; 4, 5, 6]

/-! ## eigenvalueBounds -/

/--
Output (Rayleigh bounds): 1.000000 ≤ λ_min, λ_max ≤ 3.000000
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [eigenvalueBounds] !![2, 1; 1, 2]

/--
Output (Rayleigh bounds): 1.267949 ≤ λ_min, λ_max ≤ 4.732051
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [eigenvalueBounds] !![4, 1, 0; 1, 3, 1; 0, 1, 2]

/--
Output (Rayleigh bounds): 1.267 ≤ λ_min, λ_max ≤ 4.733
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (digits := 3) [eigenvalueBounds] !![4, 1, 0; 1, 3, 1; 0, 1, 2]

theorem rayleigh_lower
    (h : ∀ x : Fin 2 → ℝ,
      1.000000 * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, !![(2 : ℝ), 1; 1, 2] i j * x i * x j ∧
        ∑ i, ∑ j, !![(2 : ℝ), 1; 1, 2] i j * x i * x j ≤ 3.000000 * ∑ i, x i ^ 2)
    (x : Fin 2 → ℝ) :
    ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, !![(2 : ℝ), 1; 1, 2] i j * x i * x j := by
  have e : (1.000000 : ℝ) = 1 := by norm_num
  have h₁ := (h x).1
  rw [e, one_mul] at h₁
  exact h₁

/--
info: 'CAS.Examples.Reference.LinearAlgebra.rayleigh_lower' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rayleigh_lower

/--
eigenvalueBounds needs a symmetric matrix
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [eigenvalueBounds] !![1, 2; 3, 4]

/--
eigenvalueBounds accepts between 1 and 2000 digits
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (digits := 0) [eigenvalueBounds] !![2, 1; 1, 2]

/-! ## positiveDefinite -/

/--
Output (Boolean): True
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [positiveDefinite] !![2, 1; 1, 2]

/--
Output (Boolean): False (xᵀAx ≤ 0 for x = [-2, 1])
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [positiveDefinite] !![1, 2; 2, 1]

/--
Output (Boolean): False (not symmetric)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [positiveDefinite] !![1, 2; 3, 4]

theorem posDef_det_pos (h : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef) :
    0 < (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).det :=
  h.det_pos

/--
info: 'CAS.Examples.Reference.LinearAlgebra.posDef_det_pos' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms posDef_det_pos

/--
Output (Boolean): False (xᵀAx ≤ 0 for x = [-1, 1])
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [positiveDefinite] !![1, 1; 1, 1]

/--
positiveDefinite: the matrix must be square
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [positiveDefinite] !![1, 2, 3; 4, 5, 6]

end CAS.Examples.Reference.LinearAlgebra

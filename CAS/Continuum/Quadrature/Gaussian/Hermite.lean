/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.Gaussian.Algebra

/-!
# Hermite interpolation at distinct nodes

Given distinct nodes `x₁, …, xₙ` with prescribed values and slopes, the Hermite interpolant
is the polynomial of degree below `2n` taking those values and first derivatives at the
nodes (`hermiteInterpolant`, with `hermiteInterpolant_eval`,
`hermiteInterpolant_derivative_eval` and `hermiteInterpolant_natDegree_lt`). It is built from
the squared Lagrange cardinal polynomials `ℓᵢ ^ 2`, which vanish together with their
derivatives at every other node, each multiplied by an affine factor that fixes the value and
slope at `xᵢ`. The Gaussian remainder in `Remainder` is the error of this interpolant.

## References

* Josef Stoer and Roland Bulirsch, *Introduction to Numerical Analysis*, 3rd ed., Texts in Applied
  Mathematics 12, Springer, New York, 2002, <https://doi.org/10.1007/978-0-387-21738-3>. §2.1.5 for
  Hermite interpolation.
-/

@[expose] public section

namespace CAS.Continuum

open Polynomial
open scoped BigOperators

noncomputable section

/-- The `i`th summand of the Hermite interpolant, `(vᵢ + cᵢ (X - xᵢ)) ℓᵢ ^ 2` with `cᵢ`
chosen so that the derivative at `xᵢ` is the prescribed slope. -/
def hermiteTerm {n : ℕ} (nodes : Fin n → ℝ) (values slopes : Fin n → ℝ)
    (i : Fin n) : ℝ[X] :=
  let l := Lagrange.basis Finset.univ nodes i
  (C (values i) + C (slopes i - 2 * values i * l.derivative.eval (nodes i)) *
    (X - C (nodes i))) * l ^ 2

/-- The Hermite interpolant: the polynomial of degree below `2n` with prescribed values and
first derivatives at `n` distinct nodes. -/
def hermiteInterpolant {n : ℕ} (nodes : Fin n → ℝ) (values slopes : Fin n → ℝ) :
    ℝ[X] :=
  ∑ i, hermiteTerm nodes values slopes i

/-- The `i`th Hermite term takes the prescribed value at its own node. -/
theorem hermiteTerm_eval_self {n : ℕ} (nodes : Fin n → ℝ)
    (hnodes : Function.Injective nodes) (values slopes : Fin n → ℝ) (i : Fin n) :
    (hermiteTerm nodes values slopes i).eval (nodes i) = values i := by
  simp [hermiteTerm, Lagrange.eval_basis_self (Set.injOn_of_injective hnodes)
    (Finset.mem_univ i)]

/-- The `i`th Hermite term vanishes at every other node. -/
theorem hermiteTerm_eval_of_ne {n : ℕ} (nodes : Fin n → ℝ)
    (values slopes : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    (hermiteTerm nodes values slopes i).eval (nodes j) = 0 := by
  simp [hermiteTerm, Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)]

/-- The derivative of the `i`th Hermite term is the prescribed slope at its own node. -/
theorem hermiteTerm_derivative_eval_self {n : ℕ} (nodes : Fin n → ℝ)
    (hnodes : Function.Injective nodes) (values slopes : Fin n → ℝ) (i : Fin n) :
    (hermiteTerm nodes values slopes i).derivative.eval (nodes i) = slopes i := by
  simp [hermiteTerm, derivative_mul, derivative_pow,
    Lagrange.eval_basis_self (Set.injOn_of_injective hnodes) (Finset.mem_univ i)]
  ring

/-- The derivative of the `i`th Hermite term vanishes at every other node. -/
theorem hermiteTerm_derivative_eval_of_ne {n : ℕ} (nodes : Fin n → ℝ)
    (values slopes : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    (hermiteTerm nodes values slopes i).derivative.eval (nodes j) = 0 := by
  simp [hermiteTerm, derivative_mul, derivative_pow,
    Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)]

/-- The Hermite interpolant takes the prescribed value at each node. -/
theorem hermiteInterpolant_eval {n : ℕ} (nodes : Fin n → ℝ)
    (hnodes : Function.Injective nodes) (values slopes : Fin n → ℝ) (i : Fin n) :
    (hermiteInterpolant nodes values slopes).eval (nodes i) = values i := by
  rw [hermiteInterpolant, eval_finsetSum, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
    fun j _ hji ↦ hermiteTerm_eval_of_ne nodes values slopes hji]
  exact hermiteTerm_eval_self nodes hnodes values slopes i

/-- The derivative of the Hermite interpolant takes the prescribed slope at each node. -/
theorem hermiteInterpolant_derivative_eval {n : ℕ} (nodes : Fin n → ℝ)
    (hnodes : Function.Injective nodes) (values slopes : Fin n → ℝ) (i : Fin n) :
    (hermiteInterpolant nodes values slopes).derivative.eval (nodes i) = slopes i := by
  rw [hermiteInterpolant, derivative_sum, eval_finsetSum, Finset.sum_eq_single_of_mem i
    (Finset.mem_univ i) fun j _ hji ↦ hermiteTerm_derivative_eval_of_ne nodes values slopes hji]
  exact hermiteTerm_derivative_eval_self nodes hnodes values slopes i

/-- Each Hermite term has degree below `2n`: `ℓᵢ` has degree at most `n - 1` and the affine
factor has degree at most one. -/
theorem hermiteTerm_natDegree_lt {n : ℕ} (hn : 0 < n) (nodes values slopes : Fin n → ℝ)
    (i : Fin n) : (hermiteTerm nodes values slopes i).natDegree < 2 * n := by
  have hdiv (x y : ℝ) : (Lagrange.basisDivisor x y).natDegree ≤ 1 := by
    rcases eq_or_ne x y with rfl | hxy
    · rw [Lagrange.natDegree_basisDivisor_self]
      exact zero_le_one
    · rw [Lagrange.natDegree_basisDivisor_of_ne hxy]
  have hl : (Lagrange.basis Finset.univ nodes i).natDegree ≤ n - 1 := by
    unfold Lagrange.basis
    refine (natDegree_prod_le _ _).trans ((Finset.sum_le_sum fun j _ ↦ hdiv _ _).trans ?_)
    simp [Finset.card_erase_of_mem]
  refine natDegree_mul_le.trans_lt ?_
  rw [natDegree_pow]
  refine (Nat.add_le_add (?_ : _ ≤ 1) (Nat.mul_le_mul_left 2 hl)).trans_lt (by omega)
  compute_degree

/-- The Hermite interpolant at `n ≥ 1` nodes has degree below `2n`. -/
theorem hermiteInterpolant_natDegree_lt {n : ℕ} (hn : 0 < n) (nodes values slopes : Fin n → ℝ) :
    (hermiteInterpolant nodes values slopes).natDegree < 2 * n :=
  (natDegree_sum_le_of_forall_le _ _ fun i _ ↦
    Nat.le_sub_one_of_lt (hermiteTerm_natDegree_lt hn nodes values slopes i)).trans_lt
    (by omega)

end
end CAS.Continuum

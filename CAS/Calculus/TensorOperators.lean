/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.SymbolicOperators
public import CAS.ClosedForm.Expression.Polynomial.Normalization

/-!
# Symbolic tensor and differential operators

`Fin`-indexed symbolic Hessians, Jacobians, symmetric gradients, dot and Frobenius products,
row-wise tensor divergence, and componentwise vector Laplacians for the verified
expression language. Apart from the vector Laplacian, which is `closedLaplacian` applied
componentwise, every derivative entry is built from `closedPartial`, and every algebraic
combination is passed through the checked normalizer `Verified.Expr.Alg.normalize`, which
preserves evaluation. The lemmas are purely algebraic evaluation lemmas; they do not identify these
operators with analytic derivatives.

## Main definitions

* `hessian`: the `(i, j)` entry is `∂ᵢ(∂ⱼ u)`.
* `jacobian`: the `(i, j)` entry is `∂ⱼ Fᵢ`.
* `symmetricGradient`: the small-strain tensor `(∂ⱼ Fᵢ + ∂ᵢ Fⱼ)/2`.
* `dotProduct`, `frobeniusInnerProduct`: the dot product of two vectors and the Frobenius inner
  product of two square tensors.
* `tensorDivergence`: the row-wise divergence `∑ⱼ ∂ⱼ Aᵢⱼ` of continuum mechanics.
* `vectorLaplacian`: the viscous term of the Stokes and Navier–Stokes residuals.

## Main results

* `dotProduct_eval_eq_sum`, `frobeniusInnerProduct_eval_eq_sum`: the products evaluate to the
  sums of the products of the evaluated entries.
-/

@[expose] public section

namespace CAS

open scoped BigOperators

/-- Symbolic Hessian indexed by its outer and inner derivative coordinates.

The `(i, j)` entry is `∂ᵢ(∂ⱼ u)`. -/
def hessian {n : Nat} (expr : Verified.Expr (Fin n)) : Fin n → Fin n → Verified.Expr (Fin n) :=
  fun i j ↦ Verified.Expr.closedPartial i (Verified.Expr.closedPartial j expr)

/-- Function-valued symbolic Jacobian: the `(i,j)` entry is `∂ⱼ Fᵢ`. -/
def jacobian {n m : Nat} (field : Fin m → Verified.Expr (Fin n)) :
    Fin m → Fin n → Verified.Expr (Fin n) :=
  fun i j ↦ Verified.Expr.closedPartial j (field i)

/-- Symbolic symmetric gradient of a vector field.

The `(i, j)` entry is the normalized expression `(∂ⱼ Fᵢ + ∂ᵢ Fⱼ) / 2`. -/
def symmetricGradient {n : Nat} (field : Fin n → Verified.Expr (Fin n)) :
    Fin n → Fin n → Verified.Expr (Fin n) :=
  fun i j ↦
    Verified.Expr.Alg.normalize
      (((Verified.Expr.closedPartial j (field i) + Verified.Expr.closedPartial i (field j)) :
        Verified.Expr (Fin n)) / 2)

/-- Symbolic Euclidean dot product of two vector-valued expressions. -/
def dotProduct {m n : Nat} (u v : Fin m → Verified.Expr (Fin n)) :
    Verified.Expr (Fin n) :=
  Verified.Expr.Alg.normalize <|
    Verified.Expr.sum (m := m) fun i ↦ u i * v i

/-- A symbolic dot product evaluates to the sum of the component products. -/
theorem dotProduct_eval_eq_sum {m n : Nat}
    (u v : Fin m → Verified.Expr (Fin n)) (x : ℝ^n) :
    (dotProduct u v).eval x = ∑ i : Fin m, (u i).eval x * (v i).eval x := by
  rw [dotProduct, Verified.Expr.Alg.eval_normalize]
  simp [Fin.sum_univ_def]

/-- Symbolic Frobenius inner product of two square tensor-valued expressions. -/
def frobeniusInnerProduct {n : Nat}
    (A B : Fin n → Fin n → Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  Verified.Expr.Alg.normalize <|
    Verified.Expr.sumFin fun i ↦
      Verified.Expr.sumFin fun j ↦
        A i j * B i j

/-- A symbolic Frobenius inner product evaluates to the double sum of entry products. -/
theorem frobeniusInnerProduct_eval_eq_sum {n : Nat}
    (A B : Fin n → Fin n → Verified.Expr (Fin n)) (x : ℝ^n) :
    (frobeniusInnerProduct A B).eval x =
      ∑ i : Fin n, ∑ j : Fin n, (A i j).eval x * (B i j).eval x := by
  rw [frobeniusInnerProduct, Verified.Expr.Alg.eval_normalize]
  simp

/-- Symbolic row-wise divergence of a square `n × n` tensor field.

The `i`th component is `∑ⱼ ∂ⱼ Aᵢⱼ`, the divergence of a matrix field in continuum
mechanics. -/
def tensorDivergence {n : Nat} (A : Fin n → Fin n → Verified.Expr (Fin n)) :
    Fin n → Verified.Expr (Fin n) :=
  fun i ↦
    Verified.Expr.Alg.normalize <|
      Verified.Expr.sumFin fun j ↦
        Verified.Expr.closedPartial j (A i j)

/-- Componentwise symbolic vector Laplacian `Δu`.

This is the viscous term of the stationary Stokes and Navier–Stokes residuals. -/
def vectorLaplacian {n : Nat} (u : Fin n → Verified.Expr (Fin n)) : Fin n → Verified.Expr (Fin n) :=
  fun i ↦ Verified.Expr.closedLaplacian (u i)


end CAS

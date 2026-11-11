/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Notation
public import CAS.ClosedForm.Expression.Elementary -- shake: keep

/-!
# Finite symbolic sums and Taylor polynomials

`Verified.Expr.sum` and `Verified.Expr.sumFin` write a finite sum as one expression through
`Verified.Expr.addList`; the symbolic operators `Verified.Expr.closedLaplacian` and
`Verified.Expr.closedDivergence` are built from `sumFin`. `powerSeriesTrunc` and `taylorTrunc`
are the partial sums `Σ k < m, c k * z ^ k` and `Σ k < m, c k * (x - center) ^ k` with explicit
coefficient expressions, and `powerSeriesTruncFormalDeriv` and `taylorTruncFormalDeriv`
differentiate them in the series variable with the coefficients held fixed, which is not a
coordinate derivative. These are finite sums, so no convergence is involved and no remainder
bound is attached: the evaluation lemmas such as `eval_taylorTrunc` only compute their values.
-/

@[expose] public section

namespace CAS

open scoped BigOperators

namespace Verified.Expr

/-- Symbolic finite sum over an arbitrary finite range. -/
def sum {m n : Nat} (term : Fin m → Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  Verified.Expr.addList ((List.finRange m).map term)

/-- Symbolic finite sum over coordinates. -/
def sumFin {n : Nat} (term : Fin n → Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  sum (m := n) term

/-- Finite power-series truncation in the symbolic variable `z`.

`powerSeriesTrunc (m := m) z c` represents the finite partial sum `Σ k < m, c k * z^k`. It is a
finite sum, not an infinite series; convergence and remainder bounds are proved separately. -/
def powerSeriesTrunc {m n : Nat} (z : Verified.Expr (Fin n))
    (coeff : Fin m → Verified.Expr (Fin n)) :
    Verified.Expr (Fin n) :=
  sum (m := m) fun k ↦ coeff k * z ^ k.val

/-- Finite Taylor truncation around `center`.

`taylorTrunc (m := m) x center coeff` represents `Σ k < m, coeff k * (x-center)^k`.
The coefficients are explicit, so users can plug in Taylor coefficients, asymptotic coefficients,
or PDE ansatz coefficients without changing the trusted expression language. -/
def taylorTrunc {m n : Nat} (x center : Verified.Expr (Fin n))
    (coeff : Fin m → Verified.Expr (Fin n)) :
    Verified.Expr (Fin n) :=
  powerSeriesTrunc (m := m) (x - center) coeff

/-- Formal derivative of a finite power-series truncation with respect to its formal variable.

`powerSeriesTruncFormalDeriv z c` represents `Σ k < m, k*c_k*z^(k-1)`, with the coefficients
held fixed. It includes neither derivatives of the coefficient expressions nor a chain-rule
factor for `z`. To differentiate the evaluated expression with respect to a coordinate, use
`Verified.Expr.diff` on the original truncation. -/
def powerSeriesTruncFormalDeriv {m n : Nat}
    (z : Verified.Expr (Fin n)) (coeff : Fin m → Verified.Expr (Fin n)) :
    Verified.Expr (Fin n) :=
  sum (m := m) fun k ↦
    (Verified.Expr.nat k.val : Verified.Expr (Fin n)) * coeff k * z ^ (k.val - 1)

/-- Formal derivative of a finite Taylor/asymptotic truncation.

The result is `Σ k < m, k*c_k*(x-center)^(k-1)`, with the coefficients and center held fixed.
It is not a coordinate derivative when those expressions depend on the coordinate, and it does
not include the derivative of the substituted expression `x - center`. -/
def taylorTruncFormalDeriv {m n : Nat}
    (x center : Verified.Expr (Fin n)) (coeff : Fin m → Verified.Expr (Fin n)) :
    Verified.Expr (Fin n) :=
  powerSeriesTruncFormalDeriv (m := m) (x - center) coeff

/-- Evaluate the finite symbolic sum in index order; an empty index set gives zero. -/
@[simp] theorem eval_sum {m n : Nat} (x : ℝ^n) (term : Fin m → Verified.Expr (Fin n)) :
    (sum term).eval x = ((List.finRange m).map fun i ↦ (term i).eval x).sum := by
  simp [sum, Function.comp_def]

/-- A symbolic sum indexed by the coordinates evaluates to the corresponding finite sum. -/
@[simp] theorem eval_sumFin {n : Nat} (x : ℝ^n) (term : Fin n → Verified.Expr (Fin n)) :
    (sumFin term).eval x = ∑ i : Fin n, (term i).eval x := by
  rw [sumFin, eval_sum, Fin.sum_univ_def]

/-- The truncation evaluates to the first `m` terms, with indices `0, …, m - 1`.
The coefficients may themselves depend on the evaluation point. -/
@[simp] theorem eval_powerSeriesTrunc {m n : Nat} (x : ℝ^n)
    (z : Verified.Expr (Fin n)) (coeff : Fin m → Verified.Expr (Fin n)) :
    (powerSeriesTrunc z coeff).eval x =
      ((List.finRange m).map fun k ↦ (coeff k).eval x * (z.eval x) ^ k.val).sum := by
  simp [powerSeriesTrunc, eval_sum, Verified.Expr.eval]

/-- Evaluate the finite series in `x - center`. The supplied coefficients include any
factorial scaling; this identity asserts no Taylor remainder or convergence bound. -/
@[simp] theorem eval_taylorTrunc {m n : Nat} (x₀ : ℝ^n)
    (x center : Verified.Expr (Fin n)) (coeff : Fin m → Verified.Expr (Fin n)) :
    (taylorTrunc x center coeff).eval x₀ =
      ((List.finRange m).map fun k ↦
        (coeff k).eval x₀ * ((x - center : Verified.Expr (Fin n)).eval x₀) ^ k.val).sum := by
  simp [taylorTrunc, eval_powerSeriesTrunc]

/-- Evaluate formal differentiation in the series variable, holding coefficients fixed.
Natural subtraction makes the exponent at `k = 0` zero; the factor `k` kills that term.
This is not differentiation of the coefficient expressions or a chain rule for `z`. -/
@[simp] theorem eval_powerSeriesTruncFormalDeriv {m n : Nat} (x₀ : ℝ^n)
    (z : Verified.Expr (Fin n)) (coeff : Fin m → Verified.Expr (Fin n)) :
    (powerSeriesTruncFormalDeriv z coeff).eval x₀ =
      ((List.finRange m).map fun k ↦
        (k.val : ℝ) * (coeff k).eval x₀ * (z.eval x₀) ^ (k.val - 1)).sum := by
  simp [powerSeriesTruncFormalDeriv, eval_sum, Verified.Expr.eval]

/-- Evaluate formal differentiation in the shifted variable `x - center`, holding both
the coefficients and the center fixed. No derivative with respect to `x₀` is asserted. -/
@[simp] theorem eval_taylorTruncFormalDeriv {m n : Nat} (x₀ : ℝ^n)
    (x center : Verified.Expr (Fin n)) (coeff : Fin m → Verified.Expr (Fin n)) :
    (taylorTruncFormalDeriv x center coeff).eval x₀ =
      ((List.finRange m).map fun k ↦
        (k.val : ℝ) * (coeff k).eval x₀ *
          ((x - center : Verified.Expr (Fin n)).eval x₀) ^ (k.val - 1)).sum := by
  simp [taylorTruncFormalDeriv, eval_powerSeriesTruncFormalDeriv]

end Verified.Expr

end CAS

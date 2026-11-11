/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import CAS.Calculus.Euclidean
public import CAS.Calculus.SymbolicOperators

/-!
# The symbolic gradient and Mathlib's gradient

`closedGradient_eval_eq_gradient`: at a point where a checked expression is valid, the
evaluated symbolic gradient `closedGradient` is Mathlib's gradient `∇` of the evaluation. The
`i`-th coordinate of `∇ f x` is the derivative of `f` in the direction of the `i`-th basis
vector, which `fderiv_eval_eq` and `symbolicFDeriv_apply_single_eq_diff_eval` compute.
`hasGradientAt_eval` adds the differentiability, and `hasGradientAt_of_closedGradient` states it
for a function and a vector given by terms equal to the evaluations.
-/

@[expose] public section

namespace CAS

open scoped Gradient

namespace Verified.Expr

/-- At a valid point, the symbolic gradient evaluates to the analytic gradient. -/
theorem closedGradient_eval_eq_gradient {n : Nat}
    (expr : Verified.Expr (Fin n)) (x : ℝ^n) (h : expr.ValidAt x) :
    WithLp.toLp 2 (fun i : Fin n ↦ (closedGradient expr i).eval x) =
      ∇ (fun y : ℝ^n ↦ expr.eval y) x := by
  ext i
  rw [← EuclideanSpace.inner_basisFun_real (Fin n) (∇ (fun y : ℝ^n ↦ expr.eval y) x) i,
    inner_gradient_left, EuclideanSpace.basisFun_apply, fderiv_eval_eq expr x h,
    symbolicFDeriv_apply_single_eq_diff_eval expr x i]
  simp [closedGradient, closedPartial, eval_trigSimplify]

/-- At a valid point, the evaluation of a checked expression has the gradient whose coordinates
are the evaluated symbolic gradient. -/
theorem hasGradientAt_eval {n : Nat} (expr : Verified.Expr (Fin n)) (x : ℝ^n)
    (h : expr.ValidAt x) :
    HasGradientAt (fun y : ℝ^n ↦ expr.eval y)
      (WithLp.toLp 2 (fun i ↦ (closedGradient expr i).eval x)) x := by
  rw [closedGradient_eval_eq_gradient expr x h]
  exact (hasFDerivAt_eval expr x h).differentiableAt.hasGradientAt

/-- If `f` is the evaluation of `input`, the symbolic gradient of `input` is `G`, each `G i`
evaluates to `g i` at `ρ` and `input` is valid at `ρ`, then `f` has the gradient `g` at `ρ`. -/
theorem hasGradientAt_of_closedGradient {n : Nat} {input : Verified.Expr (Fin n)}
    {G : Fin n → Verified.Expr (Fin n)} (hG : ∀ i, input.closedGradient i = G i)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ∀ y : EuclideanSpace ℝ (Fin n), input.eval y = f y)
    {ρ g : Fin n → ℝ} (hg : ∀ i, (G i).eval ρ = g i) (hvalid : input.ValidAt ρ) :
    HasGradientAt f (WithLp.toLp 2 g) (WithLp.toLp 2 ρ) := by
  have key := hasGradientAt_eval input (WithLp.toLp 2 ρ) hvalid
  convert key using 1
  · exact (funext hf).symm
  · congr 1; funext i; rw [hG i]; exact (hg i).symm

end Verified.Expr

end CAS

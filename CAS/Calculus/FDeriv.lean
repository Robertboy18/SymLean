/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.Euclidean
public import CAS.Calculus.Partial

/-!
# Fréchet derivatives of checked expressions in arbitrary directions

`fderiv_eval_apply_eq_sum_closedPartial`: at a valid point, the Fréchet derivative of a
checked expression applied to a direction `v` is `∑ i, v i * (closedPartial i expr).eval x`,
obtained by expanding `v` in the coordinate basis.
-/

@[expose] public section

namespace CAS

open scoped BigOperators

namespace Verified.Expr

/-- Evaluate the Fréchet derivative of a checked closed form in an arbitrary direction. -/
theorem fderiv_eval_apply_eq_sum_closedPartial {n : Nat}
    (expr : Verified.Expr (Fin n)) (x v : ℝ^n)
    (h : expr.ValidAt x) :
    (fderiv ℝ (fun y : ℝ^n ↦ expr.eval y) x) v =
      ∑ i : Fin n, v i * (closedPartial i expr).eval x := by
  have hv : v = ∑ i : Fin n, v i • EuclideanSpace.single i (1 : ℝ) := by
    ext i
    simp [Pi.single_apply]
  rw [fderiv_eval_eq expr x h]
  nth_rw 1 [hv]
  simp [closedPartial, symbolicFDeriv_apply_single_eq_diff_eval expr x _]

end Verified.Expr

end CAS

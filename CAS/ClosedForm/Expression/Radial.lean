/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Notation
public import CAS.Expr.Decomposition
public import CAS.ClosedForm.Expression.Elementary -- shake: keep

/-!
# Radial symbolic expressions

The radius `radius3 = sqrt (x² + y² + z²)` on `ℝ^3`, with its square `radiusSq3`; `radiusSq3_eval`
and `radius3_eval` identify them with the Euclidean norm.
-/

@[expose] public section

namespace CAS

/-- The squared radius `x² + y² + z²` on `ℝ^3`. -/
def radiusSq3 : Verified.Expr (Fin 3) :=
  (Euclid3.x : Verified.Expr (Fin 3)) ^ 2 + (Euclid3.y : Verified.Expr (Fin 3)) ^ 2 +
    (Euclid3.z : Verified.Expr (Fin 3)) ^ 2

/-- The radius `sqrt (x² + y² + z²)` on `ℝ^3`. -/
def radius3 : Verified.Expr (Fin 3) :=
  .sqrt radiusSq3

/-- The three-dimensional symbolic squared radius evaluates to the squared Euclidean norm. -/
@[simp]
theorem radiusSq3_eval (p : ℝ^3) :
    radiusSq3.eval p = ‖p‖ ^ 2 := by
  simpa [radiusSq3, Verified.Expr.eval, Verified.Expr.SymVar.expr,
    Fin.sum_univ_three, add_assoc] using (EuclideanSpace.real_norm_sq_eq p).symm

/-- The three-dimensional symbolic radius evaluates to the Euclidean norm. -/
@[simp]
theorem radius3_eval (p : ℝ^3) :
    radius3.eval p = ‖p‖ := by
  simp [radius3, Real.sqrt_sq (norm_nonneg p)]

end CAS

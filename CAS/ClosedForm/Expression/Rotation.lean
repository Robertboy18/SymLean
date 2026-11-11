/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Notation
public import CAS.ClosedForm.Expression.Elementary

/-!
# The planar rotation field

`rotationField2 = (-y, x)` is the infinitesimal rotation of the plane about the origin, as a
symbolic vector field on `ℝ^2`: a field that is divergence free and whose symmetric gradient
vanishes. Neither property is proved for it; the theorem `rotationField2_validAt` only states
that both components are valid closed-form expressions at every point.
-/

@[expose] public section

namespace CAS

open Euclid2

/-- The planar rotation field `(-y, x)`. -/
def rotationField2 : Fin 2 → Verified.Expr (Fin 2) :=
  ![-(y : Verified.Expr (Fin 2)), (x : Verified.Expr (Fin 2))]

/-- Both components of the rotation field are valid at every point. -/
theorem rotationField2_validAt (p : ℝ^2) (i : Fin 2) : (rotationField2 i).ValidAt p := by
  fin_cases i <;>
    simp [Verified.Expr.ValidAt, rotationField2, Verified.Expr.SymVar.expr]

end CAS

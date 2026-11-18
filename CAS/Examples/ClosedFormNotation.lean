/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.SymbolicOperators
public import CAS.Notation

/-!
# Notation of the closed-form operators

`𝕏[i]` is the variable `i` of a checked expression, and `∂ₛ[i] f`, `∇ₛ f` and `Δₛ f` are the
closed-form partial derivative, gradient and Laplacian of `f`. The library writes these
functions out, so no module read the four notations. Each is read here once, with what it
stands for, and printed once, together with `ℝ^n`: Lean shows the functions in the same
notation.
-/

@[expose] public section

namespace CAS.Examples.ClosedFormNotation

open CAS Verified

example : (𝕏[(0 : Fin 2)] : Expr (Fin 2)) = .var 0 := rfl

example (f : Expr (Fin 2)) : ∂ₛ[(0 : Fin 2)] f = Expr.closedPartialBy (0 : Fin 2) f := rfl

example (f : Expr (Fin 2)) : ∇ₛ f = Expr.closedGradient f := rfl

example (f : Expr (Fin 2)) : Δₛ f = Expr.closedLaplacian f := rfl

/--
info: ∂ₛ[0] 𝕏[1]
∇ₛ 𝕏[1]
Δₛ 𝕏[1]
ℝ^2
-/
#guard_msgs in
open Lean Elab Term in
run_elab do
  let terms ← [← `(Expr.closedPartialBy (0 : Fin 2) (Expr.var (1 : Fin 2))),
    ← `(Expr.closedGradient (Expr.var (1 : Fin 2))),
    ← `(Expr.closedLaplacian (Expr.var (1 : Fin 2))),
    ← `(EuclideanSpace ℝ (Fin 2))].mapM fun term ↦ do
      return m!"{← elabTerm term none}"
  logInfo (MessageData.joinSep terms "\n")

end CAS.Examples.ClosedFormNotation

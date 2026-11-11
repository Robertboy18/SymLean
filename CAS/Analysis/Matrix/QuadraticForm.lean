/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Scalar upper bounds for matrix quadratic forms

A real matrix `M` has quadratic-form bound `μ`, `QuadFormLE M μ`, if `vᵀ M v ≤ μ |v|²` for
every vector `v`. The definition does not require symmetry. For symmetric matrices it is
the form of an upper eigenvalue bound used in weighted energy estimates.
-/

@[expose] public section

open Matrix
open scoped Matrix

namespace CAS.Analysis.Matrix

/-- The quadratic form of `M` is bounded above by `μ` times the squared Euclidean norm. -/
def QuadFormLE {n : Type*} [Fintype n] (M : Matrix n n ℝ) (μ : ℝ) : Prop :=
  ∀ v : n → ℝ, v ⬝ᵥ (M *ᵥ v) ≤ μ * (v ⬝ᵥ v)

end CAS.Analysis.Matrix

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Notation for Euclidean space

`ℝ^n` is notation for `EuclideanSpace ℝ (Fin n)`, the space on which symbolic expressions in
`n` variables are evaluated and differentiated.
-/

@[expose] public section

/-- Standard mathematical notation for real Euclidean `n`-space. -/
notation:arg "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

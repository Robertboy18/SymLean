/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.Passes.Factorization

/-!
# Standard symbolic passes

The four unconditional passes of the ordinary fixed-point pipeline: `structuralPass` runs the
smart-constructor simplifier `simplify`, `trigPass` the trigonometric cleanup `trigSimplify`,
`algebraPass` the checked algebraic normalizer `Alg.normalize`, and `factorPass` the
common-factor extraction `factorCommonAddDeep` of `Passes.Factorization`. Each pass carries the
soundness theorem of its transformation through the shared `Pass` type.
-/

@[expose] public section

namespace CAS.Verified.Expr

/-- The structural smart-constructor simplifier pass. -/
def structuralPass {ι : Type*} [DecidableEq ι] : Pass ι where
  name := "structural"
  run := simplify
  sound := by
    intro ρ expr
    simp

/-- The checked trigonometric cleanup pass. -/
def trigPass {ι : Type*} [DecidableEq ι] : Pass ι where
  name := "trig"
  run := trigSimplify
  sound := by
    intro ρ expr
    simp

/-- The checked algebraic normalizer pass. -/
def algebraPass {ι : Type*} [DecidableEq ι] : Pass ι where
  name := "algebra"
  run := Alg.normalize
  sound := by
    intro ρ expr
    simp

/-- Checked additive common-factor reconstruction pass. -/
def factorPass {ι : Type*} [DecidableEq ι] : Pass ι where
  name := "factor-common"
  run := factorCommonAddDeep
  sound := by
    intro ρ expr
    simp

end CAS.Verified.Expr

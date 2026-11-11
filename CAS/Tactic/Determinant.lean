/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Tactic.NormDet

/-!
# Determinants of matrix literals

Bare `cas` evaluates every determinant of a matrix literal `!![...]` in its goal with Mathlib's
`norm_det` simproc (the `eval_det` tactic, `Mathlib.Tactic.NormDet`), which computes the
determinant by Bird's division-free algorithm with a certificate chain and normalizes the result
as a commutative-ring expression. The rest of the goal, an equality of numerals or of polynomials
in the entries, then goes to the ordinary arithmetic routes. Determinants of matrices that are
not literals are left alone.

## Main definitions

* `hasLiteralDeterminant`: whether a term contains the determinant of a matrix literal.
* `evaluate`: `simp only [norm_det]` on the main goal, with the state restored on failure.

## Implementation notes

We compute nothing here. Mathlib's simproc (`Mathlib/Tactic/NormDet.lean`) rewrites
`Matrix.det A` by `BirdDet.det_eq_birdDet`, proved in
`Mathlib/LinearAlgebra/Matrix/Determinant/Bird/Correctness.lean`, and normalizes Bird's
division-free formula with the certificate-chain evaluator `certBirdDet` of
`Mathlib/Tactic/Determinant/Bird/Cert.lean`, so the kernel checks a chain of ring-normalization
certificates. The determinant stage is the first built-in stage of `cas`, because the later
routes would otherwise meet the determinant unevaluated: `rfl` unfolds `Matrix.det` of a 5x5
literal by definitional unfolding until Lean's recursion limit, and `simp` expands it along rows.
When the optional Hex bridge is loaded, an equation `Matrix.det A = d` over `ℤ` or `ℚ` goes
first to Hex's `det` (`CASHex/Algebra.lean`), which certifies the fraction-free elimination of
`A` in the kernel instead.
-/

public meta section

namespace CAS.Tactic.Determinant

open Lean Elab Tactic Meta

/-- The recursion limit for evaluating and validating a determinant certificate: the certificate
of a 12x12 integer determinant is deeper than Lean's default limit of 512. -/
def recursionDepth : Nat := 16384

/-- Whether `expression` contains the determinant of a matrix built with `Matrix.of`, as the
literal `!![...]` is (`Matrix.of` is an equivalence, so the literal is a coercion application). -/
def hasLiteralDeterminant (expression : Expr) : Bool :=
  (expression.find? fun term ↦
    term.isAppOf ``Matrix.det &&
      (term.getAppArgs.back?.any fun matrix ↦
        matrix.getUsedConstants.contains ``Matrix.of)).isSome

/-- Evaluate the determinants of matrix literals in the main goal with `simp only [norm_det]`.
Returns whether the main goal changed; other goals are untouched. The main goal may be closed when
both sides reduce to the same normal form. The state is restored when `norm_det` makes no
progress, fails, or exhausts the recursion depth; heartbeat exhaustion propagates. -/
def evaluate : TacticM Bool := withMainContext do
  unless hasLiteralDeterminant (← instantiateMVars (← getMainTarget)) do
    return false
  let saved ← saveState
  tryCatchRuntimeEx
    (do
      evalTactic (← `(tactic| simp only [norm_det]))
      return true)
    fun error ↦ do
      saved.restore
      if error.isRuntime && !error.isMaxRecDepth then
        throw error
      return false

end CAS.Tactic.Determinant

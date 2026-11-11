/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Scalar.Models

/-!
# Reduction of closed-form symbolic goals

`symbolic_simp` proves an identity about the evaluation of a closed-form residual by unfolding
it into an ordinary real expression and simplifying with Mathlib's tactics. It unfolds the scalar
models (`Scalar.laplaceResidual`, `Scalar.poissonResidual`, ...), the differential operators of
`DiffExpr`, the closed-form operators (`Verified.Expr.closedLaplacian`, ...) and
`Verified.Expr.eval`, and rewrites with `Verified.Expr.eval_simplify`,
`Verified.Expr.eval_mapVars` and `Alg.eval_normalize`. It is not used by the `cas` tactic, whose
routes compute with the verified normalizers instead.

## Main definitions

* `symbolic_simp`: unfold a symbolic residual and close the resulting real identity.

## Implementation notes

The tactic tries two `simp` paths in order. The first also unfolds `Verified.Expr.simplify` and
the smart constructors (`Verified.Expr.mkAdd`, `Verified.Expr.mkDiv`, ...), simplifies once more
with `Verified.Expr.eval`, and then tries `field_simp`, which clears denominators with the
nonzero hypotheses of the local context, followed by `ring_nf`. The second unfolds only the
residual definitions and then tries `ring_nf`. Nothing is computed by a verified normalizer:
the proof is what `simp`, `field_simp` and `ring_nf` produce, so its size grows with the
unfolded expression.
-/

public meta section

namespace CAS

open scoped BigOperators
open Lean Elab Tactic

/-! ## Proof automation for symbolic residuals -/

-- Both reduction paths unfold the same list of symbolic definitions, so they reach the same
-- normal forms.
private def symbolicReductionUnfoldings : Array Name := #[
  ``CAS.Scalar.laplaceResidual,
  ``CAS.Scalar.heatSpatialResidual,
  ``CAS.Scalar.heat1DResidual,
  ``CAS.Scalar.poissonResidual,
  ``CAS.Scalar.laplace,
  ``CAS.Scalar.heatSpatial,
  ``CAS.Scalar.heat1D,
  ``CAS.Scalar.poisson,
  ``CAS.Scalar.residual,
  ``CAS.DiffExpr.Lap,
  ``CAS.DiffExpr.D,
  ``CAS.DiffExpr.D2,
  ``CAS.Scalar.u,
  ``CAS.Scalar.ansatz,
  ``CAS.Scalar.PointCondition.residual,
  ``CAS.DiffExpr.Equation.closedResidual,
  ``CAS.DiffExpr.Equation.residual,
  ``CAS.DiffExpr.lower,
  ``CAS.Verified.Expr.closedLaplacian,
  ``CAS.Verified.Expr.closedDivergence,
  ``CAS.Verified.Expr.closedCurl2,
  ``CAS.Verified.Expr.closedCurl3,
  ``CAS.Verified.Expr.closedCurl3List,
  ``CAS.Verified.Expr.closedPartial,
  ``CAS.Verified.Expr.closedPartialBy,
  ``CAS.Verified.Expr.closedGradientList,
  ``CAS.Verified.Expr.sumFin,
  ``CAS.Verified.Expr.sum,
  ``CAS.Verified.Expr.addList,
  ``CAS.Verified.Expr.eval_simplify,
  ``CAS.Verified.Expr.eval_mapVars,
  ``CAS.Verified.Expr.Alg.eval_normalize
]

-- The first path also exposes executable smart constructors before clearing denominators.
private def symbolicNormalizerUnfoldings : Array Name := #[
  ``CAS.Verified.Expr.simplify,
  ``CAS.Verified.Expr.mkAdd,
  ``CAS.Verified.Expr.mkSub,
  ``CAS.Verified.Expr.mkMul,
  ``CAS.Verified.Expr.mkDiv,
  ``CAS.Verified.Expr.mkNeg,
  ``CAS.Verified.Expr.mkPow,
  ``CAS.Verified.Expr.mkNatMul,
  ``CAS.Verified.Expr.mkIntConst
]

/-- Unfold closed-form residuals and simplify the resulting real identity.

The tactic expands symbolic evaluation, uses local nonzero hypotheses to clear denominators, and
then applies Lean's algebraic normalizers.

Typical use:
```lean
example (p : ℝ^2) (hp : (p 0)^2 + (p 1)^2 ≠ 0) :
    (Scalar.laplaceResidual phi).eval p = 0 := by
  symbolic_simp
```
-/
syntax (name := symbolicSimp) "symbolic_simp" : tactic

macro_rules
  | `(tactic| symbolic_simp) => do
      let evalName := ``CAS.Verified.Expr.eval
      let reductionNames := symbolicReductionUnfoldings.push evalName
      let normalizerNames :=
        (symbolicReductionUnfoldings ++ symbolicNormalizerUnfoldings).push evalName
      let reductionArgs ← reductionNames.mapM fun name ↦ do
        let ident := mkIdent name
        `(Parser.Tactic.simpLemma| $ident:ident)
      let normalizerArgs ← normalizerNames.mapM fun name ↦ do
        let ident := mkIdent name
        `(Parser.Tactic.simpLemma| $ident:ident)
      let reductionSimp ← `(tactic| simp [$[$reductionArgs],*])
      let normalizerSimp ← `(tactic| simp [$[$normalizerArgs],*])
      let eval := mkIdent evalName
      `(tactic|
        first
          | $normalizerSimp:tactic <;>
            simp [$eval:ident] <;>
            try field_simp <;>
            try ring_nf
          | $reductionSimp:tactic <;> try ring_nf)

end CAS

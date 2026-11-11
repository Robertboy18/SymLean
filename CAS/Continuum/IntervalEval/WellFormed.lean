/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Syntax

/-!
# Syntactic well-formedness for interval evaluation

`Expr.isWellFormed` decides intrinsic well-formedness of a `Verified.Expr`: it is `false`
exactly when the expression contains a rational literal with denominator zero
(`isWellFormed_rat_zero` for the literal itself). It checks only syntax. Range evaluation uses
checked denominator and unary providers for the total real operations; for example,
square-root ranges can include negative inputs. `Expr.ValidAt` records the stronger domain
conditions used by analytic differentiation theorems.

## Implementation notes

`Verified.Expr.eval` is total, so the malformed literal `.rat num 0` has a Lean denotation,
though it is not a rational constant. The interval evaluator returns `none` on it, but
simplification could erase it before the evaluator sees it, so
`CertifiedEvalContext.evalSimplified` and `CertifiedEvalContext.evalNormalized` run
`isWellFormed` first. A semantic side condition would not do, since on an empty domain it holds
vacuously. The check is a structural recursion into `Bool`, which the kernel evaluates with the
rest of the planner when it checks a CEGA query.
-/

@[expose] public section

namespace CAS.Verified.Expr

/-- Decide intrinsic well-formedness, rejecting rational literals with denominator zero. -/
def isWellFormed {ι : Type*} : Expr ι → Bool
  | .nat _ | .int _ | .pi | .e | .var _ => true
  | .rat _ den => den != 0
  | .add a b | .mul a b | .sub a b | .div a b => a.isWellFormed && b.isWellFormed
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a |
      .sqrt a =>
      a.isWellFormed
  | .rpow a b => a.isWellFormed && b.isWellFormed

/-- Reject a zero denominator in a rational literal, independently of any evaluation domain. -/
@[simp] theorem isWellFormed_rat_zero {ι : Type*} (num : Int) :
    isWellFormed (.rat num 0 : Expr ι) = false :=
  rfl

end CAS.Verified.Expr

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Exact.ZeroResidual

/-!
# Exact symbolic approximation routes

A symbolic equality `expr = expected` is proved by running the side-conditioned route
`symbolicApproxRoute` on the difference `expr - expected`. When the route ends at zero,
`approxOn_zero_of_symbolicApproxRoute` and `eqOn_of_symbolicApproxRoute` give the zero-error
approximation and the equality on every patch where its emitted side conditions hold. The `cas`
tactic (`CAS.Tactic.Exact`) proves goals `Set.EqOn (exprFn expr) (exprFn expected) s`, and their
zero-error `ApproxOn` form, with them.
-/

@[expose] public section

namespace CAS

namespace Exact

open MeasureTheory
open CAS.Certificate

/-! ### Generic zero-error symbolic approximation routes

The internal residual `expr - expected` gives the zero-error statement
`ApproxOn (exprFn expr) (exprFn expected) patch 0`.
-/

/-- Residual for a generic exact symbolic approximation/equality claim. -/
def symbolicApproxResidual {n : Nat} (expr expected : Verified.Expr (Fin n)) :
    Verified.Expr (Fin n) :=
  expr - expected

/-- Side-conditioned route for a generic symbolic approximation/equality claim.

The route proves the residual `expr - expected` is zero. Once that residual is
closed, the result projects to `ApproxOn expr expected patch 0`. -/
def symbolicApproxRoute {n : Nat} (expr expected : Verified.Expr (Fin n)) : SymbolicClaimRoute n :=
  SymbolicClaimRoute.withSideConditions (symbolicApproxResidual expr expected)

/-- A closed generic symbolic approximation route proves zero-error approximation on a patch. -/
theorem approxOn_zero_of_symbolicApproxRoute {n : Nat} (expr expected : Verified.Expr (Fin n))
    (s : Set (ℝ^n))
    (hside : (symbolicApproxRoute expr expected).SideHoldsOn s)
    (hzero : (symbolicApproxRoute expr expected).rhs = (0 : Verified.Expr (Fin n))) :
    ApproxOn (exprFn expr) (exprFn expected) s 0 := by
  apply approxOn_of_difference_residualBound
  simpa [symbolicApproxRoute, symbolicApproxResidual, exprFn] using
    (symbolicApproxRoute expr expected).residualBound_zero s hside hzero

/-- A closed generic symbolic approximation route also proves exact equality on the patch.

It follows from `approxOn_zero_of_symbolicApproxRoute`, since zero error is equality on the
patch. -/
theorem eqOn_of_symbolicApproxRoute {n : Nat} (expr expected : Verified.Expr (Fin n))
    (s : Set (ℝ^n))
    (hside : (symbolicApproxRoute expr expected).SideHoldsOn s)
    (hzero : (symbolicApproxRoute expr expected).rhs = (0 : Verified.Expr (Fin n))) :
    Set.EqOn (exprFn expr) (exprFn expected) s :=
  eqOn_of_approxOn_zero (approxOn_zero_of_symbolicApproxRoute expr expected s hside hzero)

end Exact

end CAS

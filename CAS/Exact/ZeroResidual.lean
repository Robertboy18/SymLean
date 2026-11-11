/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.Residual
public import CAS.Exact.ScalarRoutes
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Zero-residual projections for scalar routes

Projections for an exact scalar route whose normalized target is syntactic zero: a
zero-error `ResidualCert` (`residualCertZero`), the bound `residualBound_zero`, and equality
with the zero function (`eqOn_zero`). The `Ready` variant `eqOn_zero_ready` assumes the route
emitted no side obligations and holds on every patch.
-/

@[expose] public section

namespace CAS
namespace Exact

open MeasureTheory
open CAS.Certificate

namespace SymbolicClaimRoute

/-! ### Projections from explicit route equalities

The facts that a route ends at zero and has no side obligations are equalities of route
fields, and the projections take those equalities as hypotheses.
-/

/-- If a symbolic route computes a residual to syntactic zero, produce a zero-error
residual certificate on any patch where its side obligations hold. -/
noncomputable def residualCertZero {n : Nat} (route : SymbolicClaimRoute n)
    (s : Set (ℝ^n)) (hside : route.SideHoldsOn s)
    (hzero : route.rhs = (0 : Verified.Expr (Fin n))) :
    ResidualCert (ℝ^n) ℝ s :=
  ResidualCert.ofEqOnZero (exprFn route.lhs) (by
    intro x hx
    have hs := route.eqOn s hside hx
    have hz : (exprFn route.rhs) x = 0 := by
      rw [hzero]
      change Verified.Expr.eval x (0 : Verified.Expr (Fin n)) = 0
      simp [Verified.Expr.eval]
    exact hs.symm.trans hz)

/-- A symbolic route that closes a residual to syntactic zero proves a zero residual bound on any
patch where its emitted analytic side obligations are discharged.

For side-conditioned symbolic routes the caller supplies the patch proof, and the
result is an ordinary `ResidualBound` proposition. -/
theorem residualBound_zero {n : Nat} (route : SymbolicClaimRoute n)
    (s : Set (ℝ^n)) (hside : route.SideHoldsOn s)
    (hzero : route.rhs = (0 : Verified.Expr (Fin n))) :
    ResidualBound (exprFn route.lhs) s 0 :=
  (route.residualCertZero s hside hzero).sound

/-- A symbolic route that closes a residual to syntactic zero proves equality to the zero function
on any patch where its emitted analytic side obligations are discharged. -/
theorem eqOn_zero {n : Nat} (route : SymbolicClaimRoute n)
    (s : Set (ℝ^n)) (hside : route.SideHoldsOn s)
    (hzero : route.rhs = (0 : Verified.Expr (Fin n))) :
    Set.EqOn (exprFn route.lhs) zeroFn s :=
  (route.residualCertZero s hside hzero).eqOn_zero_of_eps_eq_zero rfl

/-- Ready symbolic zero-residual routes prove equality to the zero function on the patch. -/
theorem eqOn_zero_ready {n : Nat} (route : SymbolicClaimRoute n)
    (s : Set (ℝ^n))
    (hzero : route.rhs = (0 : Verified.Expr (Fin n))) (hnone : route.nonzero = []) :
    Set.EqOn (exprFn route.lhs) zeroFn s :=
  route.eqOn_zero s (route.sideHoldsOn_of_nonzero_eq_nil s hnone) hzero

end SymbolicClaimRoute
end Exact
end CAS

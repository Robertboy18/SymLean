/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.Configured
public import CAS.Exact.RouteSemantics

/-!
# Scalar symbolic routes

`SymbolicClaimRoute n` is a checked claim `CAS.Verified.Expr.SideClaimRoute (Fin n)` about
expressions in the coordinates of `ℝ^n`, with a possibly empty list of nonvanishing
obligations. The exact symbolic routes of the `cas` tactic and the symbolic PDE residuals are
stated with it. Its constructors run the standard pipelines, `SideHoldsOn` says that the
emitted obligations hold on a patch, and `eqOn` projects a route to equality on that patch.
These statements concern evaluated expressions; identifying a symbolic derivative with a
classical derivative needs separate analytic validity hypotheses.

## Main definitions

* `SymbolicClaimRoute`: a scalar route over `Fin n` coordinates.
* `cas`, `casWithFuel`: the checked simplification pipeline, which emits no obligations.
* `ofDifference`: the route of the normalized residual `expr - expected` of an identity.
* `factor`: the staged exact factorization.
* `withSideConditions`: the side-conditioned simplification, which keeps every obligation it
  generates.
* `SideHoldsOn`: the emitted obligations of a route hold at every point of a patch.

## Main results

* `eqOn`: a route is an identity on every patch where `SideHoldsOn` holds.
* `sideHoldsOn_of_nonzero_eq_nil`, `sideHoldsOn_of_essentialSide_eq_nil`,
  `sideHoldsOn_of_essentialSide_eq`: sufficient conditions for `SideHoldsOn`.

## Implementation notes

An unconditional route and a route that emitted denominator or singularity obligations are the
same kind of object; the difference is whether `nonzero` is empty, and a route with
`nonzero = []` satisfies `SideHoldsOn` everywhere (`sideHoldsOn_of_nonzero_eq_nil`). The
structural sign checker proves some emitted obligations by itself, and only the others, the
essential list `Verified.Expr.essentialSide`, need proofs on the patch. The `cas` tactic
(`CAS.Tactic.Exact`) first tries `sideHoldsOn_of_essentialSide_eq_nil`, and otherwise proves the
essential conditions on the patch with `symbolic_assumptions`.

We state a new exact identity, such as a PDE residual, by building its route with `ofDifference`,
or with `withSideConditions` applied to the difference when the identity holds only where the
emitted denominators are nonzero, and by stating the theorem as `Set.EqOn`, zero
`ResidualBound` or `ApproxOn` over the route projection. The `cas` tactic recognizes these
shapes, so we extend its route inference only for a shape it does not recognize.
-/

@[expose] public section

namespace CAS
namespace Exact

open CAS.Certificate
open CAS.Domain

/-- A scalar symbolic route over `Fin n` coordinates: a checked claim with a possibly empty list
of nonvanishing obligations. -/
abbrev SymbolicClaimRoute (n : Nat) := Verified.Expr.SideClaimRoute (Fin n)

namespace SymbolicClaimRoute

/-- Unconditional route for the ordinary checked simplification pipeline with explicit fuel. -/
def casWithFuel {n : Nat} (fuel : Nat) (expr : Verified.Expr (Fin n)) : SymbolicClaimRoute n :=
  Verified.Expr.checkedClaimRoute fuel expr

/-- Unconditional route for the ordinary checked simplification pipeline. -/
def cas {n : Nat} (expr : Verified.Expr (Fin n)) : SymbolicClaimRoute n :=
  casWithFuel Verified.Expr.defaultFuel expr

/-- Build a scalar symbolic route for an identity `expr = expected`.

The routed expression is the normalized residual `expr - expected`, so a successful route proves
the usual zero-residual statement for the identity. -/
def ofDifference {n : Nat} (expr expected : Verified.Expr (Fin n)) : SymbolicClaimRoute n :=
  cas (Verified.Expr.Alg.normalize (expr - expected))

/-- Unconditional route for staged exact factorization. -/
def factor {n : Nat} (expr : Verified.Expr (Fin n)) : SymbolicClaimRoute n :=
  Verified.Expr.factorClaimRoute expr

/-- Simplify an expression while retaining every generated side condition. -/
def withSideConditions {n : Nat} (expr : Verified.Expr (Fin n)) : SymbolicClaimRoute n :=
  Verified.Expr.simplifySideClaimRoute expr

/-- The checked `cas` route starts from the expression it was given. -/
@[simp]
theorem lhs_cas {n : Nat} (expr : Verified.Expr (Fin n)) :
    (cas expr).lhs = expr :=
  rfl

/-- The checked `cas` route emits no obligations. -/
@[simp]
theorem nonzero_cas {n : Nat} (expr : Verified.Expr (Fin n)) :
    (cas expr).nonzero = [] :=
  rfl

/-- A difference route emits no obligations. -/
@[simp]
theorem nonzero_ofDifference {n : Nat} (expr expected : Verified.Expr (Fin n)) :
    (ofDifference expr expected).nonzero = [] :=
  rfl

/-- The factorization route emits no obligations. -/
@[simp]
theorem nonzero_factor {n : Nat} (expr : Verified.Expr (Fin n)) :
    (factor expr).nonzero = [] :=
  rfl

/-- The side-conditioned simplification route starts from the expression it was given. -/
@[simp]
theorem lhs_withSideConditions {n : Nat} (expr : Verified.Expr (Fin n)) :
    (withSideConditions expr).lhs = expr :=
  rfl

/--
Evaluating the source of a difference route recovers the intended semantic
residual `expr - expected`.

Clients should use this theorem instead of unfolding the route implementation:
normalization may change the stored syntax, but it preserves evaluation.
-/
@[simp] theorem eval_lhs_ofDifference {n : Nat}
    (expr expected : Verified.Expr (Fin n)) (x : ℝ^n) :
    (ofDifference expr expected).lhs.eval x = expr.eval x - expected.eval x := by
  simp [ofDifference]

/-- Patch-level discharge predicate for the nonzero obligations of a scalar symbolic route. -/
def SideHoldsOn {n : Nat} (route : SymbolicClaimRoute n)
    (s : Set (ℝ^n)) : Prop :=
  ∀ x, x ∈ s →
    Verified.Expr.Alg.SideHolds (fun i : Fin n ↦ x i) route.nonzero

/-- A route whose emitted obligations are all proved nonzero by the structural sign checker,
so that its essential list is empty, satisfies them on every patch. -/
theorem sideHoldsOn_of_essentialSide_eq_nil {n : Nat}
    (route : SymbolicClaimRoute n) (s : Set (ℝ^n))
    (hnone : Verified.Expr.essentialSide route.nonzero = []) :
    route.SideHoldsOn s :=
  fun _ _ ↦ Verified.Expr.sideHolds_of_essentialSide_eq_nil hnone _

/-- Discharge a route's emitted obligations on a patch from its essential conditions, given as
an explicit list that holds at every point of the patch. -/
theorem sideHoldsOn_of_essentialSide_eq {n : Nat}
    (route : SymbolicClaimRoute n) (s : Set (ℝ^n)) (side : List (Verified.Expr (Fin n)))
    (hessential : Verified.Expr.essentialSide route.nonzero = side)
    (h : ∀ x, x ∈ s → Verified.Expr.Alg.SideHolds (fun i : Fin n ↦ x i) side) :
    route.SideHoldsOn s :=
  fun x hx ↦ Verified.Expr.sideHolds_of_essentialSide (hessential ▸ h x hx)

/-- A route with no emitted side obligations satisfies them on every patch. -/
theorem sideHoldsOn_of_nonzero_eq_nil {n : Nat}
    (route : SymbolicClaimRoute n) (s : Set (ℝ^n))
    (hnone : route.nonzero = []) :
    route.SideHoldsOn s :=
  fun _ _ ↦ route.sideHolds_of_nonzero_eq_nil hnone _

/-- Extract equality on a patch from a scalar symbolic route and a side-condition discharge. -/
theorem eqOn {n : Nat} (route : SymbolicClaimRoute n)
    (s : Set (ℝ^n)) (hside : route.SideHoldsOn s) :
    Set.EqOn (exprFn route.rhs) (exprFn route.lhs) s :=
  eqOn_of_sideClaimRoute route s hside

end SymbolicClaimRoute
end Exact
end CAS

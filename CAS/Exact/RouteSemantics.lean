/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.SideClaim
public import CAS.Certificate.Approximation
public import CAS.Exact.ExpressionSideConditions

/-!
# Semantic projections for symbolic claims

The closed-form pipelines return a claim about expressions in `Verified.Expr (Fin n)` as a
`Verified.Expr.SideClaimRoute`: its `sound` theorem says that the left and right expressions
evaluate equally at every assignment where the listed expressions are nonzero, and an
unconditional claim is one whose list is empty. Neither statement is in the language of real
analysis. `eqOn_of_sideClaimRoute` reads a claim through `exprFn` and restates it as pointwise
equality `Set.EqOn` on a patch `s ⊆ ℝ^n`. Projections for a route whose right-hand side is zero
are in `CAS.Exact.ZeroResidual`.

## Main results

* `eqOn_of_sideClaimRoute`: a route is an identity on any patch where its emitted nonzero
  obligations hold (the `hside` hypothesis).

## Implementation notes

The proof uses only the `sound` field of a route. The planner metadata of a route, its list
`steps` of `Verified.Expr.PassInfo` (the configured passes of the pipelines that built the
route, with their phases), never enters a proof.
-/

@[expose] public section

namespace CAS
namespace Exact

open CAS.Certificate

/-- A checked symbolic claim route is equality on a patch once its emitted nonzero obligations
are discharged everywhere on that patch. -/
theorem eqOn_of_sideClaimRoute {n : Nat}
    (claim : Verified.Expr.SideClaimRoute (Fin n))
    (s : Set (ℝ^n))
    (hside : ∀ x, x ∈ s →
      Verified.Expr.Alg.SideHolds (fun i : Fin n ↦ x i) claim.nonzero) :
    Set.EqOn (exprFn claim.rhs) (exprFn claim.lhs) s := fun x hx ↦ by
  simpa [exprFn] using claim.sound (fun i : Fin n ↦ x i) (hside x hx)

end Exact
end CAS

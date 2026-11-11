/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.Sparse.Semantics

/-!
# Sparse polynomial antiderivative candidates

Termwise integration of the rational-coefficient multivariate polynomials used
by the checked algebra layer. Every coordinate other than the selected one
remains a symbolic parameter.

## Implementation notes

We reflect the integrand into the sparse representation with `Verified.Expr.Alg.mvPolyOf?`,
which multiplies out products and powers, and `termAntiderivative` raises the exponent of the
selected coordinate in each term by one and divides the coefficient by the new exponent. The
result is only a candidate: the planner checks it during search, and `integrate?` accepts it
only through `IntegrationCheck.certifyCandidate?`, when `IntegrationCheck.route` reduces its
derivative residual to literal zero, so no proof depends on this executable transformation.
-/

@[expose] public section

namespace CAS.IntegrationPlanner.Polynomial

/-- Integrate one sparse polynomial term with respect to coordinate `i`. -/
def termAntiderivative {n : Nat} (i : Fin n)
    (term : Rat × Verified.Expr.Alg.MvMonomial n) :
    Rat × Verified.Expr.Alg.MvMonomial n :=
  let exponent := term.2 i
  let denominator : Rat := exponent + 1
  (term.1 / denominator,
    fun j ↦ if j = i then term.2 j + 1 else term.2 j)

/--
Candidate antiderivative for the full rational-coefficient multivariate
polynomial fragment.

Expanded products are accepted because reflection occurs before integration.
-/
def candidate? {n : Nat} (i : Fin n)
    (expr : Verified.Expr (Fin n)) : Option (Verified.Expr (Fin n)) := do
  let polynomial ← Verified.Expr.Alg.mvPolyOf? expr
  pure <| Verified.Expr.Alg.mvPolyExpr
    (polynomial.map (termAntiderivative i))

end CAS.IntegrationPlanner.Polynomial

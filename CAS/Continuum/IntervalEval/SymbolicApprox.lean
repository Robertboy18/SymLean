/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Registry.Planner
public import CAS.Exact.ExpressionSideConditions

/-!
# Checked symbolic approximation

A `SymbolicApproxAttempt patch lhs rhs` stores a rational error budget `epsQ` and a proof that
the functions of the symbolic expressions `lhs` and `rhs` on `ℝ^n` differ by at most `epsQ` on
`patch`. `toApproxCert` turns it into an `ApproxCert`. The `cega` tactic registers this carrier
in `CAS.Tactic.CEGA.Registrations`.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Certificate
open CAS.Verified

namespace CertifiedEvalRegistry

variable {α : Type*} {ι : Type*} [DecidableEq ι] {s : Set α} {ρ : α → ι → ℝ}

/-! ### Symbolic approximation certificates -/

/-- Checked rational error bound for a symbolic approximation query.

The domain and symbolic endpoints are structure parameters, while `epsQ`
records the exact rational budget. An approximation certificate can
therefore be reconstructed without allowing an attempt to carry evidence for
unrelated functions.
-/
structure SymbolicApproxAttempt {n : Nat}
    (patch : Set (ℝ^n)) (lhs rhs : Verified.Expr (Fin n)) where
  /-- Computed rational error budget. -/
  epsQ : ℚ
  /-- Semantic theorem carried by the selected CEGA route. -/
  sound : ApproxOn (Exact.exprFn lhs) (Exact.exprFn rhs) patch (epsQ : ℝ)

namespace SymbolicApproxAttempt

/-- The approximation certificate of a symbolic approximation attempt. -/
noncomputable def toApproxCert {n : Nat} {patch : Set (ℝ^n)}
    {lhs rhs : Verified.Expr (Fin n)}
    (a : SymbolicApproxAttempt patch lhs rhs) : ApproxCert (ℝ^n) ℝ patch :=
  ApproxCert.ofApproxOn
    (Exact.exprFn lhs) (Exact.exprFn rhs) (a.epsQ : ℝ) a.sound

end SymbolicApproxAttempt

end CertifiedEvalRegistry
end RationalInterval
end CAS.Continuum

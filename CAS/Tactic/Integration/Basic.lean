/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Lean.Expr
public import Lean.Syntax

/-!
# Shared data for theorem-facing integration

Data types shared by integration planning, analytic projection, and query
reporting: the analytic theorem selected for a certificate (`Projection`), the
proposed proofs kept for reporting (`CertificateEvidence`), the origin of the
primitive (`PrimitiveSource`, `PrimitiveSelection`), and the record kept after a
goal is closed (`Result`, with `StructuralEvidence` for direct Mathlib theorems).
None of these values is evidence; reporting validates the proofs they hold before
displaying them. The module imports no reflection, planner, or calculus code.
-/

@[expose] public section

namespace CAS.Tactic.Integration

open Lean

/-- Analytic theorem selected for a checked antiderivative certificate. -/
inductive Projection where
  /-- Project the certificate to a derivative along one coordinate line. -/
  | hasDerivAt
  /-- Project the certificate through the interval fundamental theorem. -/
  | intervalIntegral
deriving DecidableEq, Repr

namespace Projection

/-- Stable diagnostic label for an integration projection. -/
def label : Projection → String
  | .hasDerivAt => "coordinate-line derivative"
  | .intervalIntegral => "coordinate-line fundamental theorem of calculus"

end Projection

/-- Proof-expression candidates retained for one antiderivative certificate.

This record is diagnostic data, not a theorem certificate. Reporting converts
both expressions to `UncheckedExplanationStep` values and validates them before
displaying either one as checked evidence. -/
structure CertificateEvidence where
  /-- Proposed proof that the derivative residual vanishes. -/
  routeZeroProof : Expr
  /-- Proposed proof of the bundled analytic validity requirements. -/
  requirementsProof : Expr

/-- How the primitive of a successfully closed integral was obtained. -/
inductive PrimitiveSource where
  /-- The caller supplied an ordinary primitive explicitly. -/
  | explicitPrimitive
  /-- The primitive was reconstructed from the goal's endpoint difference. -/
  | goalPrimitive
  /-- The bounded antiderivative planner supplied the primitive. -/
  | search
deriving DecidableEq, Repr

/-- The selected primitive after its residual, analytic requirements, and goal conversion
have all been checked. This metadata is not itself proof evidence. -/
structure PrimitiveSelection where
  /-- The strategy that supplied the accepted candidate. -/
  source : PrimitiveSource
  /-- The quoted symbolic primitive used by the certificate. -/
  candidate : Expr
  /-- An ordinary function retained for explicit replay, when the candidate came from one. -/
  function? : Option Expr := none

/-- Diagnostic evidence from a direct Mathlib calculus theorem, without a symbolic certificate. -/
structure StructuralEvidence where
  /-- The declarations used, with the primary calculus theorem first. -/
  theoremNames : Array Name
  /-- Proofs of the analytic premises consumed by the selected theorem. -/
  analyticEvidence : Array Expr
  /-- The completed proof of the original goal, retained for direct replay. -/
  proof : Expr

/--
Reporting data retained after an integration goal has been closed.

The goal-closing tactic checks its final proof independently. Before any entry
of `evidence` is displayed as checked evidence, the reporting code checks
its proof term against its inferred proposition. Relations may use several
antiderivative certificates before ordinary arithmetic closes the rewritten
goal.
-/
structure Result where
  /-- The analytic certificate theorem, when a symbolic certificate was used. -/
  projection? : Option Projection := none
  /-- Whether the projected equality was used to reduce and close an ordinary relation. -/
  closedRelation : Bool := false
  /-- Whether a `HasDerivAt` goal was closed by the checked derivative route
  (`CAS.Tactic.RealDeriv`) instead of an antiderivative certificate. -/
  derivativeRoute : Bool := false
  /-- Proof-expression candidates for every antiderivative certificate used by the proof. -/
  evidence : Array CertificateEvidence := #[]
  /-- Direct analytic theorem evidence, when no symbolic certificate was needed. -/
  structural? : Option StructuralEvidence := none
  /-- Actual primitive selections in the order their integrals were processed. -/
  primitiveSelections : Array PrimitiveSelection := #[]
  /-- Caller-supplied domain evidence retained as syntax for a fresh replay. -/
  requirementsSyntax? : Option (TSyntax `term) := none
  /-- The actual analytic theorem selected for each improper integral in the goal, over a
  half-line or the whole line. Bounded interval and derivative projections continue to use
  `projection?`. -/
  improperTheorems : Array Name := #[]

end CAS.Tactic.Integration

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Planning.Precision
public import CAS.Continuum.IntervalEval.Context

/-!
# Certified evaluation registries

A `CertifiedEvalRegistry s ρ` stores, for one chart, a rational interval environment with a
proof that it encloses every chart point, the denominator lower bounds and unary range facts
found so far, and the precision policy for finding more. `toContext` compiles it into a
`CertifiedEvalContext` through `CertifiedEvalContext.fromRouteEntries`, the same proof path as
manual assembly, and `ofEnvironment` starts a registry from an environment alone.

Registries are planner state. Theorem authors use the checked queries and `cega` tactics of
`CAS.CEGA`, which build registries internally and return ordinary semantic claims or
checked certificates.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Verified

/-- Registered checked facts for one CEGA evaluation chart.

The registry stores the chart interval environment together with the finite
denominator and unary range facts discovered by CEGA search, and the precision
policy used to synthesize further facts. Compiling it uses the same
`CertifiedEvalContext.fromRouteEntries` proof path as manual assembly, so the
registry is an automation convenience rather than an expansion of
the trusted base.
-/
structure CertifiedEvalRegistry {α : Type*} {ι : Type*} [DecidableEq ι]
    (s : Set α) (ρ : α → ι → ℝ) where
  /-- Variable interval environment for this chart. -/
  env : ι → RationalInterval
  /-- Proof that every chart point satisfies the variable interval environment. -/
  hvars : ∀ x, x ∈ s → ∀ i, (env i).MemReal (ρ x i)
  /-- Registered denominator lower-bound route facts. -/
  divEntries : List (ExprAbsLowerRouteEntry s ρ) := []
  /-- Registered unary range route facts, typed against the denominator provider above. -/
  unaryEntries :
    List (UnaryRangeRouteEntry env
      (ExprAbsLowerProvider.fromRouteEntries divEntries).lookup) := []
  /-- Precision policy used when synthesizing elementary-function range facts. -/
  precision : Precision := {}

namespace CertifiedEvalRegistry

variable {α : Type*} {ι : Type*} [DecidableEq ι] {s : Set α} {ρ : α → ι → ℝ}

/--
Start automatic certified evaluation from a proved interval environment.

The resulting registry has no manually supplied denominator or unary facts.
Subsequent compiler passes may derive those facts from `env`, at the requested
precision; every derived entry remains checked.
-/
def ofEnvironment
    (env : ι → RationalInterval)
    (hvars : ∀ x, x ∈ s → ∀ i, (env i).MemReal (ρ x i))
    (precision : Precision := {}) :
    CertifiedEvalRegistry s ρ where
  env := env
  hvars := hvars
  precision := precision

/-- Compile a registry into the trusted certified evaluator context. -/
def toContext (r : CertifiedEvalRegistry s ρ) : CertifiedEvalContext s ρ :=
  CertifiedEvalContext.fromRouteEntries r.env r.hvars r.divEntries r.unaryEntries

/-- Compile a registry into a checked evaluation route. -/
def toRoute (r : CertifiedEvalRegistry s ρ) :
    CertificateRoute (CertifiedEvalContext s ρ) where
  cert := r.toContext
  steps := CertifiedEvalContext.routeEntrySteps r.env r.divEntries r.unaryEntries

end CertifiedEvalRegistry
end RationalInterval
end CAS.Continuum

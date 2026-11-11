/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Planning.Requirements
public import CAS.Continuum.IntervalEval.Registry.Core
import CAS.Domain.SideConditions -- shake: keep: `open CAS.Domain` needs the namespace, which no constant use records

/-!
# Facts an interval registry is missing for an expression

`CertifiedEvalRegistry.requirements` scans an expression and returns its `RegistryRequirements`
for one registry. A denominator whose interval excludes zero needs a reciprocal range (`.inv`),
and any other denominator an absolute lower bound unless one is registered
(`denominatorRequirement`); an `atan`, `asin`, `acos`, `exp`, `log` or `sqrt` node needs a
range fact when its argument interval can be computed and no fact is registered
(`unaryRequirement`), and a real power `a ^ b` needs the ranges of `log a` and of
`exp (log a * b)`. The result is planner data. It affects evaluation only after a solver turns
it into checked registry entries.

## Implementation notes

`requirements` is a structural recursion over the expression that evaluates as it goes, with
the lookups the registry already holds: at a quotient it evaluates the denominator with
`evalWithLookups`, and `unaryRequirement` evaluates the argument with `toContext` and asks the
unary provider for an entry at that argument interval. A missing range is therefore stated for
the interval the evaluator will compute, which is the one a new entry must match: the provider
applies an entry only to the same operation, the same argument and the same rational endpoints
(`UnaryRangeRouteEntry.lookupOne`). Nothing is shared between nodes, and the argument of every
quotient and unary node is evaluated afresh. The scan proves nothing and needs no theorem. Its
callers `extendWithSolvedDenominatorsOfSimplified?` and
`extendWithSolvedUnaryRangesOfSimplified?` (`CAS.Continuum.IntervalEval.Registry.Refinement`)
turn its lists into entries that carry their own proofs, and like the rest of the planner it
runs in the kernel when a CEGA query is reduced.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Verified
open CAS.Domain

namespace CertifiedEvalRegistry

variable {α : Type*} {ι : Type*} [DecidableEq ι] {s : Set α} {ρ : α → ι → ℝ}

/-- Requirements contributed by one denominator expression. -/
def denominatorRequirement (r : CertifiedEvalRegistry s ρ) (den : Verified.Expr ι) :
    RegistryRequirements ι :=
  match (ExprAbsLowerProvider.fromRouteEntries r.divEntries).lookup den with
  | some _cert => RegistryRequirements.empty
  | none => { RegistryRequirements.empty with missingDenominators := [den] }

/-- Requirements contributed by one certificate-driven unary operation. -/
def unaryRequirement (r : CertifiedEvalRegistry s ρ)
    (op : UnaryKind) (arg : Verified.Expr ι) : RegistryRequirements ι :=
  let plan := r.toContext
  match plan.eval arg with
  | some IA =>
      match plan.unaryProvider.lookup op arg IA with
      | some _cert => RegistryRequirements.empty
      | none =>
          { RegistryRequirements.empty with
            missingUnaryRanges := [{ op := op, arg := arg, argInterval := IA }] }
  | none => RegistryRequirements.empty

/-- Scan an expression for denominator and unary-range facts missing from this registry. -/
def requirements (r : CertifiedEvalRegistry s ρ) :
    Verified.Expr ι → RegistryRequirements ι
  | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ =>
      RegistryRequirements.empty
  | .add a b | .mul a b | .sub a b =>
      (requirements r a).append (requirements r b)
  | .div a b =>
      let baseReq := (requirements r a).append (requirements r b)
      match
        evalWithLookups r.env
          (ExprAbsLowerProvider.fromRouteEntries r.divEntries).lookup
          (UnaryRangeProvider.fromRouteEntries r.unaryEntries).lookup b with
      | some IB =>
          if _hpos : 0 < IB.lo then
            baseReq.append (r.unaryRequirement .inv b)
          else if _hneg : IB.hi < 0 then
            baseReq.append (r.unaryRequirement .inv b)
          else
            baseReq.append (r.denominatorRequirement b)
      | none =>
          baseReq.append (r.denominatorRequirement b)
  | .neg a | .pow a _ | .sin a | .cos a =>
      requirements r a
  | .atan a =>
      (requirements r a).append (r.unaryRequirement .atan a)
  | .asin a =>
      (requirements r a).append (r.unaryRequirement .asin a)
  | .acos a =>
      (requirements r a).append (r.unaryRequirement .acos a)
  | .exp a =>
      (requirements r a).append (r.unaryRequirement .exp a)
  | .log a =>
      (requirements r a).append (r.unaryRequirement .log a)
  | .sqrt a =>
      (requirements r a).append (r.unaryRequirement .sqrt a)
  | .rpow a b =>
      ((requirements r a).append (requirements r b)).append
        ((r.unaryRequirement .log a).append
          (r.unaryRequirement .exp (.mul (.log a) b)))

end CertifiedEvalRegistry
end RationalInterval
end CAS.Continuum

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Registry.Analysis
public import CAS.Continuum.IntervalEval.Registry.Denominator
public import CAS.Continuum.IntervalEval.Registry.Unary

/-!
# Extending registries and scoring subdivision coordinates

`extendWithEasyFacts?` simplifies an expression and adds to a registry the denominator lower
bounds and unary range facts it needs: first the denominators, then the unary ranges, repeated
until no new range is solved, because solving an inner operation can expose the next one
(`extendWithSolvedUnaryRangesToFixedPoint?`, with fuel `providerSensitiveNodeCount`).
`extendWithDenominatorFactsFor?` certifies an explicit list of nonzero side conditions.
`variableSensitivity?` and `variableSensitivities` score a coordinate `i` for subdivision by
its interval width times `absMax` of the enclosure of `∂ᵢ f` on the chart.

## Implementation notes

The order of the passes is forced by the types. A unary entry is typed against the denominator
lookup in force when it was built, so when `extendWithDenominatorFactsFor?` adds denominator
entries it drops every unary entry, and the unary pass rebuilds them against the new provider.
The passes only propose entries; each entry carries its own soundness proof, and a pass that
cannot solve every missing requirement returns `none` rather than a partial registry. The fuel
`providerSensitiveNodeCount expr` counts the divisions, the unary operations and two nodes per
real power, which bounds the rounds a nested chain needs.

The sensitivity score is ours and plays no part in soundness. By the mean value theorem,
`width(Bᵢ) · max |Dᵢ|`, with `Dᵢ` an enclosure of `∂ᵢ f` on the chart, bounds how much `f` can
vary along coordinate `i`, so the planner bisects where this first-order bound is largest.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Verified

namespace CertifiedEvalRegistry

variable {α : Type*} {ι : Type*} [DecidableEq ι] {s : Set α} {ρ : α → ι → ℝ}

/--
Try to extend a registry with denominator facts for an explicit side-condition frontier.

A symbolic route such as `(x / y) * y = x` already knows that it needs `y ≠ 0`,
even when the interval evaluator has not generated that requirement. CEGA can
therefore ask the chart solver to certify precisely the route's required
nonzero expressions and then reuse the exact route proof.
-/
def extendWithDenominatorFactsFor?
    (r : CertifiedEvalRegistry s ρ) (denominators : List (Verified.Expr ι)) :
    Option (CertifiedEvalRegistry s ρ) :=
  match denominators.mapM r.denominatorRouteEntry? with
  | some [] => some r
  | some generated =>
      some
        { env := r.env
          hvars := r.hvars
          divEntries := r.divEntries ++ generated
          unaryEntries := []
          precision := r.precision }
  | none => none

/--
Solve denominator requirements on an expression that has already been simplified.

Adding a denominator entry changes the provider on which unary entries depend,
so `extendWithDenominatorFactsFor?` rebuilds the unary layer from
an empty list. A fixed-point pass then reconstructs it against the new provider.
-/
def extendWithSolvedDenominatorsOfSimplified?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι) :
    Option (CertifiedEvalRegistry s ρ) :=
  r.extendWithDenominatorFactsFor? (r.requirements expr).missingDenominators

/-- Add every unary range solvable from this registry, keeping the denominator provider. -/
def extendWithSolvedUnaryRangesOfSimplified?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι) :
    Option (CertifiedEvalRegistry s ρ) :=
  let reqs := r.requirements expr
  match reqs.missingUnaryRanges.mapM r.unaryRangeRouteEntry? with
  | some generated =>
      some
        { env := r.env
          hvars := r.hvars
          divEntries := r.divEntries
          unaryEntries := r.unaryEntries ++ generated
          precision := r.precision }
  | none => none

/--
Number of provider-sensitive operations in an expression.

This is a conservative fuel bound for inside-out unary compilation. A single
round may solve several independent operations, while a nested chain may need
one round per provider-sensitive node.
-/
def providerSensitiveNodeCount : Verified.Expr ι → Nat
  | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ => 0
  | .add a b | .mul a b | .sub a b =>
      providerSensitiveNodeCount a + providerSensitiveNodeCount b
  | .div a b =>
      providerSensitiveNodeCount a + providerSensitiveNodeCount b + 1
  | .neg a | .pow a _ | .sin a | .cos a =>
      providerSensitiveNodeCount a
  | .atan a | .asin a | .acos a | .exp a | .log a | .sqrt a =>
      providerSensitiveNodeCount a + 1
  | .rpow a b =>
      providerSensitiveNodeCount a + providerSensitiveNodeCount b + 2

/--
Repeatedly solve newly exposed unary ranges, stopping at a fixed point.

One pass can certify the inner operation of a composition while an outer
operation remains blocked. Recomputing requirements against the extended
registry exposes the next operation. The structural fuel bound stops the search even when a
solver makes no progress.
-/
def extendWithSolvedUnaryRangesToFixedPoint?
    (expr : Verified.Expr ι) :
    Nat → CertifiedEvalRegistry s ρ →
      Option (CertifiedEvalRegistry s ρ)
  | 0, r => some r
  | fuel + 1, r =>
      match r.extendWithSolvedUnaryRangesOfSimplified? expr with
      | none => none
      | some r' =>
          if r'.unaryEntries.length = r.unaryEntries.length then
            some r'
          else
            extendWithSolvedUnaryRangesToFixedPoint? expr fuel r'

/--
Run the easy solvers on an expression that has already been simplified: first the denominator
pass, then unary-range closure to a fixed point with fuel `providerSensitiveNodeCount expr`.
Fails with `none` if either stage fails. `extendWithEasyFacts?` adds the simplification.
-/
def extendWithEasyFactsOfSimplified?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι) :
    Option (CertifiedEvalRegistry s ρ) :=
  match r.extendWithSolvedDenominatorsOfSimplified? expr with
  | some r₁ =>
      extendWithSolvedUnaryRangesToFixedPoint? expr
        (providerSensitiveNodeCount expr) r₁
  | none => none

/-- Run the easy CEGA solvers in sequence.

The pass first solves easy denominator targets from variable intervals, then
solves easy unary range targets such as square roots whose argument interval is
available after the denominator pass.  It is conservative: if either stage fails,
the whole combined extension fails instead of producing a partial registry.
-/
def extendWithEasyFacts?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι) :
    Option (CertifiedEvalRegistry s ρ) :=
  r.extendWithEasyFactsOfSimplified? (Verified.Expr.simplify expr)

/-! ### Subdivision candidates -/

/-- Proof-free coordinate candidate used by the subdivision planner.

`priority` is either a first-order sensitivity score or a fallback interval
width. The source width is retained only as a deterministic tie-breaker.
The construction path determines which score was used, so no separate tag is
stored. Neither quantity participates in the soundness proof of the eventual
cover.
-/
structure VariableSubdivisionChoice (ι : Type*) where
  /-- Coordinate proposed for bisection. -/
  coordinate : ι
  /-- Planner priority: influence score or fallback interval width. -/
  priority : ℚ
  /-- Width of the source interval, used to break equal-priority ties. -/
  width : ℚ

/--
Compute one first-order variable-sensitivity score when interval evaluation
can enclose the corresponding symbolic partial derivative.

Constant-width coordinates and variables absent from the expression are
discarded because bisecting either cannot improve the enclosure.
-/
def variableSensitivity?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι) (i : ι) :
    Option (VariableSubdivisionChoice ι) :=
  let source := r.env i
  let width := source.hi - source.lo
  if expr.containsVar i && decide (source.lo < source.hi) then
    match r.toContext.evalSimplified (expr.diff i) with
    | none => none
    | some derivativeRange =>
        some
          { coordinate := i
            priority := width * derivativeRange.absMax
            width }
  else
    none

/--
First-order sensitivity scores for the splittable variables among `coordinates`,
in the order of that list.

The caller supplies the coordinate enumeration (`List.finRange n` for `Fin n`)
instead of this function sorting `Finset.univ`: CEGA queries are evaluated by
the kernel, and `Finset.sort` reduces through `List.mergeSort`, whose body Lean
core does not expose to module files.
-/
def variableSensitivities
    (r : CertifiedEvalRegistry s ρ) (coordinates : List ι) (expr : Verified.Expr ι) :
    List (VariableSubdivisionChoice ι) :=
  coordinates.filterMap (r.variableSensitivity? expr)

end CertifiedEvalRegistry
end RationalInterval
end CAS.Continuum

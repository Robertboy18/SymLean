/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.SideClaim
public import CAS.Continuum.IntervalEval.Range
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import CAS.Continuum.IntervalEval.Registry.Refinement

/-!
# Enclosures through checked side-conditioned rewrites

A `SideClaimRoute` of the computer algebra system rewrites an expression `route.lhs` to
`route.rhs` under the nonzero side conditions `route.nonzero`. Given rational intervals for the
variables on a domain, `autoSideRouteEnclosureAttempt?` first adds the unary range facts needed
by the side conditions (`extendWithEasyFactsFor?`), then absolute lower bounds for them from
their interval enclosures (`extendWithIntervalDenominatorFactsFor?`, which drops the unary
entries), then the facts needed by `route.rhs` (`extendWithEasyFacts?`). It checks that the side
conditions hold on the whole domain, evaluates `route.rhs`, and transports the enclosure back to
`route.lhs` with `route.sound`. The result is an `EnclosureAttempt` for `route.lhs`, and any
failed step returns `none`.

## Implementation notes

The rewrite is a theorem of the closed-form pipeline, valid where the side conditions hold, so
the interval layer only proves those conditions on the domain and encloses the right-hand side.
A side condition `e ≠ 0` is accepted by `certifiesSideConditions`, from a registered lower bound
on `|e|` or from an interval of `e` that excludes zero. The unary facts are added before the
interval bounds because enclosing a side condition may itself need unary ranges.
The CEGA queries `encloseOn?` and `encloseBoxLevel?` use this route for the branch-aware
`exp (log _)` normalization, and the monotonicity route uses it to enclose partial derivatives
after side-conditioned normalization (`sideNormalizedPartialAttempt?`).
-/

@[expose] public section

namespace CAS.Continuum

open CAS.Verified
open Set

namespace RationalInterval

variable {ι : Type*} [DecidableEq ι]
  {expr : Verified.Expr ι} {ρ : ℝ → ι → ℝ} {s : Set ℝ}

/--
Extend a registry with the easy unary facts needed by each obligation in turn.

Obligations are processed left to right, each extension starting from the previous result.
The first failure returns `none`.
-/
def extendWithEasyFactsFor?
    {α : Type*} {s : Set α} {ρ : α → ι → ℝ}
    (registry : CertifiedEvalRegistry s ρ) :
    List (Verified.Expr ι) → Option (CertifiedEvalRegistry s ρ)
  | [] => some registry
  | obligation :: obligations => do
      let extended ← registry.extendWithEasyFacts? obligation
      extendWithEasyFactsFor? extended obligations

/--
Extend a registry with interval-derived absolute lower bounds for the listed denominators.

Each denominator receives a route entry from `intervalAbsLowerRouteEntry?`, and any failure
returns `none`. The unary entries of the input registry are dropped.
-/
noncomputable def extendWithIntervalDenominatorFactsFor?
    {α : Type*} {s : Set α} {ρ : α → ι → ℝ}
    (registry : CertifiedEvalRegistry s ρ)
    (denominators : List (Verified.Expr ι)) :
    Option (CertifiedEvalRegistry s ρ) := do
  let generated ← denominators.mapM registry.intervalAbsLowerRouteEntry?
  return {
    env := registry.env
    hvars := registry.hvars
    divEntries := registry.divEntries ++ generated
    unaryEntries := []
    precision := registry.precision
  }

/--
Automatically enclose the source of a checked side-conditioned symbolic route.

The compiler first builds easy unary facts needed by the route's side witnesses,
then synthesizes absolute lower bounds for those witnesses. It finally compiles
the route target with the ordinary denominator and unary-range machinery. A
successful result is transported back to `route.lhs` with `route.sound`.

The result encloses `route.lhs` itself on the domain by the displayed interval.
Unsupported side conditions or target operations give `none`.
-/
noncomputable def autoSideRouteEnclosureAttempt?
    {α : Type*} {s : Set α} {ρ : α → ι → ℝ}
    (route : Verified.Expr.SideClaimRoute ι)
    (env : ι → RationalInterval)
    (henv : ∀ x ∈ s, ∀ i, (env i).MemReal (ρ x i))
    (precision : Precision := {}) :
    Option (EnclosureAttempt α s (fun x ↦ route.lhs.eval (ρ x))) := by
  let base : CertifiedEvalRegistry s ρ :=
    CertifiedEvalRegistry.ofEnvironment env henv precision
  match hprepared : extendWithEasyFactsFor? base route.nonzero with
  | none => exact none
  | some prepared =>
    match hsideRegistry :
      extendWithIntervalDenominatorFactsFor? prepared route.nonzero with
    | none => exact none
    | some sideRegistry =>
      match hcompiled :
          sideRegistry.extendWithEasyFacts? route.rhs with
      | none => exact none
      | some compiled =>
          if hside : compiled.toContext.certifiesSideConditions route.nonzero then
              match hevaluated :
                  compiled.toContext.evalSimplified route.rhs with
              | none => exact none
              | some result =>
                  exact some
                    { interval := result
                      sound := by
                        intro x hx
                        have hrange :=
                          compiled.toContext.sound_simplified
                            x hx route.rhs result hevaluated
                        rw [route.sound (ρ x)
                          (compiled.toContext.sideHolds_of_certifiesSideConditions
                            route.nonzero hside x hx)]
                          at hrange
                        exact hrange
                      steps := compiled.toRoute.steps }
          else
            exact none

end RationalInterval
end CAS.Continuum

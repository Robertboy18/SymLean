/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Affine
public import CAS.Continuum.IntervalEval.Hyperbolic
public import CAS.Continuum.IntervalEval.Registry.Refinement
public import CAS.Continuum.IntervalEval.Attempt

/-!
# Selecting certified enclosures

The planner chooses among the enclosure routes for an expression on a registry chart: exact
side-condition-aware normalization, affine arithmetic (`affineEnclosureAttempt?`), the
correlated hyperbolic ranges, and the interval route with automatically synthesized facts.
`selectFiniteEnclosurePreview?` computes the candidate intervals without proofs and ranks them
by `PlannerSummary.enclosureScore`, and `selectFiniteEnclosureAttempt?` builds the checked
`EnclosureAttempt` for the selected route. The ranking plays no part in soundness, which each
attempt carries itself. `selectVariableSubdivisionChoice?` picks a coordinate for box
subdivision from first-order sensitivity scores.

## Implementation notes

We run every finite-chart route without proofs, compare the intervals by width, then by the
largest absolute endpoint, then by route length, and build only the selected certificate; a
correlated hyperbolic route that succeeds is taken at once. The natural interval extension is
the `.easy` route: the expression is simplified, `extendWithEasyFacts?` adds the denominator
bounds and unary ranges it needs, and the certified context evaluates it. What the kernel
checks is the selected `EnclosureAttempt`, whose `sound` field is the inclusion theorem of its
route (`evalWithLookups_sound` through the context, `mem_affineRange_of_memBox` for affine
arithmetic). If the selected route fails to build, the attempt is `none`; the box planner in
`CAS.CEGA.Query` then tries its next candidate.

The subdivision choice is ours and untrusted. It proposes the coordinate with the largest
positive score `width(Bᵢ) · max |Dᵢ|` from `variableSensitivities`, ties broken by width. When
no score is positive it proposes the widest coordinate whose partial derivative could not be
enclosed. The cover by the two halves of a bisection is proved for every coordinate, so the
choice only affects sharpness.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Certificate
open CAS.Verified

namespace CertifiedEvalRegistry

variable {α : Type*} {ι : Type*} [DecidableEq ι] {s : Set α} {ρ : α → ι → ℝ}

/-! ### Canonical range selection -/

/--
Select a checked enclosure, trying side-condition-aware exact normalization
before the simplifying interval route with automatically synthesized facts.

Both branches return an attempt indexed by the original expression's semantic
function. The branch choice is planner behavior; soundness is carried by the
returned attempt itself.
-/
noncomputable def selectEnclosureAttempt?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι) :
    Option (EnclosureAttempt α s (fun x ↦ expr.eval (ρ x))) :=
  let route := r.toRoute
  match route.cert.enclosureAttemptNormalized? expr route.steps with
  | some result => some result
  | none =>
      (r.extendWithEasyFacts? expr).bind fun fallback ↦
        fallback.toContext.enclosureAttemptSimplified? expr fallback.toRoute.steps

/-- Compile the affine fragment against a registered finite coordinate chart. -/
noncomputable def affineEnclosureAttempt? [Fintype ι]
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι) :
    Option (EnclosureAttempt α s (fun x ↦ expr.eval (ρ x))) :=
  match hRange : RationalInterval.affineRange? r.env expr with
  | none => none
  | some range =>
      some
        { interval := range
          sound := fun x hx ↦
            RationalInterval.mem_affineRange_of_memBox
              r.env expr range (ρ x) (r.hvars x hx) hRange
          steps := [.affineArithmetic] }

/-- Package a route's optional interval as a proof-free planner summary of the given `kind`,
recording the number of route `steps`. -/
def enclosurePreviewCandidate?
    (kind : PlannerRouteKind) (interval? : Option RationalInterval)
    (steps : List RouteStep) : Option PlannerSummary :=
  interval?.map fun interval ↦
    { kind := kind
      interval := interval
      stepCount := steps.length }

/-- Select the best proof-free finite-chart enclosure summary. -/
def selectFiniteEnclosurePreview? [Fintype ι]
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι) : Option PlannerSummary :=
  let route := r.toRoute
  let normalized := enclosurePreviewCandidate? .exact
    (route.cert.evalNormalized expr) (.exactNormalization :: route.steps)
  let affine := enclosurePreviewCandidate? .affine
    (RationalInterval.affineRange? r.env expr) [.affineArithmetic]
  let hyperbolic := enclosurePreviewCandidate? .hyperbolic
    (r.toContext.hyperbolicRange? expr r.precision.expOrder.toPNat') [.hyperbolicRange]
  let fallback := (r.extendWithEasyFacts? expr).bind fun extended ↦
    enclosurePreviewCandidate? .easy
      (extended.toContext.evalSimplified expr) extended.toRoute.steps
  PlannerSummary.bestEnclosure? [normalized, affine, hyperbolic, fallback].reduceOption

/--
Select a checked enclosure for a finite coordinate chart.

A successful correlated hyperbolic route is preferred immediately. Otherwise
the ranked preview chooses among side-condition-aware normalization, affine
arithmetic, and the simplifying interval fallback. This priority need not give
the narrowest of all candidate intervals. Every returned attempt carries its
own soundness proof; candidate scores do not participate in that proof.
-/
noncomputable def selectFiniteEnclosureAttempt? [Fintype ι]
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι) :
    Option (EnclosureAttempt α s (fun x ↦ expr.eval (ρ x))) :=
  match r.toContext.hyperbolicEnclosureAttempt? expr r.precision.expOrder.toPNat' with
  | some result => some result
  | none =>
      match (r.selectFiniteEnclosurePreview? expr).map PlannerSummary.kind with
      | some .exact =>
          let route := r.toRoute
          route.cert.enclosureAttemptNormalized? expr route.steps
      | some .affine => r.affineEnclosureAttempt? expr
      | some .hyperbolic =>
          r.toContext.hyperbolicEnclosureAttempt? expr r.precision.expOrder.toPNat'
      | some .easy =>
          (r.extendWithEasyFacts? expr).bind fun extended ↦
            extended.toContext.enclosureAttemptSimplified? expr extended.toRoute.steps
      | _ => none

/-! ### Sensitivity-guided subdivision choice -/

/-- Fallback subdivision candidate for coordinate `i`, scored by its source interval width.

The candidate is produced only when `expr` mentions `i`, the source interval of `i` is not
degenerate, and `sensitivities` holds no first-order score for `i`. -/
def unsupportedVariableSubdivisionChoice?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι)
    (sensitivities : List (VariableSubdivisionChoice ι)) (i : ι) :
    Option (VariableSubdivisionChoice ι) :=
  let source := r.env i
  let width := source.hi - source.lo
  if expr.containsVar i && decide (source.lo < source.hi) &&
      !sensitivities.any (fun sensitivity ↦ sensitivity.coordinate == i) then
    some
      { coordinate := i
        priority := width
        width }
  else
    none

/--
Choose a coordinate for interval subdivision among `coordinates`.

Positive first-order influence scores are preferred. If interval evaluation
cannot enclose any relevant partial derivative, the widest unsupported
coordinate is selected. Coordinates whose checked derivative range is exactly
zero are not subdivided merely because they are syntactically present. The
caller enumerates the coordinates (see `variableSensitivities`).
-/
def selectVariableSubdivisionChoice?
    (r : CertifiedEvalRegistry s ρ) (coordinates : List ι) (expr : Verified.Expr ι) :
    Option (VariableSubdivisionChoice ι) :=
  let sensitivities := r.variableSensitivities coordinates expr
  let positive := sensitivities.filter (fun sensitivity ↦ decide (0 < sensitivity.priority))
  let score := fun choice : VariableSubdivisionChoice ι ↦
    (toLex (choice.priority, choice.width) : ℚ ×ₗ ℚ)
  match positive.argmax score with
  | some sensitivity => some sensitivity
  | none =>
      (coordinates.filterMap
        (r.unsupportedVariableSubdivisionChoice? expr sensitivities)).argmax score

end CertifiedEvalRegistry
end RationalInterval
end CAS.Continuum

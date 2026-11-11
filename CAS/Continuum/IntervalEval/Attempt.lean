/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Context

/-!
# Certified-evaluation attempts

Checked enclosure and residual attempts are kept apart from the
computable planner records used to rank CEGA routes. One enclosure attempt
supplies every derived scalar view (ordinary bounds, absolute bounds, and
midpoint approximations) without duplicating the checked interval or route.

## Main definitions

* `PlannerSummary`, `PlannerSummary.bestEnclosure?`: untrusted computable
  snapshots of candidate routes and their lexicographic ranking by width,
  magnitude, then step count.
* `EnclosureAttempt.cert`: the enclosure certificate of an attempt.
* `EnclosureAttempt.ofBinaryCover`: gluing two local enclosures over a cover
  into the rational hull, with the covering proof carrying the soundness.

## Main results

* `EnclosureAttempt.boundOn`, `EnclosureAttempt.boundOn_abs`,
  `EnclosureAttempt.approxOn_center`: the upper bound, the bound on `|f|` by the
  largest absolute endpoint, and the midpoint approximation with the radius as
  error, all derived from one checked enclosure.

## Implementation notes

`enclosureScore` lives in the lexicographic order `ℚ ×ₗ (ℚ ×ₗ ℕ)`, so a single `<` decides the
whole ranking, and `bestEnclosure?` is Mathlib's `List.argmin` of it, which keeps the earlier
candidate on a complete tie. The summaries and their comparison are computable, and the kernel
runs them inside the planner (`selectFiniteEnclosurePreview?`, and `rankRoutes` and
`encloseBoxLevelPreview?` of `CAS.CEGA.Query`). A summary carries no proof, so the ranking
needs no theorem.

Each scalar view is a one-line proof from the `sound` field of the attempt: the upper endpoint
for `boundOn`, `RationalInterval.abs_le_absMax` for `boundOn_abs` and
`RationalInterval.midpointApproxCert` for `approxOn_center`. The `..._of_interval_eq` forms
restate them for displayed rationals; they are the theorems that `BoxQueryMode.soundTheorem`
names in `CAS.CEGA.Elaboration`, and `CAS.Tactic.CEGA.Registrations` registers both `cert`
projections and the three views with the `cega` tactic. `ofBinaryCover` proves its hull by a
case split on the cover (`RationalInterval.memReal_hull_left`,
`RationalInterval.memReal_hull_right`) and records `.boxSubdivision` before the steps of both
halves.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Certificate
open CAS.Verified

/-! ## Planner summaries and candidate selection -/

/-- Typed route family selected by the CEGA planner. -/
inductive PlannerRouteKind where
  /-- Direct side-condition-aware exact normalization. -/
  | exact
  /-- Dependency-preserving affine arithmetic on a finite coordinate chart. -/
  | affine
  /-- Correlation-preserving endpoint ranges for lowered hyperbolic functions. -/
  | hyperbolic
  /-- The conservative built-in easy pass: denominators, then unary ranges. -/
  | easy
deriving Repr, DecidableEq

/-- Untrusted computable snapshot used to compare candidates from different routes.

The canonical route builders keep `kind` aligned with the recorded interval
and step count. Freely constructed snapshots carry no theorem and must not be
used as certificate evidence.
-/
structure PlannerSummary where
  /-- Typed planner route family. -/
  kind : PlannerRouteKind
  /-- Well-formed interval computed by the route. -/
  interval : RationalInterval
  /-- Number of CEGA route steps used by the route. -/
  stepCount : Nat
deriving Repr

namespace PlannerSummary

/-- Largest absolute endpoint, used as a secondary enclosure-quality score. -/
def radiusScore (candidate : PlannerSummary) : ℚ :=
  candidate.interval.absMax

/-- Width of the enclosed interval, used as the primary route-quality score. -/
def widthScore (candidate : PlannerSummary) : ℚ :=
  candidate.interval.hi - candidate.interval.lo

/-- Lexicographic enclosure score: width, magnitude, then route length. -/
def enclosureScore (candidate : PlannerSummary) : ℚ ×ₗ (ℚ ×ₗ Nat) :=
  toLex
    (candidate.widthScore,
      toLex (candidate.radiusScore, candidate.stepCount))

/-- Does enclosure candidate `a` improve on `b`?

Enclosure selection minimizes width first, then the largest absolute endpoint,
and finally route length.
-/
def enclosureBetterThan (a b : PlannerSummary) : Bool :=
  a.enclosureScore < b.enclosureScore

/-- Select the sharpest labelled enclosure candidate. -/
def bestEnclosure? (candidates : List PlannerSummary) : Option PlannerSummary :=
  candidates.argmin enclosureScore

end PlannerSummary

namespace EnclosureAttempt

/-- The generic certificate given by the directly indexed enclosure theorem. -/
def cert {α : Type*} {s : Set α} {fn : α → ℝ}
    (a : EnclosureAttempt α s fn) : EnclosureCert α s :=
  EnclosureCert.ofEnclosedOn fn
    (a.interval.lo : ℝ) (a.interval.hi : ℝ) a.sound

/-- Restate an enclosure attempt using displayed rational endpoints. -/
theorem enclosedOn_of_interval_eq {α : Type*} {s : Set α} {fn : α → ℝ}
    (a : EnclosureAttempt α s fn)
    (lo hi : ℚ) (hlo : a.interval.lo = lo) (hhi : a.interval.hi = hi) :
    EnclosedOn fn s (lo : ℝ) (hi : ℝ) :=
  hlo ▸ hhi ▸ a.sound

/-- The displayed rational interval contains the indexed function on the attempt domain. -/
theorem memReal {α : Type*} {s : Set α} {fn : α → ℝ}
    (a : EnclosureAttempt α s fn) {x : α} (hx : x ∈ s) :
    a.interval.MemReal (fn x) :=
  a.sound x hx

/-- Forget the lower endpoint and retain the checked upper endpoint. -/
theorem boundOn {α : Type*} {s : Set α} {fn : α → ℝ}
    (a : EnclosureAttempt α s fn) :
    BoundOn fn s (a.interval.hi : ℝ) :=
  fun x hx ↦ (a.sound x hx).2

/-- Bound the function's magnitude by the largest absolute interval endpoint. -/
theorem boundOn_abs {α : Type*} {s : Set α} {fn : α → ℝ}
    (a : EnclosureAttempt α s fn) :
    BoundOn (fun x ↦ |fn x|) s (a.interval.absMax : ℝ) :=
  fun _ hx ↦ RationalInterval.abs_le_absMax (a.memReal hx)

/-- Approximate the function by the interval midpoint with the interval radius as error. -/
theorem approxOn_center {α : Type*} {s : Set α} {fn : α → ℝ}
    (a : EnclosureAttempt α s fn) :
    ApproxOn fn (fun _ ↦ (a.interval.center : ℝ)) s
      (a.interval.radius : ℝ) :=
  (RationalInterval.midpointApproxCert a.interval fun _ hx ↦ a.memReal hx).sound

/-- Restate the derived upper bound using a displayed rational endpoint. -/
theorem boundOn_of_interval_eq {α : Type*} {s : Set α} {fn : α → ℝ}
    (a : EnclosureAttempt α s fn)
    (upper : ℚ) (hupper : a.interval.hi = upper) :
    BoundOn fn s (upper : ℝ) :=
  hupper ▸ a.boundOn

/-- Restate the derived absolute bound using a displayed rational endpoint. -/
theorem boundOn_abs_of_interval_eq {α : Type*} {s : Set α} {fn : α → ℝ}
    (a : EnclosureAttempt α s fn)
    (upper : ℚ) (hupper : a.interval.absMax = upper) :
    BoundOn (fun x ↦ |fn x|) s (upper : ℝ) :=
  hupper ▸ a.boundOn_abs

/-- Restate the midpoint approximation using displayed rational data. -/
theorem approxOn_center_of_interval_eq {α : Type*} {s : Set α} {fn : α → ℝ}
    (a : EnclosureAttempt α s fn)
    (center radius : ℚ)
    (hcenter : a.interval.center = center)
    (hradius : a.interval.radius = radius) :
    ApproxOn fn (fun _ ↦ (center : ℝ)) s (radius : ℝ) :=
  hcenter ▸ hradius ▸ a.approxOn_center

/-- Transport an enclosure across pointwise equality on its certified domain. -/
def congr {α : Type*} {s : Set α} {f g : α → ℝ}
    (a : EnclosureAttempt α s f) (hfg : Set.EqOn g f s) :
    EnclosureAttempt α s g where
  interval := a.interval
  sound := by
    intro x hx
    rw [hfg hx]
    exact a.memReal hx
  steps := a.steps

/--
Glue two local enclosure attempts across a binary cover.

The output interval is the exact rational hull of the two local intervals.
The covering proof and local certificates, rather than the subdivision
heuristic, establish the global enclosure.
-/
def ofBinaryCover {α : Type*} {u s t : Set α} {fn : α → ℝ}
    (hcover : u ⊆ s ∪ t)
    (left : EnclosureAttempt α s fn) (right : EnclosureAttempt α t fn) :
    EnclosureAttempt α u fn where
  interval := left.interval.hull right.interval
  sound := by
    intro x hx
    rcases hcover hx with hx | hx
    · exact RationalInterval.memReal_hull_left (left.memReal hx)
    · exact RationalInterval.memReal_hull_right (right.memReal hx)
  steps := .boxSubdivision :: (left.steps ++ right.steps)

end EnclosureAttempt

namespace ResidualBoundAttempt

/-- The residual certificate given by the directly stored residual theorem. -/
def cert {α : Type*} {s : Set α} (a : ResidualBoundAttempt α s) :
    ResidualCert α ℝ s :=
  ResidualCert.ofResidualBound a.residual (a.interval.absMax : ℝ) a.sound

end ResidualBoundAttempt

end RationalInterval
end CAS.Continuum

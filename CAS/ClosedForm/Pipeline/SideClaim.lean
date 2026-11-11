/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.Core

/-!
# Checked symbolic claims

The proof object shared by the checked symbolic transformations. A `SideClaimRoute` records the
source and target expressions, the nonvanishing assumptions the transformation needs, and a
theorem that those assumptions imply equality of the two denotations. An unconditional
transformation is the special case with no assumptions.

## Main definitions

* `SideClaimRoute`: source, target, assumption list, the pass metadata `steps`, and soundness.
* `SideClaimRoute.exact`: the claim with no assumptions, built from a pointwise proof.
* `SideClaimRoute.trans`: the composition of two claims, with the joined assumption lists.

## Main results

* `SideClaimRoute.sound_of_nonzero_eq_nil`: a claim with an empty assumption list is an
  unconditional identity.
* `SideClaimRoute.eq_of_eval`: a claim as an identity of real terms, the form in which the
  simplification report states its result.

## Implementation notes

`SideClaimRoute` depends only on `Pipeline.Core`, not on the pipelines that build its values, so
consumers such as `Continuum.IntervalEval.AutoRange` and `Exact.RouteSemantics` import it
directly.

The `nonzero` list is read through `Alg.SideHolds`: every listed expression must evaluate to a
nonzero real. This is the only kind of assumption the list can express, so a pass that needs the
hypothesis `0 < a` records the entry `sqrt a`, since `Real.sqrt a ≠ 0` is equivalent to `0 < a`
(`Real.sqrt_ne_zero'`). The square-root cleanups `sqrtSquareCleanup` and
`sqrtProductCollectFactors`, the exp-log cleanup `expLogCleanup` and the real-power pass record
such entries, and the `#cas` output prints them as `a > 0`.
-/

@[expose] public section

namespace CAS.Verified.Expr

/-- A checked symbolic transformation with explicit nonzero assumptions.

The `sound` field shows that the generated assumptions are sufficient for the target and source
to have equal denotations. A transformation with no assumptions is a `SideClaimRoute` with
`nonzero = []`; see `SideClaimRoute.exact`. -/
structure SideClaimRoute (ι : Type*) where
  /-- Source expression. -/
  lhs : Verified.Expr ι
  /-- Target expression produced by the symbolic transformation. -/
  rhs : Verified.Expr ι
  /-- Nonzero assumptions required by the transformation, read through `Alg.SideHolds`. An
  entry `sqrt a` encodes the positivity obligation `0 < a`, since `Real.sqrt a ≠ 0 ↔ 0 < a`. -/
  nonzero : List (Verified.Expr ι)
  /-- Report metadata naming the configured passes that built the claim; empty by default. -/
  steps : List PassInfo := []
  /-- The pointwise equality certified by the claim: under the recorded assumptions the target
  and the source have equal denotations. -/
  sound : ∀ ρ : ι → ℝ, Alg.SideHolds ρ nonzero → rhs.eval ρ = lhs.eval ρ

namespace SideClaimRoute

/-- An unconditional checked claim: a transformation whose target and source evaluate equally
at every assignment, recorded with an empty assumption list. -/
def exact {ι : Type*} (lhs rhs : Verified.Expr ι)
    (proof : ∀ ρ : ι → ℝ, rhs.eval ρ = lhs.eval ρ) (steps : List PassInfo := []) :
    SideClaimRoute ι where
  lhs := lhs
  rhs := rhs
  nonzero := []
  steps := steps
  sound := fun ρ _ ↦ proof ρ

/-- An unconditional route retains the supplied source expression. -/
@[simp] theorem exact_lhs {ι : Type*} (lhs rhs : Verified.Expr ι)
    (proof : ∀ ρ : ι → ℝ, rhs.eval ρ = lhs.eval ρ) (steps : List PassInfo) :
    (exact lhs rhs proof steps).lhs = lhs :=
  rfl

/-- An unconditional route returns the supplied result expression. -/
@[simp] theorem exact_rhs {ι : Type*} (lhs rhs : Verified.Expr ι)
    (proof : ∀ ρ : ι → ℝ, rhs.eval ρ = lhs.eval ρ) (steps : List PassInfo) :
    (exact lhs rhs proof steps).rhs = rhs :=
  rfl

/-- An equality proved for every assignment needs no nonzero side conditions. -/
@[simp] theorem exact_nonzero {ι : Type*} (lhs rhs : Verified.Expr ι)
    (proof : ∀ ρ : ι → ℝ, rhs.eval ρ = lhs.eval ρ) (steps : List PassInfo) :
    (exact lhs rhs proof steps).nonzero = [] :=
  rfl

/-- An empty assumption list holds at every assignment. -/
theorem sideHolds_of_nonzero_eq_nil {ι : Type*} (claim : SideClaimRoute ι)
    (hnone : claim.nonzero = []) (ρ : ι → ℝ) :
    Alg.SideHolds ρ claim.nonzero := by
  simp [hnone, Alg.SideHolds]

/-- A claim with no assumptions is an identity of denotations at every assignment. -/
theorem sound_of_nonzero_eq_nil {ι : Type*} (claim : SideClaimRoute ι)
    (hnone : claim.nonzero = []) (ρ : ι → ℝ) :
    claim.rhs.eval ρ = claim.lhs.eval ρ :=
  claim.sound ρ (claim.sideHolds_of_nonzero_eq_nil hnone ρ)

/-- Compose two checked transformations whose intermediate expressions agree. -/
def trans {ι : Type*}
    (first second : SideClaimRoute ι) (hmid : second.lhs = first.rhs) :
    SideClaimRoute ι where
  lhs := first.lhs
  rhs := second.rhs
  nonzero := first.nonzero ++ second.nonzero
  steps := first.steps ++ second.steps
  sound := by
    intro ρ hside
    have hfirst := first.sound ρ
      (Alg.SideHolds.append_left
        (a := first.nonzero) (b := second.nonzero) hside)
    have hsecond := second.sound ρ
      (Alg.SideHolds.append_right
        (a := first.nonzero) (b := second.nonzero) hside)
    calc
      second.rhs.eval ρ = second.lhs.eval ρ := hsecond
      _ = first.rhs.eval ρ := by rw [hmid]
      _ = first.lhs.eval ρ := hfirst

/-- A checked route as an identity of real terms: when the route starts at `E`, a computation
shows that it ends at `D` with the recorded conditions `N`, the two expressions evaluate to `a`
and `b`, and the conditions hold, then `a = b`. -/
theorem eq_of_eval {ι : Type*} (route : SideClaimRoute ι) {E D : Verified.Expr ι}
    {N : List (Verified.Expr ι)} (hlhs : route.lhs = E)
    (hroute : route.rhs = D ∧ route.nonzero = N) (ρ : ι → ℝ) {a b : ℝ}
    (ha : E.eval ρ = a) (hb : D.eval ρ = b) (hside : Alg.SideHolds ρ N) : a = b := by
  have h := route.sound ρ (by rw [hroute.2]; exact hside)
  rw [hroute.1, hlhs, ha, hb] at h
  exact h.symm

end SideClaimRoute

end CAS.Verified.Expr

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.Subdivision

/-!
# Certified adaptive quadrature selection

Adaptive policy is separate from quadrature soundness.  A policy may
propose any alternative `QuadratureTree` for the same interval.  Lean then
selects the alternative with the lower proved error budget.  Since both
alternatives already carry `QuadratureCert` proofs, selection cannot invalidate
the root integral theorem.

`improveLeaves` applies a dependent refinement rule to every current leaf and
retains the better certified alternative locally.  Its main theorem proves that
the accumulated root error budget never increases.  The rule may come from a
tactic, an external adaptive driver or exact symbolic analysis; none of those
search mechanisms needs to be trusted.

`AdaptiveQuadrature.search` and `AdaptiveQuadrature.searchPartial` are the depth-bounded
bisection searches used by the panel rules: a panel is accepted once its proved error meets
the local tolerance, and otherwise it is halved and each child receives half the tolerance.

## Implementation notes

The acceptance test compares two real numbers, `tree.toCert.error ≤ tolerance`, so the searches
are noncomputable; they serve proofs and fix the semantics.
`RationalAdaptiveQuadrature.searchPartial` bisects at rational midpoints instead and accepts a
panel by comparing a rational error bound with a rational tolerance. A test that compares a
panel's value with the sum over its two halves estimates the error without bounding it; we accept
a panel only by its proved bound. Halving the tolerance at every split keeps the sum of the two
children's budgets within the parent's (`QuadratureTree.toCert_split_error`), so the result type
`QuadratureTree.WithErrorAtMost` carries the root bound. A panel that fails at depth zero gives
`none`, never an unchecked value.
-/

@[expose] public section

open MeasureTheory

namespace CAS.Continuum
namespace QuadratureTree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ → E} {a b : ℝ}

/--
Select the certified alternative with the lower error budget.

Ties retain `first`, making the choice stable.  This is a proof-level selector
over real error bounds; executable adaptive drivers may instead provide their
chosen tree directly and use the same soundness theorems.
-/
noncomputable def selectLowerError
    (first second : QuadratureTree f a b) :
    QuadratureTree f a b :=
  if first.toCert.error ≤ second.toCert.error then first else second

/-- Selection realizes the minimum of the two certified error budgets. -/
@[simp]
theorem selectLowerError_error
    (first second : QuadratureTree f a b) :
    (selectLowerError first second).toCert.error =
      min first.toCert.error second.toCert.error := by
  rw [min_def, selectLowerError]
  split_ifs <;> rfl

/-- Adaptive selection never has a larger budget than the first candidate. -/
theorem selectLowerError_error_le_first
    (first second : QuadratureTree f a b) :
    (selectLowerError first second).toCert.error ≤ first.toCert.error :=
  (selectLowerError_error first second).trans_le (min_le_left _ _)

/-- The selected tree retains an ordinary root quadrature-error theorem. -/
theorem selectLowerError_sound
    (first second : QuadratureTree f a b) :
    ‖(∫ x in a..b, f x) - (selectLowerError first second).toCert.value‖ ≤
      min first.toCert.error second.toCert.error :=
  (selectLowerError first second).sound.trans_eq (selectLowerError_error first second)

/--
A local quadrature-refinement rule.

The rule receives the accepted certificate and integrability evidence at one
leaf and proposes another quadrature tree for exactly the same endpoints.
-/
abbrev LeafRefiner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :=
  {a b : ℝ} →
    (cert : QuadratureCert f a b) →
    (integrable : IntervalIntegrable f volume a b) →
    QuadratureTree f a b

/--
Apply one refinement pass to every leaf, retaining the lower-error certified
alternative at each leaf.
-/
noncomputable def improveLeaves
    (refiner : LeafRefiner f) :
    {a b : ℝ} → QuadratureTree f a b → QuadratureTree f a b
  | _, _, .leaf cert integrable =>
      selectLowerError (.leaf cert integrable) (refiner cert integrable)
  | _, _, .split left right =>
      .split (improveLeaves refiner left) (improveLeaves refiner right)

/-- A leaf-refinement pass cannot increase the accumulated root error budget. -/
theorem improveLeaves_error_le
    (refiner : LeafRefiner f) (tree : QuadratureTree f a b) :
    (improveLeaves refiner tree).toCert.error ≤ tree.toCert.error := by
  induction tree with
  | leaf cert integrable => exact selectLowerError_error_le_first _ (refiner cert integrable)
  | split left right hleft hright => exact add_le_add hleft hright

end QuadratureTree

namespace AdaptiveQuadrature

variable {f : ℝ → ℝ}

/--
A checked local quadrature method on ordered subintervals of `s`.

The method may use any rule, derivative-bound backend, or local analytic
argument.  Adaptive bisection needs only the resulting certificate.
-/
abbrev PanelBuilderOn (f : ℝ → ℝ) (s : Set ℝ) :=
  {a b : ℝ} → a < b → Set.Icc a b ⊆ s → QuadratureCert f a b

/--
A fail-closed local quadrature method.

Returning `none` means that the current panel could not be certified. Adaptive
search may then bisect it and retry on smaller panels. Every successful result
is still an ordinary `QuadratureCert`; failure carries no fallback theorem.
-/
abbrev PartialPanelBuilderOn (f : ℝ → ℝ) (s : Set ℝ) :=
  {a b : ℝ} → a < b → Set.Icc a b ⊆ s → Option (QuadratureCert f a b)

/-- Turn one local certificate into a leaf of an adaptive tree. -/
def panel
    {s : Set ℝ} (build : PanelBuilderOn f s)
    (integrable :
      ∀ {a b : ℝ}, (hab : a < b) → Set.Icc a b ⊆ s →
        IntervalIntegrable f volume a b)
    {a b : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ s) :
    QuadratureTree f a b :=
  .leaf (build hab hsub) (integrable hab hsub)

/--
Depth-bounded adaptive bisection for a partial local quadrature method.

A panel is accepted only after its proved error is no larger than the local
tolerance, including at depth zero. If the builder returns `none` or the
certified error is too large, the panel is bisected only when depth remains;
each child receives half of the tolerance. At depth zero, failure to accept
the current panel returns `none`.
-/
noncomputable def searchPartial
    {s : Set ℝ} (build : PartialPanelBuilderOn f s)
    (integrable :
      ∀ {a b : ℝ}, (hab : a < b) → Set.Icc a b ⊆ s →
        IntervalIntegrable f volume a b) :
    (depth : ℕ) → (a b : ℝ) → (hab : a < b) →
      Set.Icc a b ⊆ s → (tolerance : ℝ) →
      Option (QuadratureTree.WithErrorAtMost f a b tolerance)
  | 0, a, b, hab, hsub, tolerance =>
      match build hab hsub with
      | none => none
      | some cert =>
          let tree : QuadratureTree f a b :=
            .leaf cert (integrable hab hsub)
          if h : tree.toCert.error ≤ tolerance then
            some ⟨tree, h⟩
          else
            none
  | depth + 1, a, b, hab, hsub, tolerance =>
      let subdivide (_ : Unit) :
          Option (QuadratureTree.WithErrorAtMost f a b tolerance) :=
        let midpoint := (a + b) / 2
        have hleft : a < midpoint := left_lt_add_div_two.mpr hab
        have hright : midpoint < b := add_div_two_lt_right.mpr hab
        match
            searchPartial build integrable depth a midpoint hleft
              ((Set.Icc_subset_Icc le_rfl hright.le).trans hsub)
              (tolerance / 2),
            searchPartial build integrable depth midpoint b hright
              ((Set.Icc_subset_Icc hleft.le le_rfl).trans hsub)
              (tolerance / 2) with
        | some left, some right =>
            some
              (QuadratureTree.WithErrorAtMost.mk
                (.split left.tree right.tree) (by
                  rw [QuadratureTree.toCert_split_error]
                  linarith [left.error_le, right.error_le]))
        | _, _ => none
      match build hab hsub with
      | none => subdivide ()
      | some cert =>
          let tree : QuadratureTree f a b :=
            .leaf cert (integrable hab hsub)
          if h : tree.toCert.error ≤ tolerance then
            some ⟨tree, h⟩
          else
            subdivide ()

/--
Depth-bounded adaptive search for a total local quadrature method.

This is the `some`-valued specialization of `searchPartial`; total and partial
builders therefore share one bisection and tolerance-allocation semantics.
-/
noncomputable def search
    {s : Set ℝ} (build : PanelBuilderOn f s)
    (integrable :
      ∀ {a b : ℝ}, (hab : a < b) → Set.Icc a b ⊆ s →
        IntervalIntegrable f volume a b) :
    (depth : ℕ) → (a b : ℝ) → (hab : a < b) →
      Set.Icc a b ⊆ s → (tolerance : ℝ) →
      Option (QuadratureTree.WithErrorAtMost f a b tolerance) :=
  searchPartial (fun hab hsub ↦ some (build hab hsub)) integrable

end AdaptiveQuadrature
end CAS.Continuum

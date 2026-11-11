/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.RationalAdaptiveSearch
public import CAS.Continuum.Quadrature.Subdivision

/-!
# Executable adaptive quadrature on rational meshes

Checked numerical backends need exact, computable panel endpoints.  The
real-endpoint search `AdaptiveQuadrature.searchPartial` is the right mathematical
interface for arbitrary local proofs, but recursively generated real
midpoints cannot in general be converted back to exact backend inputs.

The rational-mesh search uses the quadrature and subdivision semantics of the real one:

* every successful local result is the shared `RationalBudgetCandidate`,
  specialized to a quadrature-tree leaf;
* every accepted leaf stores a `QuadratureCert`;
* recursive composition uses `QuadratureTree`;
* the returned theorem is `QuadratureTree.WithErrorAtMost`.

The exact rational midpoint, tolerance splitting, stopping and failure behavior come from the
shared `RationalAdaptiveSystem`, which is also used by piecewise model refinement.
Thus any producer of local rational candidates, such as exact rational interval
evaluation, can run the same fail-closed adaptive search without exposing
numerical details to the analytic core.

## Implementation notes

`RationalAdaptiveQuadrature.system` instantiates `RationalAdaptiveSystem` with quadrature trees:
the result on `[a, b]` is a `QuadratureTree`, its error is the tree's proved budget, and two
children combine by `QuadratureTree.split`, whose budget is the sum
(`QuadratureTree.toCert_split_error`). The acceptance test of a local candidate is a Boolean on
rationals, so all control decisions are exact; the definition is still marked noncomputable
because the trees it returns carry real-valued certificates.
-/

@[expose] public section

open MeasureTheory Set

namespace CAS.Continuum.RationalAdaptiveQuadrature

variable {f : ℝ → ℝ}

/-- Quadrature-tree instance of the generic rational adaptive system. -/
noncomputable def system (f : ℝ → ℝ) : RationalAdaptiveSystem where
  Result := fun a b ↦ QuadratureTree f (a : ℝ) (b : ℝ)
  error := fun tree ↦ tree.toCert.error
  combine := fun left right ↦ .split left right
  error_combine_le := by
    intro _a _m _b left right
    rw [QuadratureTree.toCert_split_error]

/--
Depth-bounded, fail-closed quadrature search, implemented by the shared exact
rational adaptive kernel. The builder keeps rational endpoints while its
domain hypotheses and resulting quadrature tree use their real casts.
-/
noncomputable def searchPartial
    {s : Set ℝ} (build : (system f).PartialBuilderOn s)
    (depth : ℕ) (a b : ℚ) (hab : (a : ℝ) < (b : ℝ))
    (hsub : Icc (a : ℝ) (b : ℝ) ⊆ s) (tolerance : ℚ) :
    Option
      (QuadratureTree.WithErrorAtMost
        f (a : ℝ) (b : ℝ) (tolerance : ℝ)) :=
  match
      (system f).searchPartial
        build
        depth a b hab hsub tolerance with
  | none => none
  | some result =>
      some
        (QuadratureTree.WithErrorAtMost.mk result.result result.error_le)

end CAS.Continuum.RationalAdaptiveQuadrature

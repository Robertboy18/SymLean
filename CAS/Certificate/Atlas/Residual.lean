/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.Atlas.Basic
public import CAS.Certificate.Residual

/-!
# Residual certificate atlases

A `ResidualAtlasCert` holds a `ResidualCert` on every patch of a cover, all for the same
residual function and each with budget at most a global `eps`. `ResidualAtlasCert.sound`
assembles them into `ResidualBound residual domain eps` on the whole covered domain.

## Implementation notes

`sound` applies `PatchCover.lift` to the local `sound` proofs, rewriting each local residual to
the global one and weakening each local budget to `eps`. `toResidualCert` forgets the cover, and
CEGA receives residual atlases in that form. `ResidualAtlasCert.weightedSumOfCover` in
`CAS.Certificate.WeightedResidual` builds such atlases from weighted sums.
-/

@[expose] public section

namespace CAS.Certificate

open CAS.Domain

/-- Local residual certificates with one shared residual and global error budget. -/
abbrev ResidualAtlasCert (α E ι : Type*) [NormedAddCommGroup E]
    (domain : Set α) :=
  FunctionBudgetAtlasCert α E ι domain
    (ResidualCert α E) (fun cert ↦ cert.residual) (fun cert ↦ cert.eps)

namespace ResidualAtlasCert

variable {α E ι : Type*} [NormedAddCommGroup E] {domain : Set α}

/-- Global residual function assembled by the atlas. -/
abbrev residual (c : ResidualAtlasCert α E ι domain) : α → E :=
  c.fn

/-- Global residual error budget. -/
abbrev eps (c : ResidualAtlasCert α E ι domain) : ℝ :=
  c.budget

/-- Every local residual function agrees with the global residual. -/
theorem cert_residual (c : ResidualAtlasCert α E ι domain) (i : ι) :
    (c.onPatch i).residual = c.residual :=
  c.cert_fn i

/-- Every local residual budget is bounded by the global budget. -/
theorem cert_eps (c : ResidualAtlasCert α E ι domain) (i : ι) :
    (c.onPatch i).eps ≤ c.eps :=
  c.cert_budget i

/-- Build a residual atlas over an arbitrary patch cover. -/
def ofCover (cover : PatchCover α ι domain) (residual : α → E) (eps : ℝ)
    (certAt : (i : ι) → ResidualCert α E (cover.patch i))
    (cert_residual : ∀ i, (certAt i).residual = residual)
    (cert_eps : ∀ i, (certAt i).eps ≤ eps) :
    ResidualAtlasCert α E ι domain :=
  FunctionBudgetAtlasCert.ofCover
    cover residual eps certAt cert_residual cert_eps

/-- Assemble the local residual estimates on the covered domain. -/
theorem sound (c : ResidualAtlasCert α E ι domain) :
    ResidualBound c.residual domain c.eps :=
  c.cover.lift fun i y hy ↦ le_trans
    (by simpa [c.cert_residual i] using (c.onPatch i).sound y hy) (c.cert_eps i)

/-- Project an atlas to a global residual certificate. -/
def toResidualCert (c : ResidualAtlasCert α E ι domain) : ResidualCert α E domain :=
  ResidualCert.ofResidualBound c.residual c.eps c.sound

end ResidualAtlasCert

end CAS.Certificate

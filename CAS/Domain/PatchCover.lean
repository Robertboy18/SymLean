/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Data.Set.Basic

/-!
# Indexed domain covers

`PatchCover α ι domain` is a family of subsets indexed by `ι` together with a proof that
their union contains `domain`. It does not depend on any symbolic backend or certificate
type; the certificate atlases and the real-root atlases are built on it.

The constructors `restrict`, `binary`, `union`, and `bind` give restriction, binary
splitting, and hierarchical refinement. `PatchCover.lift` is the
elimination principle: a proposition proved on every patch holds on the covered domain.
-/

@[expose] public section

namespace CAS.Domain

/--
An indexed family of patches covering `domain`.

The patches may overlap. No finiteness or decidability assumption is imposed on
the index type because the structure records semantic coverage, not an
executable search strategy.
Patches need not be contained in `domain`; local hypotheses apply to each
whole patch, and `restrict` changes only the covered target domain.
-/
structure PatchCover (α ι : Type*) (domain : Set α) where
  /-- The local domains. -/
  patch : ι → Set α
  /-- Every point of the target domain belongs to some patch. -/
  covers : domain ⊆ fun x ↦ ∃ i, x ∈ patch i

namespace PatchCover

variable {α ι : Type*} {domain : Set α}

/-- Reuse a cover on a smaller target domain. -/
def restrict {subdomain : Set α} (cover : PatchCover α ι domain)
    (hsubset : subdomain ⊆ domain) :
    PatchCover α ι subdomain where
  patch := cover.patch
  covers := fun _ hx ↦ cover.covers (hsubset hx)

/--
Construct a two-patch cover.

The `true` patch is `left`, and the `false` patch is `right`.
-/
def binary {left right domain : Set α} (hcover : domain ⊆ left ∪ right) :
    PatchCover α Bool domain where
  patch := fun b ↦ if b then left else right
  covers := by
    intro x hx
    rcases hcover hx with hleft | hright
    · exact ⟨true, by simpa using hleft⟩
    · exact ⟨false, by simpa using hright⟩

/-- The canonical two-patch cover of `left ∪ right`. -/
def union (left right : Set α) : PatchCover α Bool (left ∪ right) :=
  binary (domain := left ∪ right) (left := left) (right := right) fun _ hx ↦ hx

/--
Refine every patch by a local cover.

The sigma index remembers both the original patch and the selected refinement.
-/
def bind {κ : ι → Type*} (cover : PatchCover α ι domain)
    (refine : (i : ι) → PatchCover α (κ i) (cover.patch i)) :
    PatchCover α (Sigma κ) domain where
  patch := fun ij ↦ (refine ij.1).patch ij.2
  covers := by
    intro x hx
    rcases cover.covers hx with ⟨i, hi⟩
    rcases (refine i).covers hi with ⟨j, hj⟩
    exact ⟨⟨i, j⟩, hj⟩

/-- Lift a proposition proved on every patch to the covered domain. -/
theorem lift {P : α → Prop} (cover : PatchCover α ι domain)
    (hlocal : ∀ i, ∀ x, x ∈ cover.patch i → P x) :
    ∀ x, x ∈ domain → P x := fun x hx ↦
  (cover.covers hx).elim fun i hi ↦ hlocal i x hi

end PatchCover

end CAS.Domain

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.RealRoot.Atlas
public import CAS.Polynomial.RealRoot.SturmSubdivision

/-!
# Root atlases from Sturm subdivisions

Every accepted subdivision leaf has exact root count zero or one. `toRootAtlas` turns those
leaves into the common `RootAtlas` interface: zero-count leaves are root-free regions and
one-count leaves are uniquely rooted regions (`leafRegion`, `leafRegion_valid`).
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Set
open CAS.Continuum

namespace SturmSubdivisionCertificate

/-- Leaf intervals of one accepted subdivision, carrying their membership proof. -/
abbrev LeafIndex (certificate : SturmSubdivisionCertificate) :=
  { leaf : RationalInterval // leaf ∈ certificate.subdivision.leaves }

/-- Sturm interval certificate for a leaf: the subdivision's chain, the leaf interval, and the
count computed as the chain's variation difference at the leaf endpoints. -/
def leafCertificate
    (certificate : SturmSubdivisionCertificate)
    (leaf : RationalInterval) : SturmIntervalCertificate where
  sturm := certificate.sturm
  interval := leaf
  count := certificate.sturm.variationDifference leaf.lo leaf.hi

/-- Classify an accepted leaf by its exact zero-or-one Sturm count. -/
def leafRegion (certificate : SturmSubdivisionCertificate)
    (leaf : RationalInterval) : Region :=
  let counted := certificate.leafCertificate leaf
  if counted.count = 0 then
    .countedFree counted
  else
    .countedRoot counted

/-- Both the root-containing and root-free leaf regions use the leaf's closed interval. -/
theorem leafRegion_domain
    (certificate : SturmSubdivisionCertificate)
    (leaf : RationalInterval) :
    (certificate.leafRegion leaf).domain =
      Icc (leaf.lo : ℝ) (leaf.hi : ℝ) := by
  unfold leafRegion
  dsimp only [leafCertificate]
  split <;> rfl

/-- A valid Sturm subdivision certifies each of its leaves as a region, including
the endpoint checks needed for the closed interval. -/
theorem leafRegion_valid
    {polynomial : Sparse.Univariate}
    (certificate : SturmSubdivisionCertificate)
    (hvalid : certificate.valid polynomial = true)
    (leaf : LeafIndex certificate) :
    (certificate.leafRegion leaf.1).valid polynomial = true := by
  have hsub := (Bool.and_eq_true_iff.mp hvalid).2
  obtain ⟨hlo, hhi⟩ : Sparse.evalRat polynomial leaf.1.lo ≠ 0 ∧
      Sparse.evalRat polynomial leaf.1.hi ≠ 0 :=
    (SturmSubdivision.leaf leaf.1).endpoints_nonzero_of_valid polynomial certificate.sturm
      (certificate.subdivision.leaf_valid_of_mem polynomial certificate.sturm hsub leaf.2)
  have hcounted : (certificate.leafCertificate leaf.1).valid polynomial = true := by
    simp [SturmIntervalCertificate.valid, leafCertificate, certificate.sturm_valid hvalid, hlo,
      hhi]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp
      (certificate.subdivision.leaf_count_le_one polynomial certificate.sturm hsub leaf.2) with
    h | h
  · have h' : (certificate.leafCertificate leaf.1).count = 0 := h
    simp [leafRegion, Region.valid, hcounted, h']
  · have h' : (certificate.leafCertificate leaf.1).count = 1 := h
    simp [leafRegion, Region.valid, hcounted, h']

/--
Convert an accepted Sturm subdivision to the common root-atlas abstraction.
-/
noncomputable def toRootAtlas
    {polynomial : Sparse.Univariate}
    (certificate : SturmSubdivisionCertificate)
    (hvalid : certificate.valid polynomial = true) :
    RootAtlas (LeafIndex certificate) polynomial
      (Icc (certificate.subdivision.interval.lo : ℝ)
        (certificate.subdivision.interval.hi : ℝ)) where
  region := fun leaf ↦ certificate.leafRegion leaf.1
  covers := by
    intro x hx
    have hparts := hvalid
    simp only [SturmSubdivisionCertificate.valid,
      Bool.and_eq_true] at hparts
    rcases certificate.subdivision.exists_leaf_of_mem
        polynomial certificate.sturm hparts.2 hx with
      ⟨leaf, hleaf, hxLeaf⟩
    exact
      ⟨⟨leaf, hleaf⟩,
        by simpa only [leafRegion_domain] using hxLeaf⟩
  valid := certificate.leafRegion_valid hvalid

end SturmSubdivisionCertificate

end CAS.Polynomial.RealRoot

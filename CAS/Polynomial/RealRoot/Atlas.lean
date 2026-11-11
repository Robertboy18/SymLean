/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.RealRoot.Interval
public import CAS.Polynomial.RealRoot.Radical
public import CAS.Polynomial.RealRoot.SturmInterval

/-!
# Complete real-root atlases

An atlas describes the real roots of a polynomial on a domain by regions, each classified by a
local certificate (`Region`) as

* root-free, by exact interval evaluation (`free`, checked by `rootFree`) or by a Sturm count of
  zero (`countedFree`);
* containing exactly one root, by an accepted monotone root bracket (`root`, a `RootBracket`) or
  by a Sturm count of one (`countedRoot`); or
* a region of a square-free radical with the same real roots (`equivalent`, with a
  `RadicalCertificate`).

`RootAtlas` glues those local certificates over an arbitrary domain. `GlobalRootAtlas`
additionally records the proof that this domain contains every real root.

## Implementation notes

`RootAtlas` stores the proof that its regions cover the domain (`RootAtlas.covers`) rather than a
`Domain.PatchCover`, which would be a second family of patches. The atlases of SymLean come from
Sturm subdivisions (`SturmSubdivisionCertificate.toRootAtlas`, with `countedFree` and
`countedRoot` regions), carried over to the original polynomial along a radical
(`RootAtlas.transportAlongRadical`) by `PolynomialIsolationCertificate.toRootAtlas` and
`GlobalPolynomialIsolationCertificate.toGlobalRootAtlas`. No module outside
`CAS/Polynomial/RealRoot` uses atlases; the root commands use the root lists of `RootList.lean`.
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Set
open CAS.Continuum
open CAS.Domain

/-- A locally certified real-root region. -/
inductive Region where
  | root (bracket : RootBracket)
  | free (interval : RationalInterval)
  | countedRoot (certificate : SturmIntervalCertificate)
  | countedFree (certificate : SturmIntervalCertificate)
  | equivalent (certificate : RadicalCertificate) (region : Region)
deriving DecidableEq

namespace Region

/-- The real interval represented by a root region. -/
def domain : Region → Set ℝ
  | .root bracket =>
      Icc (bracket.interval.lo : ℝ) (bracket.interval.hi : ℝ)
  | .free interval =>
      Icc (interval.lo : ℝ) (interval.hi : ℝ)
  | .countedRoot certificate =>
      Icc (certificate.interval.lo : ℝ) (certificate.interval.hi : ℝ)
  | .countedFree certificate =>
      Icc (certificate.interval.lo : ℝ) (certificate.interval.hi : ℝ)
  | .equivalent _ region => region.domain

/-- Exact local checker for a proposed region classification. -/
def valid (polynomial : Sparse.Univariate) : Region → Bool
  | .root bracket => bracket.valid polynomial
  | .free interval => rootFree polynomial interval
  | .countedRoot certificate =>
      certificate.valid polynomial && decide (certificate.count = 1)
  | .countedFree certificate =>
      certificate.valid polynomial && decide (certificate.count = 0)
  | .equivalent certificate region =>
      certificate.valid polynomial &&
        region.valid certificate.radical

/-- Whether a region is classified as containing exactly one root. -/
def hasRoot : Region → Bool
  | .root _ | .countedRoot _ => true
  | .free _ | .countedFree _ => false
  | .equivalent _ region => region.hasRoot

/-- Every valid region classified as root-free contains no root. -/
theorem nonzero_of_valid_nonroot (polynomial : Sparse.Univariate)
    (region : Region) (hvalid : region.valid polynomial = true)
    (hroot : region.hasRoot = false)
    {x : ℝ} (hx : x ∈ region.domain) :
    Sparse.evalReal polynomial x ≠ 0 := by
  cases region with
  | root _ | countedRoot _ => simp [hasRoot] at hroot
  | free interval => exact nonzeroOn_of_rootFree_eq_true polynomial interval hvalid x hx
  | countedFree certificate =>
      simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hvalid
      exact certificate.nonzeroOn polynomial hvalid.1 hvalid.2 x hx
  | equivalent certificate region =>
      simp only [valid, Bool.and_eq_true] at hvalid
      exact mt (certificate.evalReal_eq_zero_iff polynomial hvalid.1 x).mp
        (nonzero_of_valid_nonroot certificate.radical region hvalid.2 hroot hx)

end Region

/--
An atlas classifying every patch of `domain` as root-free or uniquely rooted.

The certified regions are the patches.  Storing the coverage theorem directly
avoids a second patch family and a coherence proof equating it with
`Region.domain`.
-/
structure RootAtlas (ι : Type*) (polynomial : Sparse.Univariate) (domain : Set ℝ) where
  /-- Root-count classification and local certificate assigned to each patch. -/
  region : ι → Region
  /-- Every point of the root-analysis domain belongs to a certified region. -/
  covers : domain ⊆ fun x ↦ ∃ i, x ∈ (region i).domain
  /-- Every local region passes its exact checker. -/
  valid : ∀ i, (region i).valid polynomial = true

namespace RootAtlas

variable {ι : Type*} {polynomial : Sparse.Univariate} {domain : Set ℝ}

/-- Every root in the covered domain lies in a certified unique-root region. -/
theorem root_mem_region (atlas : RootAtlas ι polynomial domain)
    {x : ℝ} (hxDomain : x ∈ domain)
    (hxRoot : Sparse.evalReal polynomial x = 0) :
    ∃ i,
      (atlas.region i).hasRoot = true ∧
        x ∈ (atlas.region i).domain := by
  obtain ⟨i, hi⟩ := atlas.covers hxDomain
  refine ⟨i, ?_, hi⟩
  by_contra hroot
  exact Region.nonzero_of_valid_nonroot polynomial _ (atlas.valid i)
    (Bool.eq_false_of_not_eq_true hroot) hi hxRoot

/--
Transport a root atlas along a checked equality of real zero sets.

The cover is unchanged.  Every local region is combined with the radical
certificate, so the theorems of the resulting atlas are about the original
polynomial.
-/
noncomputable def transportAlongRadical
    (certificate : RadicalCertificate)
    (hcertificate : certificate.valid polynomial = true)
    (atlas : RootAtlas ι certificate.radical domain) :
    RootAtlas ι polynomial domain where
  region := fun i ↦ .equivalent certificate (atlas.region i)
  covers := by
    intro x hx
    rcases atlas.covers hx with ⟨i, hi⟩
    exact ⟨i, hi⟩
  valid := by
    intro i
    simp only [Region.valid, Bool.and_eq_true]
    exact ⟨hcertificate, atlas.valid i⟩

end RootAtlas

/--
A complete real-root atlas over any proved domain containing every real root.
-/
structure GlobalRootAtlas (ι : Type*) (polynomial : Sparse.Univariate) where
  /-- Certified search domain proved to contain every real root. -/
  domain : Set ℝ
  /-- Local root classification covering `domain`. -/
  atlas : RootAtlas ι polynomial domain
  /-- Every real root lies in the search domain, so the local atlas misses no roots. -/
  containsRoots :
    ∀ {x : ℝ}, Sparse.evalReal polynomial x = 0 → x ∈ domain

namespace GlobalRootAtlas

variable {ι : Type*} {polynomial : Sparse.Univariate}

/-- Every real root belongs to one of the atlas's certified unique-root regions. -/
theorem root_mem_region (atlas : GlobalRootAtlas ι polynomial)
    {x : ℝ} (hxRoot : Sparse.evalReal polynomial x = 0) :
    ∃ i,
      (atlas.atlas.region i).hasRoot = true ∧
        x ∈ (atlas.atlas.region i).domain :=
  atlas.atlas.root_mem_region (atlas.containsRoots hxRoot) hxRoot

end GlobalRootAtlas

end CAS.Polynomial.RealRoot

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.RealRoot.IntervalNewton

/-!
# Interval Newton certificates for `x² - 2`

The first certificate proves that `[1, 2]` contains exactly one root of `x² - 2` and contracts it
to `[11/8, 23/16]`. The second proves that the same polynomial has no root in `[3, 4]` because its
checked Newton image is disjoint from that input interval. Both conclusions come from exact
rational certificate checks.
-/

@[expose] public section

namespace CAS.Examples.Numerics.IntervalNewton

open Set
open CAS
open CAS.Continuum
open CAS.Domain
open CAS.Polynomial
open CAS.Polynomial.RealRoot

/-- Sparse rational representation of `x² - 2`. -/
def sqrtTwoPolynomial : Sparse.Univariate :=
  [(1, Sparse.univariateMonomial 2), (-2, Sparse.univariateMonomial 0)]

/-- Sparse differentiation of `x² - 2` produces the single monomial `2x`. -/
theorem sqrtTwoPolynomial_derivativeRaw :
    Sparse.derivativeRaw sqrtTwoPolynomial =
      [(2, Sparse.univariateMonomial 1)] := by
  simp [sqrtTwoPolynomial, Sparse.derivativeRaw, Sparse.univariateMonomial,
    funext_iff]

/-- One interval-Newton contraction of `[1, 2]` toward the positive root of `x² - 2`. -/
def sqrtTwoCertificate : IntervalNewtonCertificate where
  interval := RationalInterval.ofBounds 1 2 (by norm_num)
  direction := .increasing
  image := RationalInterval.ofBounds (11 / 8) (23 / 16) (by norm_num)

/-- The derivative `2x` has enclosure `[2, 4]` on the initial interval `[1, 2]`. -/
theorem sqrtTwo_derivativeInterval :
    sqrtTwoCertificate.derivativeInterval sqrtTwoPolynomial =
      RationalInterval.ofBounds 2 4 (by norm_num) := by
  decide +kernel

/-- At the midpoint `3/2` of `[1, 2]`, the polynomial has value `1/4`. -/
theorem sqrtTwo_evalRat_center :
    Sparse.evalRat sqrtTwoPolynomial sqrtTwoCertificate.interval.center = 1 / 4 := by
  norm_num [sqrtTwoPolynomial, sqrtTwoCertificate, Sparse.evalRat,
    Sparse.univariateMonomial, RationalInterval.ofBounds,
    RationalInterval.center]

/-- Reciprocating the positive derivative enclosure gives `[1/4, 1/2]`. -/
theorem sqrtTwo_derivativeReciprocal :
    sqrtTwoCertificate.derivativeReciprocal sqrtTwoPolynomial =
      RationalInterval.ofBounds (1 / 4) (1 / 2) (by norm_num) := by
  have hsign : sqrtTwoCertificate.direction = .increasing := rfl
  simp [IntervalNewtonCertificate.derivativeReciprocal, hsign,
    sqrtTwo_derivativeInterval, RationalInterval.ofBounds]

/-- The interval Newton step `3/2 - (1/4) / [2, 4]` yields `[11/8, 23/16]`. -/
theorem sqrtTwo_computedImage :
    sqrtTwoCertificate.computedImage sqrtTwoPolynomial =
      sqrtTwoCertificate.image := by
  decide +kernel

/-- The proposed contraction is accepted by exact rational computation. -/
theorem sqrtTwoCertificate_valid :
    sqrtTwoCertificate.valid sqrtTwoPolynomial = true := by
  rw [IntervalNewtonCertificate.valid_eq_true_iff]
  refine ⟨by norm_num [sqrtTwoCertificate, RationalInterval.ofBounds], ?_, ?_⟩
  · have hsign : sqrtTwoCertificate.direction = .increasing := rfl
    simp [IntervalNewtonCertificate.derivativeAbsLower, hsign,
      sqrtTwo_derivativeInterval, RationalInterval.ofBounds]
  · exact sqrtTwo_computedImage.symm

/-- Exact endpoint signs and the valid Newton step certify one root in `[1, 2]`. -/
theorem sqrtTwoCertificate_isolatesRoot :
    sqrtTwoCertificate.isolatesRoot sqrtTwoPolynomial = true := by
  rw [IntervalNewtonCertificate.isolatesRoot, sqrtTwoCertificate_valid]
  norm_num [IntervalNewtonCertificate.BracketsRoot, sqrtTwoCertificate,
    sqrtTwoPolynomial, Sparse.evalRat, Sparse.univariateMonomial,
    RationalInterval.ofBounds]

/-- There is exactly one root of `x² - 2` in `[1, 2]`. -/
theorem sqrtTwo_existsUnique_root :
    ∃! x : ℝ,
      x ∈ Icc (1 : ℝ) 2 ∧
        Sparse.evalReal sqrtTwoPolynomial x = 0 := by
  simpa [sqrtTwoCertificate, RationalInterval.MemReal,
    RationalInterval.ofBounds] using
    sqrtTwoCertificate.existsUnique_root sqrtTwoPolynomial
      sqrtTwoCertificate_isolatesRoot

/-- Every root of `x² - 2` in `[1, 2]` lies in the contracted interval. -/
theorem sqrtTwo_root_mem_contraction {x : ℝ}
    (hx : x ∈ Icc (1 : ℝ) 2)
    (hroot : Sparse.evalReal sqrtTwoPolynomial x = 0) :
    x ∈ Icc (11 / 8 : ℝ) (23 / 16 : ℝ) := by
  have hx' : sqrtTwoCertificate.interval.MemReal x := by
    simpa [sqrtTwoCertificate, RationalInterval.MemReal,
      RationalInterval.ofBounds] using hx
  have hlocalized := sqrtTwoCertificate.root_mem_image sqrtTwoPolynomial
    sqrtTwoCertificate_valid hx' hroot
  simpa [sqrtTwoCertificate, RationalInterval.MemReal,
    RationalInterval.ofBounds] using hlocalized

/-- A disjoint interval-Newton image for `x² - 2` on `[3, 4]`. -/
def farCertificate : IntervalNewtonCertificate where
  interval := RationalInterval.ofBounds 3 4 (by norm_num)
  direction := .increasing
  image := RationalInterval.ofBounds (43 / 24) (71 / 32) (by norm_num)

/-- The derivative `2x` has enclosure `[6, 8]` on the exclusion interval `[3, 4]`. -/
theorem far_derivativeInterval :
    farCertificate.derivativeInterval sqrtTwoPolynomial =
      RationalInterval.ofBounds 6 8 (by norm_num) := by
  decide +kernel

/-- The Newton step `7/2 - (41/4) / [6, 8]` yields `[43/24, 71/32]`, left of `[3, 4]`. -/
theorem far_computedImage :
    farCertificate.computedImage sqrtTwoPolynomial = farCertificate.image := by
  decide +kernel

/-- Exact arithmetic verifies the nonzero derivative bound and the proposed Newton image. -/
theorem farCertificate_valid :
    farCertificate.valid sqrtTwoPolynomial = true := by
  rw [IntervalNewtonCertificate.valid_eq_true_iff]
  refine ⟨by norm_num [farCertificate, RationalInterval.ofBounds], ?_, ?_⟩
  · have hsign : farCertificate.direction = .increasing := rfl
    simp [IntervalNewtonCertificate.derivativeAbsLower, hsign,
      far_derivativeInterval, RationalInterval.ofBounds]
  · exact far_computedImage.symm

/-- Exact arithmetic accepts the root-exclusion certificate on `[3, 4]`. -/
theorem farCertificate_excludesRoots :
    farCertificate.excludesRoots sqrtTwoPolynomial = true := by
  unfold IntervalNewtonCertificate.excludesRoots
  rw [farCertificate_valid]
  norm_num [farCertificate, RationalInterval.ofBounds]

/-- The polynomial `x² - 2` is nonzero throughout `[3, 4]`. -/
theorem sqrtTwoPolynomial_nonzeroOn_far :
    NonzeroOn (Sparse.evalReal sqrtTwoPolynomial) (Icc (3 : ℝ) 4) :=
  farCertificate.nonzeroOn_of_excludesRoots_eq_true sqrtTwoPolynomial
    farCertificate_excludesRoots

end CAS.Examples.Numerics.IntervalNewton

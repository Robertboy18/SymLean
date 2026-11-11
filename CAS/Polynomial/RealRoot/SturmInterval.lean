/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.RealRoot.SturmTheorem
public import CAS.Continuum.Interval.Rational.Basic

/-!
# Counted real-root intervals

`SturmIntervalCertificate` combines one accepted Sturm chain with rational
endpoints and an expected exact root count, the number of distinct real roots in the open
interval (`rootSet_ncard`). Count zero proves that the closed interval is root-free
(`nonzeroOn`); count one proves that it contains a unique real root (`existsUnique_root`).

## Implementation notes

We check that the polynomial is nonzero at both endpoints, as Sturm's theorem
`SturmCertificate.variationDifference_eq_rootSet_ncard` requires. The variation difference
then counts the roots in the open interval, and the nonzero endpoints extend this to the
ordinary `Icc` statements used by the root atlases of `SturmAtlas.lean` (`Region.countedFree`
and `Region.countedRoot`).
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Set

/-- Exact Sturm evidence for the number of roots in one rational interval. -/
structure SturmIntervalCertificate where
  /-- Accepted Sturm chain used to compute endpoint sign variations. -/
  sturm : SturmCertificate
  /-- Rational interval whose endpoints are additionally checked to be nonroots. -/
  interval : CAS.Continuum.RationalInterval
  /-- Claimed number of roots, checked against the endpoint variation difference. -/
  count : Nat
deriving DecidableEq

namespace SturmIntervalCertificate

/-- Check the chain, non-root endpoints, and claimed exact variation count. -/
def valid (polynomial : Sparse.Univariate)
    (certificate : SturmIntervalCertificate) : Bool :=
  certificate.sturm.valid polynomial &&
    decide (Sparse.evalRat polynomial certificate.interval.lo ≠ 0) &&
    decide (Sparse.evalRat polynomial certificate.interval.hi ≠ 0) &&
    decide (certificate.sturm.variationDifference
      certificate.interval.lo certificate.interval.hi =
        certificate.count)

private theorem valid_components (polynomial : Sparse.Univariate)
    (certificate : SturmIntervalCertificate)
    (hvalid : certificate.valid polynomial = true) :
    certificate.sturm.valid polynomial = true ∧
      Sparse.evalRat polynomial certificate.interval.lo ≠ 0 ∧
      Sparse.evalRat polynomial certificate.interval.hi ≠ 0 ∧
      certificate.sturm.variationDifference
        certificate.interval.lo certificate.interval.hi =
          certificate.count := by
  simpa only [valid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hvalid

/-- The claimed count is the number of distinct real roots in the open interval `(lo, hi)`. -/
theorem rootSet_ncard (polynomial : Sparse.Univariate)
    (certificate : SturmIntervalCertificate)
    (hvalid : certificate.valid polynomial = true) :
    ((Sparse.toRealPolynomial polynomial).rootSet ℝ ∩
      Ioo (certificate.interval.lo : ℝ)
        (certificate.interval.hi : ℝ)).ncard =
      certificate.count := by
  obtain ⟨hsturm, hlo, hhi, hcount⟩ := certificate.valid_components polynomial hvalid
  exact hcount ▸ (certificate.sturm.variationDifference_eq_rootSet_ncard
    polynomial hsturm certificate.interval.hle hlo hhi).symm

private theorem polynomial_ne_zero (polynomial : Sparse.Univariate)
    (certificate : SturmIntervalCertificate)
    (hvalid : certificate.valid polynomial = true) :
    Sparse.toRealPolynomial polynomial ≠ 0 := by
  obtain ⟨-, hlo, -, -⟩ := certificate.valid_components polynomial hvalid
  intro hzero
  have h := Sparse.eval_toRealPolynomial polynomial certificate.interval.lo
  rw [hzero, Sparse.evalReal_ratCast] at h
  exact hlo (by simpa using h.symm)

private theorem endpoint_nonzero (polynomial : Sparse.Univariate)
    (certificate : SturmIntervalCertificate)
    (hvalid : certificate.valid polynomial = true) :
    Sparse.evalReal polynomial (certificate.interval.lo : ℝ) ≠ 0 ∧
      Sparse.evalReal polynomial (certificate.interval.hi : ℝ) ≠ 0 := by
  obtain ⟨-, hlo, hhi, -⟩ := certificate.valid_components polynomial hvalid
  simpa [Sparse.evalReal_ratCast] using And.intro hlo hhi

/-- A valid count-zero interval contains no real root, including endpoints. -/
theorem nonzeroOn (polynomial : Sparse.Univariate)
    (certificate : SturmIntervalCertificate)
    (hvalid : certificate.valid polynomial = true)
    (hcount : certificate.count = 0) :
    ∀ x ∈ Icc (certificate.interval.lo : ℝ)
        (certificate.interval.hi : ℝ),
      Sparse.evalReal polynomial x ≠ 0 := by
  have hempty : (Sparse.toRealPolynomial polynomial).rootSet ℝ ∩
      Ioo (certificate.interval.lo : ℝ) certificate.interval.hi = ∅ := by
    rw [← Set.ncard_eq_zero, certificate.rootSet_ncard polynomial hvalid, hcount]
  have hends := certificate.endpoint_nonzero polynomial hvalid
  intro x hx hroot
  exact hempty.subset ⟨(Polynomial.mem_rootSet_of_ne
      (certificate.polynomial_ne_zero polynomial hvalid)).mpr
        ((Sparse.evalReal_eq_zero_iff_isRoot polynomial x).mp hroot),
    hx.1.lt_of_ne fun h ↦ hends.1 (h ▸ hroot), hx.2.lt_of_ne fun h ↦ hends.2 (h ▸ hroot)⟩

/-- A valid count-one interval contains exactly one real root. -/
theorem existsUnique_root (polynomial : Sparse.Univariate)
    (certificate : SturmIntervalCertificate)
    (hvalid : certificate.valid polynomial = true)
    (hcount : certificate.count = 1) :
    ∃! x : ℝ,
      x ∈ Icc (certificate.interval.lo : ℝ)
          (certificate.interval.hi : ℝ) ∧
        Sparse.evalReal polynomial x = 0 := by
  obtain ⟨root, hroots⟩ :=
    Set.ncard_eq_one.mp ((certificate.rootSet_ncard polynomial hvalid).trans hcount)
  have hp := certificate.polynomial_ne_zero polynomial hvalid
  have hends := certificate.endpoint_nonzero polynomial hvalid
  have hroot : root ∈ (Sparse.toRealPolynomial polynomial).rootSet ℝ ∩
      Ioo (certificate.interval.lo : ℝ) certificate.interval.hi := hroots ▸ rfl
  refine ⟨root, ⟨Ioo_subset_Icc_self hroot.2, ?_⟩, fun y hy ↦ ?_⟩
  · rw [← Sparse.eval_toRealPolynomial]
    exact (Polynomial.mem_rootSet_of_ne hp).mp hroot.1
  · have hyMem : y ∈ (Sparse.toRealPolynomial polynomial).rootSet ℝ ∩
        Ioo (certificate.interval.lo : ℝ) certificate.interval.hi :=
      ⟨(Polynomial.mem_rootSet_of_ne hp).mpr
          ((Sparse.evalReal_eq_zero_iff_isRoot polynomial y).mp hy.2),
        hy.1.1.lt_of_ne fun h ↦ hends.1 (h ▸ hy.2), hy.1.2.lt_of_ne fun h ↦ hends.2 (h ▸ hy.2)⟩
    rwa [hroots] at hyMem

end SturmIntervalCertificate

end CAS.Polynomial.RealRoot

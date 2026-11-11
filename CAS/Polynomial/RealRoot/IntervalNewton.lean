/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalRefinement
public import CAS.Polynomial.RealRoot.Interval

/-!
# One-dimensional interval Newton certificates

One checked interval-Newton step for a sparse rational polynomial. An `IntervalNewtonCertificate`
names an input interval, the sign of the derivative enclosure, and the proposed Newton image. The
exact checker `valid` verifies that:

* the input interval has nonempty interior;
* the interval extension of the derivative is bounded strictly away from zero; and
* the proposed image is exactly the interval-Newton image computed from the midpoint.

Every root in the input interval belongs to the checked Newton image (`root_mem_image`).
Consequently, disjoint input and image intervals certify root exclusion
(`nonzeroOn_of_excludesRoots_eq_true`). The additional endpoint-sign check `isolatesRoot` proves
that the input interval contains exactly one root (`existsUnique_root`); the localization theorem
then places that root in the Newton image. All statements are relative to the input interval.

## Implementation notes

For the input interval `X` with midpoint `m`, the image is `m - p(m) / P'(X)`. Here `P'(X)` is
the termwise interval extension `evalInterval` of the derivative over `X`, and the quotient uses
the reciprocal interval selected by the claimed sign (`derivativeReciprocal`). The image is
computed exactly in rational arithmetic and is not intersected with `X`. A root `x` lies in it
because the mean value theorem gives `p(m) = p'(z) (m - x)` for some `z` in `X`
(`exists_hasDerivAt_eq_slope`). The certificates are used only by the example
`CAS/Examples/Numerics/IntervalNewton.lean`.

## References

* Ramon E. Moore, *Interval Analysis*, Prentice-Hall, Englewood Cliffs, N.J., 1966,
  <https://zbmath.org/?q=an:0176.13301>. For interval Newton methods.
* Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud, *Introduction to Interval Analysis*,
  SIAM, Philadelphia, 2009, <https://doi.org/10.1137/1.9780898717716>. Chapter 8, "Interval
  Newton Methods", pp. 105-128, <https://doi.org/10.1137/1.9780898717716.ch8>.
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Set
open CAS.Continuum
open CAS.Domain

/-- Proof-free proposal for one checked interval-Newton step. -/
structure IntervalNewtonCertificate where
  /-- Closed rational interval on which roots are being localized. -/
  interval : RationalInterval
  /-- Claimed monotonicity direction, checked through the derivative enclosure. -/
  direction : Direction
  /-- Proposed interval-Newton image, checked against exact rational computation. -/
  image : RationalInterval
deriving DecidableEq

namespace IntervalNewtonCertificate

/-- Interval extension of the polynomial derivative over the input interval. -/
def derivativeInterval (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate) : RationalInterval :=
  evalInterval (Sparse.derivativeRaw polynomial) certificate.interval

/-- Positive lower bound proposed for the absolute derivative. -/
def derivativeAbsLower (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate) : ℚ :=
  match certificate.direction with
  | .increasing => (certificate.derivativeInterval polynomial).lo
  | .decreasing => -(certificate.derivativeInterval polynomial).hi

/-- Reciprocal interval selected from the claimed derivative sign. -/
def derivativeReciprocal (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate) : RationalInterval :=
  let derivative := certificate.derivativeInterval polynomial
  match certificate.direction with
  | .increasing =>
      if h : 0 < derivative.lo then
        { lo := 1 / derivative.hi
          hi := 1 / derivative.lo
          hle := one_div_le_one_div_of_le h derivative.hle }
      else
        RationalInterval.const 0
  | .decreasing =>
      if h : derivative.hi < 0 then
        { lo := 1 / derivative.hi
          hi := 1 / derivative.lo
          hle := by
            have hpositive : 0 < -derivative.hi := neg_pos.mpr h
            have hnegated : -derivative.hi ≤ -derivative.lo :=
              neg_le_neg derivative.hle
            have hinverse : 1 / (-derivative.lo) ≤ 1 / (-derivative.hi) :=
              one_div_le_one_div_of_le hpositive hnegated
            have hnegInverse :
                -(1 / (-derivative.hi)) ≤ -(1 / (-derivative.lo)) :=
              neg_le_neg hinverse
            simpa [one_div, inv_neg] using hnegInverse }
      else
        RationalInterval.const 0

/-- Exact interval-Newton image computed from the midpoint and derivative enclosure. -/
def computedImage (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate) : RationalInterval :=
  let center := certificate.interval.center
  let value := RationalInterval.const (Sparse.evalRat polynomial center)
  RationalInterval.sub (RationalInterval.const center)
    (RationalInterval.mul value (certificate.derivativeReciprocal polynomial))

/-- Mathematical obligations checked for one interval-Newton proposal. -/
def Valid (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate) : Prop :=
  certificate.interval.lo < certificate.interval.hi ∧
    0 < certificate.derivativeAbsLower polynomial ∧
    certificate.image = certificate.computedImage polynomial

/-- `Decidable` for `certificate.Valid polynomial`, by unfolding `Valid` and inferring the instance
for its rational comparisons and the equality of intervals. -/
instance (polynomial : Sparse.Univariate) (certificate : IntervalNewtonCertificate) :
    Decidable (certificate.Valid polynomial) := by
  unfold Valid
  infer_instance

/-- Exact Boolean checker for an interval-Newton proposal. -/
def valid (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate) : Bool :=
  decide (certificate.Valid polynomial)

/-- The executable checker accepts exactly the stated mathematical obligations. -/
theorem valid_eq_true_iff (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate) :
    certificate.valid polynomial = true ↔ certificate.Valid polynomial := by
  simp [valid]

private theorem valid_components (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate)
    (hvalid : certificate.valid polynomial = true) :
    certificate.interval.lo < certificate.interval.hi ∧
      0 < certificate.derivativeAbsLower polynomial ∧
      certificate.image = certificate.computedImage polynomial :=
  (certificate.valid_eq_true_iff polynomial).mp hvalid

/-- The rational midpoint of a valid step lies in the open input interval. -/
theorem center_mem_interior (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate)
    (hvalid : certificate.valid polynomial = true) :
    (certificate.interval.center : ℝ) ∈
      Ioo (certificate.interval.lo : ℝ) (certificate.interval.hi : ℝ) := by
  have hproper := (certificate.valid_components polynomial hvalid).1
  simp only [mem_Ioo, Rat.cast_lt, RationalInterval.center]
  constructor <;> linarith

private theorem center_mem (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate)
    (hvalid : certificate.valid polynomial = true) :
    certificate.interval.MemReal (certificate.interval.center : ℝ) :=
  ⟨(certificate.center_mem_interior polynomial hvalid).1.le,
    (certificate.center_mem_interior polynomial hvalid).2.le⟩

/-- A valid derivative enclosure supplies the proposed positive lower bound on the absolute
derivative. -/
theorem derivativeAbsLower_le_abs (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate)
    (hvalid : certificate.valid polynomial = true)
    {x : ℝ} (hx : certificate.interval.MemReal x) :
    (certificate.derivativeAbsLower polynomial : ℝ) ≤
      |Sparse.evalReal (Sparse.derivativeRaw polynomial) x| := by
  have hbound := evalInterval_sound (Sparse.derivativeRaw polynomial) hx
  have hlower := (certificate.valid_components polynomial hvalid).2.1
  cases hsign : certificate.direction with
  | increasing =>
      simp only [derivativeAbsLower, hsign] at hlower ⊢
      rw [abs_of_pos ((Rat.cast_pos.mpr hlower).trans_le hbound.1)]
      exact hbound.1
  | decreasing =>
      simp only [derivativeAbsLower, hsign] at hlower ⊢
      rw [abs_of_neg (hbound.2.trans_lt (Rat.cast_lt_zero.mpr (neg_pos.mp hlower)))]
      exact_mod_cast neg_le_neg hbound.2

/-- The derivative of a valid interval-Newton step cannot vanish on its input interval. -/
theorem derivative_ne_zero (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate)
    (hvalid : certificate.valid polynomial = true)
    {x : ℝ} (hx : certificate.interval.MemReal x) :
    Sparse.evalReal (Sparse.derivativeRaw polynomial) x ≠ 0 := by
  have hpositive : (0 : ℝ) < certificate.derivativeAbsLower polynomial := by
    exact_mod_cast (certificate.valid_components polynomial hvalid).2.1
  exact abs_pos.mp (hpositive.trans_le (certificate.derivativeAbsLower_le_abs polynomial hvalid hx))

private theorem derivativeReciprocal_sound (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate)
    (hvalid : certificate.valid polynomial = true)
    {x : ℝ} (hx : certificate.interval.MemReal x) :
    (certificate.derivativeReciprocal polynomial).MemReal
      (Sparse.evalReal (Sparse.derivativeRaw polynomial) x)⁻¹ := by
  have hbound := evalInterval_sound (Sparse.derivativeRaw polynomial) hx
  have hlower := (certificate.valid_components polynomial hvalid).2.1
  cases hsign : certificate.direction with
  | increasing =>
      have hlo : 0 < (certificate.derivativeInterval polynomial).lo := by
        simpa [derivativeAbsLower, hsign] using hlower
      have hloReal : (0 : ℝ) < (certificate.derivativeInterval polynomial).lo := by
        exact_mod_cast hlo
      simp only [derivativeReciprocal, hsign, dite_eq_left hlo]
      constructor
      · simpa [derivativeInterval] using inv_anti₀ (hloReal.trans_le hbound.1) hbound.2
      · simpa using inv_anti₀ hloReal hbound.1
  | decreasing =>
      have hhi : (certificate.derivativeInterval polynomial).hi < 0 :=
        neg_pos.mp (by simpa [derivativeAbsLower, hsign] using hlower)
      have hhiReal : ((certificate.derivativeInterval polynomial).hi : ℝ) < 0 := by
        exact_mod_cast hhi
      simp only [derivativeReciprocal, hsign, dite_eq_left hhi]
      constructor
      · simpa using one_div_le_one_div_of_neg_of_le hhiReal hbound.2
      · simpa [derivativeInterval] using
          one_div_le_one_div_of_neg_of_le (hbound.2.trans_lt hhiReal) hbound.1

private theorem exists_secant_derivative (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate)
    (hvalid : certificate.valid polynomial = true)
    {x : ℝ} (hx : certificate.interval.MemReal x)
    (hroot : Sparse.evalReal polynomial x = 0) :
    ∃ z : ℝ,
      certificate.interval.MemReal z ∧
        Sparse.evalReal polynomial (certificate.interval.center : ℝ) =
          Sparse.evalReal (Sparse.derivativeRaw polynomial) z *
            ((certificate.interval.center : ℝ) - x) := by
  have hcenter := certificate.center_mem polynomial hvalid
  rcases lt_trichotomy x certificate.interval.center with hxc | rfl | hcx
  · obtain ⟨z, hz, hslope⟩ := exists_hasDerivAt_eq_slope _ _ hxc
      (Sparse.continuous_evalReal polynomial).continuousOn
      fun y _ ↦ Sparse.hasDerivAt_evalRealRaw polynomial y
    refine ⟨z, ⟨hx.1.trans hz.1.le, hz.2.le.trans hcenter.2⟩, ?_⟩
    rw [eq_div_iff (sub_ne_zero.mpr hxc.ne'), hroot, sub_zero] at hslope
    exact hslope.symm
  · exact ⟨_, hcenter, by simp [hroot]⟩
  · obtain ⟨z, hz, hslope⟩ := exists_hasDerivAt_eq_slope _ _ hcx
      (Sparse.continuous_evalReal polynomial).continuousOn
      fun y _ ↦ Sparse.hasDerivAt_evalRealRaw polynomial y
    refine ⟨z, ⟨hcenter.1.trans hz.1.le, hz.2.le.trans hx.2⟩, ?_⟩
    rw [eq_div_iff (sub_ne_zero.mpr hcx.ne'), hroot, zero_sub] at hslope
    linear_combination hslope

/-- Every root in the input interval belongs to the checked interval-Newton image. -/
theorem root_mem_image (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate)
    (hvalid : certificate.valid polynomial = true)
    {x : ℝ} (hx : certificate.interval.MemReal x)
    (hroot : Sparse.evalReal polynomial x = 0) :
    certificate.image.MemReal x := by
  obtain ⟨z, hz, hsecant⟩ := certificate.exists_secant_derivative polynomial hvalid hx hroot
  have hderivativeNonzero := certificate.derivative_ne_zero polynomial hvalid hz
  have hsub := RationalInterval.sub_sound
    (RationalInterval.memReal_const certificate.interval.center)
    (RationalInterval.mul_sound
      (RationalInterval.memReal_const (Sparse.evalRat polynomial certificate.interval.center))
      (certificate.derivativeReciprocal_sound polynomial hvalid hz))
  rw [← Sparse.evalReal_ratCast, hsecant, mul_comm, inv_mul_cancel_left₀ hderivativeNonzero,
    sub_sub_cancel] at hsub
  rw [(certificate.valid_components polynomial hvalid).2.2]
  exact hsub

/-- Endpoint signs that bracket a root in the direction certified for the derivative. -/
def BracketsRoot (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate) : Prop :=
  match certificate.direction with
  | .increasing =>
      Sparse.evalRat polynomial certificate.interval.lo ≤ 0 ∧
        0 ≤ Sparse.evalRat polynomial certificate.interval.hi
  | .decreasing =>
      0 ≤ Sparse.evalRat polynomial certificate.interval.lo ∧
        Sparse.evalRat polynomial certificate.interval.hi ≤ 0

/-- `Decidable` for `certificate.BracketsRoot polynomial`, by unfolding `BracketsRoot`, splitting on
the certified direction and inferring the instance for the rational comparisons. -/
instance (polynomial : Sparse.Univariate) (certificate : IntervalNewtonCertificate) :
    Decidable (certificate.BracketsRoot polynomial) := by
  unfold BracketsRoot
  cases certificate.direction <;> infer_instance

/--
Exact check that a valid interval-Newton step also has endpoint signs bracketing a root.

The endpoint condition supplies existence by the intermediate value theorem. The derivative
condition already checked by `valid` supplies uniqueness on the input interval.
-/
def isolatesRoot (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate) : Bool :=
  certificate.valid polynomial && decide (certificate.BracketsRoot polynomial)

/-- The root-isolation checker accepts exactly a valid Newton step and a root bracket. -/
theorem isolatesRoot_eq_true_iff (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate) :
    certificate.isolatesRoot polynomial = true ↔
      certificate.Valid polynomial ∧ certificate.BracketsRoot polynomial := by
  simp [isolatesRoot, valid_eq_true_iff]

private def rootBracket (certificate : IntervalNewtonCertificate) : RootBracket where
  interval := certificate.interval
  direction := certificate.direction

private theorem rootBracket_valid (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate)
    (hvalid : certificate.isolatesRoot polynomial = true) :
    certificate.rootBracket.valid polynomial = true := by
  rw [RootBracket.valid_eq_true_iff]
  obtain ⟨⟨-, hderivative, -⟩, hbracket⟩ :=
    (certificate.isolatesRoot_eq_true_iff polynomial).mp hvalid
  have hlo := enclosure_lo_pos_of_evalInterval (Sparse.derivativeRaw polynomial)
    certificate.interval
  have hhi := enclosure_hi_neg_of_evalInterval (Sparse.derivativeRaw polynomial)
    certificate.interval
  cases hdirection : certificate.direction <;>
    simp_all [rootBracket, RootBracket.Valid, BracketsRoot, derivativeAbsLower, derivativeInterval]

/--
An accepted isolating interval-Newton certificate has exactly one root in its input interval.

Uniqueness is relative to the input interval. `root_mem_image` separately localizes this root to
the checked Newton image, and no conclusion is made about roots outside the input interval.
-/
theorem existsUnique_root (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate)
    (hvalid : certificate.isolatesRoot polynomial = true) :
    ∃! x : ℝ,
      certificate.interval.MemReal x ∧
        Sparse.evalReal polynomial x = 0 := by
  simpa [rootBracket, RationalInterval.MemReal] using
    certificate.rootBracket.existsUnique_root polynomial
      (certificate.rootBracket_valid polynomial hvalid)

/-- Exact test that the Newton image is disjoint from the input interval. -/
def excludesRoots (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate) : Bool :=
  certificate.valid polynomial &&
    decide (certificate.image.hi < certificate.interval.lo ∨
      certificate.interval.hi < certificate.image.lo)

/-- An accepted disjoint interval-Newton image proves root exclusion on the input interval. -/
theorem nonzeroOn_of_excludesRoots_eq_true (polynomial : Sparse.Univariate)
    (certificate : IntervalNewtonCertificate)
    (hvalid : certificate.excludesRoots polynomial = true) :
    NonzeroOn (Sparse.evalReal polynomial)
      (Icc (certificate.interval.lo : ℝ) (certificate.interval.hi : ℝ)) := by
  simp only [excludesRoots, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  intro x hx hroot
  have hxImage := certificate.root_mem_image polynomial hvalid.1 hx hroot
  rcases hvalid.2 with hleft | hright
  · exact (not_lt_of_ge hx.1) (hxImage.2.trans_lt (Rat.cast_lt.mpr hleft))
  · exact (not_lt_of_ge hxImage.1) (hx.2.trans_lt (Rat.cast_lt.mpr hright))

end IntervalNewtonCertificate

end CAS.Polynomial.RealRoot

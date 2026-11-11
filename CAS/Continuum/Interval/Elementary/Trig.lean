/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Arithmetic
public import CAS.Continuum.Interval.Rational.DyadicHull
public import CAS.Continuum.IntervalRefinement
public import FloatLib.Numerics.Enclosure.Interval.ElementaryProof

/-!
# Sine and cosine enclosures from FloatLib

`sinBase` and `cosBase` are FloatLib's sine and cosine enclosures (period reduction and a
midpoint Lipschitz bound), rounded outward to a 128-bit dyadic grid. They are sharpened by
intersecting with enclosures built from the values at the two endpoints when the panel is
certified to lie where those values control the range: `[-π/2, π/2]` or `[0, π]` for sine,
`[0, π]`, `[-π, 0]` or a panel around zero inside `[-π, π]` for cosine, or any panel on which
the enclosure of the derivative has one sign. On `[0, π]` the sine range is clamped to be
nonnegative, and on `[-π/2, π/2]` so is the cosine range.

## Main definitions

* `sinBase`, `cosBase`: the FloatLib enclosures.
* `sinMonotoneBase`, `cosMonotoneBase`: their intersections with the endpoint enclosures.
* `RationalInterval.sin`, `RationalInterval.cos`: the enclosures used by interval evaluation.

## Main results

* `sin_sound`, `cos_sound`: `I.sin` contains `Real.sin x` and `I.cos` contains `Real.cos x` for
  every `x ∈ I`.

## Implementation notes

FloatLib's `Interval.sinBounds` and `Interval.cosBounds` use that sine and cosine are
1-Lipschitz: they enclose the value at the midpoint of `I`, widen it by the half-width and
intersect with `[-1, 1]`. A midpoint of absolute value at most `4` goes straight into the Taylor
polynomial (DLMF 4.19.1, 4.19.2) with its remainder bound. A larger one is first reduced by an
integer multiple of a rational approximation of `2π` taken from FloatLib's Machin enclosure of
`π / 4`, and the error of that approximation times the number of turns enters the radius.
FloatLib proves the remainder bounds with Mathlib's Taylor theorem.

The midpoint bound overestimates the range by about the width of `I`, also where the function is
monotone. The sharpening is ours: on a monotone branch, certified by rational comparisons with
`piInterval.lo`, or wherever FloatLib's enclosure of the derivative has one sign, the point
enclosures at the two endpoints bound the range by Mathlib's monotonicity lemmas, and we
intersect them with FloatLib's enclosure.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>.
* NIST Digital Library of Mathematical Functions, §4.19 Maclaurin Series and Laurent Series,
  Version 1.2.8 (2026-09-15), <https://dlmf.nist.gov/4.19>. Equations (4.19.1) and (4.19.2), the
  series of `sin z` and `cos z`.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

/-- A shared real value proves the rational endpoint condition required by `intersect`. -/
theorem intersectable_of_common_mem
    {I J : RationalInterval} {x : ℝ}
    (hxI : I.MemReal x) (hxJ : J.MemReal x) :
    max I.lo J.lo ≤ min I.hi J.hi := by
  exact_mod_cast (max_le hxI.1 hxJ.1).trans (le_min hxI.2 hxJ.2)


/-- FloatLib's enclosure of `Real.sin` on `I`, rounded outward to a 128-bit grid. -/
def sinBase (I : RationalInterval) : RationalInterval :=
  dyadicHull 128
    (ofFloatLib (FloatLib.Numerics.Interval.sinBounds I.toFloatLib 32)
      (ordered_of_containsReal (FloatLib.Numerics.Interval.containsReal_sinBounds
        I.toFloatLib 32 ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal))))

/-- `sinBase I` contains `Real.sin x` for every `x ∈ I`. -/
theorem sinBase_sound {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (sinBase I).MemReal (Real.sin x) := by
  apply dyadicHull_sound
  apply (memReal_ofFloatLib_iff _ _ _).mpr
  exact FloatLib.Numerics.Interval.containsReal_sinBounds I.toFloatLib 32
    ((I.toFloatLib_containsReal_iff x).mpr hx)

/-- FloatLib's enclosure of `Real.sin q` at a rational point. -/
def sinPoint (q : ℚ) : RationalInterval := sinBase (const q)

/-- `sinPoint q` contains `Real.sin q`. -/
theorem sinPoint_sound (q : ℚ) : (sinPoint q).MemReal (Real.sin (q : ℝ)) :=
  sinBase_sound (memReal_const q)

/-- FloatLib's enclosure of `Real.cos` on `I`, rounded outward to a 128-bit grid. -/
def cosBase (I : RationalInterval) : RationalInterval :=
  dyadicHull 128
    (ofFloatLib (FloatLib.Numerics.Interval.cosBounds I.toFloatLib 32)
      (ordered_of_containsReal (FloatLib.Numerics.Interval.containsReal_cosBounds
        I.toFloatLib 32 ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal))))

/-- `cosBase I` contains `Real.cos x` for every `x ∈ I`. -/
theorem cosBase_sound {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (cosBase I).MemReal (Real.cos x) := by
  apply dyadicHull_sound
  apply (memReal_ofFloatLib_iff _ _ _).mpr
  exact FloatLib.Numerics.Interval.containsReal_cosBounds I.toFloatLib 32
    ((I.toFloatLib_containsReal_iff x).mpr hx)

/-- FloatLib's enclosure of `Real.cos q` at a rational point. -/
def cosPoint (q : ℚ) : RationalInterval := cosBase (const q)

/-- `cosPoint q` contains `Real.cos q`. -/
theorem cosPoint_sound (q : ℚ) : (cosPoint q).MemReal (Real.cos (q : ℝ)) :=
  cosBase_sound (memReal_const q)

private theorem memReal_hull_of_derivative_sign
    {f f' : ℝ → ℝ} (I : RationalInterval) (hderiv : ∀ y, HasDerivAt f (f' y) y)
    {J K D : RationalInterval}
    (hleft : J.MemReal (f I.lo)) (hright : K.MemReal (f I.hi))
    (hD : ∀ y, I.MemReal y → D.MemReal (f' y))
    (hsign : 0 ≤ D.lo ∨ D.hi ≤ 0) {x : ℝ} (hx : I.MemReal x) :
    (J.hull K).MemReal (f x) := by
  have hcont : ContinuousOn f (Set.Icc (I.lo : ℝ) I.hi) :=
    fun y _ ↦ (hderiv y).continuousAt.continuousWithinAt
  rcases hsign with hnonneg | hnonpos
  · have hmono : MonotoneOn f (Set.Icc (I.lo : ℝ) I.hi) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hcont
        (fun y _ ↦ (hderiv y).hasDerivWithinAt)
        (fun y hy ↦ (by exact_mod_cast hnonneg : (0 : ℝ) ≤ D.lo).trans
          (hD y (show y ∈ Set.Icc (I.lo : ℝ) I.hi from interior_subset hy)).1)
    exact ⟨(memReal_hull_left (J := K) hleft).1.trans
        (hmono I.lo_memReal hx hx.1),
      (hmono hx I.hi_memReal hx.2).trans (memReal_hull_right (I := J) hright).2⟩
  · have hanti : AntitoneOn f (Set.Icc (I.lo : ℝ) I.hi) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hcont
        (fun y _ ↦ (hderiv y).hasDerivWithinAt)
        (fun y hy ↦
          (hD y (show y ∈ Set.Icc (I.lo : ℝ) I.hi from interior_subset hy)).2.trans
          (by exact_mod_cast hnonpos : (D.hi : ℝ) ≤ 0))
    exact ⟨(memReal_hull_right (I := J) hright).1.trans
        (hanti hx I.hi_memReal hx.2),
      (hanti I.lo_memReal hx hx.1).trans (memReal_hull_left (J := K) hleft).2⟩

/-- A certified constant derivative sign lets the endpoint bounds enclose sine on the panel. -/
theorem sin_signed_endpoint_sound (I : RationalInterval)
    (hsign : 0 ≤ (cosBase I).lo ∨ (cosBase I).hi ≤ 0)
    {x : ℝ} (hx : I.MemReal x) :
    ((sinPoint I.lo).hull (sinPoint I.hi)).MemReal (Real.sin x) :=
  memReal_hull_of_derivative_sign I Real.hasDerivAt_sin
    (sinPoint_sound I.lo) (sinPoint_sound I.hi)
    (fun _ hy ↦ cosBase_sound hy) hsign hx

/-- A certified constant derivative sign lets the endpoint bounds enclose cosine on the panel. -/
theorem cos_signed_endpoint_sound (I : RationalInterval)
    (hsign : 0 ≤ (sinBase I).neg.lo ∨ (sinBase I).neg.hi ≤ 0)
    {x : ℝ} (hx : I.MemReal x) :
    ((cosPoint I.lo).hull (cosPoint I.hi)).MemReal (Real.cos x) :=
  memReal_hull_of_derivative_sign I Real.hasDerivAt_cos
    (cosPoint_sound I.lo) (cosPoint_sound I.hi)
    (fun _ hy ↦ neg_sound (sinBase_sound hy)) hsign hx

/-- The rational midpoint, cast to a real, belongs to its closed interval. -/
theorem center_memReal (I : RationalInterval) : I.MemReal (I.center : ℝ) := by
  have h : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.hle
  constructor <;> simp only [center] <;> push_cast <;> linarith

/-- The rational branch test places every panel member in sine's monotonicity interval. -/
theorem mem_sin_principal {I : RationalInterval} {x : ℝ}
    (hprincipal : -(piInterval.lo / 2) ≤ I.lo ∧ I.hi ≤ piInterval.lo / 2)
    (hx : I.MemReal x) : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hpi : ((piInterval.lo : ℚ) : ℝ) ≤ Real.pi := piInterval_sound.1
  have hlo : -((piInterval.lo : ℝ) / 2) ≤ I.lo := by exact_mod_cast hprincipal.1
  have hhi : (I.hi : ℝ) ≤ (piInterval.lo : ℝ) / 2 := by exact_mod_cast hprincipal.2
  constructor <;> linarith [hx.1, hx.2]

/-- The rational branch test places every panel member in cosine's antitone branch `[0, π]`. -/
theorem mem_cos_principal {I : RationalInterval} {x : ℝ}
    (hprincipal : 0 ≤ I.lo ∧ I.hi ≤ piInterval.lo)
    (hx : I.MemReal x) : x ∈ Set.Icc 0 Real.pi := by
  have hpi : ((piInterval.lo : ℚ) : ℝ) ≤ Real.pi := piInterval_sound.1
  have hlo : (0 : ℝ) ≤ I.lo := by exact_mod_cast hprincipal.1
  have hhi : (I.hi : ℝ) ≤ piInterval.lo := by exact_mod_cast hprincipal.2
  constructor <;> linarith [hx.1, hx.2]

/-- Endpoint enclosure for sine on its principal monotonicity interval. -/
def sinEndpoint (I : RationalInterval)
    (hprincipal : -(piInterval.lo / 2) ≤ I.lo ∧ I.hi ≤ piInterval.lo / 2) :
    RationalInterval where
  lo := (sinPoint I.lo).lo
  hi := (sinPoint I.hi).hi
  hle := by
    have hmono : Real.sin (I.lo : ℝ) ≤ Real.sin (I.hi : ℝ) :=
      Real.monotoneOn_sin
        (mem_sin_principal hprincipal I.lo_memReal)
        (mem_sin_principal hprincipal I.hi_memReal)
        (by exact_mod_cast I.hle)
    exact_mod_cast (sinPoint_sound I.lo).1.trans (hmono.trans (sinPoint_sound I.hi).2)

/-- On sine's increasing principal branch, the endpoint certificates enclose the whole panel. -/
theorem sinEndpoint_sound {I : RationalInterval} {x : ℝ}
    (hprincipal : -(piInterval.lo / 2) ≤ I.lo ∧ I.hi ≤ piInterval.lo / 2)
    (hx : I.MemReal x) :
    (sinEndpoint I hprincipal).MemReal (Real.sin x) := by
  constructor
  · exact (sinPoint_sound I.lo).1.trans <|
      Real.monotoneOn_sin
        (mem_sin_principal hprincipal I.lo_memReal)
        (mem_sin_principal hprincipal hx) hx.1
  · exact (Real.monotoneOn_sin
        (mem_sin_principal hprincipal hx)
        (mem_sin_principal hprincipal I.hi_memReal) hx.2).trans
      (sinPoint_sound I.hi).2

/-- Endpoint enclosure for cosine on the branch where it is antitone. -/
def cosEndpoint (I : RationalInterval)
    (hprincipal : 0 ≤ I.lo ∧ I.hi ≤ piInterval.lo) : RationalInterval where
  lo := (cosPoint I.hi).lo
  hi := (cosPoint I.lo).hi
  hle := by
    have hanti : Real.cos (I.hi : ℝ) ≤ Real.cos (I.lo : ℝ) :=
      Real.antitoneOn_cos
        (mem_cos_principal hprincipal I.lo_memReal)
        (mem_cos_principal hprincipal I.hi_memReal)
        (by exact_mod_cast I.hle)
    exact_mod_cast (cosPoint_sound I.hi).1.trans (hanti.trans (cosPoint_sound I.lo).2)

/-- On `[0, π]`, the right endpoint bounds cosine below and the left endpoint bounds it above. -/
theorem cosEndpoint_sound {I : RationalInterval} {x : ℝ}
    (hprincipal : 0 ≤ I.lo ∧ I.hi ≤ piInterval.lo)
    (hx : I.MemReal x) :
    (cosEndpoint I hprincipal).MemReal (Real.cos x) := by
  constructor
  · exact (cosPoint_sound I.hi).1.trans <|
      Real.antitoneOn_cos
        (mem_cos_principal hprincipal hx)
        (mem_cos_principal hprincipal I.hi_memReal) hx.2
  · exact (Real.antitoneOn_cos
        (mem_cos_principal hprincipal I.lo_memReal)
        (mem_cos_principal hprincipal hx) hx.1).trans
      (cosPoint_sound I.lo).2

/-- Negating a panel certified inside `[-π, 0]` satisfies the rational test for `[0, π]`. -/
theorem neg_mem_cos_principal (I : RationalInterval)
    (hprincipal : -piInterval.lo ≤ I.lo ∧ I.hi ≤ 0) :
    0 ≤ I.neg.lo ∧ I.neg.hi ≤ piInterval.lo := by
  simp only [neg_lo, neg_hi]
  constructor <;> linarith [hprincipal.1, hprincipal.2]

/-- Endpoint enclosure for cosine on the negative principal branch, transported by evenness. -/
def cosNegativeEndpoint (I : RationalInterval)
    (hprincipal : -piInterval.lo ≤ I.lo ∧ I.hi ≤ 0) : RationalInterval :=
  cosEndpoint I.neg (neg_mem_cos_principal I hprincipal)

/-- Evenness transports the positive-branch cosine enclosure to a panel inside `[-π, 0]`. -/
theorem cosNegativeEndpoint_sound {I : RationalInterval} {x : ℝ}
    (hprincipal : -piInterval.lo ≤ I.lo ∧ I.hi ≤ 0)
    (hx : I.MemReal x) :
    (cosNegativeEndpoint I hprincipal).MemReal (Real.cos x) := by
  simpa [cosNegativeEndpoint, Real.cos_neg] using
    cosEndpoint_sound (neg_mem_cos_principal I hprincipal) (neg_sound hx)

/-- Endpoint enclosure for a cosine panel crossing zero inside `[-π, π]`. -/
def cosCrossZeroEndpoint (I : RationalInterval)
    (_hprincipal : -piInterval.lo ≤ I.lo ∧ I.lo ≤ 0 ∧
      0 ≤ I.hi ∧ I.hi ≤ piInterval.lo) : RationalInterval where
  lo := min (cosPoint I.lo).lo (cosPoint I.hi).lo
  hi := 1
  hle := by
    have hleft := (cosPoint_sound I.lo).1
    have hupper := Real.cos_le_one (I.lo : ℝ)
    have hreal :
        ((min (cosPoint I.lo).lo (cosPoint I.hi).lo : ℚ) : ℝ) ≤ 1 := by
      rw [Rat.cast_min]
      exact (min_le_left _ _).trans (hleft.trans hupper)
    exact_mod_cast hreal

/-- On a panel crossing zero inside `[-π, π]`, cosine is bounded below by the endpoint
certificates and above by `1`. -/
theorem cosCrossZeroEndpoint_sound {I : RationalInterval} {x : ℝ}
    (hprincipal : -piInterval.lo ≤ I.lo ∧ I.lo ≤ 0 ∧
      0 ≤ I.hi ∧ I.hi ≤ piInterval.lo)
    (hx : I.MemReal x) :
    (cosCrossZeroEndpoint I hprincipal).MemReal (Real.cos x) := by
  have hpi : ((piInterval.lo : ℚ) : ℝ) ≤ Real.pi := piInterval_sound.1
  have hlo : -(piInterval.lo : ℝ) ≤ I.lo := by exact_mod_cast hprincipal.1
  have hhi : (I.hi : ℝ) ≤ piInterval.lo := by exact_mod_cast hprincipal.2.2.2
  refine ⟨?_, by simpa [cosCrossZeroEndpoint] using Real.cos_le_one x⟩
  change ((min (cosPoint I.lo).lo (cosPoint I.hi).lo : ℚ) : ℝ) ≤ Real.cos x
  rw [Rat.cast_min]
  rcases le_total 0 x with hx0 | hx0
  · exact (min_le_right _ _).trans <| (cosPoint_sound I.hi).1.trans <|
      Real.cos_le_cos_of_nonneg_of_le_pi hx0 (by linarith) hx.2
  · have hanti := Real.cos_le_cos_of_nonneg_of_le_pi (neg_nonneg.mpr hx0)
      (by linarith : -(I.lo : ℝ) ≤ Real.pi) (neg_le_neg hx.1)
    rw [Real.cos_neg, Real.cos_neg] at hanti
    exact (min_le_left _ _).trans ((cosPoint_sound I.lo).1.trans hanti)

/-- Endpoint lower bound on sine's nonnegative arch, including panels crossing its maximum. -/
def sinPositiveEndpoint (I : RationalInterval)
    (_hprincipal : 0 ≤ I.lo ∧ I.hi ≤ piInterval.lo) : RationalInterval where
  lo := min (sinPoint I.lo).lo (sinPoint I.hi).lo
  hi := 1
  hle := by
    have hreal : ((min (sinPoint I.lo).lo (sinPoint I.hi).lo : ℚ) : ℝ) ≤ 1 := by
      rw [Rat.cast_min]
      exact (min_le_left _ _).trans ((sinPoint_sound I.lo).1.trans (Real.sin_le_one _))
    exact_mod_cast hreal

/-- Sine's two monotone branches give an endpoint lower bound throughout `[0, π]`. -/
theorem sinPositiveEndpoint_sound {I : RationalInterval} {x : ℝ}
    (hprincipal : 0 ≤ I.lo ∧ I.hi ≤ piInterval.lo) (hx : I.MemReal x) :
    (sinPositiveEndpoint I hprincipal).MemReal (Real.sin x) := by
  have hlo : (0 : ℝ) ≤ I.lo := by exact_mod_cast hprincipal.1
  have hhi : (I.hi : ℝ) ≤ Real.pi :=
    (show (I.hi : ℝ) ≤ (piInterval.lo : ℝ) by exact_mod_cast hprincipal.2).trans
      piInterval_sound.1
  constructor
  · change ((min (sinPoint I.lo).lo (sinPoint I.hi).lo : ℚ) : ℝ) ≤ Real.sin x
    rw [Rat.cast_min]
    by_cases hpeak : x ≤ Real.pi / 2
    · exact (min_le_left _ _).trans ((sinPoint_sound I.lo).1.trans
        (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hpeak hx.1))
    · have hsin : Real.sin (Real.pi - I.hi) ≤ Real.sin (Real.pi - x) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [Real.pi_pos]) (by linarith) (by linarith [hx.2])
      rw [Real.sin_pi_sub, Real.sin_pi_sub] at hsin
      exact (min_le_right _ _).trans ((sinPoint_sound I.hi).1.trans hsin)
  · simpa [sinPositiveEndpoint] using Real.sin_le_one x

/-- Intersect the sine Lipschitz enclosure with a monotone endpoint enclosure when available. -/
def sinMonotoneBase (I : RationalInterval) : RationalInterval :=
  if hprincipal : -(piInterval.lo / 2) ≤ I.lo ∧ I.hi ≤ piInterval.lo / 2 then
    (sinBase I).intersect (sinEndpoint I hprincipal)
      (intersectable_of_common_mem
        (sinBase_sound (center_memReal I))
        (sinEndpoint_sound hprincipal (center_memReal I)))
  else if hpositive : 0 ≤ I.lo ∧ I.hi ≤ piInterval.lo then
    (sinBase I).intersect (sinPositiveEndpoint I hpositive)
      (intersectable_of_common_mem
        (sinBase_sound I.lo_memReal) (sinPositiveEndpoint_sound hpositive I.lo_memReal))
  else if hsign : 0 ≤ (cosBase I).lo ∨ (cosBase I).hi ≤ 0 then
    (sinBase I).intersect ((sinPoint I.lo).hull (sinPoint I.hi))
      (intersectable_of_common_mem
        (sinBase_sound I.lo_memReal) (sin_signed_endpoint_sound I hsign I.lo_memReal))
  else
    sinBase I

private theorem sinMonotoneBase_sound {I : RationalInterval} {x : ℝ}
    (hx : I.MemReal x) :
    (sinMonotoneBase I).MemReal (Real.sin x) := by
  unfold sinMonotoneBase
  split_ifs with hprincipal hpositive hsign
  · exact intersect_sound _ (sinBase_sound hx) (sinEndpoint_sound hprincipal hx)
  · exact intersect_sound _ (sinBase_sound hx) (sinPositiveEndpoint_sound hpositive hx)
  · exact intersect_sound _ (sinBase_sound hx) (sin_signed_endpoint_sound I hsign hx)
  · exact sinBase_sound hx

/-- Intersect the cosine Lipschitz enclosure with its antitone endpoint enclosure when available. -/
def cosMonotoneBase (I : RationalInterval) : RationalInterval :=
  if hprincipal : 0 ≤ I.lo ∧ I.hi ≤ piInterval.lo then
    (cosBase I).intersect (cosEndpoint I hprincipal)
      (intersectable_of_common_mem
        (cosBase_sound (center_memReal I))
        (cosEndpoint_sound hprincipal (center_memReal I)))
  else if hnegative : -piInterval.lo ≤ I.lo ∧ I.hi ≤ 0 then
    (cosBase I).intersect (cosNegativeEndpoint I hnegative)
      (intersectable_of_common_mem
        (cosBase_sound (center_memReal I))
        (cosNegativeEndpoint_sound hnegative (center_memReal I)))
  else if hcross : -piInterval.lo ≤ I.lo ∧ I.lo ≤ 0 ∧
      0 ≤ I.hi ∧ I.hi ≤ piInterval.lo then
    (cosBase I).intersect (cosCrossZeroEndpoint I hcross)
      (intersectable_of_common_mem
        (cosBase_sound (center_memReal I))
        (cosCrossZeroEndpoint_sound hcross (center_memReal I)))
  else if hsign : 0 ≤ (sinBase I).neg.lo ∨ (sinBase I).neg.hi ≤ 0 then
    (cosBase I).intersect ((cosPoint I.lo).hull (cosPoint I.hi))
      (intersectable_of_common_mem
        (cosBase_sound I.lo_memReal) (cos_signed_endpoint_sound I hsign I.lo_memReal))
  else
    cosBase I

private theorem cosMonotoneBase_sound {I : RationalInterval} {x : ℝ}
    (hx : I.MemReal x) :
    (cosMonotoneBase I).MemReal (Real.cos x) := by
  unfold cosMonotoneBase
  split_ifs with hprincipal hnegative hcross hsign
  · exact intersect_sound _ (cosBase_sound hx) (cosEndpoint_sound hprincipal hx)
  · exact intersect_sound _ (cosBase_sound hx) (cosNegativeEndpoint_sound hnegative hx)
  · exact intersect_sound _ (cosBase_sound hx) (cosCrossZeroEndpoint_sound hcross hx)
  · exact intersect_sound _ (cosBase_sound hx) (cos_signed_endpoint_sound I hsign hx)
  · exact cosBase_sound hx

/-- Raise an interval's lower endpoint to zero when its upper endpoint is nonnegative. -/
def clampNonnegative (I : RationalInterval) (hhi : 0 ≤ I.hi) : RationalInterval where
  lo := max I.lo 0
  hi := I.hi
  hle := max_le I.hle hhi

private theorem clampNonnegative_sound {I : RationalInterval} {x : ℝ}
    (hhi : 0 ≤ I.hi) (hx : I.MemReal x) (hxnonneg : 0 ≤ x) :
    (clampNonnegative I hhi).MemReal x :=
  ⟨by exact_mod_cast max_le hx.1 hxnonneg, hx.2⟩

/-- On the nonnegative sine branch, the upper endpoint permits clamping the lower one to zero. -/
theorem sinMonotoneBase_hi_nonneg (I : RationalInterval)
    (hprincipal : 0 ≤ I.lo ∧ I.hi ≤ piInterval.lo) :
    0 ≤ (sinMonotoneBase I).hi := by
  have hle : (I.lo : ℝ) ≤ piInterval.lo := by exact_mod_cast I.hle.trans hprincipal.2
  exact_mod_cast (Real.sin_nonneg_of_nonneg_of_le_pi (by exact_mod_cast hprincipal.1)
    (hle.trans piInterval_sound.1)).trans (sinMonotoneBase_sound I.lo_memReal).2

/-- On the nonnegative cosine branch, the upper endpoint permits clamping the lower one to zero. -/
theorem cosMonotoneBase_hi_nonneg (I : RationalInterval)
    (hprincipal : -(piInterval.lo / 2) ≤ I.lo ∧ I.hi ≤ piInterval.lo / 2) :
    0 ≤ (cosMonotoneBase I).hi := by
  have hpi : ((piInterval.lo : ℚ) : ℝ) ≤ Real.pi := piInterval_sound.1
  have hlo : -((piInterval.lo : ℝ) / 2) ≤ I.lo := by exact_mod_cast hprincipal.1
  have hhi : (I.lo : ℝ) ≤ (piInterval.lo : ℝ) / 2 := by exact_mod_cast I.hle.trans hprincipal.2
  exact_mod_cast (Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)).trans
    (cosMonotoneBase_sound I.lo_memReal).2

/--
The sine enclosure of a rational interval: `sinMonotoneBase I`, with its lower endpoint raised to
`0` when `I` is certified to lie in `[0, π]`.
-/
def sin (I : RationalInterval) : RationalInterval :=
  if hprincipal : 0 ≤ I.lo ∧ I.hi ≤ piInterval.lo then
    clampNonnegative (sinMonotoneBase I) (sinMonotoneBase_hi_nonneg I hprincipal)
  else
    sinMonotoneBase I

/--
The cosine enclosure of a rational interval: `cosMonotoneBase I`, with its lower endpoint raised
to `0` when `I` is certified to lie in `[-π / 2, π / 2]`.
-/
def cos (I : RationalInterval) : RationalInterval :=
  if hprincipal : -(piInterval.lo / 2) ≤ I.lo ∧ I.hi ≤ piInterval.lo / 2 then
    clampNonnegative (cosMonotoneBase I) (cosMonotoneBase_hi_nonneg I hprincipal)
  else
    cosMonotoneBase I

/-- `I.sin` contains `Real.sin x` for every `x ∈ I`. -/
theorem sin_sound {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    I.sin.MemReal (Real.sin x) := by
  unfold sin
  split_ifs with hprincipal
  · have hlo : (0 : ℝ) ≤ I.lo := by exact_mod_cast hprincipal.1
    have hhi : (I.hi : ℝ) ≤ piInterval.lo := by exact_mod_cast hprincipal.2
    exact clampNonnegative_sound _ (sinMonotoneBase_sound hx)
      (Real.sin_nonneg_of_nonneg_of_le_pi (hlo.trans hx.1)
        (hx.2.trans (hhi.trans piInterval_sound.1)))
  · exact sinMonotoneBase_sound hx

/-- `I.cos` contains `Real.cos x` for every `x ∈ I`. -/
theorem cos_sound {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    I.cos.MemReal (Real.cos x) := by
  unfold cos
  split_ifs with hprincipal
  · have hpi : ((piInterval.lo : ℚ) : ℝ) ≤ Real.pi := piInterval_sound.1
    have hlo : -((piInterval.lo : ℝ) / 2) ≤ I.lo := by exact_mod_cast hprincipal.1
    have hhi : (I.hi : ℝ) ≤ (piInterval.lo : ℝ) / 2 := by exact_mod_cast hprincipal.2
    exact clampNonnegative_sound _ (cosMonotoneBase_sound hx)
      (Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hx.1]) (by linarith [hx.2]))
  · exact cosMonotoneBase_sound hx

end RationalInterval
end CAS.Continuum

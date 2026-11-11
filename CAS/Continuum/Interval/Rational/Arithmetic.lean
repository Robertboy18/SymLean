/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Basic

/-!
# Rational interval arithmetic through FloatLib

Addition, negation, subtraction, multiplication, natural powers and reciprocals of rational
intervals are FloatLib's exact rational interval operations with the endpoint-order proof of
`RationalInterval` attached. With exact rational rounding these operations always succeed. The
reciprocal `invPositive` and the quotient `divPositive` require a denominator with positive lower
endpoint. `divByAbsLower I δ` encloses `x / y` for `x ∈ I` and every `y` with `δ ≤ |y|`: it
widens the numerator to `[-absMax, absMax]` and divides by `δ`.

## Main results

* `add_sound`, `neg_sound`, `sub_sound`, `mul_sound`, `powNat_sound`: the inclusion property of
  interval arithmetic, for example `x ∈ I` and `y ∈ J` imply `x * y ∈ I.mul J`.
* `invPositive_sound`, `divPositive_sound`, `divByAbsLower_sound`: the same for reciprocals and
  quotients under the stated conditions on the denominator.
* `add_lo`, `mul_lo`, `invPositive_hi` and the other endpoint `simp` lemmas.

## Implementation notes

The endpoint formulas are the classical ones of Rump, (5.4) and (5.5): endpoint sums and
differences for `add` and `sub`, and the minimum and maximum of the four endpoint products for
`mul`. FloatLib proves the inclusion theorems for `add`, `neg`, `sub`, `mul` and `powNat`, and
we translate its `ContainsReal` into `MemReal`. The reciprocal is proved here, from its endpoint
formulas and the antitonicity of `y ↦ y⁻¹` on the positive reals. `divByAbsLower` is ours. It
gives up the sharp quotient for a symmetric enclosure that needs only a lower bound `δ ≤ |y|`,
which `positiveAbsLower` and `negativeAbsLower` supply for a denominator interval that excludes
zero.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>.
* Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud, *Introduction to Interval Analysis*,
  SIAM, Philadelphia, 2009, <https://doi.org/10.1137/1.9780898717716>. Chapter 2, The Interval
  Number System.
* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Section 5.1 for the operations, Section 5.5 for the inclusion property (5.16).
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open FloatLib.Numerics.Interval

local notation "rounding" => FloatLib.Numerics.Interval.Internal.rationalOutwardRounding

/-- Interval addition computed by FloatLib's exact rational backend. -/
def add (I J : RationalInterval) : RationalInterval :=
  ofFloatLib ((add? rounding I.toFloatLib J.toFloatLib).get (by rfl))
    (ordered_of_containsReal (containsReal_add? rounding rfl
      ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal)
      ((J.toFloatLib_containsReal_iff _).mpr J.lo_memReal)))

/-- Interval negation computed by FloatLib. -/
def neg (I : RationalInterval) : RationalInterval :=
  ofFloatLib ((neg? rounding I.toFloatLib).get (by rfl))
    (ordered_of_containsReal (containsReal_neg? rounding rfl
      ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal)))

/-- Interval subtraction computed by FloatLib. -/
def sub (I J : RationalInterval) : RationalInterval :=
  ofFloatLib ((sub? rounding I.toFloatLib J.toFloatLib).get (by rfl))
    (ordered_of_containsReal (containsReal_sub? rounding rfl
      ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal)
      ((J.toFloatLib_containsReal_iff _).mpr J.lo_memReal)))

/-- Sharp four-corner multiplication, computed and certified by FloatLib. -/
@[irreducible] def mul (I J : RationalInterval) : RationalInterval :=
  ofFloatLib ((mul? rounding I.toFloatLib J.toFloatLib).get (by rfl))
    (ordered_of_containsReal (containsReal_mul? rounding rfl
      ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal)
      ((J.toFloatLib_containsReal_iff _).mpr J.lo_memReal)))

/-- Natural powers use FloatLib's sharp odd/even endpoint bounds and binary powering. -/
def powNat (I : RationalInterval) (k : Nat) : RationalInterval :=
  ofFloatLib (powBounds I.toFloatLib k)
    (ordered_of_containsReal (containsReal_pow? rounding k rfl
      ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal)))

/-- The maximum absolute magnitude is the upper endpoint of FloatLib's absolute enclosure. -/
def absMax (I : RationalInterval) : ℚ :=
  (absBounds I.toFloatLib).hi

/-- `absMax I = max |I.lo| |I.hi|`. -/
theorem absMax_eq_max (I : RationalInterval) : I.absMax = max |I.lo| |I.hi| := by
  unfold absMax absBounds
  split_ifs with h1 h2
  · simp [abs_of_nonneg h1, abs_of_nonneg (h1.trans I.hle), I.hle]
  · simp [abs_of_nonpos h2, abs_of_nonpos (I.hle.trans h2), I.hle]
  · simp [abs_of_neg (not_le.mp h1), abs_of_pos (not_le.mp h2)]

/-- Maximum absolute endpoint magnitude is nonnegative. -/
theorem absMax_nonneg (I : RationalInterval) : 0 ≤ I.absMax :=
  absMax_eq_max I ▸ (abs_nonneg I.lo).trans (le_max_left _ _)

/-- Reciprocal of a positive interval, computed by FloatLib's guarded reciprocal. -/
def invPositive (J : RationalInterval) (hJ : 0 < J.lo) : RationalInterval :=
  ofFloatLib ((inv? rounding J.toFloatLib).get (by
    simp [inv?, decode?, Internal.rationalOutwardRounding, encloseInterval?, point, hJ]))
    (ordered_of_containsReal (containsReal_inv? rounding (by
      simp [inv?, decode?, Internal.rationalOutwardRounding, encloseInterval?, point, hJ])
      ((J.toFloatLib_containsReal_iff _).mpr J.lo_memReal)))

/-- Sharp division by a positive interval, using FloatLib multiplication and reciprocal. -/
def divPositive (I J : RationalInterval) (hJ : 0 < J.lo) : RationalInterval :=
  I.mul (J.invPositive hJ)

/-- Divide when the denominator has a positive lower endpoint; otherwise return zero.
The fallback keeps finite evaluators total. A real quotient enclosure still requires
the positive-denominator hypothesis in `divPositiveOrZero_sound`. -/
def divPositiveOrZero (I J : RationalInterval) : RationalInterval :=
  if h : 0 < J.lo then I.divPositive J h else const 0

/-- Nonnegative scaling is FloatLib multiplication by a singleton interval. -/
def scaleNonneg (q : ℚ) (_hq : 0 ≤ q) (I : RationalInterval) : RationalInterval :=
  (const q).mul I

/--
Conservative division from a positive lower bound on the absolute denominator.

The supplied side condition in `divByAbsLower_sound` permits widening the numerator to its
symmetric absolute bound and dividing by the singleton lower bound.
-/
def divByAbsLower (I : RationalInterval) (δ : ℚ) (hδ : 0 < δ) : RationalInterval :=
  (ofBounds (-I.absMax) I.absMax (neg_le_self I.absMax_nonneg)).divPositive (const δ) hδ

/-- A positive denominator interval supplies its lower endpoint. -/
def positiveAbsLower (J : RationalInterval) : ℚ := J.lo

/-- A negative denominator interval supplies the negative of its upper endpoint. -/
def negativeAbsLower (J : RationalInterval) : ℚ := -J.hi

/-! ## Endpoint formulas

These simp lemmas give the endpoints of each operation without unfolding the FloatLib adapters.
For positive division, `simp [divPositive]` combines the multiplication and reciprocal rules.
The separate `absMax_eq_max` theorem exposes the maximum absolute endpoint when needed.
-/

/-- The lower endpoint of a sum is the sum of the lower endpoints. -/
@[simp] theorem add_lo (I J : RationalInterval) : (I.add J).lo = I.lo + J.lo := rfl
/-- The upper endpoint of a sum is the sum of the upper endpoints. -/
@[simp] theorem add_hi (I J : RationalInterval) : (I.add J).hi = I.hi + J.hi := rfl
/-- The lower endpoint after negation is the negated upper endpoint. -/
@[simp] theorem neg_lo (I : RationalInterval) : I.neg.lo = -I.hi := rfl
/-- The upper endpoint after negation is the negated lower endpoint. -/
@[simp] theorem neg_hi (I : RationalInterval) : I.neg.hi = -I.lo := rfl
/-- Subtraction subtracts the upper endpoint from the lower endpoint. -/
@[simp] theorem sub_lo (I J : RationalInterval) : (I.sub J).lo = I.lo - J.hi := rfl
/-- Subtraction subtracts the lower endpoint from the upper endpoint. -/
@[simp] theorem sub_hi (I J : RationalInterval) : (I.sub J).hi = I.hi - J.lo := rfl

/-- The lower product endpoint is the minimum of the four endpoint products. -/
@[simp] theorem mul_lo (I J : RationalInterval) :
    (I.mul J).lo = min (min (I.lo * J.lo) (I.lo * J.hi))
      (min (I.hi * J.lo) (I.hi * J.hi)) := by
  unfold mul
  rfl

/-- The upper product endpoint is the maximum of the four endpoint products. -/
@[simp] theorem mul_hi (I J : RationalInterval) :
    (I.mul J).hi = max (max (I.lo * J.lo) (I.lo * J.hi))
      (max (I.hi * J.lo) (I.hi * J.hi)) := by
  unfold mul
  rfl

/-- The lower reciprocal endpoint is the reciprocal of the positive upper endpoint. -/
@[simp] theorem invPositive_lo (J : RationalInterval) (hJ : 0 < J.lo) :
    (J.invPositive hJ).lo = 1 / J.hi := by
  simp [invPositive, inv?, decode?, Internal.rationalOutwardRounding, encloseInterval?,
    point, ofFloatLib, hJ, one_div]

/-- The upper reciprocal endpoint is the reciprocal of the positive lower endpoint. -/
@[simp] theorem invPositive_hi (J : RationalInterval) (hJ : 0 < J.lo) :
    (J.invPositive hJ).hi = 1 / J.lo := by
  simp [invPositive, inv?, decode?, Internal.rationalOutwardRounding, encloseInterval?,
    point, ofFloatLib, hJ, one_div]

/-- Nonnegative scaling multiplies the lower endpoint by the scale. -/
@[simp] theorem scaleNonneg_lo (q : ℚ) (hq : 0 ≤ q) (I : RationalInterval) :
    (I.scaleNonneg q hq).lo = q * I.lo := by
  simp [scaleNonneg, const, point, min_eq_left (mul_le_mul_of_nonneg_left I.hle hq)]

/-- Nonnegative scaling multiplies the upper endpoint by the scale. -/
@[simp] theorem scaleNonneg_hi (q : ℚ) (hq : 0 ≤ q) (I : RationalInterval) :
    (I.scaleNonneg q hq).hi = q * I.hi := by
  simp [scaleNonneg, const, point, max_eq_right (mul_le_mul_of_nonneg_left I.hle hq)]

/-- The absolute-denominator fallback has lower endpoint negative absolute bound over δ. -/
@[simp] theorem divByAbsLower_lo (I : RationalInterval) (δ : ℚ) (hδ : 0 < δ) :
    (I.divByAbsLower δ hδ).lo = -(I.absMax / δ) := by
  simp [divByAbsLower, divPositive, ofBounds, const, point, ← div_eq_mul_inv, neg_div,
    min_eq_left (neg_le_self (div_nonneg I.absMax_nonneg hδ.le))]

/-- The absolute-denominator fallback has upper endpoint absolute bound over δ. -/
@[simp] theorem divByAbsLower_hi (I : RationalInterval) (δ : ℚ) (hδ : 0 < δ) :
    (I.divByAbsLower δ hδ).hi = I.absMax / δ := by
  simp [divByAbsLower, divPositive, ofBounds, const, point, ← div_eq_mul_inv, neg_div,
    max_eq_right (neg_le_self (div_nonneg I.absMax_nonneg hδ.le))]

/-- Addition of singleton intervals is exact. -/
@[simp] theorem const_add_const (a b : ℚ) :
    (const a).add (const b) = const (a + b) := rfl

/-- Negation of a singleton interval is exact. -/
@[simp] theorem neg_const (a : ℚ) : (const a).neg = const (-a) := rfl

/-- Subtraction of singleton intervals is exact. -/
@[simp] theorem const_sub_const (a b : ℚ) :
    (const a).sub (const b) = const (a - b) := rfl

/-- Multiplication of singleton intervals is exact. -/
@[simp] theorem const_mul_const (a b : ℚ) :
    (const a).mul (const b) = const (a * b) := by
  simp [mul, mul?, liftBinary?, decode?, Internal.rationalOutwardRounding,
    encloseInterval?, point, ofFloatLib, const, minOfFour, maxOfFour]

/-! ## Real containment from FloatLib -/

/-- Addition contains the sum of any two contained real values. -/
theorem add_sound {I J : RationalInterval} {x y : ℝ}
    (hx : I.MemReal x) (hy : J.MemReal y) :
    (I.add J).MemReal (x + y) :=
  ((I.add J).toFloatLib_containsReal_iff _).mp (containsReal_add? rounding rfl
    ((I.toFloatLib_containsReal_iff _).mpr hx) ((J.toFloatLib_containsReal_iff _).mpr hy))

/-- Negation contains the negation of every contained real value. -/
theorem neg_sound {I : RationalInterval} {x : ℝ}
    (hx : I.MemReal x) : I.neg.MemReal (-x) :=
  (I.neg.toFloatLib_containsReal_iff _).mp (containsReal_neg? rounding rfl
    ((I.toFloatLib_containsReal_iff _).mpr hx))

/-- Subtraction contains the difference of any two contained real values. -/
theorem sub_sound {I J : RationalInterval} {x y : ℝ}
    (hx : I.MemReal x) (hy : J.MemReal y) :
    (I.sub J).MemReal (x - y) :=
  ((I.sub J).toFloatLib_containsReal_iff _).mp (containsReal_sub? rounding rfl
    ((I.toFloatLib_containsReal_iff _).mpr hx) ((J.toFloatLib_containsReal_iff _).mpr hy))

/-- Multiplication contains the product of any two contained real values. -/
theorem mul_sound {I J : RationalInterval} {x y : ℝ}
    (hx : I.MemReal x) (hy : J.MemReal y) :
    (I.mul J).MemReal (x * y) :=
  ((I.mul J).toFloatLib_containsReal_iff _).mp (containsReal_mul? rounding (by unfold mul; rfl)
    ((I.toFloatLib_containsReal_iff _).mpr hx) ((J.toFloatLib_containsReal_iff _).mpr hy))

/-- Natural powers contain the corresponding real powers. -/
theorem powNat_sound {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) (k : Nat) :
    (I.powNat k).MemReal (x ^ k) :=
  ((I.powNat k).toFloatLib_containsReal_iff _).mp (containsReal_pow? rounding k rfl
    ((I.toFloatLib_containsReal_iff _).mpr hx))

/-- FloatLib's absolute enclosure bounds the magnitude of every real member. -/
theorem abs_le_absMax {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    |x| ≤ (I.absMax : ℝ) :=
  ((containsReal_some_iff _ _).mp (containsReal_abs? rounding rfl
    ((I.toFloatLib_containsReal_iff _).mpr hx))).2

/-- If `x ∈ I` and `δ ≤ |y|`, then `x / y ∈ I.divByAbsLower δ hδ`. -/
theorem divByAbsLower_sound {I : RationalInterval} {δ : ℚ} (hδ : 0 < δ)
    {x y : ℝ} (hx : I.MemReal x) (hyabs : (δ : ℝ) ≤ |y|) :
    (I.divByAbsLower δ hδ).MemReal (x / y) := by
  have hquot : |x / y| ≤ ((I.absMax / δ : ℚ) : ℝ) := by
    rw [abs_div, Rat.cast_div]
    exact (div_le_div_of_nonneg_right (abs_le_absMax hx) (abs_nonneg y)).trans
      (div_le_div_of_nonneg_left (Rat.cast_nonneg.mpr I.absMax_nonneg) (Rat.cast_pos.mpr hδ) hyabs)
  simpa only [MemReal, divByAbsLower_lo, divByAbsLower_hi, Rat.cast_neg] using abs_le.mp hquot

/-- A positive interval lower endpoint bounds the absolute value of every member. -/
theorem positiveAbsLower_sound {J : RationalInterval} {y : ℝ}
    (hpos : 0 < J.lo) (hy : J.MemReal y) :
    ((J.positiveAbsLower : ℚ) : ℝ) ≤ |y| := by
  simpa [positiveAbsLower, abs_of_nonneg ((Rat.cast_pos.mpr hpos).le.trans hy.1)] using hy.1

/-- A negative interval upper endpoint bounds the absolute value of every member. -/
theorem negativeAbsLower_sound {J : RationalInterval} {y : ℝ}
    (hneg : J.hi < 0) (hy : J.MemReal y) :
    ((J.negativeAbsLower : ℚ) : ℝ) ≤ |y| := by
  have hy_nonpos : y ≤ 0 := hy.2.trans (by exact_mod_cast hneg.le)
  simpa [negativeAbsLower, abs_of_nonpos hy_nonpos] using neg_le_neg hy.2

/-- The reciprocal of a positive interval contains every reciprocal value. -/
theorem invPositive_sound {J : RationalInterval} (hJ : 0 < J.lo) {y : ℝ}
    (hy : J.MemReal y) : (J.invPositive hJ).MemReal y⁻¹ := by
  have hpos : (0 : ℝ) < J.lo := Rat.cast_pos.mpr hJ
  simp only [MemReal, invPositive_lo, invPositive_hi, one_div, Rat.cast_inv]
  exact ⟨inv_anti₀ (hpos.trans_le hy.1) hy.2, inv_anti₀ hpos hy.1⟩

/-- Positive-denominator interval division contains the real quotient. -/
theorem divPositive_sound {I J : RationalInterval} (hJ : 0 < J.lo)
    {x y : ℝ} (hx : I.MemReal x) (hy : J.MemReal y) :
    (I.divPositive J hJ).MemReal (x / y) := by
  simpa only [divPositive, div_eq_mul_inv] using mul_sound hx (invPositive_sound hJ hy)

/-- A checked positive denominator validates the total division evaluator. -/
theorem divPositiveOrZero_sound {I J : RationalInterval} (hJ : 0 < J.lo)
    {x y : ℝ} (hx : I.MemReal x) (hy : J.MemReal y) :
    (I.divPositiveOrZero J).MemReal (x / y) := by
  simpa only [divPositiveOrZero, dite_eq_left hJ] using divPositive_sound hJ hx hy

/-- Nonnegative scaling contains the scaled value of every interval member. -/
theorem scaleNonneg_sound {I : RationalInterval} {q : ℚ} (hq : 0 ≤ q) {x : ℝ}
    (hx : I.MemReal x) : (I.scaleNonneg q hq).MemReal ((q : ℝ) * x) :=
  mul_sound (memReal_const q) hx

end RationalInterval
end CAS.Continuum

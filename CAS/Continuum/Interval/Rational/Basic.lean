/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Proof
public import FloatLib.Numerics.Enclosure.Interval.Hyperbolic
public import FloatLib.Numerics.Enclosure.Interval.OperationsProof
public import FloatLib.Numerics.Enclosure.Trigonometric.AtanProof
public import CAS.Continuum.IntervalBackend

/-!
# Ordered FloatLib intervals for CEGA

CEGA uses FloatLib intervals with rational endpoints. `RationalInterval` adds an
endpoint-order proof, so that every interval has a midpoint and a nonnegative radius, which
refinement and quadrature use. Arithmetic and elementary-function enclosures are FloatLib's.
`MemReal I x` is the statement `I.lo ≤ x ∧ x ≤ I.hi` over `ℝ` used in the certificates.

## Main definitions

* `RationalInterval`, `MemReal`, `instRealIntervalBackend`: the representation, real
  membership, and the `RealIntervalBackend` instance.
* `const`, `ofBounds`, `hull`, `rationalHull`: singletons, intervals from ordered endpoints,
  the hull of two intervals, and a rational interval with denominator `d` around a real interval.
* `center`, `radius`, `midpointApproxCert`: midpoint data and the approximation certificate that
  replaces an enclosed function by the midpoint with error the radius.
* `negOneOne`, `piInterval`, `eInterval`: the intervals `[-1, 1]` and twenty-decimal enclosures
  of `π` and `e`.

## Main results

* `piInterval_sound`, `eInterval_sound`: `π ∈ piInterval` and `exp 1 ∈ eInterval`. FloatLib's
  degree-24 enclosures of `π / 4` and `exp 1` lie inside the fixed brackets, and the rational
  endpoint comparisons are checked by the kernel.

The arithmetic operations and their soundness theorems are in
`CAS.Continuum.Interval.Rational.Arithmetic`.

## Implementation notes

With the exact rounding `Internal.rationalOutwardRounding`, FloatLib's operations on
`Interval ℚ` never round, and FloatLib proves their containment theorems. The order proof of a
result follows from such a theorem applied at `I.lo` (`ordered_of_containsReal`), so the
arithmetic operations lift to `RationalInterval` without reasoning about their endpoints. The
fixed brackets of `π` and `e` have far shorter endpoints than FloatLib's series enclosures, which
keeps later computations with them small. The center of `eInterval` is the rational of Mathlib's
`Real.exp_one_near_20`, and its radius is the error `10⁻²⁰` proved there.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>.
-/

@[expose] public section

namespace CAS.Continuum

open CAS.Certificate

/--
A FloatLib interval with ordered rational endpoints.

The endpoint-order proof is the only well-formedness invariant.
-/
structure RationalInterval extends FloatLib.Numerics.Interval ℚ where
  /-- Endpoint-order invariant. -/
  hle : lo ≤ hi
deriving DecidableEq, Repr

namespace RationalInterval

/-- The interval passed directly to FloatLib's arithmetic and enclosure routines. -/
abbrev toFloatLib (I : RationalInterval) : FloatLib.Numerics.Interval ℚ :=
  I.toInterval

/-- Attach the endpoint-order proof required by CEGA to a FloatLib interval. -/
def ofFloatLib (I : FloatLib.Numerics.Interval ℚ) (h : I.lo ≤ I.hi) :
    RationalInterval :=
  { toInterval := I, hle := h }

/--
Real membership in a rational interval.

The endpoints are cast to `ℝ` because CEGA relations describe real-valued
functions.
-/
def MemReal (I : RationalInterval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- FloatLib's real containment is exactly the endpoint predicate used by CEGA. -/
theorem toFloatLib_containsReal_iff (I : RationalInterval) (x : ℝ) :
    I.toFloatLib.ContainsReal some x ↔ I.MemReal x :=
  FloatLib.Numerics.Interval.containsReal_some_iff _ _

/-- Containing a real value certifies that a FloatLib interval has ordered endpoints. -/
theorem ordered_of_containsReal {I : FloatLib.Numerics.Interval ℚ} {x : ℝ}
    (h : I.ContainsReal some x) : I.lo ≤ I.hi := by
  have hx := (FloatLib.Numerics.Interval.containsReal_some_iff I x).mp h
  exact_mod_cast hx.1.trans hx.2

/-- Attaching the order proof preserves FloatLib's real containment. -/
@[simp] theorem memReal_ofFloatLib_iff (I : FloatLib.Numerics.Interval ℚ)
    (h : I.lo ≤ I.hi) (x : ℝ) :
    (ofFloatLib I h).MemReal x ↔ I.ContainsReal some x :=
  (FloatLib.Numerics.Interval.containsReal_some_iff I x).symm

/-- The lower endpoint belongs to its rational interval. -/
@[simp] theorem lo_memReal (I : RationalInterval) : I.MemReal (I.lo : ℝ) := by
  exact ⟨le_rfl, by exact_mod_cast I.hle⟩

/-- The upper endpoint belongs to its rational interval. -/
@[simp] theorem hi_memReal (I : RationalInterval) : I.MemReal (I.hi : ℝ) := by
  exact ⟨by exact_mod_cast I.hle, le_rfl⟩

/-- The exact rational interval implementation of `RealIntervalBackend`. -/
@[reducible] instance instRealIntervalBackend : RealIntervalBackend RationalInterval where
  lo I := I.lo
  hi I := I.hi
  MemReal := MemReal
  lower_mem h := h.1
  upper_mem h := h.2

/-- The generic backend lower endpoint is the real cast of the rational lower endpoint. -/
@[simp] theorem realIntervalBackend_lo (I : RationalInterval) :
    RealIntervalBackend.lo I = (I.lo : ℝ) :=
  rfl

/-- The generic backend upper endpoint is the real cast of the rational upper endpoint. -/
@[simp] theorem realIntervalBackend_hi (I : RationalInterval) :
    RealIntervalBackend.hi I = (I.hi : ℝ) :=
  rfl

/-- Generic backend membership specializes to rational-interval real membership. -/
@[simp] theorem realIntervalBackend_memReal (I : RationalInterval) (x : ℝ) :
    RealIntervalBackend.MemReal I x ↔ I.MemReal x :=
  Iff.rfl

/-! ## Constructors and hulls -/

/-- The singleton interval `{q}`. -/
def const (q : ℚ) : RationalInterval where
  toInterval := FloatLib.Numerics.Interval.point q
  hle := le_rfl

/-- The lower endpoint of a singleton is its value. -/
@[simp] theorem const_lo (q : ℚ) : (const q).lo = q := rfl

/-- The upper endpoint of a singleton is its value. -/
@[simp] theorem const_hi (q : ℚ) : (const q).hi = q := rfl

/-- The singleton interval contains the real cast of its endpoint. -/
@[simp] theorem memReal_const (q : ℚ) : (const q).MemReal (q : ℝ) := by
  simp [MemReal, const, FloatLib.Numerics.Interval.point]

/-- The closed rational interval with the supplied ordered endpoints. -/
def ofBounds (a b : ℚ) (hab : a ≤ b) : RationalInterval where
  lo := a
  hi := b
  hle := hab

/-- The smallest endpointwise rational interval containing `I` and `J`. -/
def hull (I J : RationalInterval) : RationalInterval :=
  let K := (FloatLib.Numerics.Interval.hull?
    FloatLib.Numerics.Interval.Internal.rationalOutwardRounding I.toFloatLib J.toFloatLib)
      |>.getD I.toFloatLib
  ofFloatLib K (by
    dsimp [K, FloatLib.Numerics.Interval.hull?,
      FloatLib.Numerics.Interval.Internal.rationalOutwardRounding,
      FloatLib.Numerics.Interval.decode?]
    simp only [I.hle, J.hle, and_self, ↓reduceIte, Option.getD_some]
    split <;> split <;> linarith [I.hle, J.hle])

/-- FloatLib's hull selects the smaller lower endpoint. -/
@[simp] theorem hull_lo (I J : RationalInterval) :
    (I.hull J).lo = min I.lo J.lo := by
  simp [hull, ofFloatLib, FloatLib.Numerics.Interval.hull?,
    FloatLib.Numerics.Interval.Internal.rationalOutwardRounding,
    FloatLib.Numerics.Interval.decode?, I.hle, J.hle, min_def]

/-- FloatLib's hull selects the larger upper endpoint. -/
@[simp] theorem hull_hi (I J : RationalInterval) :
    (I.hull J).hi = max I.hi J.hi := by
  simp [hull, ofFloatLib, FloatLib.Numerics.Interval.hull?,
    FloatLib.Numerics.Interval.Internal.rationalOutwardRounding,
    FloatLib.Numerics.Interval.decode?, I.hle, J.hle, max_def]

/-- Every real point of the left interval belongs to the binary hull. -/
theorem memReal_hull_left {I J : RationalInterval} {x : ℝ}
    (hx : I.MemReal x) : (I.hull J).MemReal x :=
  ⟨by simp [hx.1], by simp [hx.2]⟩

/-- Every real point of the right interval belongs to the binary hull. -/
theorem memReal_hull_right {I J : RationalInterval} {x : ℝ}
    (hx : J.MemReal x) : (I.hull J).MemReal x :=
  ⟨by simp [hx.1], by simp [hx.2]⟩

/-- Real points between rational endpoints belong to `ofBounds`. -/
theorem memReal_ofBounds {a b : ℚ} (hab : a ≤ b)
    {x : ℝ} (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    (ofBounds a b hab).MemReal x := by
  simpa [ofBounds, MemReal] using hx

/--
A fixed-denominator rational interval containing an arbitrary ordered real interval.

For a positive denominator `d`, the endpoints are `⌊d * a⌋ / d` and `⌈d * b⌉ / d`. Each
endpoint overshoots its real target by less than `1 / d` unless it is exact.
-/
noncomputable def rationalHull (d : ℕ) (hd : 0 < d)
    (a b : ℝ) (hab : a ≤ b) : RationalInterval where
  lo := (⌊(d : ℝ) * a⌋ : ℤ) / (d : ℚ)
  hi := (⌈(d : ℝ) * b⌉ : ℤ) / (d : ℚ)
  hle := by
    apply div_le_div_of_nonneg_right
    · exact_mod_cast
        ((Int.floor_le ((d : ℝ) * a)).trans
          ((mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg d)).trans
            (Int.le_ceil ((d : ℝ) * b))))
    · exact_mod_cast hd.le

/-- Every point of `[a, b]` lies in `rationalHull d hd a b hab`. -/
theorem memReal_rationalHull {d : ℕ} (hd : 0 < d)
    {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Set.Icc a b) :
    (rationalHull d hd a b hab).MemReal x := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [rationalHull, MemReal, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast,
    div_le_iff₀ hdR, le_div_iff₀ hdR]
  constructor
  · linarith [Int.floor_le ((d : ℝ) * a), mul_le_mul_of_nonneg_left hx.1 hdR.le]
  · linarith [Int.le_ceil ((d : ℝ) * b), mul_le_mul_of_nonneg_left hx.2 hdR.le]

/-! ## Midpoint data -/

/-- Midpoint of a rational interval. -/
def center (I : RationalInterval) : ℚ :=
  (I.lo + I.hi) / 2

/-- Radius of a rational interval around `center`. -/
def radius (I : RationalInterval) : ℚ :=
  (I.hi - I.lo) / 2

/-- The rational interval radius is nonnegative. -/
theorem radius_nonneg (I : RationalInterval) : 0 ≤ I.radius :=
  div_nonneg (sub_nonneg.mpr I.hle) zero_le_two

/-- The midpoint minus the radius is the lower endpoint. -/
theorem center_sub_radius_eq_lo (I : RationalInterval) :
    I.center - I.radius = I.lo := by
  unfold center radius
  ring

/-- The midpoint plus the radius is the upper endpoint. -/
theorem center_add_radius_eq_hi (I : RationalInterval) :
    I.center + I.radius = I.hi := by
  unfold center radius
  ring

/--
Interval containment gives a CEGA approximation by the interval midpoint.

This is the checked form of replacing an interval by its midpoint with the radius as a uniform
error budget.
-/
noncomputable def midpointApproxCert {α : Type*} {f : α → ℝ} {s : Set α}
    (I : RationalInterval) (h : ∀ x, x ∈ s → I.MemReal (f x)) :
    ApproxCert α ℝ s :=
  RealIntervalBackend.approxCertAroundOfMemRealLe
    (ι := RationalInterval) I (I.center : ℝ) (I.radius : ℝ)
    (by
      change (I.center : ℝ) - (I.radius : ℝ) ≤ (I.lo : ℝ)
      rw [← Rat.cast_sub, I.center_sub_radius_eq_lo])
    (by
      change (I.hi : ℝ) ≤ (I.center : ℝ) + (I.radius : ℝ)
      rw [← Rat.cast_add, I.center_add_radius_eq_hi])
    h

/-! ## Built-in constant ranges -/

/-- The universal trigonometric range interval `[-1, 1]`. -/
def negOneOne : RationalInterval where
  lo := -1
  hi := 1
  hle := by norm_num

/-- Twenty-decimal rational lower bound for `π`, certified by FloatLib's Machin enclosure. -/
def piLower : ℚ := 314159265358979323846 / 100000000000000000000

/-- Twenty-decimal rational upper bound for `π`, certified by FloatLib's Machin enclosure. -/
def piUpper : ℚ := 314159265358979323847 / 100000000000000000000

/-- The shared exact-rational enclosure for `π`, of width `10⁻²⁰`. -/
def piInterval : RationalInterval where
  lo := piLower
  hi := piUpper
  hle := by norm_num [piLower, piUpper]

/-- `piLower ≤ π`. -/
theorem piLower_le_pi : (piLower : ℝ) ≤ Real.pi := by
  have hlo : piLower ≤ 4 * (FloatLib.Numerics.Enclosure.piQuarter 24).lo := by decide +kernel
  have hloR : (piLower : ℝ) ≤ 4 * ((FloatLib.Numerics.Enclosure.piQuarter 24).lo : ℝ) := by
    exact_mod_cast hlo
  linarith [(FloatLib.Numerics.Enclosure.contains_piQuarter 24).1]

/-- `π ≤ piUpper`. -/
theorem pi_le_piUpper : Real.pi ≤ (piUpper : ℝ) := by
  have hhi : 4 * (FloatLib.Numerics.Enclosure.piQuarter 24).hi ≤ piUpper := by decide +kernel
  have hhiR : 4 * ((FloatLib.Numerics.Enclosure.piQuarter 24).hi : ℝ) ≤ (piUpper : ℝ) := by
    exact_mod_cast hhi
  linarith [(FloatLib.Numerics.Enclosure.contains_piQuarter 24).2]

/-- `piInterval` contains `π`. -/
theorem piInterval_sound : piInterval.MemReal Real.pi := by
  simpa [piInterval, MemReal] using And.intro piLower_le_pi pi_le_piUpper

/-- The rational center used in Mathlib's approximation `Real.exp_one_near_20`. -/
def eApprox : ℚ := 363916618873 / 133877442384

/-- Twenty-decimal rational lower bound for `e = exp 1`. -/
def eLower : ℚ := eApprox - 1 / 10 ^ 20

/-- Twenty-decimal rational upper bound for `e = exp 1`. -/
def eUpper : ℚ := eApprox + 1 / 10 ^ 20

/--
The shared exact-rational enclosure for Euler's number `e = exp 1`, of width `2 · 10⁻²⁰`.

FloatLib's degree-24 exponential enclosure lies inside these fixed endpoints.
-/
def eInterval : RationalInterval where
  lo := eLower
  hi := eUpper
  hle := by
    unfold eLower eUpper
    linarith [show (0 : ℚ) < 1 / 10 ^ 20 by norm_num]

/-- `eInterval` contains `exp 1`. -/
theorem eInterval_sound : eInterval.MemReal (Real.exp 1) := by
  have h := FloatLib.Numerics.Enclosure.contains_exp 1 24
  rw [Rat.cast_one] at h
  have hlo : eLower ≤ (FloatLib.Numerics.Enclosure.exp 1 24).lo := by decide +kernel
  have hhi : (FloatLib.Numerics.Enclosure.exp 1 24).hi ≤ eUpper := by decide +kernel
  exact ⟨(Rat.cast_le.mpr hlo).trans h.1, h.2.trans (Rat.cast_le.mpr hhi)⟩

end RationalInterval

end CAS.Continuum

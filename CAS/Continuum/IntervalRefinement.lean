/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Basic

/-!
# Inflation and intersection of rational intervals

Two operations on rational intervals; the sine and cosine enclosures sharpen their ranges with
`intersect`.

* `inflate I r hr` is `[I.lo - r, I.hi + r]` for `hr : 0 ≤ r`; by `inflate_sound` it contains
  every `value` with `|value - center| ≤ r` for some `center ∈ I`;
* `intersect I J h` is the intersection of `I` and `J` given a proof `h` that it is nonempty,
  computed by FloatLib's `intersect?`; by `intersect_sound` it contains every common member of
  `I` and `J`.

## Implementation notes

Both operations are executable; their proof arguments only establish the endpoint order and are
erased at run time. `inflate` subtracts and adds `r` in `ℚ`, and `inflate_sound` splits the
hypothesis with `abs_le` and closes both sides by `linarith`. For `intersect` we call FloatLib's
`intersect?` with the exact rounding `Internal.rationalOutwardRounding`. When it runs, it still
compares `max I.lo J.lo` with `min I.hi J.hi`; `hoverlap` proves that it returns `some`, so
`Option.get` needs no fallback. `intersect_lo` and `intersect_hi` compute the two endpoints by
`simp`, and `intersect_sound` follows from them.

In `CAS.Continuum.Interval.Elementary.Trig`, which intersects FloatLib's enclosure with one
built from the values at the endpoints, `hoverlap` comes from `intersectable_of_common_mem` at
the center or the lower endpoint of `I`, which both enclosures contain. `IntervalBalls.inflate`
of `CAS.Numerics.IntervalBalls` is the ball version of `inflate` (`IntervalBalls.inflate_encloses`).

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open FloatLib.Numerics.Interval

local notation "rounding" => FloatLib.Numerics.Interval.Internal.rationalOutwardRounding

/-- Inflate both sides of an interval by a nonnegative rational radius. -/
def inflate (I : RationalInterval) (r : ℚ) (hr : 0 ≤ r) : RationalInterval where
  lo := I.lo - r
  hi := I.hi + r
  hle := by
    linarith [I.hle]

/-- If `center ∈ I` and `|value - center| ≤ r`, then `value ∈ I.inflate r hr`. -/
theorem inflate_sound {I : RationalInterval} {r : ℚ} (hr : 0 ≤ r)
    {center value : ℝ} (hcenter : I.MemReal center)
    (herror : |value - center| ≤ (r : ℝ)) :
    (I.inflate r hr).MemReal value := by
  obtain ⟨h1, h2⟩ := abs_le.mp herror
  push_cast [MemReal, inflate]
  constructor <;> linarith [hcenter.1, hcenter.2]

/--
The intersection `[max I.lo J.lo, min I.hi J.hi]` of two rational intervals, given that it is
nonempty.

FloatLib computes the endpoints, and the overlap hypothesis, an exact rational inequality,
makes its partial operation succeed.
-/
def intersect (I J : RationalInterval)
    (hoverlap : max I.lo J.lo ≤ min I.hi J.hi) : RationalInterval :=
  let K := (intersect? rounding I.toFloatLib J.toFloatLib).get (by
    simp [intersect?, Internal.rationalOutwardRounding, decode?, hoverlap])
  ofFloatLib K (by
    dsimp [K, intersect?, Internal.rationalOutwardRounding, decode?]
    simp only [hoverlap, ↓reduceIte, Option.get_some]
    simpa only [max_def, min_def] using hoverlap)

/-- FloatLib's intersection selects the larger lower endpoint. -/
@[simp] theorem intersect_lo (I J : RationalInterval)
    (hoverlap : max I.lo J.lo ≤ min I.hi J.hi) :
    (I.intersect J hoverlap).lo = max I.lo J.lo := by
  simp [intersect, ofFloatLib, intersect?, Internal.rationalOutwardRounding,
    decode?, max_def]

/-- FloatLib's intersection selects the smaller upper endpoint. -/
@[simp] theorem intersect_hi (I J : RationalInterval)
    (hoverlap : max I.lo J.lo ≤ min I.hi J.hi) :
    (I.intersect J hoverlap).hi = min I.hi J.hi := by
  simp [intersect, ofFloatLib, intersect?, Internal.rationalOutwardRounding,
    decode?, min_def]

/-- Membership in both input intervals gives membership in their intersection. -/
theorem intersect_sound {I J : RationalInterval}
    (hoverlap : max I.lo J.lo ≤ min I.hi J.hi)
    {x : ℝ} (hI : I.MemReal x) (hJ : J.MemReal x) :
    (I.intersect J hoverlap).MemReal x :=
  ⟨by simp [hI.1, hJ.1], by simp [hI.2, hJ.2]⟩

end RationalInterval
end CAS.Continuum

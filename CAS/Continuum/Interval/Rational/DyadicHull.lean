/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Basic
public import FloatLib.Numerics.Enclosure.Interval.BinaryGridProof

/-!
# Outward dyadic hulls of rational intervals

`dyadicHull bits I` rounds the lower endpoint of `I` down and the upper endpoint up to FloatLib's
binary grid of spacing `2 ^ (-bits)`. The result contains `I` (`dyadicHull_sound`), and its
endpoint denominators divide `2 ^ bits`.

## Implementation notes

The grid rounding `BinaryGrid.enclose` and its containment theorem `BinaryGrid.contains_enclose`
are FloatLib's. `BinaryGrid.enclose bits q` shifts the numerator of `q` left by `bits` and makes
one floor division by the denominator, with a product test for the ceiling, and `BinaryGrid.toRat`
returns the endpoint over `2 ^ bits`. `grid_enclose_bounds` decodes FloatLib's theorem into two
rational inequalities, and `dyadicHull_sound` chains them with the membership.

We round to a fixed grid to bound the growth of denominators when many enclosures are added or
composed. The enclosures `sinBase`, `cosBase`, `atanRange`, `asinPointInterval` and
`acosPointInterval` round their results this way, and so does the `#cas [N d]` evaluator of
`CAS.Continuum.IntervalEval.Digits` for its products, powers, sines, cosines and arctangents and
for its enclosure of `π / 2`. `dyadicHull_lo` and `dyadicHull_hi` in
`CAS.Continuum.Interval.Rational.DyadicHullEndpoints` give the endpoints as
`⌊I.lo * 2 ^ bits⌋ / 2 ^ bits` and `⌈I.hi * 2 ^ bits⌉ / 2 ^ bits`.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>.
* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Section 5.3 for the outward rounding (5.14) of the endpoints, there to floating-point numbers.
-/

@[expose] public section

namespace CAS.Continuum.RationalInterval

open FloatLib.Numerics.Interval

/-- The decoded endpoints of FloatLib's grid enclosure bracket the rational input. -/
theorem grid_enclose_bounds (bits : ℕ) (q : ℚ) :
    BinaryGrid.toRat bits (BinaryGrid.enclose bits q).lo ≤ q ∧
      q ≤ BinaryGrid.toRat bits (BinaryGrid.enclose bits q).hi := by
  simpa [FloatLib.Numerics.Interval.Contains, BinaryGrid.decode] using
    BinaryGrid.contains_enclose bits q

/-- Both endpoints of `I` rounded outward to the binary grid of spacing `2 ^ (-bits)`. -/
def dyadicHull (bits : ℕ) (I : RationalInterval) : RationalInterval where
  lo := BinaryGrid.toRat bits (BinaryGrid.enclose bits I.lo).lo
  hi := BinaryGrid.toRat bits (BinaryGrid.enclose bits I.hi).hi
  hle := (grid_enclose_bounds bits I.lo).1.trans
    (I.hle.trans (grid_enclose_bounds bits I.hi).2)

/-- Every member of `I` is a member of `dyadicHull bits I`. -/
theorem dyadicHull_sound (bits : ℕ) {I : RationalInterval} {x : ℝ}
    (hx : I.MemReal x) : (dyadicHull bits I).MemReal x :=
  ⟨(Rat.cast_le.mpr (grid_enclose_bounds bits I.lo).1).trans hx.1,
    hx.2.trans (Rat.cast_le.mpr (grid_enclose_bounds bits I.hi).2)⟩

end CAS.Continuum.RationalInterval

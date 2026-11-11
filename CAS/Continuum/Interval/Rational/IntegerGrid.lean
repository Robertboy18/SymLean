/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Arithmetic
public import CAS.Continuum.Interval.Rational.FiniteSum
public import FloatLib.Numerics.Enclosure.Interval.BinaryGrid
import CAS.ExactTactic

/-!
# Scaled signed integer intervals

`mulUnits p q` multiplies two integer intervals with FloatLib's `BinaryGrid.mul` at zero
fractional bits, which returns the exact minimum and maximum of the four endpoint products
(`mulUnits_eq`). `unitsRange p hp d hd` is the rational interval `[d * p.1, d * p.2]` for a scale
`d ≥ 0`. By `unitsRange_mul`, the product of two scaled intervals is the scaled integer product
with scale `a * b`, so the product can be computed on the integer endpoints.

## Implementation notes

At zero fractional bits, FloatLib's `BinaryGrid.mul` forms the four integer products and shifts
their minimum and maximum by zero bits, so `mulUnits_eq` reduces it to the four-corner formula by
`simp`. On the integers a product needs no gcd, while each rational product (`Rat.mul`)
computes two; the new scale `a * b` is a single rational product. `unitsRange_mul` is an
equation with `RationalInterval.mul`, proved by `ext` and `simp` with `mul_lo`, `mul_hi`,
`scaleNonneg_lo`, `scaleNonneg_hi`, `mul_min_of_nonneg` and `mul_max_of_nonneg`, after `cas`
regroups `a * x * (b * y)`. Enclosures of the product then come from `mul_sound`. No module of
SymLean imports this one; it serves certificates built on the library.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>.
-/

@[expose] public section

namespace CAS.Continuum.RationalInterval

/-- Sort the two integer endpoints of a recorded range. -/
def orderedUnits (p : ℤ × ℤ) : ℤ × ℤ :=
  (min p.1 p.2, max p.1 p.2)

/-- FloatLib multiplication on the integer grid before the common denominator is restored. -/
def mulUnits (p q : ℤ × ℤ) : ℤ × ℤ :=
  let I := FloatLib.Numerics.Interval.BinaryGrid.mul 0 ⟨p.1, p.2⟩ ⟨q.1, q.2⟩
  (I.lo, I.hi)

/-- At zero fractional bits, FloatLib's integer product has exact four-corner endpoints. -/
theorem mulUnits_eq (p q : ℤ × ℤ) :
    mulUnits p q =
      (min (min (p.1 * q.1) (p.1 * q.2)) (min (p.2 * q.1) (p.2 * q.2)),
        max (max (p.1 * q.1) (p.1 * q.2)) (max (p.2 * q.1) (p.2 * q.2))) := by
  simp [mulUnits, FloatLib.Numerics.Interval.BinaryGrid.mul,
    FloatLib.Numerics.Interval.BinaryGrid.roundDown,
    FloatLib.Numerics.Interval.BinaryGrid.roundUp,
    FloatLib.Numerics.Interval.minOfFour, FloatLib.Numerics.Interval.maxOfFour]

/-- The integer product interval is ordered. -/
theorem mulUnits_ordered (p q : ℤ × ℤ) : (mulUnits p q).1 ≤ (mulUnits p q).2 := by
  rw [mulUnits_eq]
  exact (min_le_left _ _).trans (min_le_max.trans (le_max_left _ _))

/-- Restore the rational scale of ordered integer endpoints. -/
def unitsRange (p : ℤ × ℤ) (hp : p.1 ≤ p.2) (d : ℚ) (hd : 0 ≤ d) :
    RationalInterval :=
  scaleNonneg d hd (ofBounds p.1 p.2 (by exact_mod_cast hp))

/-- Multiplication of scaled integer endpoints agrees with rational interval arithmetic. -/
theorem unitsRange_mul (p q : ℤ × ℤ) (hp : p.1 ≤ p.2) (hq : q.1 ≤ q.2)
    (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (unitsRange p hp a ha).mul (unitsRange q hq b hb) =
      unitsRange (mulUnits p q) (mulUnits_ordered p q) (a * b) (mul_nonneg ha hb) := by
  have hprod (x y : ℚ) : a * x * (b * y) = (a * b) * (x * y) := by cas
  ext <;>
    simp only [unitsRange, mul_lo, mul_hi, scaleNonneg_lo, scaleNonneg_hi, ofBounds,
      mulUnits_eq, Int.cast_min, Int.cast_max, Int.cast_mul, hprod,
      mul_min_of_nonneg _ _ (mul_nonneg ha hb),
      mul_max_of_nonneg _ _ (mul_nonneg ha hb)]

end CAS.Continuum.RationalInterval

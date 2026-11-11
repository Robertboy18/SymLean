/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.DyadicHull

/-!
# Outward rounding to a relative precision

`relativeHull bits I` rounds the endpoints of `I` outward to dyadic rationals with about `bits`
significant bits: each endpoint `q` is replaced by a multiple of `2 ^ (-e)` with
`e = bits - ⌊log₂ |num q|⌋ + ⌊log₂ (den q)⌋`. Unlike the fixed grids of `dyadicHull`, the
precision follows the magnitude of the endpoints.

`quotientHull bits I` rounds each endpoint `q` outward on FloatLib's binary grid of spacing
`2 ^ (-gridBits bits q)`. The grid has `bits` fractional bits for `|q| ≥ 1` and at least
`bits + k` for `|q| < 2 ^ (-k)`, so the rounding error is at most `2 ^ (1 - bits)` times `|q|`.

## Main definitions

* `relativeExponent`: the exponent `e` with `2 ^ (-e)` about `2 ^ (-bits)` times `|q|`.
* `roundDownRel`: `q` rounded down to a multiple of `2 ^ (-relativeExponent bits q)`;
  `roundUpRel` rounds up.
* `relativeHull`: the interval with both endpoints rounded outward to `bits` significant bits.
* `bitLength`: the number of binary digits of a natural number.
* `gridBits`: the fractional bits of the grid on which `quotientHull` rounds an endpoint.
* `quotientHull`: the interval with both endpoints rounded outward on the grid of `gridBits`.

## Main results

* `roundDownRel_le`: rounding down does not increase `q`.
* `le_roundUpRel`: rounding up does not decrease `q`.
* `relativeHull_sound`: `relativeHull bits I` contains every member of `I`.
* `quotientHull_sound`: `quotientHull bits I` contains every member of `I`.

## Implementation notes

We compute `relativeHull` in `ℚ`: the exponent comes from `Nat.log2` of the numerator and the
denominator, and each endpoint is `⌊q * 2 ^ e⌋ / 2 ^ e` or `⌈q * 2 ^ e⌉ / 2 ^ e`. For `q ≠ 0` the
product `|q| * 2 ^ e` lies strictly between `2 ^ bits / 2` and `2 * 2 ^ bits`, so each rounded
endpoint is an integer of about `bits` binary digits times a power of two, whatever the size of
`q`. `roundDownRel_le` and `le_roundUpRel` clear the positive power and apply `Int.floor_le` and
`Int.le_ceil`, which gives `relativeHull_sound`. `IntervalJet.round` in
`CAS.Numerics.IntervalJets` rounds every jet coefficient this way.

`quotientHull` calls FloatLib's `BinaryGrid.enclose`, one floor division of the shifted numerator
by the denominator and one product test, at the precision `gridBits`. For the bit lengths,
`bitLength` doubles a bound until `n >>> hi` vanishes and then bisects between `0` and that bound,
shifting `n` once per step; both searches recurse structurally on a fuel of `64` steps. The
kernel computes each `Nat.shiftRight` of numerals in one step, while it unfolds `Nat.log2`, a
`Nat.rec`, once per binary digit of the argument. `quotientHull_sound` rests only on
`grid_enclose_bounds`, which holds at every precision, so the bit lengths affect the accuracy and
never the soundness. The `#cas [N d]` evaluator (`CAS.Continuum.IntervalEval.Digits`) rounds
reciprocals and quotients with `quotientHull`.

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

/-- The exponent `e` with `2 ^ (-e)` about `2 ^ (-bits)` times `|q|`. -/
def relativeExponent (bits : ℕ) (q : ℚ) : ℤ :=
  (bits : ℤ) - (Nat.log2 q.num.natAbs : ℤ) + (Nat.log2 q.den : ℤ)

/-- `q` rounded down to a multiple of `2 ^ (-relativeExponent bits q)`. -/
def roundDownRel (bits : ℕ) (q : ℚ) : ℚ :=
  (⌊q * 2 ^ relativeExponent bits q⌋ : ℚ) / 2 ^ relativeExponent bits q

/-- `q` rounded up to a multiple of `2 ^ (-relativeExponent bits q)`. -/
def roundUpRel (bits : ℕ) (q : ℚ) : ℚ :=
  (⌈q * 2 ^ relativeExponent bits q⌉ : ℚ) / 2 ^ relativeExponent bits q

/-- Rounding down to `bits` significant bits does not increase `q`. -/
theorem roundDownRel_le (bits : ℕ) (q : ℚ) : roundDownRel bits q ≤ q := by
  unfold roundDownRel
  rw [div_le_iff₀ (zpow_pos (by norm_num) _)]
  exact Int.floor_le _

/-- Rounding up to `bits` significant bits does not decrease `q`. -/
theorem le_roundUpRel (bits : ℕ) (q : ℚ) : q ≤ roundUpRel bits q := by
  unfold roundUpRel
  rw [le_div_iff₀ (zpow_pos (by norm_num) _)]
  exact Int.le_ceil _

/-- The interval with both endpoints rounded outward to `bits` significant bits. -/
def relativeHull (bits : ℕ) (I : RationalInterval) : RationalInterval where
  lo := roundDownRel bits I.lo
  hi := roundUpRel bits I.hi
  hle := ((roundDownRel_le bits I.lo).trans I.hle).trans (le_roundUpRel bits I.hi)

/-- `relativeHull bits I` contains every member of `I`. -/
theorem relativeHull_sound (bits : ℕ) {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (relativeHull bits I).MemReal x :=
  ⟨(Rat.cast_le.mpr (roundDownRel_le bits I.lo)).trans hx.1,
    hx.2.trans (Rat.cast_le.mpr (le_roundUpRel bits I.hi))⟩

/-- The bit length of `n` by bisection between `n >>> lo ≠ 0` and `n >>> hi = 0`, with `fuel`
steps. -/
def bitLengthBisect (n : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, hi => hi
  | fuel + 1, lo, hi =>
    if Nat.ble hi (lo + 1) then hi
    else
      let mid := (lo + hi) / 2
      if Nat.beq (Nat.shiftRight n mid) 0 then bitLengthBisect n fuel lo mid
      else bitLengthBisect n fuel mid hi

/-- The first of `hi, 2 hi, 4 hi, ...` with `n >>> hi = 0`, within `fuel` doublings. -/
def bitLengthUpper (n : ℕ) : ℕ → ℕ → ℕ
  | 0, hi => hi
  | fuel + 1, hi => if Nat.beq (Nat.shiftRight n hi) 0 then hi else bitLengthUpper n fuel (2 * hi)

/-- The number of binary digits of `n`, and `0` for `n = 0`. -/
def bitLength (n : ℕ) : ℕ :=
  if Nat.beq n 0 then 0 else bitLengthBisect n 64 0 (bitLengthUpper n 64 1)

/-- The fractional bits of the grid on which `quotientHull bits` rounds the endpoint `q`: `bits`
plus the binary orders of magnitude by which `|q|` is below `1`. -/
def gridBits (bits : ℕ) (q : ℚ) : ℕ :=
  bits + (bitLength q.den - bitLength q.num.natAbs)

/-- Both endpoints of `I` rounded outward on the binary grid of spacing `2 ^ (-gridBits bits q)`
at the endpoint `q`. -/
def quotientHull (bits : ℕ) (I : RationalInterval) : RationalInterval where
  lo := BinaryGrid.toRat (gridBits bits I.lo) (BinaryGrid.enclose (gridBits bits I.lo) I.lo).lo
  hi := BinaryGrid.toRat (gridBits bits I.hi) (BinaryGrid.enclose (gridBits bits I.hi) I.hi).hi
  hle := (grid_enclose_bounds _ I.lo).1.trans (I.hle.trans (grid_enclose_bounds _ I.hi).2)

/-- `quotientHull bits I` contains every member of `I`. -/
theorem quotientHull_sound (bits : ℕ) {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (quotientHull bits I).MemReal x :=
  ⟨(Rat.cast_le.mpr (grid_enclose_bounds _ I.lo).1).trans hx.1,
    hx.2.trans (Rat.cast_le.mpr (grid_enclose_bounds _ I.hi).2)⟩

end CAS.Continuum.RationalInterval

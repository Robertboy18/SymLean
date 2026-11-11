/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.DyadicHull
public import FloatLib.Numerics.Enclosure.Interval.ElementaryProof

/-!
# Arctangent enclosures from FloatLib

`atanRangeWith I terms` is FloatLib's arctangent enclosure of `I`, from the point enclosures of
its endpoints with `terms + 1` terms of the series in each reduced argument. `atanRange I` uses
the degree `16`, so `17` terms, and rounds outward to a 128-bit dyadic grid. `atanRangeWith_sound`
and `atanRange_sound` show that they contain `Real.arctan x` for every `x ∈ I`.

## Implementation notes

The algorithm and its proof are FloatLib's. `Real.arctan` is monotone, so `Interval.atanBounds`
evaluates the point enclosure `Enclosure.atan` at the two endpoints. The point enclosure uses
odd symmetry, `arctan x = π / 2 - arctan (1 / x)` for `x > 1` and
`arctan x = π / 4 + arctan ((x - 1) / (x + 1))` for `1 / 2 < x ≤ 1`, so that the series DLMF
4.24.3 is summed only at arguments of absolute value at most `1 / 2`, with a geometric bound on
its tail; `π / 4` is Machin's `4 arctan (1 / 5) - arctan (1 / 239)`. FloatLib proves the tail
bound and takes Machin's identity from Mathlib.

FloatLib's series `Enclosure.atanTaylor` is a `Finset` sum of rationals, which the kernel
normalizes after every term; FloatLib compiles it to the binary splitting `Taylor.atan`, which
composes integer Horner blocks and normalizes once (`atanTaylor_eq_binarySplit`). Kernel
reduction does not use compiler substitutions, so `AtanSplit.bounds` restates FloatLib's
`Interval.atanBounds` with `Taylor.atan` in place of the sum (`AtanSplit.bounds_eq`), and our
enclosures use it. From about 80 terms on, as in the digits of `#cas [N d]`, the kernel
evaluates it two to four times faster; at the 17 terms of `atanRange` the difference is within
measurement noise.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>.
* NIST Digital Library of Mathematical Functions, §4.24 Inverse Trigonometric Functions: Further
  Properties, Version 1.2.8 (2026-09-15), <https://dlmf.nist.gov/4.24>. Equation (4.24.3), the
  series of `arctan z` for `|z| ≤ 1`.
* David H. Bailey, Jonathan M. Borwein, Peter B. Borwein and Simon Plouffe, "The Quest for Pi",
  *The Mathematical Intelligencer* 19 (1997), pp. 50-57, <https://doi.org/10.1007/BF03024340>.
  Section 2 for Machin's formula.
-/

@[expose] public section

namespace CAS.Continuum

namespace AtanSplit

open FloatLib.Numerics FloatLib.Numerics.Enclosure

/-- `Enclosure.atanSmall` with the series by binary splitting. -/
def small (x : ℚ) (degree : ℕ) : FloatLib.Numerics.RationalInterval :=
  .around (Taylor.atan x (degree + 1)) (atanRadius x (degree + 1))

/-- `Enclosure.piQuarter`, Machin's formula, with the series by binary splitting. -/
def piQuarter (degree : ℕ) : FloatLib.Numerics.RationalInterval :=
  ((small (1 / 5) degree).scaleNonnegative 4).sub (small (1 / 239) degree)

/-- `Enclosure.atanUnit` with the series by binary splitting. -/
def unit (x : ℚ) (degree : ℕ) : FloatLib.Numerics.RationalInterval :=
  if x ≤ 1 / 2 then small x degree
  else (piQuarter degree).add (small ((x - 1) / (x + 1)) degree)

/-- `Enclosure.atanNonnegative` with the series by binary splitting. -/
def nonnegative (x : ℚ) (degree : ℕ) : FloatLib.Numerics.RationalInterval :=
  if x ≤ 1 then unit x degree
  else ((piQuarter degree).scaleNonnegative 2).sub (unit x⁻¹ degree)

/-- `Enclosure.atan` with the series by binary splitting. -/
def atan (x : ℚ) (degree : ℕ) : FloatLib.Numerics.RationalInterval :=
  if x < 0 then (nonnegative (-x) degree).neg else nonnegative x degree

/-- The binary-splitting arctangent is FloatLib's `Enclosure.atan`. -/
theorem atan_eq : atan = Enclosure.atan := by
  funext x degree
  simp only [atan, nonnegative, unit, piQuarter, small, Enclosure.atan, atanNonnegative, atanUnit,
    Enclosure.piQuarter, atanSmall, atanTaylor_eq_binarySplit]

/-- FloatLib's interval arctangent `Interval.atanBounds` with the series by binary splitting. -/
def bounds (I : Interval ℚ) (terms : ℕ) : Interval ℚ :=
  Interval.monotoneBounds (fun x ↦
    let J := atan x terms
    ⟨J.lo, J.hi⟩) I

/-- `bounds` is FloatLib's `Interval.atanBounds`. -/
theorem bounds_eq : bounds = Interval.atanBounds := by
  funext I terms
  simp only [bounds, Interval.atanBounds, atan_eq]

/-- `bounds I terms` contains `Real.arctan x` for every `x` that `I` contains. -/
theorem containsReal_bounds (I : Interval ℚ) (terms : ℕ) {x : ℝ} (hx : I.ContainsReal some x) :
    (bounds I terms).ContainsReal some (Real.arctan x) :=
  bounds_eq ▸ Interval.containsReal_atanBounds I terms hx

end AtanSplit

namespace RationalInterval

/-- FloatLib's arctangent enclosure with `terms` as the series degree. -/
def atanRangeWith (I : RationalInterval) (terms : ℕ) : RationalInterval :=
  ofFloatLib (AtanSplit.bounds I.toFloatLib terms)
    (ordered_of_containsReal (AtanSplit.containsReal_bounds
      I.toFloatLib terms ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal)))

/-- `atanRangeWith I terms` contains `Real.arctan x` for every `x ∈ I`. -/
theorem atanRangeWith_sound (I : RationalInterval) (terms : ℕ)
    {x : ℝ} (hx : I.MemReal x) :
    (atanRangeWith I terms).MemReal (Real.arctan x) :=
  (memReal_ofFloatLib_iff _ _ _).mpr
    (AtanSplit.containsReal_bounds I.toFloatLib terms
      ((I.toFloatLib_containsReal_iff x).mpr hx))

/-- FloatLib's arctangent enclosure with the degree `16` (`17` terms), rounded outward on a
128-bit binary grid. -/
def atanRange (I : RationalInterval) : RationalInterval :=
  dyadicHull 128 (atanRangeWith I 16)

/-- `atanRange I` contains `Real.arctan x` for every `x ∈ I`. -/
theorem atanRange_sound (I : RationalInterval)
    {x : ℝ} (hx : I.MemReal x) :
    (atanRange I).MemReal (Real.arctan x) :=
  dyadicHull_sound 128 (atanRangeWith_sound I 16 hx)

end RationalInterval
end CAS.Continuum

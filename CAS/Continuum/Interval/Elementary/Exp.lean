/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Basic
public import FloatLib.Numerics.Enclosure.Interval.ElementaryProof

/-!
# Exponential enclosures from FloatLib

`expRangeWith I order` is FloatLib's exponential enclosure of `I` at Taylor order
`max order 1`, and `expRange` fixes the order `defaultExpTaylorOrder = 8`. Both enclosures contain
`Real.exp x` for every `x ∈ I` (`expRangeWith_sound`, `expRange_sound`).

## Implementation notes

The algorithm and its proof are FloatLib's. `Interval.expBounds` evaluates the point enclosure
`Enclosure.exp` at the two endpoints, which suffices because `Real.exp` is monotone, and raises a
negative lower bound to `0`. The point enclosure divides the argument by a power of two until its
absolute value is below one, sums the Taylor polynomial (DLMF 4.2.19) in exact rational
arithmetic with a remainder bound, and restores the scale by repeated squaring; FloatLib derives
the remainder bound from Mathlib's `Real.exp_bound`. We add the endpoint order of the
`RationalInterval`, which follows from FloatLib's containment theorem at `I.lo`, and the default
order.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>.
* NIST Digital Library of Mathematical Functions, §4.2 Definitions, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/4.2>. Equation (4.2.19), the exponential series.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

/-- FloatLib's enclosure of `Real.exp` on `I` at Taylor order `max order 1`. -/
def expRangeWith (I : RationalInterval) (order : Nat) : RationalInterval :=
  ofFloatLib (FloatLib.Numerics.Interval.expBounds I.toFloatLib (max order 1))
    (ordered_of_containsReal (FloatLib.Numerics.Interval.containsReal_expBounds
      I.toFloatLib (max order 1) ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal)))

/-- `expRangeWith I order` contains `Real.exp x` for every `x ∈ I`. -/
theorem expRangeWith_sound (I : RationalInterval) (order : Nat)
    {x : ℝ} (hx : I.MemReal x) :
    (expRangeWith I order).MemReal (Real.exp x) :=
  (memReal_ofFloatLib_iff _ _ _).mpr (FloatLib.Numerics.Interval.containsReal_expBounds
    I.toFloatLib (max order 1) ((I.toFloatLib_containsReal_iff x).mpr hx))

/-- Default FloatLib exponential degree used by automatic interval compilation. -/
def defaultExpTaylorOrder : Nat := 8

/-- Exponential enclosure at the default order `defaultExpTaylorOrder`. -/
def expRange (I : RationalInterval) : RationalInterval :=
  expRangeWith I defaultExpTaylorOrder

/-- `expRange I` contains `Real.exp x` for every `x ∈ I`. -/
theorem expRange_sound (I : RationalInterval) {x : ℝ} (hx : I.MemReal x) :
    (expRange I).MemReal (Real.exp x) :=
  expRangeWith_sound I defaultExpTaylorOrder hx


end RationalInterval
end CAS.Continuum

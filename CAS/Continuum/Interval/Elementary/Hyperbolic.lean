/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Basic
public import FloatLib.Numerics.Enclosure.Interval.HyperbolicProof

/-!
# Hyperbolic enclosures from FloatLib

`sinhRange`, `coshRange` and `tanhRange` are FloatLib's enclosures of `Real.sinh`, `Real.cosh`
and `Real.tanh` on a rational interval at a positive series order. The `_sound` theorems show
that each contains the function value at every point of the interval.

## Implementation notes

The enclosures and their proofs are FloatLib's, built from its exponential point enclosure (see
`CAS.Continuum.Interval.Elementary.Exp`). `sinh x = (exp x - exp (-x)) / 2` is monotone and is
enclosed from its values at the two endpoints. `cosh` is enclosed in the same way on the range
of `|x|`, with its lower bound raised to `1`. `tanh x = (u - 1) / (u + 1)` with `u = exp (2 x)`,
where the bounds for `u` are raised to `0` so that the denominator stays positive. We add only
the endpoint order of the `RationalInterval` and the translation to `MemReal`.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

/-- FloatLib's enclosure of `Real.sinh` on `I` at series order `order`. -/
def sinhRange (order : ℕ+) (I : RationalInterval) : RationalInterval :=
  ofFloatLib (FloatLib.Numerics.Interval.sinhBounds I.toFloatLib order)
    (ordered_of_containsReal (FloatLib.Numerics.Interval.containsReal_sinhBounds
      I.toFloatLib order ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal)))

/-- `sinhRange order I` contains `Real.sinh x` for every `x ∈ I`. -/
theorem sinhRange_sound (order : ℕ+) (I : RationalInterval)
    {x : ℝ} (hx : I.MemReal x) :
    (sinhRange order I).MemReal (Real.sinh x) :=
  (memReal_ofFloatLib_iff _ _ _).mpr (FloatLib.Numerics.Interval.containsReal_sinhBounds
    I.toFloatLib order ((I.toFloatLib_containsReal_iff x).mpr hx))

/-- FloatLib's enclosure of `Real.cosh` on `I` at series order `order`. -/
def coshRange (order : ℕ+) (I : RationalInterval) : RationalInterval :=
  ofFloatLib (FloatLib.Numerics.Interval.coshBounds I.toFloatLib order)
    (ordered_of_containsReal (FloatLib.Numerics.Interval.containsReal_coshBounds
      I.toFloatLib order ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal)))

/-- `coshRange order I` contains `Real.cosh x` for every `x ∈ I`. -/
theorem coshRange_sound (order : ℕ+) (I : RationalInterval)
    {x : ℝ} (hx : I.MemReal x) :
    (coshRange order I).MemReal (Real.cosh x) :=
  (memReal_ofFloatLib_iff _ _ _).mpr (FloatLib.Numerics.Interval.containsReal_coshBounds
    I.toFloatLib order ((I.toFloatLib_containsReal_iff x).mpr hx))

/-- FloatLib's enclosure of `Real.tanh` on `I` at series order `order`. -/
def tanhRange (order : ℕ+) (I : RationalInterval) : RationalInterval :=
  ofFloatLib (FloatLib.Numerics.Interval.tanhBounds I.toFloatLib order)
    (ordered_of_containsReal (FloatLib.Numerics.Interval.containsReal_tanhBounds
      I.toFloatLib order ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal)))

/-- `tanhRange order I` contains `Real.tanh x` for every `x ∈ I`. -/
theorem tanhRange_sound (order : ℕ+) (I : RationalInterval)
    {x : ℝ} (hx : I.MemReal x) :
    (tanhRange order I).MemReal (Real.tanh x) :=
  (memReal_ofFloatLib_iff _ _ _).mpr (FloatLib.Numerics.Interval.containsReal_tanhBounds
    I.toFloatLib order ((I.toFloatLib_containsReal_iff x).mpr hx))


end RationalInterval
end CAS.Continuum

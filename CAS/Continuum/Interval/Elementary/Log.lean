/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Basic
public import FloatLib.Numerics.Enclosure.Interval.ElementaryProof

/-!
# Logarithm enclosures on positive intervals from FloatLib

For a rational interval `I` with `0 < I.lo`, `logRangeWith I terms hpos` is FloatLib's
logarithm enclosure, and `logRange` uses `logSeriesTerms = 10` terms. FloatLib's `logBounds?`
cannot fail on a positive interval, so no fallback is needed. The point versions
`logPointIntervalWith` and `logPointInterval` treat a positive rational `q`. Each `_sound`
theorem shows that the enclosure contains `Real.log x` for every `x ∈ I`.

## Implementation notes

The algorithm and its proof are FloatLib's. `Real.log` is monotone on the positive reals, so
`Interval.logBounds?` evaluates the point enclosure `Enclosure.log` at the two endpoints. The
point enclosure inverts an argument below `1` and negates the result, divides by the largest
power of two not above the argument, and evaluates `log (1 + t) - log (1 - t)` with
`t = (x - 1) / (x + 1)`, so `|t| ≤ 1 / 3`; each series is a partial sum of DLMF 4.6.1 with a
geometric tail bound, and the removed multiple of `log 2` is added back from the same series at
`x = 2`. FloatLib proves the bounds from Mathlib's `Real.abs_log_sub_add_sum_range_le`. We pass
`logFloatLibDegree terms = 2 * max terms 1` as FloatLib's degree and rule out the `none` branch
with `0 < I.lo`.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>.
* NIST Digital Library of Mathematical Functions, §4.6 Power Series, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/4.6>. Equation (4.6.1), the series of `ln (1 + z)`, and (4.6.4), the
  series in `(z - 1) / (z + 1)`.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

/-- Default number of logarithm series terms. -/
def logSeriesTerms : Nat := 10

/-- FloatLib series degree for `terms` requested terms: `2 * max terms 1`. -/
def logFloatLibDegree (terms : ℕ) : ℕ := 2 * max terms 1

/-- FloatLib's enclosure of `Real.log` on an interval with positive lower endpoint. -/
def logRangeWith (I : RationalInterval) (terms : ℕ) (hpos : 0 < I.lo) :
    RationalInterval :=
  match h : FloatLib.Numerics.Interval.logBounds? I.toFloatLib (logFloatLibDegree terms) with
  | some J => ofFloatLib J (ordered_of_containsReal
      (FloatLib.Numerics.Interval.containsReal_logBounds? h
        ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal)))
  | none => False.elim (by simp [FloatLib.Numerics.Interval.logBounds?, hpos] at h)

/-- `logRangeWith I terms hpos` contains `Real.log x` for every `x ∈ I`. -/
theorem logRangeWith_sound (I : RationalInterval) (terms : ℕ) (hpos : 0 < I.lo)
    {x : ℝ} (hx : I.MemReal x) :
    (logRangeWith I terms hpos).MemReal (Real.log x) := by
  unfold logRangeWith
  split
  next J h =>
    exact (memReal_ofFloatLib_iff _ _ _).mpr
      (FloatLib.Numerics.Interval.containsReal_logBounds? h
        ((I.toFloatLib_containsReal_iff x).mpr hx))
  next h => simp [FloatLib.Numerics.Interval.logBounds?, hpos] at h

/-- Logarithm enclosure of a positive interval with `logSeriesTerms` terms. -/
def logRange (I : RationalInterval) (hpos : 0 < I.lo) : RationalInterval :=
  logRangeWith I logSeriesTerms hpos

/-- `logRange I hpos` contains `Real.log x` for every `x ∈ I`. -/
theorem logRange_sound (I : RationalInterval) (hpos : 0 < I.lo)
    {x : ℝ} (hx : I.MemReal x) : (logRange I hpos).MemReal (Real.log x) :=
  logRangeWith_sound I logSeriesTerms hpos hx

/-- FloatLib's enclosure of `Real.log q` for a positive rational `q`. -/
def logPointIntervalWith (terms : ℕ) (q : ℚ) (hq : 0 < q) : RationalInterval :=
  logRangeWith (const q) terms hq

/-- `logPointIntervalWith terms q hq` contains `Real.log q`. -/
theorem logPointIntervalWith_sound (terms : ℕ) (q : ℚ) (hq : 0 < q) :
    (logPointIntervalWith terms q hq).MemReal (Real.log q) :=
  logRangeWith_sound (const q) terms hq (memReal_const q)

/-- Enclosure of `Real.log q` with `logSeriesTerms` terms. -/
def logPointInterval (q : ℚ) (hq : 0 < q) : RationalInterval :=
  logPointIntervalWith logSeriesTerms q hq

/-- `logPointInterval q hq` contains `Real.log q`. -/
theorem logPointInterval_sound (q : ℚ) (hq : 0 < q) :
    (logPointInterval q hq).MemReal (Real.log q) :=
  logPointIntervalWith_sound logSeriesTerms q hq


end RationalInterval
end CAS.Continuum

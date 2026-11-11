/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.DyadicHull
public import FloatLib.Numerics.Enclosure.Interval.InverseTrigProof

/-!
# Arcsine enclosures from FloatLib

Mathlib's `Real.arcsin` is total and constant outside `[-1, 1]`, so clamping the argument with
`inverseTrigArgument` does not change its value (`arcsin_inverseTrigArgument`).
`asinPointInterval q` evaluates FloatLib's `asinBounds?` at the clamped argument, rounds the
result outward to a dyadic grid, and falls back to `[-piUpper / 2, piUpper / 2]` when FloatLib
rejects the precision. Monotonicity of `Real.arcsin` turns the endpoint enclosures into
`asinRange I`, which contains `Real.arcsin x` for every `x ∈ I` (`asinRange_sound`).

## Implementation notes

FloatLib computes and proves the point enclosure. An interior argument goes through
`arctan (x / √(1 - x ^ 2))`, with integer square-root bounds for the denominator and FloatLib's
arctangent kernel, at series degree `32`, for the quotient; `±1` give `±π / 2` from the Machin
enclosure of `π / 4`. FloatLib returns `none` outside `[-1, 1]` and when its square-root lower
bound cannot separate the root from zero. The clamping, the fallback, the interval version and
the precision schedule are ours. Since `√(1 - q ^ 2) ≥ 1 / q.den` for `|q| < 1`, the
square-root precision `inverseTrigPrecision q = 32 + 2 * q.den.log2` grows with the
denominator, and the dyadic hull rounds on a grid 32 bits finer, of at least 128 bits.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

/-- The rational `q` clamped to `[-1, 1]`. -/
def inverseTrigArgument (q : ℚ) : ℚ := max (-1) (min 1 q)

/-- Mathlib's total arcsine agrees with its value at the clamped argument. -/
theorem arcsin_inverseTrigArgument (q : ℚ) :
    Real.arcsin (inverseTrigArgument q : ℝ) = Real.arcsin (q : ℝ) := by
  simpa [inverseTrigArgument, Set.coe_projIcc] using Real.arcsin_projIcc (q : ℝ)

/-- The interval `[-piUpper / 2, piUpper / 2]`, which contains every value of `Real.arcsin`. -/
def asinFallback : RationalInterval where
  lo := -piUpper / 2
  hi := piUpper / 2
  hle := by norm_num [piUpper]

/-- `asinFallback` contains `Real.arcsin x` for every real `x`. -/
theorem asinFallback_sound (x : ℝ) : asinFallback.MemReal (Real.arcsin x) := by
  push_cast [MemReal, asinFallback]
  constructor <;>
    linarith [pi_le_piUpper, Real.neg_pi_div_two_le_arcsin x, Real.arcsin_le_pi_div_two x]

/-- FloatLib square-root precision for the argument `q`: `32 + 2 * q.den.log2`. -/
def inverseTrigPrecision (q : ℚ) : Nat := 32 + 2 * q.den.log2

/-- Outward rounding precision: at least 128 bits and 32 bits beyond `inverseTrigPrecision`. -/
def inverseTrigRoundingPrecision (q : ℚ) : Nat := max 128 (inverseTrigPrecision q + 32)

/-- FloatLib arcsine with outward rounding finer than its square-root precision. -/
def asinPointInterval (q : ℚ) : RationalInterval :=
  match h : FloatLib.Numerics.Interval.asinBounds?
      (const (inverseTrigArgument q)).toFloatLib 32 (inverseTrigPrecision q) with
  | some J => dyadicHull (inverseTrigRoundingPrecision q)
      (ofFloatLib J (ordered_of_containsReal
        (FloatLib.Numerics.Interval.containsReal_asinBounds? h
          (((const (inverseTrigArgument q)).toFloatLib_containsReal_iff _).mpr
            (memReal_const _)))))
  | none => asinFallback

/-- `asinPointInterval q` contains `Real.arcsin q`. -/
theorem asinPointInterval_sound (q : ℚ) :
    (asinPointInterval q).MemReal (Real.arcsin (q : ℝ)) := by
  unfold asinPointInterval
  split
  next J h =>
    exact dyadicHull_sound _ ((memReal_ofFloatLib_iff _ _ _).mpr (arcsin_inverseTrigArgument q ▸
      FloatLib.Numerics.Interval.containsReal_asinBounds? h
        (((const (inverseTrigArgument q)).toFloatLib_containsReal_iff _).mpr (memReal_const _))))
  next => exact asinFallback_sound _

/-- Arcsine range of an interval from the point enclosures at its two endpoints. -/
def asinRange (I : RationalInterval) : RationalInterval where
  lo := (asinPointInterval I.lo).lo
  hi := (asinPointInterval I.hi).hi
  hle := by
    have hmono := Real.arcsin_le_arcsin
      (show (I.lo : ℝ) ≤ I.hi by exact_mod_cast I.hle)
    exact_mod_cast (asinPointInterval_sound I.lo).1.trans
      (hmono.trans (asinPointInterval_sound I.hi).2)

/-- `asinRange I` contains `Real.arcsin x` for every `x ∈ I`. -/
theorem asinRange_sound (I : RationalInterval) {x : ℝ} (hx : I.MemReal x) :
    (asinRange I).MemReal (Real.arcsin x) := by
  -- Rewriting to the endpoint pair first keeps the kernel from comparing the structure
  -- `asinRange I` with `asinPointInterval I.lo`, which evaluates FloatLib's arcsine at a
  -- variable endpoint (30 s of kernel time for the term proof).
  have h : (asinRange I).toInterval =
      ⟨(asinPointInterval I.lo).lo, (asinPointInterval I.hi).hi⟩ := rfl
  rw [MemReal, h]
  exact ⟨(asinPointInterval_sound I.lo).1.trans (Real.arcsin_le_arcsin hx.1),
    (Real.arcsin_le_arcsin hx.2).trans (asinPointInterval_sound I.hi).2⟩

end RationalInterval
end CAS.Continuum

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Elementary.Asin

/-!
# Arccosine enclosures from FloatLib

`acosPointInterval q` encloses `Real.arccos q` for every rational `q`. It evaluates FloatLib's
`acosBounds?` at the argument clamped to `[-1, 1]`, which leaves Mathlib's total arccosine
unchanged (`arccos_inverseTrigArgument`), and falls back to `[0, piUpper]` when FloatLib rejects
the precision. Since `Real.arccos` is antitone, `acosRange I` is bounded below by the enclosure
at `I.hi` and above by the enclosure at `I.lo`; `acosRange_sound` shows that it contains
`Real.arccos x` for every `x ∈ I`.

## Implementation notes

FloatLib's `acosBounds?` is `π / 2 - arcsin x`, from its arcsine enclosure and its Machin
enclosure of `π / 4`, with the lower bound raised to `0` and the exact value `0` at `x = 1`;
FloatLib proves its containment. The clamping, the precision schedule and the dyadic rounding
are those of `asinPointInterval`; the fallback and the interval version are ours.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

/-- Mathlib's total arccosine agrees with its value at the clamped argument. -/
theorem arccos_inverseTrigArgument (q : ℚ) :
    Real.arccos (inverseTrigArgument q : ℝ) = Real.arccos (q : ℝ) := by
  simp only [Real.arccos_eq_pi_div_two_sub_arcsin, arcsin_inverseTrigArgument]

/-- The interval `[0, piUpper]`, which contains every value of `Real.arccos`. -/
def acosFallback : RationalInterval where
  lo := 0
  hi := piUpper
  hle := by norm_num [piUpper]

/-- `acosFallback` contains `Real.arccos x` for every real `x`. -/
theorem acosFallback_sound (x : ℝ) : acosFallback.MemReal (Real.arccos x) := by
  exact ⟨by simpa [acosFallback] using Real.arccos_nonneg x,
    (Real.arccos_le_pi x).trans pi_le_piUpper⟩

/-- FloatLib arccosine, clamped for totality and rounded outward to compact dyadic endpoints. -/
def acosPointInterval (q : ℚ) : RationalInterval :=
  match h : FloatLib.Numerics.Interval.acosBounds?
      (const (inverseTrigArgument q)).toFloatLib 32 (inverseTrigPrecision q) with
  | some J => dyadicHull (inverseTrigRoundingPrecision q)
      (ofFloatLib J (ordered_of_containsReal
        (FloatLib.Numerics.Interval.containsReal_acosBounds? h
          (((const (inverseTrigArgument q)).toFloatLib_containsReal_iff _).mpr
            (memReal_const _)))))
  | none => acosFallback

/-- `acosPointInterval q` contains `Real.arccos q`. -/
theorem acosPointInterval_sound (q : ℚ) :
    (acosPointInterval q).MemReal (Real.arccos (q : ℝ)) := by
  unfold acosPointInterval
  split
  next J h =>
    exact dyadicHull_sound _ ((memReal_ofFloatLib_iff _ _ _).mpr (arccos_inverseTrigArgument q ▸
      FloatLib.Numerics.Interval.containsReal_acosBounds? h
        (((const (inverseTrigArgument q)).toFloatLib_containsReal_iff _).mpr (memReal_const _))))
  next => exact acosFallback_sound _

/-- Arccosine range of an interval from the point enclosures at its two endpoints. -/
def acosRange (I : RationalInterval) : RationalInterval where
  lo := (acosPointInterval I.hi).lo
  hi := (acosPointInterval I.lo).hi
  hle := by
    have hanti := Real.arccos_le_arccos
      (show (I.lo : ℝ) ≤ I.hi by exact_mod_cast I.hle)
    exact_mod_cast (acosPointInterval_sound I.hi).1.trans
      (hanti.trans (acosPointInterval_sound I.lo).2)

/-- `acosRange I` contains `Real.arccos x` for every `x ∈ I`. -/
theorem acosRange_sound (I : RationalInterval) {x : ℝ} (hx : I.MemReal x) :
    (acosRange I).MemReal (Real.arccos x) := by
  -- As for `asinRange_sound`: the endpoint pair keeps the kernel from evaluating FloatLib's
  -- arccosine at a variable endpoint.
  have h : (acosRange I).toInterval =
      ⟨(acosPointInterval I.hi).lo, (acosPointInterval I.lo).hi⟩ := rfl
  rw [MemReal, h]
  exact ⟨(acosPointInterval_sound I.hi).1.trans (Real.arccos_le_arccos hx.2),
    (Real.arccos_le_arccos hx.1).trans (acosPointInterval_sound I.lo).2⟩

end RationalInterval
end CAS.Continuum

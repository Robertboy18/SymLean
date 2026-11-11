/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Integral
public import CAS.Certificate.Quadrature

/-!
# Integrating a uniform rational interval range

If `f` is integrable on a rational interval `X` and `f x ∈ I` for every `x ∈ X`, then
`∫ x in X.lo..X.hi, f x` lies in `(X.hi - X.lo) • I` (`cellIntegralInterval_sound`).

## Implementation notes

`cellIntegralInterval` is `scaleNonneg` with the width `X.hi - X.lo`, which multiplies the point
interval at that width by `I`, so it costs one rational interval multiplication. Its only caller
is `BatchRange.panel`, and the kernel evaluates it once per panel when it checks
`BatchRange.rangeCheck`. The theorem restates `intervalIntegral_mem` of
`CAS.Continuum.Interval.Rational.Integral`, whose hypothesis asks for the range only on the open
interval and follows from the one on `X`.
-/

@[expose] public section

open MeasureTheory Set

namespace CAS.Continuum.RationalInterval

/-- The interval `(X.hi - X.lo) • I`, which contains the integral over `X` of a function with
values in `I`. -/
def cellIntegralInterval (X I : RationalInterval) : RationalInterval :=
  scaleNonneg (X.hi - X.lo) (sub_nonneg.mpr X.hle) I

/-- If `f` is integrable on `X` and `f x ∈ I` for `x ∈ X`, then `cellIntegralInterval X I`
contains `∫ x in X.lo..X.hi, f x`. -/
theorem cellIntegralInterval_sound (X I : RationalInterval) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (X.lo : ℝ) (X.hi : ℝ))
    (hbound : ∀ x, X.MemReal x → I.MemReal (f x)) :
    (cellIntegralInterval X I).MemReal (∫ x in (X.lo : ℝ)..(X.hi : ℝ), f x) :=
  intervalIntegral_mem X.hle hf fun x hx ↦ hbound x ⟨hx.1.le, hx.2.le⟩

end CAS.Continuum.RationalInterval

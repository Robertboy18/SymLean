/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Arithmetic
public import CAS.Continuum.Interval.Rational.FiniteSum

public import CAS.Analysis.Fourier.HilbertTransform.LogPotential.Polynomial
public import CAS.Continuum.Interval.Elementary.Log

/-!
# Interval evaluation of the primitives of `t ^ n * log |t|`

`logMonomialPrimitive n t = t ^ (n + 1) log t / (n + 1) - t ^ (n + 1) / (n + 1) ^ 2` is the
continuous primitive of `t ^ n * log t` vanishing at zero. `logAbsPointIntervalWith terms q`
encloses Mathlib's total `Real.log q` at every rational `q`: through `Real.log |q|` for `q ≠ 0`,
and `q = 0` gives `[0, 0]`. `logMonomialPrimitiveInterval terms n q` evaluates the primitive at
`q` with these enclosures, and `logMonomialPrimitiveInterval_sound` shows that it contains
`logMonomialPrimitive n q`.

## Implementation notes

Only the logarithm is an interval. The coefficients `q ^ (n + 1) / (n + 1)` and
`q ^ (n + 1) / (n + 1) ^ 2` are exact rationals passed as `const`, so one primitive costs one
logarithm enclosure, one interval product and one subtraction. The logarithm is
`logPointIntervalWith` of `CAS.Continuum.Interval.Elementary.Log`, FloatLib's enclosure at the
positive point `|q|`. `logAbsPointIntervalWith_sound` rewrites with `Rat.cast_abs` and
`Real.log_abs`, and `logMonomialPrimitiveInterval_sound` composes `mul_sound`, `sub_sound` and
`memReal_const` and then matches the casts with `logMonomialPrimitive`. The panel sums of
`CAS.Continuum.Interval.Rational.TranslatedLogPanel` are built from these primitives, and
`logAbsPointFrac` in `CAS.Numerics.GridBallLog` mirrors `logAbsPointIntervalWith` on balls.
-/

@[expose] public section

namespace CAS.Continuum.RationalInterval

open CAS.Analysis

/-- An enclosure of Mathlib's total `Real.log q` at any rational `q`, using `log |q|`. -/
def logAbsPointIntervalWith (terms : ℕ) (q : ℚ) : RationalInterval :=
  if hq : q = 0 then const 0
  else logPointIntervalWith terms |q| (abs_pos.mpr hq)

/-- `logAbsPointIntervalWith terms q` contains `Real.log q`, including `Real.log 0 = 0`. -/
theorem logAbsPointIntervalWith_sound (terms : ℕ) (q : ℚ) :
    (logAbsPointIntervalWith terms q).MemReal (Real.log q) := by
  unfold logAbsPointIntervalWith
  split_ifs with hq
  · simpa [hq] using memReal_const 0
  · simpa only [Rat.cast_abs, Real.log_abs] using
      logPointIntervalWith_sound terms |q| (abs_pos.mpr hq)

/-- Interval evaluation of `logMonomialPrimitive n q` at a rational point. -/
def logMonomialPrimitiveInterval (terms n : ℕ) (q : ℚ) : RationalInterval :=
  ((const (q ^ (n + 1) / (n + 1))).mul (logAbsPointIntervalWith terms q)).sub
    (const (q ^ (n + 1) / (n + 1) ^ 2))

/-- `logMonomialPrimitiveInterval terms n q` contains `logMonomialPrimitive n q`. -/
theorem logMonomialPrimitiveInterval_sound (terms n : ℕ) (q : ℚ) :
    (logMonomialPrimitiveInterval terms n q).MemReal (logMonomialPrimitive n q) := by
  have h := sub_sound
    (mul_sound (memReal_const (q ^ (n + 1) / (n + 1)))
      (logAbsPointIntervalWith_sound terms q))
    (memReal_const (q ^ (n + 1) / (n + 1) ^ 2))
  simpa only [logMonomialPrimitiveInterval, logMonomialPrimitive, Rat.cast_div,
    Rat.cast_pow, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, div_mul_eq_mul_div] using h

end CAS.Continuum.RationalInterval

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.IntervalBalls

/-!
# Squares of interval balls of any sign

`IntervalBalls.sqAny P S` encloses `I.powNat 2` for every interval `I` enclosed by `S`, whatever
the signs of its endpoints (`sqAny_encloses`). In each of the three sign cases the exact
absolute-value range `absBounds I` has the lower endpoint `max (max 0 I.lo) (max 0 (-I.hi))` and
the upper endpoint `max (-I.lo) I.hi` (`absBounds_lo_eq`, `absBounds_hi_eq`); `absRange` computes
both with clamps and maxima of balls, and `sqAny` squares them.

## Implementation notes

We compute the absolute-value range without a branch. `IntervalBalls.powNat P S 2` follows the
sign branch of the exact range only when the balls decide that sign, so an interval with an
endpoint exactly zero, such as a product with a vanishing cutoff, gives invalid balls there.
-/

@[expose] public section

namespace CAS.Numerics

open CAS.Continuum

namespace IntervalBalls

/-- Balls of the absolute-value range of an interval of any sign. -/
def absRange (S : IntervalBalls) : IntervalBalls :=
  ⟨GridBall.max S.lo.clamp S.hi.neg.clamp, GridBall.max S.lo.neg S.hi⟩

/-- The square of an interval at precision `P`, for an interval of any sign. -/
def sqAny (P : ℕ) (S : IntervalBalls) : IntervalBalls :=
  ⟨GridBall.sqNonneg P (absRange S).lo, GridBall.sqNonneg P (absRange S).hi⟩

/-- The lower endpoint of the absolute-value range without a case distinction. -/
theorem absBounds_lo_eq (I : RationalInterval) :
    (FloatLib.Numerics.Interval.absBounds I.toFloatLib).lo =
      max (max 0 I.lo) (max 0 (-I.hi)) := by
  have hle : I.lo ≤ I.hi := I.hle
  unfold FloatLib.Numerics.Interval.absBounds
  split_ifs with h₁ h₂
  · rw [max_eq_right h₁, max_eq_left (by linarith : -I.hi ≤ 0), max_eq_left h₁]
  · rw [max_eq_left (not_le.mp h₁).le, max_eq_right (by linarith : (0 : ℚ) ≤ -I.hi),
      max_eq_right (by linarith : (0 : ℚ) ≤ -I.hi)]
  · rw [max_eq_left (not_le.mp h₁).le, max_eq_left (by linarith : -I.hi ≤ 0), max_self]

/-- The upper endpoint of the absolute-value range without a case distinction. -/
theorem absBounds_hi_eq (I : RationalInterval) :
    (FloatLib.Numerics.Interval.absBounds I.toFloatLib).hi = max (-I.lo) I.hi := by
  have hle : I.lo ≤ I.hi := I.hle
  unfold FloatLib.Numerics.Interval.absBounds
  split_ifs with h₁ h₂
  · rw [max_eq_right (by linarith)]
  · rw [max_eq_left (by linarith)]
  · rfl

/-- If `S` encloses `I` at precision `P`, then `absRange S` encloses both endpoints of FloatLib's
absolute-value range `Interval.absBounds I.toFloatLib`, whatever the signs of the endpoints of
`I`. -/
theorem absRange_encloses {P : ℕ} {S : IntervalBalls} {I : RationalInterval}
    (hS : S.Encloses P I) :
    (absRange S).lo.Encloses P (FloatLib.Numerics.Interval.absBounds I.toFloatLib).lo ∧
      (absRange S).hi.Encloses P (FloatLib.Numerics.Interval.absBounds I.toFloatLib).hi := by
  rw [absBounds_lo_eq, absBounds_hi_eq]
  exact ⟨GridBall.max_encloses (GridBall.clamp_encloses_max hS.1)
      (GridBall.clamp_encloses_max (GridBall.neg_encloses hS.2)),
    GridBall.max_encloses (GridBall.neg_encloses hS.1) hS.2⟩

/-- If `S` encloses `I` at precision `P`, then `sqAny P S` encloses `I.powNat 2`, whatever the signs
of the endpoints of `I`. -/
theorem sqAny_encloses {P : ℕ} {S : IntervalBalls} {I : RationalInterval}
    (hS : S.Encloses P I) : (sqAny P S).Encloses P (I.powNat 2) := by
  have hlo : (I.powNat 2).lo = (FloatLib.Numerics.Interval.absBounds I.toFloatLib).lo ^ 2 := by
    change (FloatLib.Numerics.Interval.powBounds I.toFloatLib 2).lo = _
    simp only [FloatLib.Numerics.Interval.powBounds, show (2 : ℕ) ≠ 0 by norm_num, ↓reduceIte,
      show 2 % 2 = 0 by norm_num, npowBinRec_eq_pow]
  have hhi : (I.powNat 2).hi = (FloatLib.Numerics.Interval.absBounds I.toFloatLib).hi ^ 2 := by
    change (FloatLib.Numerics.Interval.powBounds I.toFloatLib 2).hi = _
    simp only [FloatLib.Numerics.Interval.powBounds, show (2 : ℕ) ≠ 0 by norm_num, ↓reduceIte,
      show 2 % 2 = 0 by norm_num, npowBinRec_eq_pow]
  have hA := absRange_encloses hS
  have hN := absBounds_nonneg I
  exact ⟨hlo ▸ GridBall.sqNonneg_encloses hA.1 hN.1, hhi ▸ GridBall.sqNonneg_encloses hA.2 hN.2⟩

end IntervalBalls

end CAS.Numerics

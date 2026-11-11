/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Basic

/-!
# Widening rational interval bounds

`mem_Icc_of_bounds`: if `x` lies in a rational interval `I` and `a ≤ I.lo`, `I.hi ≤ b`, then
`x ∈ Set.Icc a b`. `memReal_of_bounds` is the same statement with `[a, b]` given as a rational
interval. `checkBounds` gives an executable endpoint check with a soundness theorem.

## Implementation notes

`checkBounds` is a `Bool`, two `decide`d comparisons of rationals joined by `&&`, so the kernel
decides a closed instance by evaluation; `checkBounds_sound` turns a successful check back into
the two inequalities by `Bool.and_eq_true` and `decide_eq_true_eq`. The bounds can be proposed
by any computation: they need only contain `I`. The ball certificates of
`CAS.Numerics.IntervalBalls` decide `checkBoundsCertain` and recover `checkBounds` through
`checkBounds_of_certain`, and `sum_memReal_of_bounds` of
`CAS.Continuum.Interval.Rational.FiniteSum` rests on `mem_Icc_of_bounds`.
-/

@[expose] public section

open Set

namespace CAS.Continuum.RationalInterval

/-- Check whether proposed rational endpoints contain an interval. -/
def checkBounds (bounds : ℚ × ℚ) (I : RationalInterval) : Bool :=
  decide (bounds.1 ≤ I.lo) && decide (I.hi ≤ bounds.2)

/-- A successful endpoint check establishes both rational bounds. -/
theorem checkBounds_sound {bounds : ℚ × ℚ} {I : RationalInterval}
    (h : checkBounds bounds I = true) :
    bounds.1 ≤ I.lo ∧ I.hi ≤ bounds.2 := by
  simpa only [checkBounds, Bool.and_eq_true, decide_eq_true_eq] using h

/-- A member of `I` lies in every rational interval `[a, b]` containing `I`. -/
theorem mem_Icc_of_bounds {I : RationalInterval} {x : ℝ} {a b : ℚ}
    (hx : I.MemReal x) (ha : a ≤ I.lo) (hb : I.hi ≤ b) :
    x ∈ Icc (a : ℝ) (b : ℝ) :=
  ⟨(Rat.cast_le.mpr ha).trans hx.1, hx.2.trans (Rat.cast_le.mpr hb)⟩

/-- A member of `J` is a member of every rational interval `I` containing `J`. -/
theorem memReal_of_bounds {I J : RationalInterval} {x : ℝ}
    (hlo : I.lo ≤ J.lo) (hhi : J.hi ≤ I.hi) (hx : J.MemReal x) : I.MemReal x :=
  mem_Icc_of_bounds hx hlo hhi

end CAS.Continuum.RationalInterval

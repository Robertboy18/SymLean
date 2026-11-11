/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Basic

/-!
# The meet of two rational intervals

When a real number is enclosed by two intervals computed in different ways, it lies in their
intersection. `RationalInterval.meet I J` is that intersection when its endpoints are ordered,
and `I` otherwise; in both cases it contains every common member (`memReal_meet`).

## Main definitions

* `RationalInterval.meet`: the intersection of `I` and `J` when it is nonempty, and `I` otherwise.

## Main results

* `memReal_meet`: a common member of two intervals lies in their meet.

## Implementation notes

`meet` compares `max I.lo J.lo` with `min I.hi J.hi` in `ℚ` and builds the result with
`ofBounds`, without FloatLib. Unlike `intersect` of `CAS.Continuum.IntervalRefinement`, it needs
no overlap proof: a common member forces the endpoint order, so the fallback `I` only makes the
function total, and `memReal_meet` closes that branch with the membership in `I` and the other
by `simp` with `ofBounds`. No module of SymLean imports this one; it serves certificates built on
the library.
-/

@[expose] public section

namespace CAS.Continuum.RationalInterval

/-- The intersection of `I` and `J` when it is nonempty, and `I` otherwise. -/
def meet (I J : RationalInterval) : RationalInterval :=
  if h : max I.lo J.lo ≤ min I.hi J.hi then ofBounds _ _ h else I

/-- A common member of two intervals lies in their meet. -/
theorem memReal_meet {I J : RationalInterval} {x : ℝ} (hI : I.MemReal x) (hJ : J.MemReal x) :
    (I.meet J).MemReal x := by
  unfold meet
  split
  · exact ⟨by simp [ofBounds, hI.1, hJ.1], by simp [ofBounds, hI.2, hJ.2]⟩
  · exact hI

end CAS.Continuum.RationalInterval

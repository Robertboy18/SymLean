/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

/-!
# Absorption of a mixed quadratic term

A nonpositive discriminant bounds the mixed term by the diagonal energies:
`mixed_energy_le_of_discriminant` proves `b E H ≤ A E² + B H²` from `0 ≤ A`, `0 ≤ B` and
`b² ≤ 4 A B`, including the degenerate case `A = 0`, without dividing by `A` or `B`. The
arithmetic phase of `cas` (`CAS.Tactic.Arithmetic`) applies it to scalar mixed quadratic terms.
-/

@[expose] public section

namespace CAS.Analysis.Scalar

/-- A scalar discriminant certifies absorption of the mixed low/high term.
The two diagonal margins may vanish, so no division by a margin is used. -/
theorem mixed_energy_le_of_discriminant (A B b E H : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hdisc : b ^ 2 ≤ 4 * A * B) :
    b * E * H ≤ A * E ^ 2 + B * H ^ 2 := by
  rcases eq_or_lt_of_le hA with hzero | hpos
  · subst A
    have hb : b = 0 := by nlinarith only [hdisc, sq_nonneg b]
    rw [hb]
    simpa using mul_nonneg hB (sq_nonneg H)
  · have hquad := add_nonneg (sq_nonneg (2 * A * E - b * H))
      (mul_nonneg (sub_nonneg.mpr hdisc) (sq_nonneg H))
    have hfactor : 0 ≤ 4 * A * (A * E ^ 2 + B * H ^ 2 - b * E * H) := by
      nlinarith only [hquad]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (by positivity : 0 < 4 * A)).mp hfactor)

end CAS.Analysis.Scalar

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Basic
public import FloatLib.Numerics.Enclosure.Interval.ElementaryProof

/-!
# Square-root enclosures from FloatLib

For a nonnegative rational `q`, FloatLib's `sqrtPointBounds` is applied to `q * q.den ^ 2` and
the result is divided by `q.den`. This keeps exact rational squares exact and gives an enclosure
of `√q` of width at most `1 / (q.den * 2 ^ steps)` (`sqrtNonnegativePointInterval_width_le`).
Mathlib's `Real.sqrt` is zero on negative arguments, so `sqrtPointInterval` returns `[0, 0]`
there. Monotonicity of `Real.sqrt` gives the interval version `sqrtRangeInterval`, defined on
every interval, including those that contain negative numbers; `sqrtRange` fixes
`defaultSqrtRefinementSteps = 12`.

## Implementation notes

FloatLib's `Interval.sqrtPointBounds x p` takes the integer square root of `⌊x * 4 ^ p⌋` as the
lower endpoint on the grid of spacing `2 ^ (-p)` and one grid step more as the upper endpoint,
unless the lower endpoint squares to `x`; FloatLib proves the containment and the width bound
`2 ^ (-p)`. The scaling is ours. `q * q.den ^ 2 = q.num * q.den` is an integer, so the floor
loses nothing; a square `(a / b) ^ 2` in lowest terms scales to `(a * b) ^ 2`, whose root is
found exactly; and the division by `q.den` turns FloatLib's width bound into
`1 / (q.den * 2 ^ steps)`. The `[0, 0]` branch and the interval version are ours as well.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

private theorem scaledSqrtBounds_sound (q : ℚ) (hq : 0 ≤ q) (steps : Nat) :
    let B := FloatLib.Numerics.Interval.sqrtPointBounds (q * (q.den : ℚ) ^ 2) steps
    ((B.lo / q.den : ℚ) : ℝ) ≤ Real.sqrt (q : ℝ) ∧
      Real.sqrt (q : ℝ) ≤ ((B.hi / q.den : ℚ) : ℝ) := by
  have h := (FloatLib.Numerics.Interval.containsReal_some_iff _ _).mp
    (FloatLib.Numerics.Interval.containsReal_sqrtPointBounds
      (q * (q.den : ℚ) ^ 2) steps (mul_nonneg hq (sq_nonneg _)))
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hsqrt : Real.sqrt ((q * (q.den : ℚ) ^ 2 : ℚ) : ℝ) = Real.sqrt (q : ℝ) * q.den := by
    push_cast
    rw [Real.sqrt_mul (Rat.cast_nonneg.mpr hq), Real.sqrt_sq hd.le]
  rw [hsqrt] at h
  push_cast
  exact ⟨(div_le_iff₀ hd).mpr h.1, (le_div_iff₀ hd).mpr h.2⟩

/-- Enclosure of `√q` from FloatLib's bounds for `√(q * q.den ^ 2)`, divided by `q.den`. -/
def sqrtNonnegativePointInterval (q : ℚ) (hq : 0 ≤ q) (steps : Nat) :
    RationalInterval where
  lo := (FloatLib.Numerics.Interval.sqrtPointBounds (q * (q.den : ℚ) ^ 2) steps).lo / q.den
  hi := (FloatLib.Numerics.Interval.sqrtPointBounds (q * (q.den : ℚ) ^ 2) steps).hi / q.den
  hle := by
    have h := scaledSqrtBounds_sound q hq steps
    exact_mod_cast h.1.trans h.2

/-- `sqrtNonnegativePointInterval q hq steps` contains `Real.sqrt q`. -/
theorem sqrtNonnegativePointInterval_sound (q : ℚ) (hq : 0 ≤ q) (steps : Nat) :
    (sqrtNonnegativePointInterval q hq steps).MemReal (Real.sqrt (q : ℝ)) :=
  scaledSqrtBounds_sound q hq steps

/-- The enclosure of `√q` has width at most `1 / (q.den * 2 ^ steps)`. -/
theorem sqrtNonnegativePointInterval_width_le (q : ℚ) (hq : 0 ≤ q) (steps : Nat) :
    (sqrtNonnegativePointInterval q hq steps).hi -
      (sqrtNonnegativePointInterval q hq steps).lo ≤ 1 / ((q.den : ℚ) * 2 ^ steps) := by
  change _ / (q.den : ℚ) - _ / (q.den : ℚ) ≤ _
  rw [← sub_div, mul_comm (q.den : ℚ), ← div_div]
  exact div_le_div_of_nonneg_right
    (FloatLib.Numerics.Interval.sqrtPointBounds_width_le _ steps) (Nat.cast_nonneg _)

/-- Enclosure of Mathlib's total `Real.sqrt q`; negative `q` gives the interval `[0, 0]`. -/
def sqrtPointInterval (q : ℚ) (steps : Nat) : RationalInterval :=
  if hq : 0 ≤ q then sqrtNonnegativePointInterval q hq steps else const 0

/-- `sqrtPointInterval q steps` contains `Real.sqrt q` for every rational `q`. -/
theorem sqrtPointInterval_sound (q : ℚ) (steps : Nat) :
    (sqrtPointInterval q steps).MemReal (Real.sqrt (q : ℝ)) := by
  unfold sqrtPointInterval
  split_ifs with hq
  · exact sqrtNonnegativePointInterval_sound q hq steps
  · simpa [Real.sqrt_eq_zero_of_nonpos, (not_le.mp hq).le] using memReal_const 0

/-- Square-root range of an interval from the point enclosures at its two endpoints. -/
def sqrtRangeInterval (I : RationalInterval) (steps : Nat) : RationalInterval where
  lo := (sqrtPointInterval I.lo steps).lo
  hi := (sqrtPointInterval I.hi steps).hi
  hle := by
    have hlo := sqrtPointInterval_sound I.lo steps
    have hhi := sqrtPointInterval_sound I.hi steps
    have hmono := Real.sqrt_le_sqrt (show (I.lo : ℝ) ≤ I.hi by exact_mod_cast I.hle)
    exact_mod_cast hlo.1.trans (hmono.trans hhi.2)

/-- `sqrtRangeInterval I steps` contains `Real.sqrt x` for every `x ∈ I`. -/
theorem sqrtRangeInterval_sound (I : RationalInterval) (steps : Nat)
    {x : ℝ} (hx : I.MemReal x) :
    (sqrtRangeInterval I steps).MemReal (Real.sqrt x) :=
  ⟨(sqrtPointInterval_sound I.lo steps).1.trans (Real.sqrt_le_sqrt hx.1),
    (Real.sqrt_le_sqrt hx.2).trans (sqrtPointInterval_sound I.hi steps).2⟩

/-- Default binary precision on the denominator grid. -/
def defaultSqrtRefinementSteps : Nat := 12

/-- Square-root range at the default precision `defaultSqrtRefinementSteps`. -/
def sqrtRange (I : RationalInterval) : RationalInterval :=
  sqrtRangeInterval I defaultSqrtRefinementSteps

/-- `sqrtRange I` contains `Real.sqrt x` for every `x ∈ I`. -/
theorem sqrtRange_sound (I : RationalInterval) {x : ℝ} (hx : I.MemReal x) :
    (sqrtRange I).MemReal (Real.sqrt x) :=
  sqrtRangeInterval_sound I defaultSqrtRefinementSteps hx

end RationalInterval
end CAS.Continuum

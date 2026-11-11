/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Basic

/-!
# Decimal digits from a rational enclosure

Closed Boolean comparisons of a rational interval with two decimal bounds, and the statements
they give for every real number in the interval. A computation that encloses a real value `y`
in `I` (a special-function evaluator, a quadrature rule) turns into certified decimal digits of
`y` through the check.

* `decimalLowerCheck I lo hi`: `lo ≤ I.lo` and `I.hi < hi`, hence `lo ≤ y < hi`.
* `decimalUpperCheck I lo hi`: `lo < I.lo` and `I.hi ≤ hi`, hence `lo < y ≤ hi`.
* `decimalEnclosureCheck I lo hi`: `lo ≤ I.lo` and `I.hi ≤ hi`, hence `lo ≤ y ≤ hi`.

The theorems `of_decimalLowerCheck` and its variants state the conclusions with the bounds
written as `m / 10 ^ k` or `m * 10 ^ k`.

## Implementation notes

Each check is a `Bool`, two `decide`d comparisons of rationals joined by `&&`, so one kernel
evaluation decides a closed instance. We use half-open intervals because they fix the digits:
`m / 10 ^ k ≤ y < (m + 1) / 10 ^ k` says that `⌊10 ^ k * y⌋ = m`, and the upper check gives the
digits of `|y|` for a negative `y`. The primed theorems unfold the check with `Bool.and_eq_true`
and `decide_eq_true_eq` and chain the comparisons with `I.MemReal y` through `Rat.cast_le` and
`Rat.cast_lt`; the unprimed ones push the casts of the decimal bounds by `simpa`.
`CAS.Command.SpecialFunctions` imports the module, but no SymLean declaration calls the checks:
`#cas [N d]` decides `DigitsEval.lowerCheck` and its variants, the same comparisons on the
interval returned by its evaluator.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

/-- `I` lies in `[lo, hi)`. -/
def decimalLowerCheck (I : RationalInterval) (lo hi : ℚ) : Bool :=
  decide (lo ≤ I.lo) && decide (I.hi < hi)

/-- `I` lies in `(lo, hi]`. -/
def decimalUpperCheck (I : RationalInterval) (lo hi : ℚ) : Bool :=
  decide (lo < I.lo) && decide (I.hi ≤ hi)

/-- `I` lies in `[lo, hi]`. -/
def decimalEnclosureCheck (I : RationalInterval) (lo hi : ℚ) : Bool :=
  decide (lo ≤ I.lo) && decide (I.hi ≤ hi)

variable {I : RationalInterval} {y : ℝ}

/-- If `y` lies in the rational interval `I` and `decimalLowerCheck I lo hi` holds, then
`lo ≤ y < hi`, for all rational `lo` and `hi`. -/
theorem of_decimalLowerCheck' (hy : I.MemReal y) {lo hi : ℚ}
    (h : I.decimalLowerCheck lo hi = true) : (lo : ℝ) ≤ y ∧ y < hi := by
  simp only [decimalLowerCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨(Rat.cast_le.mpr h.1).trans hy.1, hy.2.trans_lt (Rat.cast_lt.mpr h.2)⟩

/-- If `y` lies in the rational interval `I` and `decimalUpperCheck I lo hi` holds, then
`lo < y ≤ hi`, for all rational `lo` and `hi`. -/
theorem of_decimalUpperCheck' (hy : I.MemReal y) {lo hi : ℚ}
    (h : I.decimalUpperCheck lo hi = true) : (lo : ℝ) < y ∧ y ≤ hi := by
  simp only [decimalUpperCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨(Rat.cast_lt.mpr h.1).trans_le hy.1, hy.2.trans (Rat.cast_le.mpr h.2)⟩

/-- If `y` lies in the rational interval `I` and `decimalEnclosureCheck I lo hi` holds, then
`lo ≤ y ≤ hi`, for all rational `lo` and `hi`. -/
theorem of_decimalEnclosureCheck' (hy : I.MemReal y) {lo hi : ℚ}
    (h : I.decimalEnclosureCheck lo hi = true) : (lo : ℝ) ≤ y ∧ y ≤ hi := by
  simp only [decimalEnclosureCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨(Rat.cast_le.mpr h.1).trans hy.1, hy.2.trans (Rat.cast_le.mpr h.2)⟩

/-- The digits of a positive value: `m / 10 ^ k ≤ y < (m + 1) / 10 ^ k`. -/
theorem of_decimalLowerCheck (hy : I.MemReal y) {m k : ℕ}
    (h : I.decimalLowerCheck ((m : ℚ) / 10 ^ k) (((m : ℚ) + 1) / 10 ^ k) = true) :
    (m : ℝ) / 10 ^ k ≤ y ∧ y < ((m : ℝ) + 1) / 10 ^ k := by
  simpa using of_decimalLowerCheck' hy h

/-- The digits of a negative value: `-(m + 1) / 10 ^ k < y ≤ -m / 10 ^ k`. -/
theorem of_decimalUpperCheck (hy : I.MemReal y) {m k : ℕ}
    (h : I.decimalUpperCheck (-((m : ℚ) + 1) / 10 ^ k) (-(m : ℚ) / 10 ^ k) = true) :
    -((m : ℝ) + 1) / 10 ^ k < y ∧ y ≤ -(m : ℝ) / 10 ^ k := by
  simpa using of_decimalUpperCheck' hy h

/-- The leading digits of a large positive value: `m 10 ^ k ≤ y < (m + 1) 10 ^ k`. -/
theorem of_scaledLowerCheck (hy : I.MemReal y) {m k : ℕ}
    (h : I.decimalLowerCheck ((m : ℚ) * 10 ^ k) (((m : ℚ) + 1) * 10 ^ k) = true) :
    (m : ℝ) * 10 ^ k ≤ y ∧ y < ((m : ℝ) + 1) * 10 ^ k := by
  simpa using of_decimalLowerCheck' hy h

/-- The leading digits of a large negative value: `-(m + 1) 10 ^ k < y ≤ -m 10 ^ k`. -/
theorem of_scaledUpperCheck (hy : I.MemReal y) {m k : ℕ}
    (h : I.decimalUpperCheck (-((m : ℚ) + 1) * 10 ^ k) (-(m : ℚ) * 10 ^ k) = true) :
    -((m : ℝ) + 1) * 10 ^ k < y ∧ y ≤ -(m : ℝ) * 10 ^ k := by
  simpa using of_decimalUpperCheck' hy h

/-- A decimal enclosure: `lo / 10 ^ k ≤ y ≤ hi / 10 ^ k`. -/
theorem of_decimalEnclosureCheck (hy : I.MemReal y) {lo hi : ℤ} {k : ℕ}
    (h : I.decimalEnclosureCheck ((lo : ℚ) / 10 ^ k) ((hi : ℚ) / 10 ^ k) = true) :
    (lo : ℝ) / 10 ^ k ≤ y ∧ y ≤ (hi : ℝ) / 10 ^ k := by
  simpa using of_decimalEnclosureCheck' hy h

end RationalInterval
end CAS.Continuum

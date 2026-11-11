/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Basic.Real.Basic
import CAS.CEGA

/-!
# CEGA domains presented as conjunctions and absolute bounds

Conjunctions of rational bounds describe the same boxes as interval memberships.
The ordinary inequality frontend reads nested conjunctions, retains the strongest
endpoints, and projects their proofs without changing the hypotheses. Absolute
upper bounds supply both endpoints of a symmetric box. Strict
hypotheses still describe closed query boxes, and unsupported logical forms
must not supply bounds.
-/

@[expose] public section

namespace CAS.Examples.CEGA.Domains

/-- A conjunctive domain supplies both endpoints to the ordinary box route. -/
theorem conjunction_upper (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    x * (1 - x) ≤ 1 / 4 := by
  cega

/-- Explicit queries use the same domain reader. -/
example (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    x * (1 - x) ≤ 1 / 4 := by
  cega [enclose x in [0, 1]] (x * (1 - x))

/-- The conjunction may be the premise of a quantified goal. -/
example : ∀ x : ℝ, 0 ≤ x ∧ x ≤ 1 → x * (1 - x) ≤ 1 / 4 := by
  cega

/-- One nested conjunction can bound two variables. -/
example (x y : ℝ) (h : (0 ≤ x ∧ x ≤ 1) ∧ (2 ≤ y ∧ y ≤ 3)) :
    x + y ≤ 4 := by
  cega

/-- Tighter endpoints in either branch supersede the wider bounds. -/
theorem nested_sharpest (x : ℝ) (hx : (-1 ≤ x ∧ x ≤ 1) ∧ (0 ≤ x ∧ x ≤ 2)) :
    x * (1 - x) ≤ 1 / 4 := by
  cega

/-- Interval memberships and strict bounds combine to the box `[0, 1]`. -/
example (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 2 ∧ (x > 0 ∧ x < 1)) :
    x * (1 - x) ≤ 1 / 4 := by
  cega

/-- A half-open interval gives its closure as the query box. -/
example (x : ℝ) (hx : x ∈ Set.Ico (1 : ℝ) 2) :
    1 / 2 ≤ 1 / x ∧ 1 / x ≤ 1 := by
  cega [enclose x in [1, 2]] (1 / x)

/-- A strictly positive closed box gives a positive reciprocal. -/
example (x : ℝ) (hx : x ∈ Set.Ioc (1 : ℝ) 2) :
    0 < 1 / x := by
  cega

/-- An open interval and a strict goal with a gap. -/
example (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    |x - 2| < 3 := by
  cega

-- Regressions for the conjunction reader: a query box must cover the hypotheses' box, strict
-- bounds give closed endpoints, and a disjunction gives no bounds.
/-- A too-small query box or a too-tight goal is refused before the valid replay. -/
example (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  fail_if_success cega [enclose x in [0, 1 / 2]] (x * (1 - x))
  fail_if_success
    have : x * (1 - x) ≤ 1 / 5 := by
      cega
  cega

/-- A strict conjunct does not create a gap at the endpoint of the closed box. -/
example : ∀ x : ℝ, 0 ≤ x ∧ x < 1 → x < 1 := by
  fail_if_success cega
  intro x hx
  exact hx.2

/-- Strict positivity alone cannot separate a denominator interval from zero. -/
example (x : ℝ) (hx : 0 < x ∧ x ≤ 1) : 0 < 1 / x := by
  fail_if_success cega
  exact one_div_pos.mpr hx.1

/-- Disjuncts are alternatives, so their endpoints cannot be intersected. -/
example (x : ℝ) (hx : (0 ≤ x ∧ x ≤ 1) ∨ (2 ≤ x ∧ x ≤ 3)) : x ≤ 3 := by
  fail_if_success cega
  rcases hx with hx | hx
  · exact hx.2.trans (by norm_num)
  · exact hx.2

/-- An absolute upper bound supplies both endpoints without a manual `abs_le.mp` step. -/
theorem absolute_upper (x : ℝ) (hx : |x| ≤ 1) : x ^ 2 ≤ 1 := by
  cega

/-- A rational absolute bound keeps this denominator uniformly positive. -/
theorem absolute_reciprocal (x : ℝ) (hx : |x| ≤ 1 / 2) : 1 / (1 - x) ≤ 2 := by
  cega

/-- Strict absolute bounds give the closed box; the `>` spelling has the same meaning. -/
example (x : ℝ) (hx : 1 > |x|) : x ^ 2 ≤ 1 := by
  cega

/-- Absolute and one-sided bounds are reconciled across nested conjunctions. -/
example (x : ℝ) (hx : |x| ≤ 2 ∧ (1 ≥ |x| ∧ 0 ≤ x)) :
    x * (1 - x) ≤ 1 / 4 := by
  cega

-- Regressions for the absolute-value reader: `1 ≤ |x|` gives no upper endpoint, `|x| ≤ 1` keeps
-- the pole of `1 / (1 - x)` in the box, `|x| < 1` gives a closed box, a disjunction no bounds.
/-- A lower absolute bound cannot be read as an upper bound. -/
example (x : ℝ) (hx : 1 ≤ |x|) : 1 ≤ |x| := by
  fail_if_success
    have : x ^ 2 ≤ 1 := by
      cega
  exact hx

/-- An absolute bound does not remove poles from the resulting closed box. -/
example (x : ℝ) (hx : |x| ≤ 1) : x ^ 2 ≤ 1 := by
  fail_if_success
    have : 1 / (1 - x) ≤ 2 := by
      cega
  cega

/-- A strict absolute bound does not turn a closed endpoint into a strict certificate. -/
example (x : ℝ) (hx : |x| < 1) : x < 1 := by
  fail_if_success cega
  exact (abs_lt.mp hx).2

/-- Disjunctive absolute bounds must be handled as separate cases. -/
example (x : ℝ) (hx : |x| ≤ 1 ∨ |x| ≤ 2) : |x| ≤ 2 := by
  fail_if_success cega
  rcases hx with hx | hx
  · exact hx.trans (by norm_num)
  · exact hx

end CAS.Examples.CEGA.Domains

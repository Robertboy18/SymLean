/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Tactics

The compiled examples of the docstrings of the Tactics family: the tactics `cas`, `cas?` and
`cas_nf`, and the `conv` form of `cas_nf`. Each section closes the goals of its examples, pins the
suggestions of `cas?` and the messages of the refusals, proves the theorem of its docstring, and
checks the axioms of that proof.
-/

@[expose] public section

namespace CAS.Examples.Reference.Tactics

set_option linter.hashCommand false

/-! ## cas -/

example (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
  cas

example (x : ℝ) (hx : x ≠ 0) : deriv (fun t : ℝ ↦ t * Real.log t) x = Real.log x + 1 := by
  cas using hx

example : (∫ x in (0 : ℝ)..1, x * Real.exp x) = 1 := by
  cas

example : AnalyticAt ℝ (fun x ↦ Real.exp (Real.sin x) / (1 + x ^ 2)) 0 := by
  cas

open Filter Topology in
example : Tendsto (fun x : ℝ ↦ (x ^ 2 + 1) / (2 * x ^ 2 - 3)) atTop (𝓝 (1 / 2)) := by
  cas

theorem exp_lt_four (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x < 4 := by
  have h : Real.exp x ≤ 3 := by cas
  linarith

/--
info: 'CAS.Examples.Reference.Tactics.exp_lt_four' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exp_lt_four

/--
cas could not prove this arithmetic relation. The statement may be false, or it may lie outside
the supported normalization and arithmetic fragment
-/
#guard_msgs (whitespace := lax, substring := true) in
example (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 2 := by
  cas

/--
cas computed a checked derivative, but it does not match the stated result.
-/
#guard_msgs (whitespace := lax, substring := true) in
example (x : ℝ) : deriv (fun x ↦ x ^ 2) x = 3 * x := by
  cas

/--
Box enclosure route:
  cas box route: no rational bounds on `x` in the hypotheses
-/
#guard_msgs (whitespace := lax, substring := true) in
example (x : ℝ) : Real.exp x ≥ x + 1 := by
  cas

/-! ## cas? -/

/--
Try this: [apply] cas
Lean checked the suggested replacement against the original goal. Selected route: CAS route:
ordinary Lean simplification/arithmetic.
-/
#guard_msgs (whitespace := lax, substring := true) in
example (x : ℝ) : (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by
  cas?

/--
Try this: [apply] cega [enclose x in [0, 1]] (Real.exp x)
Lean checked the suggested replacement against the original goal. Selected route: CAS route:
checked CEGA box enclosure of an ordinary inequality.
-/
#guard_msgs (whitespace := lax, substring := true) in
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 3 := by
  cas?

/--
Try this: [apply] cas using [h₁, h₂]
Lean checked the suggested replacement against the original goal. Selected route: CAS route:
polynomial consequences of equation hypotheses.
-/
#guard_msgs (whitespace := lax, substring := true) in
example (x y : ℝ) (h₁ : x + y = 3) (h₂ : x - y = 1) : x = 2 := by
  cas? using [h₁, h₂]

theorem exp_le_three (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 3 := by
  cega [enclose x in [0, 1]] (Real.exp x)

/--
info: 'CAS.Examples.Reference.Tactics.exp_le_three' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exp_le_three

/--
cas could not prove this arithmetic relation. The statement may be false, or it may lie outside
the supported normalization and arithmetic fragment
-/
#guard_msgs (whitespace := lax, substring := true) in
example (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 2 := by
  cas?

/--
cas exceeded Lean's maximum recursion depth (the option maxRecDepth is 12; some routes run with a
higher limit of their own). This is a resource limit, not a refutation of the goal.
-/
#guard_msgs (whitespace := lax, substring := true) in
example (x : ℝ) : x + 1 = 1 + x := by
  set_option maxRecDepth 12 in cas?

/-! ## cas_nf -/

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  cas_nf

example (F : ℝ → ℝ) (x y z : ℝ) (hden : x - y ≠ 0) (h : F (x + y) = z) :
    F ((x ^ 2 - y ^ 2) / (x - y)) = z := by
  cas_nf using hden
  exact h

example (P : ℝ → ℝ → Prop) (x y : ℝ) (h : P (x * y * 2 + x ^ 2 + y ^ 2) ((x + y) ^ 2)) :
    P ((x + y) ^ 2) ((x + y) ^ 2) := by
  conv =>
    arg 1
    cas_nf
  exact h

theorem square_le (x y c : ℝ) (h : (x + y) ^ 2 ≤ c) : x ^ 2 + 2 * x * y + y ^ 2 ≤ c := by
  cas_nf at h ⊢
  exact h

/--
info: 'CAS.Examples.Reference.Tactics.square_le' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms square_le

/--
`cas_nf` made no progress on the goal
-/
#guard_msgs (whitespace := lax, substring := true) in
example (P : ℝ → Prop) (x : ℝ) (h : P x) : P x := by
  cas_nf

/--
cas_nf could not prove the real analytic domain conditions.
A denominator or logarithm argument may need to be nonzero, a square-root argument may need to be
positive, or an inverse-trigonometric argument may need to avoid a branch endpoint. Supply the
relevant ordinary hypothesis with `cas_nf using h`.
-/
#guard_msgs (whitespace := lax, substring := true) in
example (P : ℝ → Prop) (x : ℝ) (h : P ((x ^ 2 - 1) / (x - 1))) : P (x + 1) := by
  cas_nf at h
  exact h

end CAS.Examples.Reference.Tactics

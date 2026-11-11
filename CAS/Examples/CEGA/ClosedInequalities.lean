/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Complex.Exponential
import CAS.CEGA

/-!
# Closed and mixed numerical inequalities

Closed elementary expressions use the zero-dimensional box. A nonrational endpoint
is enclosed by the same checked pipeline, including when the user specifies a query.
Applied real terms may be coordinates when their rational bounds are proved in context.
-/

@[expose] public section

namespace CAS.Examples.CEGA.ClosedInequalities

/-- A closed square root needs no artificial coordinate or bounded variable. -/
theorem sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  cega

/-- Both closed transcendental sides pass through the checked enclosure evaluator. -/
theorem exp_one_le_exp_three : Real.exp 1 ≤ Real.exp 3 := by
  cega

/-- The closed right side is enclosed after bounding the variable-dependent left side. -/
theorem exp_le_exp_three (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp x ≤ Real.exp 3 := by
  cega

example : Real.sqrt 2 ∈ Set.Icc (1 : ℝ) 2 := by
  cega

example : 1 ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ Real.exp 1 := by
  cega

example : √(√(2 : ℝ) + 1) ≤ 2 := by
  cega [enclose] √(√(2 : ℝ) + 1)

/-- Bounds on an application suffice; the user need not generalize it to a variable. -/
theorem applied_exp_bound {α : Type*} (f : α → ℝ) (x : α)
    (hx : 0 ≤ f x ∧ f x ≤ 1) : Real.exp (f x) ≤ Real.exp 3 := by
  cega

/-- Repeated applications denote the same coordinate and preserve algebraic dependence. -/
example {α : Type*} (f : α → ℝ) (x : α) (hx : f x ∈ Set.Icc (0 : ℝ) 1) :
    f x * (1 - f x) ≤ 1 / 4 := by
  cega

end CAS.Examples.CEGA.ClosedInequalities

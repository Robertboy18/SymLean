/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.CEGA

/-!
# CEGA ranges inside `dyadic_interval`

The `cega_real` family adds CEGA's certified ranges to Mathlib's `dyadic_interval`: quotients,
natural powers, `π`, `exp`, `log`, `sqrt`, the trigonometric and inverse trigonometric
functions, and the hyperbolic functions. The goal may be any proposition the `inclusion` tactic
reads (inequalities, equalities, interval memberships, `∧`, `∨`, `¬`), with variables bounded
by hypotheses. `prec := n` rounds every intermediate result to `2 ^ (-n)` and raises CEGA's
Taylor orders to match; `binSplit := k` cuts each variable's interval into `2 ^ k` pieces.

Bare `cega` uses the same evaluation for goals without free variables that its carrier and
box routes do not prove.
-/

@[expose] public section

namespace CAS.Examples.CEGA.Inclusion

/-! ## Constants -/

example : Real.exp 1 < 2.7183 ∧ 2.7182 < Real.exp 1 := by
  dyadic_interval [cega_real, prec := 20]

example : Real.sqrt 2 ∈ Set.Ioo 1.4142 1.4143 := by dyadic_interval [cega_real, prec := 24]

/-- Mathlib's square root is zero on negative arguments. -/
example : Real.sqrt (-4) = 0 := by dyadic_interval [cega_real, prec := 4]

example : Real.log 3 / Real.log 2 < 1.585 := by dyadic_interval [cega_real, prec := 24]

example : Real.arctan 1 * 4 < 3.1416 := by dyadic_interval [cega_real, prec := 24]

example : (1.1 : ℝ) ^ 10 < 2.6 := by dyadic_interval [cega_real, prec := 20]

/-- An exact equality of dyadic rationals. -/
example : (1 : ℝ) / 4 + 1 / 4 = 1 / 2 := by dyadic_interval [cega_real, prec := 4]

/-! ## Bare `cega` on closed goals -/

example : ¬ (Real.pi < 3.14) := by cega

example : Real.pi < 3.14 ∨ Real.pi < 3.15 := by cega

/-! ## Variables -/

/-- Without hypotheses a variable ranges over the whole line, and the fallback ranges of
`sin` and `exp` still decide the goal. -/
example (x : ℝ) : Real.sin x ^ 2 ≤ 1 ∧ 0 ≤ Real.exp x := by dyadic_interval [cega_real]

/-- The global hyperbolic ranges also apply to unbounded arguments. -/
example (x : ℝ) : -1 ≤ Real.tanh x ∧ Real.tanh x ≤ 1 ∧ 1 ≤ Real.cosh x := by
  dyadic_interval [cega_real]

/-- The negative reciprocal range reverses the endpoint order. -/
example (x : ℝ) (_hx : x ∈ Set.Icc (-2 : ℝ) (-1)) :
    x⁻¹ ∈ Set.Icc (-1 : ℝ) (-1 / 2) := by
  dyadic_interval [cega_real, prec := 4]

/-- Splitting `[0, 1]` into 64 pieces controls the dependency between `x` and `1 - x`. -/
example (x : ℝ) (_h0 : 0 ≤ x) (_h1 : x ≤ 1) : x * (1 - x) ≤ 0.26 := by
  dyadic_interval [cega_real, prec := 10, binSplit := 6]

/-- A reciprocal across zero is unbounded, so the bound is not proved. -/
example (x : ℝ) (_h0 : -1 ≤ x) (_h1 : x ≤ 1) : x⁻¹ ≤ 1 ∨ 1 ≤ x⁻¹ ∨ x⁻¹ < 1 := by
  fail_if_success dyadic_interval [cega_real, prec := 20]
  rcases lt_or_ge x⁻¹ 1 with h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

end CAS.Examples.CEGA.Inclusion

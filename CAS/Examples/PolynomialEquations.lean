/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ExactTactic

/-!
# Polynomial equations in ordinary Lean syntax

Two vanishing minors imply a third after multiplication by their shared entry.
The multiplier matters: cancelling it without a nonzero hypothesis would make
the statement false. Explicit fact lists may mix equations, inequalities and other
propositions. The examples use applied proofs and rational equations with
nonzero denominators, and derive a cubic identity by elimination.
-/

public section

namespace CAS.Examples.PolynomialEquations

/-- Equation hints work over any commutative ring, without order or division. -/
theorem mul_minor_eq_zero {R : Type*} [CommRing R] (a b c d e f : R)
    (h₁ : a * d = b * c) (h₂ : c * f = e * d) :
    c * (a * f - b * e) = 0 := by
  cas using [h₁, h₂]

/-- Each equation hint is elaborated separately, so it can be an applied theorem. -/
theorem mul_minor_eq_zero_of_family (a b c d e f : ℝ)
    (h₁ : ∀ t : ℝ, a * d + t = b * c + t)
    (h₂ : ∀ t : ℝ, c * f + t = e * d + t) :
    c * (a * f - b * e) = 0 := by
  cas using [h₁ 0, h₂ 0]

/-- Eliminating the middle variable gives a cubic identity. -/
theorem cube_eq_cube (x y z : ℝ) (h₁ : x * y = z ^ 2) (h₂ : y * z = x ^ 2) :
    x ^ 3 = z ^ 3 := by
  cas

/-- Nonzero denominator evidence makes the rational equations usable as polynomials. -/
theorem mul_minor_eq_zero_of_div (a b c d e f q r : ℝ)
    (hq : q ≠ 0) (hr : r ≠ 0)
    (h₁ : a * d / q = b * c / q) (h₂ : c * f / r = e * d / r) :
    c * (a * f - b * e) = 0 := by
  cas using [h₁, h₂]

/-- Applied inequality facts are available to the arithmetic solver. -/
theorem square_le_of_fact_list (x : ℝ)
    (hlower : ∀ t : ℝ, t = x → 1 ≤ t) (hupper : ∀ t : ℝ, t = x → t ≤ 2) :
    x ^ 2 ≤ 4 := by
  cas using [hlower x rfl, hupper x rfl]

/-- A supplied positive-value theorem discharges the actual denominator condition. -/
theorem self_div_of_positive_fact (f : ℝ → ℝ) (x : ℝ)
    (hpositive : ∀ t, 0 < f t) : f x / f x = 1 := by
  cas using [hpositive x]

/-- A single applied bound reaches arithmetic as a local proposition. -/
theorem nonneg_of_applied_bound (f : ℝ → ℝ) (h : ∀ t, (1 : ℝ) ≤ f t) :
    0 ≤ f 0 := by
  cas using (h 0)

/-- Polynomial equations use nonvanishing facts from the same explicit list. -/
theorem mul_minor_eq_zero_of_mixed_facts (a b c d e f q : ℝ)
    (h₁ : a * d / q = b * c / q) (h₂ : c * f = e * d)
    (hq : ∀ t : ℝ, t = q → t ≠ 0) :
    c * (a * f - b * e) = 0 := by
  cas using [h₁, h₂, hq q rfl]

/-- An applied single hint can combine with another equation from the local context. -/
example {R : Type*} [CommRing R] (a b c d e f : R)
    (h₁ : ∀ t : R, a * d + t = b * c + t) (h₂ : c * f = e * d) :
    c * (a * f - b * e) = 0 := by
  cas using (h₁ 0)

/-- A reversed hint `← h` is used as a rewrite rule from right to left. -/
example (x y : ℝ) (h : x = y) : 2 * x = 2 * y := by
  cas [← h]

end CAS.Examples.PolynomialEquations

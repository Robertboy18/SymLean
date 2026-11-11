/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ExactTactic

/-!
# `cas_nf` in open goals and hypotheses

`cas_nf` normalizes the target, selected hypotheses (`at h ⊢`, `at *`) or a `conv` focus
without closing the goal. The examples normalize under opaque predicates, functions and
binders, cancel polynomial factors with denominator evidence from `using` or the context,
resolve the branches of `exp (log x)` and `√x ^ 2` from sign hypotheses, rewrite `√(x ^ 2)` to
`|x|`, keep Lean's totalized values at zero, and normalize expressions under binders.
-/

@[expose] public section

namespace CAS.Examples.Normalization

/-- Polynomial normalization may close the resulting reflexive equality. -/
theorem polynomial_identity (x y : ℝ) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  cas_nf

/-- Polynomial normalization preserves an open inequality and its selected hypothesis. -/
theorem polynomial_locations (x y c : ℝ) (h : (x + y) ^ 2 ≤ c) :
    x ^ 2 + 2 * x * y + y ^ 2 ≤ c := by
  cas_nf at h ⊢
  exact h

/-- Polynomial conversions change only their selected argument. -/
theorem polynomial_conversion (P : ℝ → ℝ → Prop) (x y : ℝ)
    (h : P (x * y * 2 + x ^ 2 + y ^ 2) ((x + y) ^ 2)) :
    P ((x + y) ^ 2) ((x + y) ^ 2) := by
  conv =>
    arg 1
    cas_nf
  exact h

/-- A polynomial common factor cancels inside an arbitrary predicate. -/
theorem quartic_quotient (P : ℝ → Prop) (x y : ℝ) (hden : x ^ 2 - y ^ 2 ≠ 0)
    (h : P ((x ^ 4 - y ^ 4) / (x ^ 2 - y ^ 2))) : P (x ^ 2 + y ^ 2) := by
  cas_nf using hden at h
  exact h

/-- The target can be normalized under an opaque function. -/
theorem quotient_under_function (F : ℝ → ℝ) (x y z : ℝ) (hden : x - y ≠ 0) (h : F (x + y) = z) :
    F ((x ^ 2 - y ^ 2) / (x - y)) = z := by
  cas_nf using hden
  exact h

/-- The trigonometric identity supplies a replacement in an open hypothesis. -/
theorem pythagorean_identity (P : ℝ → Prop) (x : ℝ) (h : P (Real.sin x ^ 2 + Real.cos x ^ 2)) :
    P 1 := by
  cas_nf at h
  exact h

/-- A conversion changes only the selected one of two identical occurrences. -/
theorem selected_quotient (P : ℝ → ℝ → Prop) (x y : ℝ) (hden : x - y ≠ 0)
    (h : P (x + y) ((x ^ 2 - y ^ 2) / (x - y))) :
    P ((x ^ 2 - y ^ 2) / (x - y)) ((x ^ 2 - y ^ 2) / (x - y)) := by
  conv =>
    arg 1
    cas_nf using hden
  exact h

/-- Cancellation requires evidence that the denominator is nonzero. -/
theorem self_div_of_ne_zero (P : ℝ → Prop) (x : ℝ) (hx : x ≠ 0) (h : P (x / x)) : P 1 := by
  cas_nf using hx at h
  exact h

/-- Wildcard normalization skips unchanged locations and preserves its rewritten hypothesis. -/
theorem wildcard_locations (P : ℝ → Prop) (x : ℝ) (h : P (x + 0)) : P (x + 0) := by
  cas_nf at *
  exact h

/-- Division at zero retains Lean’s totalized value. -/
theorem zero_div_zero (P : ℝ → Prop) (h : P ((0 : ℝ) / 0)) : P 0 := by
  cas_nf at h
  exact h

/-- Positive logarithm arguments give the ordinary inverse identity. -/
theorem exp_log_of_pos (P : ℝ → Prop) (x : ℝ) (hx : 0 < x) (h : P (Real.exp (Real.log x))) :
    P x := by
  cas_nf using hx at h
  exact h

/-- A nonzero argument determines an absolute value without fixing its sign. -/
theorem exp_log_of_ne_zero (P : ℝ → Prop) (x : ℝ) (hx : x ≠ 0) (h : P (Real.exp (Real.log x))) :
    P |x| := by
  cas_nf using hx at h
  exact h

/-- The negative logarithm branch reduces to the negated argument. -/
theorem exp_log_of_neg (P : ℝ → Prop) (x : ℝ) (hx : x < 0) (h : P (Real.exp (Real.log x))) :
    P (-x) := by
  cas_nf using hx at h
  exact h

/-- The logarithm at zero has a separate exponential value. -/
theorem exp_log_zero (P : ℝ → Prop) (h : P (Real.exp (Real.log 0))) : P 1 := by
  cas_nf at h
  exact h

/-- Squaring a square root recovers a nonnegative argument. -/
theorem sq_sqrt_of_nonneg (P : ℝ → Prop) (x : ℝ) (hx : 0 ≤ x) (h : P (√x ^ 2)) : P x := by
  cas_nf using hx at h
  exact h

/-- A square root vanishes on a nonpositive argument. -/
theorem sq_sqrt_of_nonpos (P : ℝ → Prop) (x : ℝ) (hx : x ≤ 0) (h : P (√x ^ 2)) : P 0 := by
  cas_nf using hx at h
  exact h

/-- The square root of a square retains the absolute value. -/
theorem sqrt_sq (P : ℝ → Prop) (x : ℝ) (h : P (√(x ^ 2))) : P |x| := by
  cas_nf at h
  exact h

/-- A zero numerator needs no nonzero denominator hypothesis. -/
theorem zero_div (P : ℝ → Prop) (x : ℝ) (h : P (0 / x)) : P 0 := by
  cas_nf at h
  exact h

/-- A zero denominator has its totalized value. -/
theorem div_zero (P : ℝ → Prop) (x : ℝ) (h : P (x / 0)) : P 0 := by
  cas_nf at h
  exact h

/-- Analytic cleanup in one argument does not skip algebra in another. -/
theorem both_function_arguments (P : ℝ → Prop) (F : ℝ → ℝ → ℝ) (x y z : ℝ)
    (hz : 0 < z) (hden : x - y ≠ 0)
    (h : P (F (Real.exp (Real.log z)) ((x ^ 2 - y ^ 2) / (x - y)))) :
    P (F z (x + y)) := by
  cas_nf using And.intro hz hden at h
  exact h

/-- Opaque real atoms may be indexed by a type in any universe. -/
theorem atoms_over_arbitrary_type {α : Type*} (P : ℝ → Prop) (F : α → ℝ) (a b : α)
    (hden : F a - F b ≠ 0) (h : P ((F a ^ 2 - F b ^ 2) / (F a - F b))) :
    P (F a + F b) := by
  cas_nf using hden at h
  exact h

/-- Congruence descends into a function-valued argument. -/
theorem function_argument (F : (ℝ → ℝ) → ℝ) (P : ℝ → Prop) (h : P (F (fun t ↦ (t + t) / 2))) :
    P (F (fun t ↦ t)) := by
  cas_nf at h
  exact h

/-- A focused conversion uses evidence mentioning its locally introduced variable. -/
theorem conversion_under_binder (F : ℝ → ℝ) (hden : ∀ t, F t ≠ 0) :
    (fun t ↦ F t / F t) = (fun _ ↦ (1 : ℝ)) := by
  conv =>
    lhs
    intro t
    cas_nf using hden t

/-- Arguments normalize before equal opaque atoms are collected algebraically. -/
theorem coincident_atoms (P : ℝ → Prop) (F : ℝ → ℝ) (x : ℝ)
    (h : P (F (x + 0) + F x)) : P (2 * F x) := by
  cas_nf at h
  exact h

end CAS.Examples.Normalization

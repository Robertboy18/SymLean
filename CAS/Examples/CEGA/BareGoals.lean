/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
public meta import CAS.CEGA

/-!
# Bare `cega` on integrals, certificate goals and conjunctions

Bare `cega` reads the problem off the goal. A bound on one interval integral with rational
limits is proved by checked quadrature panels: Simpson panels where the domain checker certifies
the integrand and its first four derivatives, range panels, which need only continuity,
elsewhere. A certificate goal whose domain is a coordinate box is unfolded to an ordinary goal on
the coordinates of its point, which the checked box query proves. A conjunction of bounds, or an
interval membership, is proved with one kernel check for each expression it bounds, and a closed
goal that the box query does not prove is evaluated with `dyadic_interval` at the precision of
`(prec := n)`.
-/

@[expose] public section

namespace CAS.Examples.CEGA.BareGoals

open CAS.Certificate
open CAS.CEGA

/-! ## Interval integrals -/

/-- The panel count doubles until the enclosure of the Gaussian integral proves the bound. -/
example : (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 3 / 4 := by
  cega

/-- `(panels := n)` gives the panel count instead of the doubling search. -/
example : |(∫ x in (0 : ℝ)..1, Real.exp x) - 17182818 / 10000000| ≤ 1 / 10000 := by
  cega (panels := 2)

/-- With the limits reversed, the bound is on the integral as written. -/
example : (∫ x in (1 : ℝ)..0, Real.exp x) < -1 := by
  cega

/-- The absolute value has a corner at `0`, so range panels give this lower bound. -/
example : 1 / 2 < ∫ x in (-1 : ℝ)..1, |x| := by
  cega

/-! ## Certificate goals on a coordinate box -/

/-- An enclosure on the interval `[0, 1]`, written as a set of points of `ℝ^1`. -/
example : EnclosedOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0)) {p | 0 ≤ p 0 ∧ p 0 ≤ 1} 0 (1 / 2) := by
  cega

/-- An upper bound on the same interval. -/
example : BoundOn (fun p : ℝ^1 ↦ |p 0 - 2|) {p | 0 ≤ p 0 ∧ p 0 ≤ 1} 3 := by
  cega

/-- An approximation by a constant, whose norm on `ℝ` is the absolute value. -/
example : ApproxOn (fun p : ℝ^1 ↦ p 0) (fun _ ↦ (1 / 2 : ℝ)) {p | 0 ≤ p 0 ∧ p 0 ≤ 1} 1 := by
  cega

/-- A box with two coordinates, as on the Certified Numerics page of the site. -/
example :
    BoundOn (fun p : ℝ^2 ↦ p 0 * p 1) {p : ℝ^2 | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 2 ≤ p 1 ∧ p 1 ≤ 3} 4 := by
  cega

/-- The sharp range of `x / (1 + x²)` on `[-2, 2]` needs the subdivision that bare `cega` tries
when the first query falls short, here at the turning points `±1`. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0 ^ 2)) {p | -2 ≤ p 0 ∧ p 0 ≤ 2}
      (-1 / 2 : ℝ) (1 / 2 : ℝ) := by
  cega

/-- The upper bound that the sharp range implies, after the same subdivision. -/
example :
    BoundOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0 ^ 2)) {p | -2 ≤ p 0 ∧ p 0 ≤ 2} (1 / 2 : ℝ) := by
  cega

/-- The bound on the absolute value after the same subdivision. -/
example :
    BoundOn (fun p : ℝ^1 ↦ |p 0 / (1 + p 0 ^ 2)|) {p | -2 ≤ p 0 ∧ p 0 ≤ 2} (1 / 2 : ℝ) := by
  cega

/-- The approximation by the midpoint `0` of the sharp range, with its radius `1 / 2`. -/
example :
    ApproxOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0 ^ 2)) (fun _ ↦ (0 : ℝ))
      {p | -2 ≤ p 0 ∧ p 0 ≤ 2} (1 / 2 : ℝ) := by
  cega

-- A domain that bounds a coordinate on one side only is not a coordinate box.
/-- error: This goal has the head symbol `CAS.Certificate.EnclosedOn`, a certificate
proposition whose domain -/
#guard_msgs (error, substring := true, whitespace := lax) in
example : EnclosedOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0)) {p | 0 ≤ p 0} 0 1 := by
  cega

/-! ## Conjunctions and interval memberships -/

/-- A strict two-sided bound. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 < x * (1 - x) + 1 ∧ x * (1 - x) + 1 < 2 := by
  cega

/-- Membership in an open interval. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ∈ Set.Ioo (-1 : ℝ) 1 := by
  cega

/-- Memberships in half-open intervals. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ∈ Set.Ico (0 : ℝ) 1 := by
  cega

example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ∈ Set.Ioc (-1 : ℝ) (1 / 2) := by
  cega

/-- Bounds on several expressions, each checked once. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ x / (1 + x) ∧ Real.exp x ≤ 3 ∧ |Real.sin x| < 1 := by
  cega

/-! ## Closed goals -/

/-- Sixteen digits of `e` need more than the 32 bits of the default interval evaluation. -/
example : Real.exp 1 < 2.718281828459046 ∧ 2.718281828459045 < Real.exp 1 := by
  cega (prec := 64)

end CAS.Examples.CEGA.BareGoals

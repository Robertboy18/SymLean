/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Ordinary inequalities on rational boxes

The hypotheses give the box, and the conclusion is an ordinary real inequality.
Bare `cas` and `cega` infer the bounds from context; an explicit query records the
box in the proof. The examples include polynomial and transcendental bounds,
comparisons of variable-dependent expressions, and arctangent ranges.

The `cega [fast]` examples illustrate the native checking mode. Native evaluation is
an explicit trust choice; kernel checking proves the same finite statements, here for
`x * (1 - x) ≤ 1 / 4` and in `Trust.lean` for the other two.
-/

@[expose] public section

namespace CAS.Examples.CEGA.BoxInequalities

open CAS.Certificate

/-! ## One bound, three tactics -/

/-- The bound the Mathlib arithmetic script does not find on its own (it needs the hint
`sq_nonneg (x - 1/2)`): the affine interval route certifies the exact range `[0, 1/4]`. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cas

/-- Bare `cega` on the same ordinary goal. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega

/-- The explicit query names the box and the mode the proof depends on. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega [enclose x in [0, 1]] (x * (1 - x))

/-- In the fast profile (`set_option cega.nativeCertificates true`, or
`lake build -R -Kcertificates=fast`) this certificate is checked by native evaluation, which trusts
Lean's compiler; in the default profile `cega [fast]` is `cega` and the kernel checks it. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * x ≤ 1 := by
  cega [fast]

/-- Natural intervals lose this dependency; the fast form falls back to the sharper
kernel planner, which certifies the same bound as bare `cega` above. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    x * (1 - x) ≤ 1 / 4 := by
  cega [fast]

/-! ## Closed finite certificates

The checking profile changes how we evaluate these finite statements. It does not
change their mathematical meaning. -/

/-- The finite certificate of `finite_rows` in `Trust.lean` can use the native profile. -/
example : ∀ i : Fin 32, (i.val : ℤ) ^ 2 < 1024 := by
  cega [fast]

/-- A local definition in the goal is expanded before the finite certificate decides it. -/
example : (1 : ℚ) / 3 < 1 := by
  let q : ℚ := 1 / 3
  change q < 1
  cega [fast]

/-! ## Elementary functions and two-sided bounds -/

/-- An exponential bound from an interval membership hypothesis; eight Taylor terms certify
`exp 1 ≤ 876809 / 322560 ≈ 2.7182818`. -/
example (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : Real.exp x ≤ 2.72 := by
  cas

/-- A two-sided enclosure, stated as a conjunction; the derivative-sign route gives the sharp
range `[0, 1/2]`. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ x / (1 + x) ∧ x / (1 + x) ≤ 1 / 2 := by
  cas

/-- The same enclosure stated as an interval membership, with `≥` in a hypothesis. -/
example (x : ℝ) (h0 : x ≥ 0) (h1 : x ≤ 1) : x / (1 + x) ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  cega

/-- A lower bound uses the lower endpoint of the enclosure (`cosh` on `[1, 2]` starts at
`497719 / 322560 ≈ 1.543`). -/
example (x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2) : 3 / 2 ≤ Real.cosh x := by
  cas

/-- A strict bound needs the certified value strictly below the stated one. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) < 3 / 10 := by
  cas

/-- An absolute bound runs the absolute-bound query. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : |x - 2| ≤ 2 := by
  cas

/-- A comparison of two variable-dependent sides is proved through the difference; the
derivative `exp x - 1` keeps one sign on `[0, 1]`, so the monotonicity route gives the range of
`exp x - (2 + x)` from the endpoints. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 2 + x := by
  cas

/-- Two variables give a two-dimensional box. A polynomial bound such as `x * y ≤ 3` is already
closed by the Mathlib arithmetic script that runs first; the exponential needs the box query,
whose eight Taylor terms certify `exp 3 ≤ 20.09`. -/
example (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 2 ≤ y) (hy' : y ≤ 3) :
    Real.exp (x * y) ≤ 21 := by
  cas

/-- Enclosures use the total real square root, which is zero on negative inputs. -/
example (x : ℝ) (hx : x ∈ Set.Icc (-2 : ℝ) (-1)) :
    0 ≤ Real.sqrt x ∧ Real.sqrt x ≤ 0 := by
  cega [enclose x in [-2, -1]] (sqrt x)

/-- The elementary arctangent enclosure uses both half-line bounds across zero. -/
theorem arctan_near_zero (x : ℝ) (hx : x ∈ Set.Icc (-1 / 4 : ℝ) (1 / 4)) :
    Real.arctan x ∈ Set.Icc (-1 / 4 : ℝ) (1 / 4) := by
  cega [enclose x in [-1 / 4, 1 / 4]] (atan x)

/-- Large positive arguments use the reciprocal arctangent enclosure. -/
theorem arctan_large_positive (x : ℝ) (hx : x ∈ Set.Icc (3 : ℝ) 4) :
    Real.arctan x ∈ Set.Icc (1 : ℝ) (3 / 2) := by
  cega [enclose x in [3, 4]] (atan x)

/-- Oddness transports the reciprocal enclosure to negative arguments. -/
theorem arctan_large_negative (x : ℝ) (hx : x ∈ Set.Icc (-4 : ℝ) (-3)) :
    Real.arctan x ∈ Set.Icc (-3 / 2 : ℝ) (-1) := by
  cega [enclose x in [-4, -3]] (atan x)

/-! ## Subdivision, precision, and decimals

When its first query falls short of the stated bound, bare `cega` bisects the box and encloses
the pieces, by default to depth two; `cega (depth := n)` bisects deeper, and `cega (prec := n)`
raises the precision of the query, as in the explicit form. Bounds and coefficients may be
written as decimals, which are read as exact quotients. -/

/-- The planner's range of `exp x - (1.1 + 2 * x)` on `[0, 1]` reaches above zero; on the
pieces of two bisections it stays below. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 1.1 + 2 * x := by
  cega

/-- The maximum of `x / (1 + x ^ 2)` on `[-2, 2]` is `1/2`; three levels of bisection certify
this bound. -/
example (x : ℝ) (h0 : -2 ≤ x) (h1 : x ≤ 2) : x / (1 + x ^ 2) ≤ 0.55 := by
  cega (depth := 3)

/-- An absolute bound is subdivided as well: the planner bounds `|x / (1 + x ^ 2)|` on `[-2, 2]`
by `2`, and after two bisections by its maximum `1/2`. -/
example (x : ℝ) (h0 : -2 ≤ x) (h1 : x ≤ 2) : |x / (1 + x ^ 2)| ≤ 1 / 2 := by
  cega

/-- `π` comes from a fixed decimal bracket, so eight digits of it need no precision setting. -/
example : |Real.pi - 3.14159265| < 1e-8 := by
  cega

/-- Decimal endpoints and coefficients in an explicit query. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1.5) : x * 0.5 ≤ 0.75 := by
  cega [enclose x in [0, 1.5]] (x * 0.5)

end CAS.Examples.CEGA.BoxInequalities

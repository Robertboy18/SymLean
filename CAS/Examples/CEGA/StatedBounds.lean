/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Goals that state their bounds

A goal such as `EnclosedOn f s (-1) 1` or `x * (1 - x) ≤ 1 / 4` states the bound it wants.
`cega` checks such a bound with one kernel check: the kernel runs the planner while it checks a
theorem that compares the interval of the query with the stated numbers, so the search for the
interval in the elaborator and the read-back of its endpoints are skipped. When the kernel rejects
the stated bound, the explicit query runs the search and refuses the goal with its usual message,
and bare `cega` refuses it with the values its queries certify, read back in one kernel
evaluation. The trace class `cega.stated` reports each check.
-/

@[expose] public section

namespace CAS.Examples.CEGA.StatedBounds

open CAS.Certificate

set_option linter.hashCommand false

/-! ## Bounds the kernel accepts -/

/--
trace: [cega.stated] enclose query, stated bound ∈ [-1, 1]: checked by the kernel
-/
#guard_msgs in
set_option trace.cega.stated true in
/-- The range of `sin x * cos x` on `[0, 1]` lies in `[-1, 1]`. -/
theorem sin_mul_cos_mem :
    EnclosedOn (fun p : ℝ^1 ↦ Real.sin (p 0) * Real.cos (p 0))
      {p : ℝ^1 | 0 ≤ p 0 ∧ p 0 ≤ 1} (-1) 1 := by
  cega [enclose x in [0, 1]] (sin x * cos x)

/--
info: 'CAS.Examples.CEGA.StatedBounds.sin_mul_cos_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sin_mul_cos_mem

/--
trace: [cega.stated] bound query, stated bound ≤ 1/4: checked by the kernel
-/
#guard_msgs in
set_option trace.cega.stated true in
/-- An ordinary bound under hypotheses, by bare `cega`. -/
theorem mul_one_sub_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega

/--
trace: [cega.stated] bound query, stated bound < 1/3: checked by the kernel
---
trace: [cega.stated] enclose query, stated bound ≥ 0: checked by the kernel
---
trace: [cega.stated] enclose query, stated bound > -1/2: checked by the kernel
---
trace: [cega.stated] absBound query, stated bound |·| < 1: checked by the kernel
---
trace: [cega.stated] bound query, stated bound ≤ 3/10: checked by the kernel
-/
#guard_msgs in
set_option trace.cega.stated true in
/-- The other shapes: a strict upper bound, a lower bound, a strict lower bound, a strict
absolute bound, and the `≥` spelling. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    x * (1 - x) < 1 / 3 ∧ 0 ≤ x * (1 - x) ∧ x * (1 - x) > -1 / 2 ∧ |x - 1 / 2| < 1 ∧
      3 / 10 ≥ x * (1 - x) :=
  ⟨by cega, by cega, by cega, by cega, by cega⟩

/--
trace: [cega.stated] bound query, stated bound ≤ 13/50: checked by the kernel
---
trace: [cega.stated] bound query, stated bound ≤ 3/8: checked by the kernel
-/
#guard_msgs in
set_option trace.cega.stated true in
/-- Bounds written with scientific notation and with powers are read as exact rationals. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    x * (1 - x) ≤ 2.6e-1 ∧ x * (1 - x) ≤ 3 / 2 ^ 3 :=
  ⟨by cega, by cega⟩

/--
trace: [cega.stated] approx query, stated bound = 1/8 ± 1/8: checked by the kernel
-/
#guard_msgs in
set_option trace.cega.stated true in
/-- A midpoint approximation states the center and the radius. -/
example :
    ApproxOn (fun p : ℝ^1 ↦ p 0 * (1 - p 0)) (fun _ ↦ (1 / 8 : ℝ))
      {p : ℝ^1 | 0 ≤ p 0 ∧ p 0 ≤ 1} (1 / 8) := by
  cega [enclose x in [0, 1]] (x * (1 - x))

/--
trace: [cega.stated] enclose query, stated bound ≥ 0: checked by the kernel
-/
#guard_msgs in
set_option trace.cega.stated true in
/-- The explicit query proves the bound the goal states, here a lower bound. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ x * (1 - x) := by
  cega [enclose x in [0, 1]] (x * (1 - x))

/-! ## Edge cases

A bound at the certified endpoint is accepted, and the strict bound at the same endpoint is
rejected. A closed bound that is not a numeral expression is checked through the difference, and
the replay of that check is bare `cega`. A bound that the first query misses is checked again on
the subdivided box. A check is reused by the same query at the same precision, and only there. -/

/--
trace: [cega.stated] bound query, stated bound ≤ 1: checked by the kernel
-/
#guard_msgs in
set_option trace.cega.stated true in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ≤ 1 := by
  cega [enclose x in [0, 1]] x

/--
trace: [cega.stated] bound query, stated bound < 1: rejected by the kernel
-/
#guard_msgs (trace, drop error) in
set_option trace.cega.stated true in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x < 1 := by
  cega [enclose x in [0, 1]] x

/--
cega generated a checked upper bound certificate for the stated query, but could not transport
it to this ordinary inequality.
-/
#guard_msgs (substring := true, whitespace := lax) in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x < 1 := by
  cega [enclose x in [0, 1]] x

/--
trace: [cega.stated] bound query, stated bound ≤ 0: checked by the kernel
-/
#guard_msgs in
set_option trace.cega.stated true in
example : (4 / 11 : ℝ) ≤ Real.exp (-1) := by
  cega

/--
info: Try this:
  [apply] cega

Lean checked the suggested replacement against the original goal. Selected route: CEGA route: checked box enclosure of an ordinary inequality.
-/
#guard_msgs in
example : (3 / 11 : ℝ) ≤ Real.exp (-1) := by
  cega?

/-- The suggested replacement. -/
example : (3 / 11 : ℝ) ≤ Real.exp (-1) := by
  cega

/--
trace: [cega.stated] bound query, stated bound ≤ 0: rejected by the kernel
[cega.stated] subdivided bound query, stated bound ≤ 0: checked by the kernel
-/
#guard_msgs in
set_option trace.cega.stated true in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 1.1 + 2 * x := by
  cega

/--
trace: [cega.stated] enclose query, stated bound ∈ [1, 84946307139345163605009/31250000000000000000000]: checked by the kernel
---
trace: [cega.stated] enclose query, stated bound ∈ [1, 84946307139345163605009/31250000000000000000000]: reusing the theorem checked for this query
-/
#guard_msgs in
set_option trace.cega.stated true in
/-- Twenty-four decimals of `e`, at a higher precision, twice: the second check reuses the
first. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ Real.exp (p 0)) {p : ℝ^1 | 0 ≤ p 0 ∧ p 0 ≤ 1}
        (1 : ℝ) (2.718281828459045235360288 : ℝ) ∧
      EnclosedOn (fun p : ℝ^1 ↦ Real.exp (p 0)) {p : ℝ^1 | 0 ≤ p 0 ∧ p 0 ≤ 1}
        (1 : ℝ) (2.718281828459045235360288 : ℝ) :=
  ⟨by cega (prec := 40) [enclose x in [0, 1]] (exp x),
    by cega (prec := 40) [enclose x in [0, 1]] (exp x)⟩

/--
trace: [cega.stated] enclose query, stated bound ∈ [1, 84946307139345163605009/31250000000000000000000]: rejected by the kernel
-/
#guard_msgs (trace, drop error) in
set_option trace.cega.stated true in
/-- The same bound at the default precision is checked afresh, and the kernel rejects it: the
theorem checked at the higher precision does not stand in for it. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ Real.exp (p 0)) {p : ℝ^1 | 0 ≤ p 0 ∧ p 0 ≤ 1}
      (1 : ℝ) (2.718281828459045235360288 : ℝ) := by
  cega [enclose x in [0, 1]] (exp x)

/--
trace: [cega.stated] bound query, stated bound ≤ 2/7: checked by the kernel
---
trace: [cega.stated] bound query, stated bound ≤ 3/11: checked by the kernel
---
trace: [cega.stated] bound query, stated bound ≤ 2/7: checked by the kernel
-/
#guard_msgs in
set_option trace.cega.stated true in
set_option linter.unusedTactic false in
/-- A check whose theorem was rolled back with its proof state is made again, even when a later
check has reused its auxiliary name. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 2 / 7 ∧ x * (1 - x) ≤ 3 / 11 := by
  try (have : x * (1 - x) ≤ 2 / 7 := by cega
       fail)
  have h : x * (1 - x) ≤ 3 / 11 := by cega
  exact ⟨by cega, h⟩

/-! ## Bounds the kernel rejects

A stated bound that the query's interval does not give is rejected by the kernel. The explicit
query then runs the search, which refuses the goal with its usual message; bare `cega` names the
value that its queries certify. -/

/--
trace: [cega.stated] enclose query, stated bound ∈ [7/20, 1/4]: rejected by the kernel
-/
#guard_msgs (trace, drop error) in
set_option trace.cega.stated true in
example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0 * Real.exp (-p 0))
      {p : ℝ^1 | 9 / 10 ≤ p 0 ∧ p 0 ≤ 11 / 10} (7 / 20) (1 / 4) := by
  cega [enclose x in [9 / 10, 11 / 10]] (x * exp (-x))

/--
cega generated a checked enclosure certificate, but it does not prove this exact goal. Check the
expression, rational box, and requested bounds.
-/
#guard_msgs (substring := true, whitespace := lax) in
example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0 * Real.exp (-p 0))
      {p : ℝ^1 | 9 / 10 ≤ p 0 ∧ p 0 ≤ 11 / 10} (7 / 20) (1 / 4) := by
  cega [enclose x in [9 / 10, 11 / 10]] (x * exp (-x))

/--
trace: [cega.stated] bound query, stated bound ≤ 1/5: rejected by the kernel
[cega.stated] subdivided bound query, stated bound ≤ 1/5: rejected by the kernel
-/
#guard_msgs (trace, drop error) in
set_option trace.cega.stated true in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 5 := by
  cega

/--
cega box route: comparison with the stated bound: the certified value does not give the stated
bound.
-/
#guard_msgs (substring := true, whitespace := lax) in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 5 := by
  cega

/-! ## Goals the route leaves to the search

An approximation whose stated center is not the midpoint of the certified interval is rejected by
the kernel and refused by the search, as before. A bound beyond the numeral reader's size cap goes
to the difference form. A query that the search has already run goes to the search, which reuses its
reduction. Bare `cega` refused the bound query of `x * (1 - x)` on `[0, 1]` above without the
search, so that query is not memoized, and the kernel checks a later bound on it. -/

/--
trace: [cega.stated] approx query, stated bound = 1/4 ± 1/4: rejected by the kernel
-/
#guard_msgs (trace, drop error) in
set_option trace.cega.stated true in
example :
    ApproxOn (fun p : ℝ^1 ↦ p 0 * (1 - p 0)) (fun _ ↦ (1 / 4 : ℝ))
      {p : ℝ^1 | 0 ≤ p 0 ∧ p 0 ≤ 1} (1 / 4) := by
  cega [enclose x in [0, 1]] (x * (1 - x))

/--
cega generated a checked midpoint approximation certificate, but it does not prove this exact
goal.
-/
#guard_msgs (substring := true, whitespace := lax) in
example :
    ApproxOn (fun p : ℝ^1 ↦ p 0 * (1 - p 0)) (fun _ ↦ (1 / 4 : ℝ))
      {p : ℝ^1 | 0 ≤ p 0 ∧ p 0 ≤ 1} (1 / 4) := by
  cega [enclose x in [0, 1]] (x * (1 - x))

/--
trace: [cega.stated] bound query, stated bound ≤ 0: checked by the kernel
-/
#guard_msgs in
set_option trace.cega.stated true in
/-- A power past the size cap of the numeral reader is not read as a rational; the bound is
then checked through the difference. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ ((2 : ℝ) ^ 4096) ^ 17 := by
  cega

/--
trace: [cega.stated] bound query, stated bound ≤ 7/20: checked by the kernel
-/
#guard_msgs in
set_option trace.cega.stated true in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 7 / 20 := by
  cega

end CAS.Examples.CEGA.StatedBounds

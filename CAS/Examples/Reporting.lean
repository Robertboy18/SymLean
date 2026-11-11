/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
public import CAS.Numerics.Tactic

/-!
# The reports of `cas?` and `cega?`

`cas?` takes the arguments of `cas`, and `cega?` those of `cega`. Each proves the goal as the
plain tactic does, names the route that closed it, and suggests the call to keep in the proof:
the explicit call of the route that closed the goal, such as the `cega [enclose ...]` query of a
box inequality, once that call has closed the original goal, and otherwise the plain call. Every
form of either tactic has one example, and the last command prints the order in which `cas` tries
its routes.
-/

@[expose] public section

namespace CAS.Examples.Reporting

open CAS.Certificate

set_option linter.hashCommand false

/-! ## `cas?` -/

/--
info: Try this:
  [apply] cas

Lean checked the suggested replacement against the original goal. Selected route: CAS route: ordinary Lean simplification/arithmetic.
-/
#guard_msgs in
example (x : ℝ) : (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by
  cas?

/--
info: Try this:
  [apply] cas using hx

Lean checked the suggested replacement against the original goal. Selected route: CAS route: checked symbolic derivative.
-/
#guard_msgs in
example (x : ℝ) (hx : 0 < x) :
    deriv (fun t : ℝ ↦ t ^ (3 / 2 : ℝ)) x = (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
  cas? using hx

/--
info: Try this:
  [apply] cas using [h₁, h₂]

Lean checked the suggested replacement against the original goal. Selected route: CAS route: polynomial consequences of equation hypotheses.
-/
#guard_msgs in
example (x y : ℝ) (h₁ : x + y = 3) (h₂ : x - y = 1) : x = 2 := by
  cas? using [h₁, h₂]

/-- A definition for `cas? [square]` to unfold. -/
def square (x : ℝ) : ℝ := x * x

/--
info: Try this:
  [apply] cas [square]

Lean checked the suggested replacement against the original goal. Selected route: CAS route: ordinary Lean simplification/arithmetic.
-/
#guard_msgs in
example (x : ℝ) : square (x + 1) = x ^ 2 + 2 * x + 1 := by
  cas? [square]

/--
info: Try this:
  [apply] cas [integrate primitive := fun x ↦ x ^ 2]

Lean checked the suggested replacement against the original goal. Selected route: CAS route: checked integration, explicit primitive verification.
-/
#guard_msgs in
example : (∫ x in (0 : ℝ)..1, 2 * x) = 1 := by
  cas? [integrate primitive := fun x ↦ x ^ 2]

/--
info: Try this:
  [apply] cas [integrate primitive := fun t ↦ Real.log t ^ 2 / 2 using h]

Lean checked the suggested replacement against the original goal. Selected route: CAS route: checked integration, explicit primitive verification.
-/
#guard_msgs in
example (a b : ℝ) (h : ∀ t ∈ Set.uIcc a b, t ≠ 0) :
    (∫ t in a..b, Real.log t / t) = Real.log b ^ 2 / 2 - Real.log a ^ 2 / 2 := by
  cas? [integrate primitive := fun t ↦ Real.log t ^ 2 / 2 using h]

-- The planner finds the primitive, and the suggestion checks it.
/--
info: Try this:
  [apply] cas

Lean checked the suggested replacement against the original goal. Selected route: CAS route: checked integration, bounded antiderivative search.
-/
#guard_msgs in
example : (∫ x in (0 : ℝ)..1, x * Real.exp x) = 1 := by
  cas?

-- The box route closes the goal, and the suggestion is the query it ran.
/--
info: Try this:
  [apply] cega [enclose x in [0, 1]] (Real.exp x)

Lean checked the suggested replacement against the original goal. Selected route: CAS route: checked CEGA box enclosure of an ordinary inequality.
-/
#guard_msgs in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 3 := by
  cas?

-- The suggested query proves the same goal.
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 3 := by
  cega [enclose x in [0, 1]] (Real.exp x)

/-! ## `cega?` -/

/--
info: Try this:
  [apply] cega [enclose x in [0, 1]] (x * (1 - x))

Lean checked the suggested replacement against the original goal. Selected route: CEGA route: checked box enclosure of an ordinary inequality.
-/
#guard_msgs in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega?

/-- A stored enclosure of the cosine on `[0, 1]`. -/
noncomputable def cosineEnclosure : EnclosureCert ℝ (Set.Icc 0 1) where
  fn := Real.cos
  lo := 1 / 2
  hi := 1
  sound := by
    intro x hx
    obtain ⟨h0, h1⟩ := hx
    constructor <;> cega

/--
info: Try this:
  [apply] cega using cosineEnclosure

Lean checked the suggested replacement against the original goal. Selected route: CEGA route: checked certificate.
-/
#guard_msgs in
example : EnclosedOn Real.cos (Set.Icc 0 1) (1 / 2 : ℝ) 1 := by
  cega? using cosineEnclosure

/--
info: Try this:
  [apply] cega [fast]

Lean checked the suggested replacement against the original goal.
-/
#guard_msgs in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * x ≤ 1 := by
  cega? [fast]

/--
info: Try this:
  [apply] cega (depth := 3)

Lean checked the suggested replacement against the original goal.
-/
#guard_msgs in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega? (depth := 3)

/--
info: Try this:
  [apply] cega [enclose x in [0, 1]] (x * (1 - x))

Lean checked the suggested replacement against the original goal. Selected route: CEGA box query: upper bound.
-/
#guard_msgs in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega? [enclose x in [0, 1]] (x * (1 - x))

/--
info: Try this:
  [apply] cega (depth := 2) [enclose x in [0, 1]] (x / (1 + x))

Lean checked the suggested replacement against the original goal. Selected route: CEGA box query: enclosure after checked box refinement.
-/
#guard_msgs in
example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0))
      {p : ℝ^1 | 0 ≤ p 0 ∧ p 0 ≤ 1} 0 (1 / 2) := by
  cega? (depth := 2) [enclose x in [0, 1]] (x / (1 + x))

/--
info: Try this:
  [apply] cega

Lean checked the suggested replacement against the original goal. Selected route: CEGA route: checked batch quadrature of an interval integral.
-/
#guard_msgs in
example : |(∫ x in (0 : ℝ)..1, x ^ 2) - 1 / 3| ≤ 1 / 100 := by
  cega?

/--
info: Try this:
  [apply] cega [batch := 3]

Lean checked the suggested replacement against the original goal.
-/
#guard_msgs in
example : ∀ i : Fin 10, i.val * i.val < 100 := by
  cega? [batch := 3]

/--
info: Try this:
  [apply] cega [fast, batch := 4]

Lean checked the suggested replacement against the original goal.
-/
#guard_msgs in
example : ∀ i : Fin 10, i.val * i.val < 100 := by
  cega? [fast, batch := 4]

/-! ## The route order of `cas` -/

/--
info: [(determinant, 2000),
 (ideal, 1950),
 (algebraStatement, 1900),
 (algebraicEquality, 1800),
 (commandStatement, 1700),
 (derivative, 1600),
 (integral, 1500),
 (semantic, 1400),
 (reflectedEquality, 1300),
 (arithmetic, 1200),
 (equationHint, 1150),
 (polynomialEquations, 1100),
 (checkedIdentity, 1050),
 (box, 900),
 (command, 800),
 (elementary, 700),
 (normNum, 600),
 (grind, 500)]
-/
#guard_msgs in
run_meta do
  Lean.logInfo m!"{← CAS.ExactTactic.routeOrder}"

end CAS.Examples.Reporting

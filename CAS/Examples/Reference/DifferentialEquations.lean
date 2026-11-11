/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Differential equations

The compiled examples of the docstrings of the DifferentialEquations family: linear differential
equations solved exactly, and certified numerical solutions of initial-value problems. Each
section pins the report lines that a docstring shows and proves its theorem, and checks the axioms
of that proof.
-/

@[expose] public section

namespace CAS.Examples.Reference.DifferentialEquations

set_option linter.hashCommand false

/-! ## dsolve -/

/--
Output (order 2, characteristic roots: ±i): y(x) = c₁*cos(x) + c₂*sin(x)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [dsolve y x] (y'' + y = 0)

/--
Output (order 1, characteristic roots: -2): y(x) = -(1/4) + 1/2*x + c₁*exp(-(2*x))
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [dsolve y x] (y' + 2*y = x)

/--
Output (order 2, characteristic roots: ±i): y(x) = cos(x)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [dsolve y x, y 0 = 1, y' 0 = 0] (y'' + y = 0)

theorem dsolve_solution (c₁ x : ℝ) :
    HasDerivAt (fun x ↦ -(1 / 4) + 1 / 2 * x + c₁ * Real.exp (-(2 * x)))
      (x - 2 * (-(1 / 4) + 1 / 2 * x + c₁ * Real.exp (-(2 * x)))) x := by
  cas

/--
info: 'CAS.Examples.Reference.DifferentialEquations.dsolve_solution' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dsolve_solution

/--
dsolve: the equation is not linear in y and its derivatives
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [dsolve y x] (y' * y = 1)

/--
dsolve: the equation has no derivative of y
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [dsolve y x] (z'' + z = 0)

/--
dsolve: the initial values must be given at one point
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [dsolve y x, y 0 = 1, y 1 = 2] (y'' + y = 0)

/-! ## ndsolve -/

/--
Output (certified enclosures of width at most 10^-6; the solution exists and is unique on [0, 1]
(5 pieces)): y(1) ∈ [1.5574077, 1.5574078]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [ndsolve y t in [0, 1], y 0 = 0] (y' = 1 + y ^ 2)

/--
Output (certified enclosures of width at most 10^-10; the solution exists and is unique on
[0, 1] (5 pieces)): y(1/2) ∈ [1.64872127070, 1.64872127071],
y(1) ∈ [2.71828182845, 2.71828182846]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (digits := 10) [ndsolve y t in [0, 1], y 0 = 1, at [1/2, 1]] (y' = y)

theorem ndsolve_exp_bounds : 2.7182818 ≤ Real.exp 1 ∧ Real.exp 1 ≤ 2.7182819 := by
  cas

/--
info: 'CAS.Examples.Reference.DifferentialEquations.ndsolve_exp_bounds' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ndsolve_exp_bounds

/--
ndsolve: no certified step at t = 49841/50000; the solution may blow up there
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [ndsolve y t in [0, 2], y 0 = 1] (y' = y ^ 2)

/--
ndsolve: f must be a polynomial in t and y with rational coefficients
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [ndsolve y t in [0, 1], y 0 = 1] (y' = sin y)

/--
ndsolve: the initial condition must be at t₀ = 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [ndsolve y t in [0, 1], y 1 = 1] (y' = y)

end CAS.Examples.Reference.DifferentialEquations

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Equations and inequalities

The compiled examples of the docstrings of the Equations family: the real solutions of polynomial
equations and systems, the reduction of polynomial and rational relations to intervals, and the
certified real and complex roots of a polynomial. Each section pins the report lines that a
docstring shows and proves its theorem, and checks the axioms of that proof. The last part proves
inequalities between polynomials by sums of squares.
-/

@[expose] public section

namespace CAS.Examples.Reference.Equations

set_option linter.hashCommand false

/-! ## solve -/

/--
Output (equivalent real solution predicate): x = sqrt(2) ∨ x = -sqrt(2)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [solve x] (x ^ 2 = 2)

/--
Output (equivalent real solution predicate): x = ρ0
ρ0: the root of x^3 - 2 in (1.25992104, 1.25992105)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [solve x] (x ^ 3 - 2 = 0)

/--
Output (complete list of real solutions): {x = -1, y = -2}, {x = -2, y = -1}, {x = 2, y = 1},
{x = 1, y = 2}
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [solve x, y] (x^2 + y^2 = 5 ∧ x * y = 2)

theorem solve_square : ∀ x : ℝ, x ^ 2 = 1 ↔ x = 1 ∨ x = -1 := by
  cas

/--
info: 'CAS.Examples.Reference.Equations.solve_square' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solve_square

/--
supported fragment: polynomials with rational coefficients in one real variable; for other
equations, #cas [findRoot x in [a, b]] (f = g) finds a certified root in an interval
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [solve x] (sin x = 0)

/--
solve expects an equation; use reduce for an affine comparison
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [solve x] (x < 1)

/--
solve: the system has infinitely many complex solutions; the nonlinear solver takes systems
with finitely many
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [solve x, y] (x^2 + y^2 = 1)

/-! ## reduce -/

/--
Output (equivalent real solution predicate): x ≥ -2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [reduce x] (-2 * x + 3 ≤ 7)

/--
Output (equivalent condition on the real roots): ρ0 < x < ρ1, where ρ0 = -1.41421356237309504880…,
ρ1 = 1.41421356237309504880…
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [reduce x] (x^2 < 2)

/--
Output (equivalent condition on the real roots): x < -2 ∨ 1 < x
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [reduce x] ((x - 1) / (x + 2) > 0)

theorem reduce_positive : ∀ x : ℝ, 0 < x ^ 2 - x + 1 := by
  cas

/--
info: 'CAS.Examples.Reference.Equations.reduce_positive' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reduce_positive

/--
expected a real equation or comparison
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [reduce x] (x^2 + 1)

/--
supported fragment: polynomials with rational coefficients in one real variable; for other
equations, #cas [findRoot x in [a, b]] (f = g) finds a certified root in an interval
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [reduce x] (sin x > 0)

/-! ## roots -/

/--
Output (the only real solution, by 20 decimals, truncated): 2.09455148154232659148
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [roots x] (x^3 - 2*x - 5 = 0)

/--
Output (all 4 real solutions; enclosed ones by 20 decimals, truncated): -2, 1,
-1.41421356237309504880, 1.41421356237309504880
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [roots x] ((x - 1)^2 * (x + 2) * (x^2 - 2))

/--
Output (all 2 real solutions; enclosed ones by 40 decimals, truncated):
-1.4142135623730950488016887242096980785696, 1.4142135623730950488016887242096980785696
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (digits := 40) [roots x] (x^2 = 2)

theorem roots_cubic : ∃ x : ℝ, x ^ 3 - 2 * x - 5 = 0 ∧ 2 < x ∧ x < 3 := by
  cas

/--
info: 'CAS.Examples.Reference.Equations.roots_cubic' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms roots_cubic

/--
the polynomial is zero; every real number is a solution
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [roots x] (x = x)

/--
roots supports polynomial equations with rational coefficients
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [roots x] (sin x = 0)

/--
roots accepts between 1 and 60 digits
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (digits := 61) [roots x] (x^2 = 2)

/-!
## Inequalities between polynomials by sums of squares

`cas [oracle := sympy]` (in `CASOracle`) proves `0 ≤ p`, `a ≤ b` and `a ≥ b` between real
polynomials by writing the difference as a sum `∑ dᵢ * ℓᵢ ^ 2 * ∏ gⱼ`, where the weights `dᵢ` are
positive rationals and the factors `gⱼ` come from hypotheses `0 ≤ gⱼ`, or `a ≤ b` read as
`0 ≤ b - a`. The oracle finds the sum numerically with cvxpy and rounds it to exact rationals.
Lean checks the identity with `ring` and the sign of every term with `positivity` by running the
script that the tactic suggests, as printed, which no longer needs the oracle.

For `0 < p`, `a < b` and `a > b` the sum also has a positive term, a positive constant or a
positive constant times hypotheses `0 < hⱼ`, and `positivity` proves the sum positive. The oracle
looks for such a sum equal to `p` first. When it finds none, it tries a multiplier `M` of the same
form as the sum, of degree at most 2 and then at most 4, such that `M * p` is a sum with a
positive term, and `pos_of_mul_pos_right` turns `0 < M * p` and `0 ≤ M` into `0 < p`.

The proofs of `quartic_nonneg` to `not_attained` are the scripts that `cas [oracle := sympy]`
suggested for their goals, with line breaks added, and they compile in the default build, where
no oracle runs. Another solver can round to another sum of squares.

A nonnegative polynomial need not be a sum of squares. For Motzkin's
`x^4*y^2 + x^2*y^4 - 3*x^2*y^2 + 1` the oracle finds no positive semidefinite Gram matrix, and
that refusal says nothing about the inequality. The refusal "no sum of squares with a positive
term" of a strict inequality says nothing either.
-/

/-- The rounded Gram matrix gives four squares, where the two of
`(x ^ 2 - y ^ 2) ^ 2 + 2 * (x * y - 1) ^ 2` would also do. -/
theorem quartic_nonneg (x y : ℝ) : 0 ≤ x ^ 4 + y ^ 4 - 4 * x * y + 2 := by
  rw [show x ^ 4 + y ^ 4 - 4 * x * y + 2 =
      (1 / 4) * (2 * x ^ 2 - y ^ 2 - 1) ^ 2 + (x * y - 1) ^ 2 + (3 / 4) * (y ^ 2 - 1) ^ 2 +
        (x - y) ^ 2 by ring]
  positivity

/-- Under `∀` binders the script starts with `intro`, as in the proof that
`#cas [sos x, y, oracle := sympy] (x ^ 4 + y ^ 4 - 4 * x * y + 2)` prints. -/
theorem quartic_nonneg_forall : ∀ x y : ℝ, 0 ≤ x ^ 4 + y ^ 4 - 4 * x * y + 2 := by
  intro x y
  rw [show x ^ 4 + y ^ 4 - 4 * x * y + 2 =
      (1 / 4) * (2 * x ^ 2 - y ^ 2 - 1) ^ 2 + (x * y - 1) ^ 2 + (3 / 4) * (y ^ 2 - 1) ^ 2 +
        (x - y) ^ 2 by ring]
  positivity

/-- A goal `a ≥ b` becomes `0 ≤ a - b`. -/
theorem square_ge (x y : ℝ) : (x ^ 2 + y ^ 2) ^ 2 ≥ 4 * x ^ 2 * y ^ 2 := by
  rw [ge_iff_le, ← sub_nonneg,
    show (x ^ 2 + y ^ 2) ^ 2 - 4 * x ^ 2 * y ^ 2 = (x ^ 2 - y ^ 2) ^ 2 by ring]
  positivity

/-- The premises `x ≥ 0` and `y ≥ 0` multiply the squares, and `positivity` finds them in
context. -/
theorem cubic_ge (x y : ℝ) : x ≥ 0 → y ≥ 0 → x ^ 3 + y ^ 3 ≥ x ^ 2 * y + x * y ^ 2 := by
  intro h₁ h₂
  rw [ge_iff_le, ← sub_nonneg,
    show x ^ 3 + y ^ 3 - (x ^ 2 * y + x * y ^ 2) = (x - y) ^ 2 * x + (x - y) ^ 2 * y by ring]
  positivity

/-- A hypothesis `x ≤ 1` enters as `0 ≤ 1 - x`, stated by `sub_nonneg.mpr`. -/
theorem cube_le_square (x : ℝ) (h : x ≤ 1) : x ^ 3 ≤ x ^ 2 := by
  have h₁ := sub_nonneg.mpr h
  rw [← sub_nonneg, show x ^ 2 - x ^ 3 = x ^ 2 * (1 - x) by ring]
  positivity

/-- The weights are positive rationals. -/
theorem rational_weights : ∀ x y : ℝ, 0 ≤ x ^ 2 + x * y + y ^ 2 := by
  intro x y
  rw [show x ^ 2 + x * y + y ^ 2 = (1 / 4) * (2 * x + y) ^ 2 + (3 / 4) * y ^ 2 by ring]
  positivity

/-- For `0 < p` the sum has a positive term, here the constant `1 / 2`. -/
theorem quartic_pos : ∀ x : ℝ, 0 < x ^ 4 - x + 1 := by
  intro x
  rw [show x ^ 4 - x + 1 =
      (1 / 4) * (2 * x ^ 2 - 1) ^ 2 + (1 / 4) * (2 * x - 1) ^ 2 + (1 / 2) by ring]
  positivity

/-- A goal `a < b` becomes `0 < b - a`. -/
theorem sum_lt : ∀ x y : ℝ, x * y + x + y < x ^ 2 + y ^ 2 + 2 := by
  intro x y
  rw [← sub_pos, show x ^ 2 + y ^ 2 + 2 - (x * y + x + y) =
      (1 / 4) * (2 * x - y - 1) ^ 2 + (3 / 4) * (y - 1) ^ 2 + 1 by ring]
  positivity

/-- The premise `0 < x` enters as a factor, possibly repeated, and `positivity` finds it in
context. The rounded solution spreads the weight over every allowed term, where `x ^ 2 * x + x`
would also do. -/
theorem cubic_pos : ∀ x : ℝ, 0 < x → 0 < x ^ 3 + x := by
  intro x h₁
  rw [show x ^ 3 + x =
      (1 / 12) * x ^ 2 + (1 / 8) * (2 * x - 1) ^ 2 * x + (7 / 8) * x + (5 / 12) * x * x +
        (1 / 2) * x * x * x by ring]
  positivity

/-- `(x * y - 1) ^ 2 + x ^ 2` is positive. Without premises the positive term of a sum is a
constant `c > 0`, and no such sum equals this polynomial, which takes values below every such `c`,
at `x = 1 / y` for large `y`. The proof multiplies it by a sum of squares `M`, and
`pos_of_mul_pos_right` turns `0 < M * p` and `0 ≤ M` into `0 < p`. -/
theorem not_attained : ∀ x y : ℝ, 0 < (x * y - 1) ^ 2 + x ^ 2 := by
  intro x y
  refine pos_of_mul_pos_right (a := (1 / 16) * (4 * x + y) ^ 2 + (27 / 16) * y ^ 2 + (3 / 2)) ?_
    (by positivity)
  rw [show ((1 / 16) * (4 * x + y) ^ 2 + (27 / 16) * y ^ 2 + (3 / 2)) *
        ((x * y - 1) ^ 2 + x ^ 2) =
      (1 / 16) * (4 * x ^ 2 * y + x * y ^ 2 - 2 * x - y) ^ 2 +
        (3 / 16) * (3 * x * y ^ 2 + 2 * x - 3 * y) ^ 2 +
        (1 / 16) * (4 * x ^ 2 - x * y + 1) ^ 2 + (1 / 176) * (11 * x * y - 3) ^ 2 + x ^ 2 +
        (61 / 44) by ring]
  positivity

/--
info: 'CAS.Examples.Reference.Equations.quartic_nonneg' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms quartic_nonneg

/--
info: 'CAS.Examples.Reference.Equations.quartic_nonneg_forall' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms quartic_nonneg_forall

/--
info: 'CAS.Examples.Reference.Equations.square_ge' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms square_ge

/--
info: 'CAS.Examples.Reference.Equations.cubic_ge' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cubic_ge

/--
info: 'CAS.Examples.Reference.Equations.cube_le_square' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cube_le_square

/--
info: 'CAS.Examples.Reference.Equations.rational_weights' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rational_weights

/--
info: 'CAS.Examples.Reference.Equations.quartic_pos' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms quartic_pos

/--
info: 'CAS.Examples.Reference.Equations.sum_lt' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sum_lt

/--
info: 'CAS.Examples.Reference.Equations.cubic_pos' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cubic_pos

/--
info: 'CAS.Examples.Reference.Equations.not_attained' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms not_attained

end CAS.Examples.Reference.Equations

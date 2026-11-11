/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Nonlinear polynomial systems

`#cas [solve x, y, …]` on polynomial equations with rational coefficients, at least one of them
nonlinear, lists every real solution and proves the list complete. The commands at the end of this
file run in the build, each inside `#guard_msgs`, which checks its report.

The first answer is `{x = -1, y = -2}, {x = -2, y = -1}, {x = 2, y = 1}, {x = 1, y = 2}`, with
the theorem

`∀ (x y : ℝ), x ^ 2 + y ^ 2 = 5 ∧ x * y = 2 ↔`
`x = -1 ∧ y = -2 ∨ x = -2 ∧ y = -1 ∨ x = 2 ∧ y = 1 ∨ x = 1 ∧ y = 2`.

The circle and the parabola meet at `{x = ±0.78615137775742328606…, y ≈ 0.618033988749895}`; the
theorem names the two roots of the eliminant `x ^ 4 + x ^ 2 - 1`:

`∃ ρ, ((-78615137775742328607 / 10 ^ 20 < ρ 0 ∧ ρ 0 < -78615137775742328606 / 10 ^ 20) ∧`
`78615137775742328606 / 10 ^ 20 < ρ 1 ∧ ρ 1 < 78615137775742328607 / 10 ^ 20) ∧`
`∀ (x y : ℝ), x ^ 2 + y ^ 2 = 1 ∧ y = x ^ 2 ↔ x = ρ 0 ∧ y = ρ 0 ^ 2 ∨ x = ρ 1 ∧ y = ρ 1 ^ 2`.

The third system mixes a rational and two irrational points, `{x = ±1.73205080756887729352…,
y ≈ 1}` and `{x = 0, y = -2}`; the theorem keeps the rational point exact,
`… ↔ x = ρ 0 ∧ y = ρ 0 ^ 2 - 2 ∨ x = 0 ∧ y = -2 ∨ x = ρ 2 ∧ y = ρ 2 ^ 2 - 2`. In the fourth the
four points `(±1/√2, ±1/√2)` share their coordinates in pairs, so the basis is computed for the
separating form `x + 2 y` and the coordinates are cubics in its roots,
`x = 1 / 3 * ρ j ^ 3 - 7 / 6 * ρ j ∧ y = -(1 / 6 * ρ j ^ 3) + 13 / 12 * ρ j` for `j < 4`. The fifth
system is `(x + i y) ^ 3 = 1`, with the real points `{x = 1, y = 0}` and
`{x ≈ -0.5, y ≈ ±0.866025403784439}`. The sixth has no real point, `∀ (x y : ℝ),
¬(x ^ 2 + y ^ 2 = -1 ∧ x = y)`. The three-variable system gives `{x = -1, y = -1, z = -1},
{x = 1, y = 1, z = 1}`; the symmetric system `x + y + z = 0 ∧ x y + y z + z x = -1 ∧ x y z = 0`,
whose solutions are the six permutations of `(-1, 0, 1)`, takes about 60 s and is not run in the
build. The grid `x ∈ {0, 1, 2, 3, 5}`, `y ∈ {0, 1, 2}` has fifteen points; each unknown takes
each of its values at several of them, and the first form of the family `x + c y` that separates
them all is `x + 6 y`. With an eliminant of degree 15 its proof takes about 13 minutes, so it is
not run in the build either. The circle alone is refused: it has infinitely many complex points.

Behind each answer are two proofs. The system is equivalent to its triangular form, by
`linear_combination` in both directions; the roots of the eliminant come from one kernel
evaluation of `reduceCheck`, and `solve_of_reduceCheck` joins the two into the list of points.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [solve x, y]
Domain: (x, y) ∈ ℝ^2
Input (polynomial system): (x^2 + y^2 = 5 ∧ x * y = 2)
Output (complete list of real solutions): {x = -1, y = -2}, {x = -2, y = -1}, {x = 2, y = 1}, {x =
1, y = 2}

[CAS.Command.details] More details
  [CAS.Command.computation] Gröbner basis
    lexicographic basis in shape position with respect to y; eliminant of degree 4, 4 real roots, 4
polynomials in the derivation
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Complete list of real solutions
        Proposition: ∀ (x y : ℝ),
          x ^ 2 + y ^ 2 = 5 ∧ x * y = 2 ↔ x = -1 ∧ y = -2 ∨ x = -2 ∧ y = -1 ∨ x = 2 ∧ y = 1 ∨ x = 1
∧ y = 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [solve x, y] (x^2 + y^2 = 5 ∧ x * y = 2)

/--
info: #cas [solve x, y]
Domain: (x, y) ∈ ℝ^2
Input (polynomial system): (x^2 + y^2 = 1 ∧ y = x^2)
Output (complete list of real solutions): {x = -0.78615137775742328606…, y ≈ 0.618033988749895}, {x
= 0.78615137775742328606…, y ≈ 0.618033988749895}

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x, y] (x^2 + y^2 = 1 ∧ y = x^2)

/--
info: #cas [solve x, y]
Domain: (x, y) ∈ ℝ^2
Input (polynomial system): (x^2 + y^2 = 4 ∧ y = x^2 - 2)
Output (complete list of real solutions): {x = -1.73205080756887729352…, y ≈ 1}, {x = 0, y = -2}, {x
= 1.73205080756887729352…, y ≈ 1}

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x, y] (x^2 + y^2 = 4 ∧ y = x^2 - 2)

/--
info: #cas [solve x, y]
Domain: (x, y) ∈ ℝ^2
Input (polynomial system): (x^2 + y^2 = 1 ∧ x^2 - y^2 = 0)
Output (complete list of real solutions): {x ≈ -0.707106781186548, y ≈ -0.707106781186548}, {x ≈
0.707106781186548, y ≈ -0.707106781186548}, {x ≈ -0.707106781186548, y ≈ 0.707106781186548}, {x ≈
0.707106781186548, y ≈ 0.707106781186548}

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x, y] (x^2 + y^2 = 1 ∧ x^2 - y^2 = 0)

/--
info: #cas [solve x, y]
Domain: (x, y) ∈ ℝ^2
Input (polynomial system): (x^3 - 3*x*y^2 = 1 ∧ 3*x^2*y - y^3 = 0)
Output (complete list of real solutions): {x ≈ -0.5, y ≈ -0.866025403784439}, {x ≈ -0.5, y ≈
0.866025403784439}, {x = 1, y = 0}

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x, y] (x^3 - 3*x*y^2 = 1 ∧ 3*x^2*y - y^3 = 0)

/--
info: #cas [solve x, y]
Domain: (x, y) ∈ ℝ^2
Input (polynomial system): (x^2 + y^2 = -1 ∧ x = y)
Output (complete list of real solutions): False

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x, y] (x^2 + y^2 = -1 ∧ x = y)

/--
info: #cas [solve x, y, z]
Domain: (x, y, z) ∈ ℝ^3
Input (polynomial system): (x^2 + y^2 + z^2 = 3 ∧ x = y ∧ y = z)
Output (complete list of real solutions): {x = -1, y = -1, z = -1}, {x = 1, y = 1, z = 1}

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x, y, z] (x^2 + y^2 + z^2 = 3 ∧ x = y ∧ y = z)

/--
error: solve: the system has infinitely many complex solutions; the nonlinear solver takes systems
with finitely many
-/
#guard_msgs in
#cas [solve x, y] (x^2 + y^2 = 1)


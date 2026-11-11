/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Linear systems with a parameter

`#cas [solve x, y, …]` on a square linear system whose coefficients are polynomials in one further
symbol solves it for every value of that symbol: the generic solution where the determinant does not
vanish, and the system at each rational root of the determinant. The commands at the end of this
file run in the build, each inside `#guard_msgs`, which checks its report.

The outputs are `x = 1/(a + 1) ∧ y = 1/(a + 1) for a ≠ 1 ∧ a ≠ -1; a = 1: x = 1 - y;
a = -1: no solution`; `x = (a - 4)/(a - 1) ∧ y = 1/(a - 1) ∧ z = 2/(a - 1) for a ≠ 1;
a = 1: no solution`; and, for the last system, whose determinant `2 a ^ 2 - 1` has no rational root,
the generic solution under `2*a^2 - 1 ≠ 0` with the note that its real roots are not treated. The
first theorem is

`(∀ (a x y : ℝ), a ≠ 1 → a ≠ -1 → (a * x + y = 1 ∧ x + a * y = 1 ↔ x = 1 / (a + 1) ∧`
`y = 1 / (a + 1))) ∧ (∀ (a x y : ℝ), a = 1 → (a * x + y = 1 ∧ x + a * y = 1 ↔ x = 1 - y)) ∧`
`∀ (a x y : ℝ), a = -1 → ¬(a * x + y = 1 ∧ x + a * y = 1)`.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [solve x, y]
Domain: (x, y) ∈ ℝ^2, a ∈ ℝ
Input (linear system with the parameter a): (a*x + y = 1 ∧ x + a*y = 1)
Output (solution by cases of the parameter): x = 1/(a + 1) ∧ y = 1/(a + 1) for a ≠ 1 ∧ a ≠ -1; a =
1: x = 1 - y; a = -1: no solution

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The solution for every value of the parameter
        Proposition: (∀ (a x y : ℝ),
            a ≠ 1 → a ≠ -1 → (a * x + y = 1 ∧ x + a * y = 1 ↔ x = 1 / (a + 1) ∧ y = 1 / (a + 1))) ∧
          (∀ (a x y : ℝ), a = 1 → (a * x + y = 1 ∧ x + a * y = 1 ↔ x = 1 - y)) ∧
            ∀ (a x y : ℝ), a = -1 → ¬(a * x + y = 1 ∧ x + a * y = 1)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [solve x, y] (a*x + y = 1 ∧ x + a*y = 1)

/--
info: #cas [solve x, y, z]
Domain: (x, y, z) ∈ ℝ^3, a ∈ ℝ
Input (linear system with the parameter a): (x + y + z = 1 ∧ x + a*y + z = 2 ∧ x + y + a*z = 3)
Output (solution by cases of the parameter): x = (a - 4)/(a - 1) ∧ y = 1/(a - 1) ∧ z = 2/(a - 1) for
a ≠ 1; a = 1: no solution

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x, y, z] (x + y + z = 1 ∧ x + a*y + z = 2 ∧ x + y + a*z = 3)

/--
info: #cas [solve x, y]
Domain: (x, y) ∈ ℝ^2, a ∈ ℝ
Input (linear system with the parameter a): (a*x + y = 1 ∧ x + 2*a*y = 1)
Output (solution by cases of the parameter): x = (a - 1/2)/(a^2 - 1/2) ∧ y = (1/2*a - 1/2)/(a^2 -
1/2) for 2*a^2 - 1 ≠ 0; the determinant has a factor without rational roots, whose real roots are
not treated

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x, y] (a*x + y = 1 ∧ x + 2*a*y = 1)


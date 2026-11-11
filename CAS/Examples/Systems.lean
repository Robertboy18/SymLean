/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Linear systems

`#cas [solve x, y, …] (e₁ = f₁ ∧ …)` solves a linear system with rational coefficients and proves
the equivalence with the solved form for every real assignment. Each command runs in the build
inside `#guard_msgs`, which checks its report.

The outputs are `x = 1 ∧ y = -1`; `x = 5/3 ∧ y = 5/3 ∧ z = 8/3`; `False` (the third system is
inconsistent: the first two equations give `2 x + z = 6`); `x = 2 + z ∧ y = -1 - 2*z` with the
free parameter `z`; `x = 6/5 ∧ y = 6/5`; and `x = «u + -v»` with the free parameter `«u + -v»`,
whose name prints with Lean's escapes. The first statement is
`∀ (x y : ℝ), 2 * x + y = 1 ∧ x - y = 2 ↔ x = 1 ∧ y = -1`.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [solve x, y]
Domain: (x, y) ∈ ℝ^2
Input (linear system): (2*x + y = 1 ∧ x - y = 2)
Output (unique solution): x = 1 ∧ y = -1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Equivalence with the solved form for every real assignment
        Proposition: ∀ (x y : ℝ), 2 * x + y = 1 ∧ x - y = 2 ↔ x = 1 ∧ y = -1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [solve x, y] (2*x + y = 1 ∧ x - y = 2)

/--
info: #cas [solve x, y, z]
Domain: (x, y, z) ∈ ℝ^3
Input (linear system): (x + y + z = 6 ∧ x - y = 0 ∧ x + 2*z = 7)
Output (unique solution): x = 5/3 ∧ y = 5/3 ∧ z = 8/3

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x, y, z] (x + y + z = 6 ∧ x - y = 0 ∧ x + 2*z = 7)

/--
info: #cas [solve x, y, z]
Domain: (x, y, z) ∈ ℝ^3
Input (linear system): (x + y + z = 6 ∧ x - y = 0 ∧ 2*x + z = 5)
Output (equivalent real solution predicate): False

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x, y, z] (x + y + z = 6 ∧ x - y = 0 ∧ 2*x + z = 5)

/--
info: #cas [solve x, y, z]
Domain: (x, y, z) ∈ ℝ^3
Input (linear system): (x + y + z = 1 ∧ x - z = 2)
Output (solutions with free parameters [z]): x = 2 + z ∧ y = -1 - 2*z

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x, y, z] (x + y + z = 1 ∧ x - z = 2)

/--
info: #cas [solve x, y]
Domain: (x, y) ∈ ℝ^2
Input (linear system): (x/2 + y/3 = 1 ∧ x = y)
Output (unique solution): x = 6/5 ∧ y = 6/5

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x, y] (x/2 + y/3 = 1 ∧ x = y)

/--
info: #cas [solve x, «u + -v»]
Domain: (x, «u + -v») ∈ ℝ^2
Input (linear system): (x = «u + -v»)
Output (solutions with free parameters [«u + -v»]): x = «u + -v»

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x, «u + -v»] (x = «u + -v»)


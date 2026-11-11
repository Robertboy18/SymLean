/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Ranked simplification

`#cas [fullSimplify] e` proposes several forms of `e`, ranks them by a complexity function and
reports the simplest form whose identity with `e` the kernel accepts. `#cas [expand]`,
`#cas [factor]` and `#cas [trigExpand]` restrict the proposals. Each command runs in the build
inside `#guard_msgs`, which checks its report.

The outputs are `(x + 1)^5`, `(x^2 - 1)^2`, `0`, `0`, `|x + 1|`, `0` under `x ≠ 0` and
`y ≠ 0`, `x^2 + 1` under `x^2 - 1 ≠ 0`, `(x + y)^3`, `x` under `x > 0`, `(x + 1)^2`,
`(x - 1)^2*(2*x + 1)`, `x*y*(x - y)*(x + y)`,
`x^3*y - 2*x^3 + 3*x^2*y - 6*x^2 + 3*x*y - 6*x + y - 2` and `sin(x)*cos(y) + cos(x)*sin(y)`.
For the logarithm, the report states and checks
`∀ (x y : ℝ), x ≠ 0 → y ≠ 0 → Real.log (x * y) - Real.log x - Real.log y = 0`. The first, third,
fifth and sixth inputs are the expansions and identities that the configured `simplify` pass
leaves unchanged or only reorders.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [fullSimplify]
Domain: x ∈ ℝ
Input (scalar ℝ): (x^5 + 5*x^4 + 10*x^3 + 10*x^2 + 5*x + 1)
Output (scalar ℝ): (x + 1)^5

[CAS.Command.details] More details
  [CAS.Command.computation] Ranked candidates (proposals, not proof)
    factored polynomial: (x + 1)^5  [leafCount 5, conditions 0]
    input: x^5 + 5*x^4 + 10*x^3 + 10*x^2 + 5*x + 1  [leafCount 27, conditions 0]
    exact passes: x^5 + 5*(x^4 + 2*(x^3 + x^2 + 1/2*(x + 1/5)))  [leafCount 29, conditions 0]
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the factored polynomial
        Proposition: ∀ (x : ℝ), x ^ 5 + 5 * x ^ 4 + 10 * x ^ 3 + 10 * x ^ 2 + 5 * x + 1 = (x + 1) ^
5
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [fullSimplify] (x^5 + 5*x^4 + 10*x^3 + 10*x^2 + 5*x + 1)

/--
info: #cas [fullSimplify]
Domain: x ∈ ℝ
Input (scalar ℝ): (x^4 - 2*x^2 + 1)
Output (scalar ℝ): (x^2 - 1)^2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fullSimplify] (x^4 - 2*x^2 + 1)

/--
info: #cas [fullSimplify]
Domain: x ∈ ℝ
Input (scalar ℝ): (sin (2*x) - 2*sin x*cos x)
Output (scalar ℝ): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fullSimplify] (sin (2*x) - 2*sin x*cos x)

/--
info: #cas [fullSimplify]
Domain: x ∈ ℝ
Input (scalar ℝ): (cos x ^ 2 - sin x ^ 2 - cos (2*x))
Output (scalar ℝ): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fullSimplify] (cos x ^ 2 - sin x ^ 2 - cos (2*x))

/--
info: #cas [fullSimplify]
Domain: x ∈ ℝ
Input (scalar ℝ): (sqrt (x^2 + 2*x + 1))
Output (scalar ℝ): |x + 1|

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fullSimplify] (sqrt (x^2 + 2*x + 1))

/--
info: #cas [fullSimplify]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (log (x*y) - log x - log y)
Output (scalar ℝ): 0
Conditions: x ≠ 0; y ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fullSimplify] (log (x*y) - log x - log y)

/--
info: #cas [fullSimplify]
Domain: x ∈ ℝ
Input (scalar ℝ): ((x^4 - 1)/(x^2 - 1))
Output (scalar ℝ): x^2 + 1
Conditions: x^2 - 1 ≠ 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fullSimplify] ((x^4 - 1)/(x^2 - 1))

/--
info: #cas [fullSimplify]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (x^3 + 3*x^2*y + 3*x*y^2 + y^3)
Output (scalar ℝ): (x + y)^3

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fullSimplify] (x^3 + 3*x^2*y + 3*x*y^2 + y^3)

/--
info: #cas [fullSimplify]
Domain: x ∈ ℝ
Input (scalar ℝ): (exp (log x))
Output (scalar ℝ): x
Conditions: x > 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fullSimplify] (exp (log x))

/--
info: #cas [fullSimplify depth]
Domain: x ∈ ℝ
Input (scalar ℝ): (x^2 + 2*x + 1)
Output (scalar ℝ): (x + 1)^2

[CAS.Command.details] More details
  [CAS.Command.computation] Ranked candidates (proposals, not proof)
    factored polynomial: (x + 1)^2  [depth 3, conditions 0]
    input: x^2 + 2*x + 1  [depth 4, conditions 0]
    exact passes: x^2 + 2*(x + 1/2)  [depth 4, conditions 0]
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the factored polynomial
        Proposition: ∀ (x : ℝ), x ^ 2 + 2 * x + 1 = (x + 1) ^ 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [fullSimplify depth] (x^2 + 2*x + 1)

/--
info: #cas [factor]
Domain: x ∈ ℝ
Input (scalar ℝ): (2*x^3 - 3*x^2 + 1)
Output (scalar ℝ): (x - 1)^2*(2*x + 1)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [factor] (2*x^3 - 3*x^2 + 1)

/--
info: #cas [factor]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (x^3*y - x*y^3)
Output (scalar ℝ): x*y*(x - y)*(x + y)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [factor] (x^3*y - x*y^3)

/--
info: #cas [expand]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): ((x + 1)^3 * (y - 2))
Output (scalar ℝ): x^3*y - 2*x^3 + 3*x^2*y - 6*x^2 + 3*x*y - 6*x + y - 2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [expand] ((x + 1)^3 * (y - 2))

/--
info: #cas [trigExpand]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (sin (x + y))
Output (scalar ℝ): sin(x)*cos(y) + cos(x)*sin(y)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [trigExpand] (sin (x + y))


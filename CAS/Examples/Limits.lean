/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Limits at infinity, one-sided limits and poles

`#cas [limit x → ∞]`, `#cas [limit x → -∞]`, `#cas [limit x → a from above]` and `from below` prove
finite and infinite limits; `#cas [limit x → a]` at a pole proves the infinite limit, or both
one-sided limits when they differ. Each command runs in the build inside `#guard_msgs`, which checks
its report.

The outputs are `1/2`, `0`, `∞`, `∞`, `1`, `1`, `∞`, `-∞`, `∞`, `∞` and
`Indeterminate (∞ from above, -∞ from below)`. The theorems are
`Filter.Tendsto (fun x ↦ (x ^ 2 + 1) / (2 * x ^ 2 - 3)) Filter.atTop (nhds (1 / 2))`,
`Filter.Tendsto (fun x ↦ (x ^ 3 + 1) / (x + 2)) Filter.atBot Filter.atTop`,
`Filter.Tendsto (fun x ↦ x * Real.sin (1 / x)) Filter.atTop (nhds 1)`,
`Filter.Tendsto (fun x ↦ 1 / x) (nhdsWithin 0 (Set.Iio 0)) Filter.atBot`,
`Filter.Tendsto (fun x ↦ 1 / x ^ 2) (nhdsWithin 0 {0}ᶜ) Filter.atTop`, and for `1 / x` at `0`
the conjunction of the two one-sided limits. The last command is refused: away from `0`,
`1 / (x + x / x)` is `1 / (x + 1)`, and the exact values of the symbolic derivatives at `0` suggest
a pole, but `x / x` is not valid at `0`, so the domain checker does not certify the denominator.

A limit at infinity goes through `t = 1 / x`: `inversion` writes the expression as
`N (t) / t ^ j`, and the limit is that of `N (t) / t ^ j` as `t → 0` from one side, from the
Taylor coefficients of `N` at `0`. This route needs an expression built from `x` by field
operations and functions of arguments with a finite limit; limits such as those of `exp x`,
`atan x` and `sqrt (x^2 + 1) - x` at `∞` go through the growth comparison of
`AsymptoticLimits.lean` and `AsymptoticCancel.lean` instead.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): ((x^2 + 1) / (2*x^2 - 3))
Output (exact limit from the terms of order 0): 1/2

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Limit
        Proposition: Filter.Tendsto (fun x ↦ (x ^ 2 + 1) / (2 * x ^ 2 - 3)) Filter.atTop (nhds (1 /
2))
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [limit x → ∞] ((x^2 + 1) / (2*x^2 - 3))

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): ((3*x + 1) / (x^2 + 1))
Output (exact limit from the terms of order 0): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → ∞] ((3*x + 1) / (x^2 + 1))

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): (x^3 / (x + 1))
Output (infinite limit at a pole of order 2): ∞

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → ∞] (x^3 / (x + 1))

/--
info: #cas [limit x → -∞]
Domain: x → -∞
Input (scalar ℝ): ((x^3 + 1) / (x + 2))
Output (infinite limit at a pole of order 2): ∞

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → -∞] ((x^3 + 1) / (x + 2))

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): (x * sin (1 / x))
Output (exact limit from the terms of order 1): 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → ∞] (x * sin (1 / x))

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): (x * (exp (1 / x) - 1))
Output (limit from the dominant term): 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → ∞] (x * (exp (1 / x) - 1))

/--
info: #cas [limit x → 0 from above]
Domain: x → 0⁺
Input (scalar ℝ): (1 / x)
Output (infinite limit at a pole of order 1): ∞

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → 0 from above] (1 / x)

/--
info: #cas [limit x → 0 from below]
Domain: x → 0⁻
Input (scalar ℝ): (1 / x)
Output (infinite limit at a pole of order 1): -∞

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → 0 from below] (1 / x)

/--
info: #cas [limit x → 1 from below]
Domain: x → 1⁻
Input (scalar ℝ): (x / (x - 1)^2)
Output (infinite limit at a pole of order 2): ∞

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → 1 from below] (x / (x - 1)^2)

/--
info: #cas [limit x → 0]
Domain: x → 0, x ≠ 0
Input (scalar ℝ): (1 / x^2)
Output (infinite limit at a pole of order 2): ∞

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → 0] (1 / x^2)

/--
info: #cas [limit x → 0]
Domain: x → 0, x ≠ 0
Input (scalar ℝ): (1 / x)
Output (no two-sided limit: a pole of order 1): Indeterminate (∞ from above, -∞ from below)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → 0] (1 / x)

/--
error: limit: the domain checker did not certify that the denominator and its derivatives through
order 1 are defined at 0
-/
#guard_msgs (error, whitespace := lax) in
#cas [limit x → 0] (1 / (x + x / x))


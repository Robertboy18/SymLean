/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Limits at infinity whose dominant terms cancel

When the dominant terms of a sum cancel, `#cas [limit x → ∞]` multiplies a square root by its
conjugate, combines two logarithms into the logarithm of a quotient, uses `e ^ u - 1 ~ u` and
`log P ~ P - 1` for `u → 0` and `P → 1`, and expands polynomials, until the dominant term survives.
Each command runs in the build inside `#guard_msgs`, which checks its report.

The outputs are `0`, `3/2`, `1/2`, `0`, `0`, `0` and `1`; the seven take 3 s. The third
theorem is `Filter.Tendsto (fun x ↦ x * (√(x ^ 2 + 1) - x)) Filter.atTop (nhds (1 / 2))`.
`log (exp x + 1) - x` needs a further expansion and is refused.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): (sqrt (x^2 + 1) - x)
Output (limit from the dominant term): 0

[CAS.Command.details] More details
  [CAS.Command.computation] Asymptotic equivalent
    f ~ c x^-1 e^(0 x) (log x)^0
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Limit by asymptotic comparison
        Proposition: Filter.Tendsto (fun x ↦ √(x ^ 2 + 1) - x) Filter.atTop (nhds 0)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [limit x → ∞] (sqrt (x^2 + 1) - x)

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): (sqrt (x^2 + 3 * x) - x)
Output (limit from the dominant term): 3/2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → ∞] (sqrt (x^2 + 3 * x) - x)

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): (x * (sqrt (x^2 + 1) - x))
Output (limit from the dominant term): 1/2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → ∞] (x * (sqrt (x^2 + 1) - x))

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): (x - sqrt (x^2 - 1))
Output (limit from the dominant term): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → ∞] (x - sqrt (x^2 - 1))

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): (sqrt (x + 1) - sqrt x)
Output (limit from the dominant term): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → ∞] (sqrt (x + 1) - sqrt x)

/--
info: #cas [limit x → -∞]
Domain: x → -∞
Input (scalar ℝ): (sqrt (x^2 + 1) + x)
Output (limit from the dominant term): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → -∞] (sqrt (x^2 + 1) + x)

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): (x * (log (x + 1) - log x))
Output (limit from the dominant term): 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → ∞] (x * (log (x + 1) - log x))


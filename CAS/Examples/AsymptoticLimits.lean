/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Limits at infinity with exponentials, logarithms, roots and the arctangent

`#cas [limit x → ∞]` and `#cas [limit x → -∞]` compare growth in the scale `xᵃ eᵇˣ (log x)ᵏ`: every
subexpression gets an equivalent `c xᵃ eᵇˣ (log x)ᵏ`, sums keep their dominant term, and the limit
is that of the equivalent. Each command runs in the build inside `#guard_msgs`, which checks its
report.

The outputs of the eight commands are `0`, `∞`, `0`, `1`, `2`, `pi/2`, `0` and `-∞`. The
theorems are stated for the expression as written, such as
`Filter.Tendsto (fun x ↦ (x ^ 2 + Real.exp x) / (Real.exp x + 1)) Filter.atTop (nhds 1)` and
`Filter.Tendsto (fun x ↦ Real.exp x / x ^ 3) Filter.atTop Filter.atTop`. When the dominant
terms cancel, as in `sqrt (x^2 + 1) - x`, the next term is reached as in
`AsymptoticCancel.lean`.

The compiled theorem is the comparison behind the first answer.
-/

public section

namespace CAS.Examples.AsymptoticLimits

open Filter Topology CAS.Asymptotic

/-- `x² e⁻ˣ → 0`: the triple `(a, b, k) = (2, -1, 0)` is lexicographically negative in
`(b, a, k)`. -/
example : Tendsto (scale 2 (-1) 0) atTop (𝓝 0) :=
  tendsto_scale_zero (Or.inl (by norm_num))

end CAS.Examples.AsymptoticLimits

end

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): (x^2 * exp (-x))
Output (limit from the dominant term): 0

[CAS.Command.details] More details
  [CAS.Command.computation] Asymptotic equivalent
    f ~ c x^2 e^(-1 x) (log x)^0
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Limit by asymptotic comparison
        Proposition: Filter.Tendsto (fun x ↦ x ^ 2 * Real.exp (-x)) Filter.atTop (nhds 0)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [limit x → ∞] (x^2 * exp (-x))

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): (exp x / x^3)
Output (limit from the dominant term): ∞

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → ∞] (exp x / x^3)

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): ((log x)^2 / sqrt x)
Output (limit from the dominant term): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → ∞] ((log x)^2 / sqrt x)

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): ((x^2 + exp x) / (exp x + 1))
Output (limit from the dominant term): 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → ∞] ((x^2 + exp x) / (exp x + 1))

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): (log (x^2 + 1) / log x)
Output (limit from the dominant term): 2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → ∞] (log (x^2 + 1) / log x)

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): (atan x)
Output (limit from the dominant term): pi/2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → ∞] (atan x)

/--
info: #cas [limit x → -∞]
Domain: x → -∞
Input (scalar ℝ): (x * exp x)
Output (limit from the dominant term): 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → -∞] (x * exp x)

/--
info: #cas [limit x → ∞]
Domain: x → ∞
Input (scalar ℝ): (x^3 - exp (x/2))
Output (limit from the dominant term): -∞

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → ∞] (x^3 - exp (x/2))


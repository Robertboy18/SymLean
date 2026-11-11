/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Laurent series

`#cas [series x a n] (g / h)`, where `h` vanishes at `a`, prints the Laurent series through
`(x - a) ^ n` and proves the little-o remainder on a punctured neighbourhood of `a`. Each command
runs in the build inside `#guard_msgs`, which checks its report.

The outputs are `1/x + 1/6*x + 7/360*x^3 + o(x^3)`; `1/x - 1/3*x - 1/45*x^3 + o(x^3)`;
`1/x - 1/2 + 1/12*x - 1/720*x^3 + o(x^3)`, with the Bernoulli numbers; `1/x^2 + 1/3 + 1/15*x^2
+ o(x^2)`; `1/(2*(x - 1)) - 1/4 + 1/8*(x - 1) - 1/16*(x - 1)^2 + o((x - 1)^2)` and, at the other
pole of the same function, `-1/(2*(x + 1)) - 1/4 - 1/8*(x + 1) - 1/16*(x + 1)^2 + o((x + 1)^2)`;
and `1 - 1/6*x^2 + 1/120*x^4 + o(x^4)`, the removable singularity of `sin x / x`. The first
theorem is

`(fun x ↦ 1 / Real.sin x - (x⁻¹ + 1 / 6 * x + 7 / 360 * x ^ 3)) =o[nhdsWithin 0 {0}ᶜ]`
`fun x ↦ x ^ 3`.

The coefficients come from the division of the Taylor series of numerator and denominator,
checked by `laurentCheck` in the kernel together with the two Taylor checks.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [series x 0 3]
Domain: x → 0, x ≠ 0
Input (scalar ℝ): (1 / sin x)
Output (Laurent series with a pole of order 1): 1/x + 1/6*x + 7/360*x^3 + o(x^3)

[CAS.Command.details] More details
  [CAS.Command.computation] Series division
    the denominator vanishes to order 1; numerator coefficients [1,
     0,
     0,
     0,
     0], denominator coefficients [0, 1, 0, -1/6, 0, 1/120]
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laurent expansion with a little-o remainder
        Proposition: (fun x ↦ 1 / Real.sin x - (x⁻¹ + 1 / 6 * x + 7 / 360 * x ^ 3)) =o[nhdsWithin 0
{0}ᶜ] fun x ↦ x ^ 3
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [series x 0 3] (1 / sin x)

/--
info: #cas [series x 0 3]
Domain: x → 0, x ≠ 0
Input (scalar ℝ): (cos x / sin x)
Output (Laurent series with a pole of order 1): 1/x - 1/3*x - 1/45*x^3 + o(x^3)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [series x 0 3] (cos x / sin x)

/--
info: #cas [series x 0 3]
Domain: x → 0, x ≠ 0
Input (scalar ℝ): (1 / (exp x - 1))
Output (Laurent series with a pole of order 1): 1/x - 1/2 + 1/12*x - 1/720*x^3 + o(x^3)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [series x 0 3] (1 / (exp x - 1))

/--
info: #cas [series x 0 2]
Domain: x → 0, x ≠ 0
Input (scalar ℝ): (1 / sin x ^ 2)
Output (Laurent series with a pole of order 2): 1/x^2 + 1/3 + 1/15*x^2 + o(x^2)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [series x 0 2] (1 / sin x ^ 2)

/--
info: #cas [series x 1 2]
Domain: x → 1, x ≠ 1
Input (scalar ℝ): (1 / (x^2 - 1))
Output (Laurent series with a pole of order 1): 1/(2*(x - 1)) - 1/4 + 1/8*(x - 1) - 1/16*(x - 1)^2 +
o((x - 1)^2)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [series x 1 2] (1 / (x^2 - 1))

/--
info: #cas [series x -1 2]
Domain: x → -1, x ≠ -1
Input (scalar ℝ): (1 / (x^2 - 1))
Output (Laurent series with a pole of order 1): -1/(2*(x + 1)) - 1/4 - 1/8*(x + 1) - 1/16*(x + 1)^2
+ o((x + 1)^2)

[CAS.Command.details] More details
-/
#guard_msgs (info, whitespace := lax, substring := true) in
#cas [series x -1 2] (1 / (x^2 - 1))

/--
info: #cas [series x 0 4]
Domain: x → 0, x ≠ 0
Input (scalar ℝ): (sin x / x)
Output (Taylor series of a removable singularity): 1 - 1/6*x^2 + 1/120*x^4 + o(x^4)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [series x 0 4] (sin x / x)


/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Integrals with a square root or a fractional power at `0`

`#cas [nintegrate x in [0, b]] f` with `sqrt x` or `x ^ (p / q : ℝ)` in `f` substitutes `x = u ^ k`
before the Simpson check, so the certified error bound applies although `f` is not smooth at `0`.
The commands run in the build, each inside `#guard_msgs`, which checks its report: the first four
here, `sqrt x * cos x` in `NIntegrateSingularOsc.lean` and `x ^ (2/3) / (1 + x)` in
`NIntegrateSingularRational.lean`.

The outputs are `0.666667 ± 10^-6` (4 panels in `u`), `0.750000 ± 10^-6` (4 panels),
`1.255630 ± 10^-6` (32 panels), `1.885618 ± 10^-6`, `-2.318381 ± 10^-6` (64 panels) and
`0.379348 ± 10^-6` (32 panels). The upper limit `2` is not a square of a rational, so the
fourth integral is split at `(11/8) ^ 2`: the substitution on `[0, 121/64]` and the direct check
on `[121/64, 2]`. The third theorem is
`|(∫ (x : ℝ) in 0..1, √x * Real.exp x) - 1255630 / 10 ^ 6| ≤ 1 / 10 ^ 6`. The six queries take
between 1 s and 38 s. Eight digits of the last integral need 64 panels and about 90 s, too long
for the build, which runs six.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [nintegrate x in [0, 1]]
Domain: x ∈ [0, 1]
Input (scalar ℝ): (sqrt x)
Output (certified value of the integral): 0.666667 ± 10^-6

[CAS.Command.details] More details
  [CAS.Command.computation] Certified quadrature
    substitution x = u^2 on [0, 1], 4 panels on [0, 1] in u
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Substitution x = u ^ 2 and certified Simpson panels
        Proposition: |(∫ (x : ℝ) in 0..1, √x) - 666667 / 10 ^ 6| ≤ 1 / 10 ^ 6
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [nintegrate x in [0, 1]] (sqrt x)

/--
info: #cas [nintegrate x in [0, 1]]
Domain: x ∈ [0, 1]
Input (scalar ℝ): (x ^ (1/3 : ℝ))
Output (certified value of the integral): 0.750000 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nintegrate x in [0, 1]] (x ^ (1/3 : ℝ))

/--
info: #cas [nintegrate x in [0, 1]]
Domain: x ∈ [0, 1]
Input (scalar ℝ): (sqrt x * exp x)
Output (certified value of the integral): 1.255630 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nintegrate x in [0, 1]] (sqrt x * exp x)

/--
info: #cas [nintegrate x in [0, 2]]
Domain: x ∈ [0, 2]
Input (scalar ℝ): (sqrt x)
Output (certified value of the integral): 1.885618 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nintegrate x in [0, 2]] (sqrt x)


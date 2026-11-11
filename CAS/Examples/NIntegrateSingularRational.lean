/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Certified integral of `x ^ (2/3) / (1 + x)` on `[0, 1]`

The last command of `NIntegrateSingular.lean`,
`#cas [nintegrate x in [0, 1]] (x ^ (2/3 : ℝ) / (1 + x))`, run inside `#guard_msgs`, which checks
its report. After the substitution `x = u ^ 3` the Simpson check uses 32 panels and takes about 25
s.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [nintegrate x in [0, 1]]
Domain: x ∈ [0, 1]
Input (scalar ℝ): (x ^ (2/3 : ℝ) / (1 + x))
Output (certified value of the integral): 0.379348 ± 10^-6

[CAS.Command.details] More details
  [CAS.Command.computation] Certified quadrature
    substitution x = u^3 on [0, 1], 32 panels on [0, 1] in u
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Substitution x = u ^ 3 and certified Simpson panels
        Proposition: |(∫ (x : ℝ) in 0..1, x ^ (2 / 3 : ℝ) / (1 + x)) - 379348 / 10 ^ 6| ≤ 1 / 10 ^ 6
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [nintegrate x in [0, 1]] (x ^ (2/3 : ℝ) / (1 + x))


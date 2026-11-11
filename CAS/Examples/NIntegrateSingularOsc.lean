/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Certified integral of `√x cos x` on `[0, 4]`

The fifth command of `NIntegrateSingular.lean`, `#cas [nintegrate x in [0, 4]] (sqrt x * cos x)`,
run inside `#guard_msgs`, which checks its report. After the substitution `x = u ^ 2` the Simpson
check uses 64 panels and takes about 38 s, so it has a module of its own.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [nintegrate x in [0, 4]]
Domain: x ∈ [0, 4]
Input (scalar ℝ): (sqrt x * cos x)
Output (certified value of the integral): -2.318381 ± 10^-6

[CAS.Command.details] More details
  [CAS.Command.computation] Certified quadrature
    substitution x = u^2 on [0, 4], 64 panels on [0, 2] in u
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Substitution x = u ^ 2 and certified Simpson panels
        Proposition: |(∫ (x : ℝ) in 0..4, √x * Real.cos x) + 2318381 / 10 ^ 6| ≤ 1 / 10 ^ 6
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [nintegrate x in [0, 4]] (sqrt x * cos x)


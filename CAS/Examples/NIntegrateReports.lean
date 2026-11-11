/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Reports of `#cas [nintegrate]`

The six commands of `NIntegrate.lean`, each run inside `#guard_msgs`, which checks its report.
Their kernel checks are slow, so the reports have a module of their own.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [nintegrate x in [0, 1]]
Domain: x ∈ [0, 1]
Input (scalar ℝ): (exp (-x^2))
Output (certified value of the integral): 0.746824 ± 10^-6

[CAS.Command.details] More details
  [CAS.Command.computation] Certified quadrature
    Batch Simpson certificate with 16 panels; fourth-derivative bounds by interval evaluation of the
simplified symbolic derivative
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Certified Simpson panels in one kernel check
        Proposition: |(∫ (x : ℝ) in 0..1, Real.exp (-x ^ 2)) - 746824 / 10 ^ 6| ≤ 1 / 10 ^ 6
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [nintegrate x in [0, 1]] (exp (-x^2))

/--
info: #cas [nintegrate x in [0, 1]]
Domain: x ∈ [0, 1]
Input (scalar ℝ): (1 / (1 + x^2))
Output (certified value of the integral): 0.785398 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nintegrate x in [0, 1]] (1 / (1 + x^2))

/--
info: #cas (digits := 8) [nintegrate x in [0, 1]]
Domain: x ∈ [0, 1]
Input (scalar ℝ): (sin x)
Output (certified value of the integral): 0.45969770 ± 10^-8

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (digits := 8) [nintegrate x in [0, 1]] (sin x)

/--
info: #cas (digits := 8) [nintegrate x in [1, 2]]
Domain: x ∈ [1, 2]
Input (scalar ℝ): (log x)
Output (certified value of the integral): 0.38629436 ± 10^-8

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (digits := 8) [nintegrate x in [1, 2]] (log x)

/--
info: #cas (digits := 4) [nintegrate x in [0, 2]]
Domain: x ∈ [0, 2]
Input (scalar ℝ): (x * exp x)
Output (certified value of the integral): 8.3891 ± 10^-4

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (digits := 4) [nintegrate x in [0, 2]] (x * exp x)

/--
info: #cas [nintegrate x in [0, 1]]
Domain: x ∈ [0, 1]
Input (scalar ℝ): (exp x)
Output (certified value of the integral): 1.718282 ± 10^-6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [nintegrate x in [0, 1]] (exp x)


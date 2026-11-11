/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Infinite sums: `#cas [sum k a ∞]`

Each command below runs in the build inside `#guard_msgs`, which checks its report; each report's
theorem is kernel-checked when the command runs. The summands are sums of terms `c kʲ rᵏ` with
`|r| < 1`; the sums come from Mathlib's `hasSum_pow_mul_geometric_of_norm_lt_one`. The same
command sums `c / k ^ (2m)` by the zeta values (`ZetaValues.lean`). The refusals are a divergent
geometric series and the harmonic series `∑ 1 / k`, which is in neither fragment.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

-- Infinite sums
/--
info: #cas [sum k 0 ∞]
Domain: k ∈ ℕ, k ≥ 0
Input (summand): ((1/2)^k)
Output (sum of the series): 2

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of the series
        Proposition: HasSum (fun k ↦ (1 / 2) ^ k) 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [sum k 0 ∞] ((1/2)^k)

/--
info: #cas [sum k 1 ∞]
Domain: k ∈ ℕ, k ≥ 1
Input (summand): (k / 2^k)
Output (sum of the series): 2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 1 ∞] (k / 2^k)

/--
info: #cas [sum k 0 ∞]
Domain: k ∈ ℕ, k ≥ 0
Input (summand): (k^2 * (1/3)^k)
Output (sum of the series): 3/2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 0 ∞] (k^2 * (1/3)^k)

/--
info: #cas [sum k 2 ∞]
Domain: k ∈ ℕ, k ≥ 2
Input (summand): (3 * (2/5)^k - (1/2)^k)
Output (sum of the series): 3/10

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 2 ∞] (3 * (2/5)^k - (1/2)^k)

/--
info: #cas [sum k 0 ∞]
Domain: k ∈ ℕ, k ≥ 0
Input (summand): ((k + 1) * (-1/2)^k)
Output (sum of the series): 4/9

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 0 ∞] ((k + 1) * (-1/2)^k)

set_option linter.style.longLine false in
/--
error: sum: the term with ratio 2 has |2| ≥ 1, so the series diverges (Mathlib's tsum of a non-summable series is 0)
-/
#guard_msgs (error, drop info) in
#cas [sum k 0 ∞] (2^k)

/--
error: sum: infinite sums are computed for sums of terms c k ^ j r ^ k with rational c and r
-/
#guard_msgs (error, drop info) in
#cas [sum k 1 ∞] (1/k)


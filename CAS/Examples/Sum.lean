/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Symbolic sums

`#cas [sum k a n] f` gives the closed form of `∑ k ∈ Finset.Icc a n, f k` for polynomial and
geometric summands and their products, proved for every `n` by induction; a numeric upper bound
gives the value. Each command runs in the build inside `#guard_msgs`, which checks its report.

The outputs are `n*(n + 1)*(2*n + 1)/6`, `n^2*(n + 1)^2/4`, `2*2^n - 1`, `2*(n - 1)*2^n + 2`,
`-(1/2)^n + 2`, `1/2*(-1)^n + 1/2`, `(n - 2)*(n + 4)`, `«n-m»`, `385` and `7381/2520`. The first
theorem is `∀ (n : ℕ), ∑ k ∈ Finset.Icc 1 n, ↑k ^ 2 = ↑n * (↑n + 1) * (2 * ↑n + 1) / 6`; with the
lower bound `3` the statement carries `2 ≤ n`, below which the sum is empty and the closed form is
not `0`. An upper bound named `«n-m»` keeps its escapes, so that it does not read as `n - m`. The
ten commands take 2 s.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [sum k 1 n]
Domain: k ∈ [1, n]
Input (summand): (k^2)
Output (closed form): n*(n + 1)*(2*n + 1)/6

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Closed form for every upper bound
        Proposition: ∀ (n : ℕ), ∑ k ∈ Finset.Icc 1 n, ↑k ^ 2 = ↑n * (↑n + 1) * (2 * ↑n + 1) / 6
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [sum k 1 n] (k^2)

/--
info: #cas [sum k 1 n]
Domain: k ∈ [1, n]
Input (summand): (k^3)
Output (closed form): n^2*(n + 1)^2/4

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 1 n] (k^3)

/--
info: #cas [sum k 0 n]
Domain: k ∈ [0, n]
Input (summand): (2^k)
Output (closed form): 2*2^n - 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 0 n] (2^k)

/--
info: #cas [sum k 1 n]
Domain: k ∈ [1, n]
Input (summand): (k * 2^k)
Output (closed form): 2*(n - 1)*2^n + 2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 1 n] (k * 2^k)

/--
info: #cas [sum k 0 n]
Domain: k ∈ [0, n]
Input (summand): ((1/2)^k)
Output (closed form): -(1/2)^n + 2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 0 n] ((1/2)^k)

/--
info: #cas [sum k 0 n]
Domain: k ∈ [0, n]
Input (summand): ((-1)^k)
Output (closed form): 1/2*(-1)^n + 1/2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 0 n] ((-1)^k)

/--
info: #cas [sum k 3 n]
Domain: k ∈ [3, n]
Input (summand): (2*k + 1)
Output (closed form): (n - 2)*(n + 4)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 3 n] (2*k + 1)

/--
info: #cas [sum k 1 «n-m»]
Domain: k ∈ [1, «n-m»]
Input (summand): 1
Output (closed form): «n-m»

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 1 «n-m»] 1

/--
info: #cas [sum k 1 10]
Domain: k ∈ [1, 10]
Input (summand): (k^2)
Output (exact value): 385

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 1 10] (k^2)

/--
info: #cas [sum k 1 10]
Domain: k ∈ [1, 10]
Input (summand): (1/k)
Output (exact value): 7381/2520

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 1 10] (1/k)


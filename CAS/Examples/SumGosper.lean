/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Telescoping sums and Gosper's algorithm

`#cas [sum k a n] f` for a summand `cᵏ R(k)` with a rational function `R`, or a sum of such terms,
finds the closed form by Gosper's algorithm and proves it for every `n` by induction. Each command
runs in the build inside `#guard_msgs`, which checks its report.

The outputs are `n / (n + 1)`, `n (n + 3) / (4 (n + 1) (n + 2))`, `n (n + 2) / (n + 1) ^ 2`,
`n / (2 n + 1)`, `(n - 1) (3 n + 2) / (4 n (n + 1))` and `2 ^ (n + 1) / (n + 2) - 1`. The first
theorem is `∀ (n : ℕ), ∑ k ∈ Finset.Icc 1 n, 1 / (↑k * (↑k + 1)) = ↑n / (↑n + 1)`; with the lower
bound `2` the statement carries `1 ≤ n`. The six commands take 3 s. The shift between the factors
of `1 / (k (k + 70))` is `69`, and its closed form has degree 70 over `∏ (n + j)` for
`j = 1, …, 70`; the command takes about 30 s, most of it in the kernel. The ratios of
`1 / k ^ 6 - 1 / (k + 1) ^ 6` and `1 / (k ^ 6 + 1) - 1 / ((k + 1) ^ 6 + 1)` have factors of degree
11, whose shifts the command tests one by one, and `k ^ 11 / 2 ^ k` and the like are polynomials
times a geometric term. `#cas [sum k 1 n] (1 / k)` is refused: Gosper's algorithm proves that the
harmonic numbers have no closed form in hypergeometric terms. `1 / (k (k + 1000))`, which needs a
polynomial of degree 999, and a summand with a parameter are refused with what the command would
need. A `maxHeartbeats` below what the search needs stops the search itself.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [sum k 1 n]
Domain: k ∈ [1, n]
Input (hypergeometric summand): (1 / (k * (k + 1)))
Output (closed form (Gosper)): n/(n + 1)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Closed form for every upper bound, from Gosper's algorithm
        Proposition: ∀ (n : ℕ), ∑ k ∈ Finset.Icc 1 n, 1 / (↑k * (↑k + 1)) = ↑n / (↑n + 1)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [sum k 1 n] (1 / (k * (k + 1)))

/--
info: #cas [sum k 1 n]
Domain: k ∈ [1, n]
Input (hypergeometric summand): (1 / (k * (k + 1) * (k + 2)))
Output (closed form (Gosper)): n*(n + 3)/(4*(n + 1)*(n + 2))

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 1 n] (1 / (k * (k + 1) * (k + 2)))

/--
info: #cas [sum k 1 n]
Domain: k ∈ [1, n]
Input (hypergeometric summand): ((2 * k + 1) / (k ^ 2 * (k + 1) ^ 2))
Output (closed form (Gosper)): n*(n + 2)/(n + 1)^2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 1 n] ((2 * k + 1) / (k ^ 2 * (k + 1) ^ 2))

/--
info: #cas [sum k 1 n]
Domain: k ∈ [1, n]
Input (hypergeometric summand): (1 / ((2 * k - 1) * (2 * k + 1)))
Output (closed form (Gosper)): n/(2*n + 1)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 1 n] (1 / ((2 * k - 1) * (2 * k + 1)))

/--
info: #cas [sum k 2 n]
Domain: k ∈ [2, n]
Input (hypergeometric summand): (1 / (k ^ 2 - 1))
Output (closed form (Gosper)): (n - 1)*(3*n + 2)/(4*n*(n + 1))

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 2 n] (1 / (k ^ 2 - 1))

/--
info: #cas [sum k 0 n]
Domain: k ∈ [0, n]
Input (hypergeometric summand): (k * 2 ^ k / ((k + 1) * (k + 2)))
Output (closed form (Gosper)): -1 + 2^n*2/(n + 2)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 0 n] (k * 2 ^ k / ((k + 1) * (k + 2)))

/--
info: #cas [sum k 1 n]
Domain: k ∈ [1, n]
Input (hypergeometric summand): (1 / (k * (k + 5)))
Output (closed form (Gosper)): n*(10538 + 15525*n + 8045*n^2 + 1755*n^3 + 137*n^4)/(300*(n + 1)*(n + 2)*(n + 3)*(n + 4)*(n + 5))

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [sum k 1 n] (1 / (k * (k + 5)))

/--
info: #cas [sum k 1 n]
Domain: k ∈ [1, n]
Input (hypergeometric summand): (1 / (k * (k + 70)))
Output (closed form (Gosper)): n*(171925468487854529724222107311393788430592207030178151794055463544889097151107768638046920087843529030300375973888000000000000000 + 704168782481831416531256561126723976894645070529224977202784407747261430568080030517303344395966215997128014573862912000000000000*n
-/
#guard_msgs (info, substring := true) in
#cas [sum k 1 n] (1 / (k * (k + 70)))

-- The ratios of these summands have factors of degree 11 whose roots are at most 46 apart, so
-- the shifts are tested one by one; their resultant would have degree 121.
/--
info: #cas [sum k 1 n]
Domain: k ∈ [1, n]
Input (hypergeometric summand): (1 / k ^ 6 - 1 / (k + 1) ^ 6)
Output (closed form (Gosper)): n*(n + 2)*(3 + 6*n + 7*n^2 + 4*n^3 + n^4)/(n + 1)^6
-/
#guard_msgs (info, substring := true) in
#cas [sum k 1 n] (1 / k ^ 6 - 1 / (k + 1) ^ 6)

/--
info: #cas [sum k 1 n]
Domain: k ∈ [1, n]
Input (hypergeometric summand): (1 / (k ^ 6 + 1) - 1 / ((k + 1) ^ 6 + 1))
Output (closed form (Gosper)): n*(n + 2)*(3 + 6*n + 7*n^2 + 4*n^3 + n^4)/(2*(2 + 6*n + 15*n^2 + 20*n^3 + 15*n^4 + 6*n^5 + n^6))
-/
#guard_msgs (info, substring := true) in
#cas [sum k 1 n] (1 / (k ^ 6 + 1) - 1 / ((k + 1) ^ 6 + 1))

-- A polynomial divided by a geometric term is a polynomial times a geometric term.
/--
info: #cas [sum k 0 n]
Domain: k ∈ [0, n]
Input (summand): (k ^ 11 / 2 ^ k)
Output (closed form): -1*(3245265146 + 2249446386*n + 779598710*n^2 + 180125550*n^3 + 31213380*n^4 + 4327092*n^5 + 499884*n^6 + 49500*n^7 + 4290*n^8 + 330*n^9 + 22*n^10 + n^11)*(1/2)^n + 3245265146
-/
#guard_msgs (info, substring := true) in
#cas [sum k 0 n] (k ^ 11 / 2 ^ k)

/--
info: #cas [sum k 0 n]
Domain: k ∈ [0, n]
Input (summand): (k ^ 12 / 3 ^ k)
Output (closed form): -1*(282090900 + 309908529*n + 170234658*n^2 + 62340630*n^3 + 17122050*n^4 + 3762099*n^5 + 688842*n^6 + 108108*n^7 + 14850*n^8 + 1815*n^9 + 198*n^10 + 18*n^11 + n^12)/2*(1/3)^n + 141045450
-/
#guard_msgs (info, substring := true) in
#cas [sum k 0 n] (k ^ 12 / 3 ^ k)

/--
info: #cas [sum k 0 n]
Domain: k ∈ [0, n]
Input (summand): ((k + 1) ^ 11 / 2 ^ k)
Output (closed form): -1*(6490530291 + 4498892761*n + 1559197365*n^2 + 360250935*n^3 + 62426430*n^4 + 8653722*n^5 + 999306*n^6 + 98670*n^7 + 8415*n^8 + 605*n^9 + 33*n^10 + n^11)*(1/2)^n + 6490530292
-/
#guard_msgs (info, substring := true) in
#cas [sum k 0 n] ((k + 1) ^ 11 / 2 ^ k)

/-- error: sum: Gosper's algorithm finds no closed form in hypergeometric terms for this summand -/
#guard_msgs in
#cas [sum k 1 n] (1 / k)

-- The roots of the factors of this ratio, of degree 11, are no integer apart: no closed form.
/-- error: sum: Gosper's algorithm finds no closed form in hypergeometric terms for this summand -/
#guard_msgs in
#cas [sum k 1 n] (1 / ((k + 1/13) * (k + 2/13) * (k + 3/13) * (k + 4/13) * (k + 5/13) *
  (k + 6/13) * (k + 7/13) * (k + 8/13) * (k + 9/13) * (k + 10/13) * (k + 11/13)))

-- The roots of these factors are up to `2 · 10 ^ 4` apart, too far to test each shift, and their
-- resultant has degree 121.
/--
error: sum: Gosper's algorithm needs the integer shifts between the factors of this summand's ratio,
which may be up to 17316 apart; the command tests them one by one for at most 10000 shifts and
4194304 coefficient operations, here 9160693, and finds them as the integer roots of a resultant up
to degree 100, here 121
-/
#guard_msgs in
#cas [sum k 1 n] (1 / ((k ^ 11 + 10 ^ 40) * ((k + 1) ^ 11 + 10 ^ 40)))

/--
error: sum: Gosper's algorithm needs a polynomial of degree at least 999 for this summand, whose
ratio has factors 999 apart, and the command searches up to degree 100
-/
#guard_msgs in
#cas [sum k 1 n] (1 / (k * (k + 1000)))

-- The search checks `maxHeartbeats` at each step, the linear system for `x` included. The closed
-- form of `1 / (k (k + 96))` takes about 9,500 heartbeats to find, so a limit of 2,000 stops the
-- search, before the proof.
/-- error: (deterministic) timeout at `sum`, maximum number of heartbeats (2000) has been reached -/
#guard_msgs (error, substring := true) in
set_option maxHeartbeats 2000 in
#cas [sum k 1 n] (1 / (k * (k + 96)))

/--
error: sum: the summand may contain only the summation variable k; sums with parameters, here a,
are not supported
-/
#guard_msgs in
#cas [sum k 1 n] (a / (k * (k + 1)))

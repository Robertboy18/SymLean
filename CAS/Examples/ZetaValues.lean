/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Bernoulli numbers and zeta values: `#cas (BernoulliB n)`, `#cas (zeta s)`, `#cas [sum k a ∞]`

Each command below runs in the build inside `#guard_msgs`, which checks its report; each report's
theorem is kernel-checked when the command runs.

* `#cas (BernoulliB n)` is Mathematica's `BernoulliB[n]` for `n ≤ 60`, as Mathlib's
  `bernoulli n` (`B₁ = -1/2`), read from a table that the kernel evaluates (`decide +kernel`).
* `#cas (zeta s)` is Mathematica's `Zeta[s]` at an even positive integer `s ≤ 60`
  (`riemannZeta s = q π ^ s`, Mathlib's `riemannZeta_two_mul_nat`) and at an integer
  `-59 ≤ s ≤ 0` (`riemannZeta s = q`, `riemannZeta_neg_nat_eq_bernoulli`). It refuses `s = 1`,
  the pole, whose Mathlib value is a convention, and odd `s ≥ 3` ("unsupported formula": no
  rational multiple of `π ^ s` is known for them).
* `#cas [sum k a ∞] (c / k ^ (2m))` for `1 ≤ a ≤ 50` is Mathematica's
  `Sum[c/k^(2m), {k, a, Infinity}]`, stated as a `HasSum` over `k + a`, `k ∈ ℕ`. The same command
  sums the geometric series of `CAS.Command.InfiniteSum`, as the last checks show.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

-- Bernoulli numbers
/--
info: #cas (BernoulliB 0)
Domain: ℚ (Mathlib's bernoulli, B₁ = -1/2)
Input (natural number): 0
Output (Bernoulli number): 1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bernoulli number from the kernel-evaluated numerators
        Proposition: bernoulli 0 = 1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (BernoulliB 0)

/--
info: #cas (BernoulliB 1)
Domain: ℚ (Mathlib's bernoulli, B₁ = -1/2)
Input (natural number): 1
Output (Bernoulli number): -1/2

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bernoulli number from the kernel-evaluated numerators
        Proposition: bernoulli 1 = -(1 / 2)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (BernoulliB 1)

/--
info: #cas (BernoulliB 10)
Domain: ℚ (Mathlib's bernoulli, B₁ = -1/2)
Input (natural number): 10
Output (Bernoulli number): 5/66

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bernoulli number from the kernel-evaluated numerators
        Proposition: bernoulli 10 = 5 / 66
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (BernoulliB 10)

/--
info: #cas (BernoulliB 20)
Domain: ℚ (Mathlib's bernoulli, B₁ = -1/2)
Input (natural number): 20
Output (Bernoulli number): -174611/330

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bernoulli number from the kernel-evaluated numerators
        Proposition: bernoulli 20 = -(174611 / 330)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (BernoulliB 20)

/--
error: BernoulliB computes Bₙ for n ≤ 60
-/
#guard_msgs in
#cas (BernoulliB 61)

/--
error: BernoulliB takes integer arguments; `1/2` is not an integer
-/
#guard_msgs in
#cas (BernoulliB (1/2))

-- Values of the zeta function
/--
info: #cas (zeta 2)
Domain: ℂ (Mathlib's riemannZeta)
Input (even positive integer): s = 2
Output (exact value of ζ): pi^2/6

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] ζ(2k) by Bernoulli numbers (riemannZeta_two_mul_nat)
        Proposition: riemannZeta 2 = ↑Real.pi ^ 2 / 6
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (zeta 2)

/--
info: #cas (zeta 4)
Domain: ℂ (Mathlib's riemannZeta)
Input (even positive integer): s = 4
Output (exact value of ζ): pi^4/90

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] ζ(2k) by Bernoulli numbers (riemannZeta_two_mul_nat)
        Proposition: riemannZeta 4 = ↑Real.pi ^ 4 / 90
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (zeta 4)

/--
info: #cas (zeta 12)
Domain: ℂ (Mathlib's riemannZeta)
Input (even positive integer): s = 12
Output (exact value of ζ): 691*pi^12/638512875

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] ζ(2k) by Bernoulli numbers (riemannZeta_two_mul_nat)
        Proposition: riemannZeta 12 = 691 * ↑Real.pi ^ 12 / 638512875
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (zeta 12)

/--
info: #cas (zeta 0)
Domain: ℂ (Mathlib's riemannZeta)
Input (nonpositive integer): s = 0
Output (exact value of ζ): -1/2

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] ζ(-k) by Bernoulli numbers (riemannZeta_neg_nat_eq_bernoulli)
        Proposition: riemannZeta 0 = -(1 / 2)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (zeta 0)

/--
info: #cas (zeta (-1))
Domain: ℂ (Mathlib's riemannZeta)
Input (nonpositive integer): s = -1
Output (exact value of ζ): -1/12

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] ζ(-k) by Bernoulli numbers (riemannZeta_neg_nat_eq_bernoulli)
        Proposition: riemannZeta (-1) = -(1 / 12)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (zeta (-1))

/--
info: #cas (zeta (-2))
Domain: ℂ (Mathlib's riemannZeta)
Input (nonpositive integer): s = -2
Output (exact value of ζ): 0

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] ζ(-k) by Bernoulli numbers (riemannZeta_neg_nat_eq_bernoulli)
        Proposition: riemannZeta (-2) = 0
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (zeta (-2))

/--
info: #cas (zeta (-7))
Domain: ℂ (Mathlib's riemannZeta)
Input (nonpositive integer): s = -7
Output (exact value of ζ): 1/240

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] ζ(-k) by Bernoulli numbers (riemannZeta_neg_nat_eq_bernoulli)
        Proposition: riemannZeta (-7) = 1 / 240
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (zeta (-7))

set_option linter.style.longLine false in
/--
error: zeta: s = 1 is the pole of ζ; Mathlib's riemannZeta 1 is a convention, not a value of the series, and is not reported
-/
#guard_msgs in
#cas (zeta 1)

set_option linter.style.longLine false in
/--
error: zeta: unsupported formula at the odd integer `3`; exact values are computed at even positive and at nonpositive integers
-/
#guard_msgs in
#cas (zeta 3)

/--
error: zeta: exact values are computed at integers
-/
#guard_msgs in
#cas (zeta (1/2))

/--
error: zeta: exact values are computed for s ≤ 60
-/
#guard_msgs in
#cas (zeta 62)

-- Series of inverse even powers
/--
info: #cas [sum k 1 ∞]
Domain: k ∈ ℕ, k ≥ 1
Input (summand): 1/k^2
Output (sum of the series (ζ value)): pi^2/6

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of the series by hasSum_zeta_nat
        Proposition: HasSum (fun k ↦ 1 / ↑(k + 1) ^ 2) (Real.pi ^ 2 / 6)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [sum k 1 ∞] (1/k^2)

/--
info: #cas [sum k 1 ∞]
Domain: k ∈ ℕ, k ≥ 1
Input (summand): 1/k^4
Output (sum of the series (ζ value)): pi^4/90

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of the series by hasSum_zeta_nat
        Proposition: HasSum (fun k ↦ 1 / ↑(k + 1) ^ 4) (Real.pi ^ 4 / 90)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [sum k 1 ∞] (1/k^4)

/--
info: #cas [sum k 3 ∞]
Domain: k ∈ ℕ, k ≥ 3
Input (summand): 6/k^2
Output (sum of the series (ζ value)): pi^2 - 15/2

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of the series by hasSum_zeta_nat
        Proposition: HasSum (fun k ↦ 6 / ↑(k + 3) ^ 2) (Real.pi ^ 2 - 15 / 2)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [sum k 3 ∞] (6/k^2)

/--
info: #cas [sum k 2 ∞]
Domain: k ∈ ℕ, k ≥ 2
Input (summand): -3/k^2
Output (sum of the series (ζ value)): -pi^2/2 + 3

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of the series by hasSum_zeta_nat
        Proposition: HasSum (fun k ↦ -3 / ↑(k + 2) ^ 2) (-(Real.pi ^ 2 / 2) + 3)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [sum k 2 ∞] (-3/k^2)

/--
info: #cas [sum k 1 ∞]
Domain: k ∈ ℕ, k ≥ 1
Input (summand): 2/k^6
Output (sum of the series (ζ value)): 2*pi^6/945

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of the series by hasSum_zeta_nat
        Proposition: HasSum (fun k ↦ 2 / ↑(k + 1) ^ 6) (2 * Real.pi ^ 6 / 945)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [sum k 1 ∞] (2 * (1/k^6))

/--
error: sum: unsupported formula for the odd exponent 3 (ζ(3))
-/
#guard_msgs in
#cas [sum k 1 ∞] (1/k^3)

/--
error: sum: the summand 1/k^2 is undefined at k = 0; start the sum at 1
-/
#guard_msgs in
#cas [sum k 0 ∞] (1/k^2)

/--
error: sum: infinite sums are computed for sums of terms c k ^ j r ^ k with rational c and r
-/
#guard_msgs in
#cas [sum k 1 ∞] (1/k)

-- Geometric series
/--
info: #cas [sum k 1 ∞]
Domain: k ∈ ℕ, k ≥ 1
Input (summand): ((1/2)^k)
Output (sum of the series): 1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of the series
        Proposition: HasSum (fun k ↦ (1 / 2) ^ (k + 1)) 1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [sum k 1 ∞] ((1/2)^k)

/--
info: #cas [sum k 0 ∞]
Domain: k ∈ ℕ, k ≥ 0
Input (summand): (1 / 2 ^ k)
Output (sum of the series): 2

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Sum of the series
        Proposition: HasSum (fun k ↦ 1 / 2 ^ k) 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [sum k 0 ∞] (1 / 2 ^ k)

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Extrema on an interval: `#cas [minimize x in [a, b]]`, `#cas [maximize x in [a, b]]`

Each command below runs in the build inside `#guard_msgs`, which checks its report; each report's
theorem is kernel-checked when the command runs. The commands are Mathematica's
`Minimize[{p, a <= x <= b}, x]` and `Maximize[{p, a <= x <= b}, x]` for a real polynomial `p` and
rational `a < b`. When the search finds the extremum at a rational point the theorem is exact,
`(∀ x ∈ Set.Icc a b, m ≤ p x) ∧ x₀ ∈ Set.Icc a b ∧ p x₀ = m`; otherwise it is a certified
enclosure `(∀ x ∈ Set.Icc a b, lo ≤ p x) ∧ x₁ ∈ Set.Icc a b ∧ p x₁ ≤ hi` with decimals `lo`, `hi`,
so the minimum lies in `[lo, hi]` (`(digits := d)` sets the decimals, up to 6). The refusals are
reversed endpoints, a non-polynomial function and too many digits.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/-! ### Exact extrema at a rational point: interior critical points and endpoints -/
set_option linter.style.longLine false in
/--
info: #cas [minimize x in [0, 2]]
Domain: x ∈ [0, 2]
Input (polynomial): (x^2 - 2*x)
Output (exact minimum on the interval): min = -1 at x = 1

[CAS.Command.details] More details
  [CAS.Command.computation] Candidates
    Endpoints and real roots of the derivative in the interval (not proof): 3
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bound on the interval attained at the point
        Proposition: (∀ x ∈ Set.Icc 0 2, -1 ≤ x ^ 2 - 2 * x) ∧ 1 ∈ Set.Icc 0 2 ∧ (fun x ↦ x ^ 2 - 2 * x) 1 = -1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [minimize x in [0, 2]] (x^2 - 2*x)

set_option linter.style.longLine false in
/--
info: #cas [maximize x in [0, 2]]
Domain: x ∈ [0, 2]
Input (polynomial): (x^2 - 2*x)
Output (exact maximum on the interval): max = 0 at x = 0

[CAS.Command.details] More details
  [CAS.Command.computation] Candidates
    Endpoints and real roots of the derivative in the interval (not proof): 3
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bound on the interval attained at the point
        Proposition: (∀ x ∈ Set.Icc 0 2, x ^ 2 - 2 * x ≤ 0) ∧ 0 ∈ Set.Icc 0 2 ∧ (fun x ↦ x ^ 2 - 2 * x) 0 = 0
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [maximize x in [0, 2]] (x^2 - 2*x)

set_option linter.style.longLine false in
/--
info: #cas [minimize x in [-1, 2]]
Domain: x ∈ [-1, 2]
Input (polynomial): (x^3 - 3*x)
Output (exact minimum on the interval): min = -2 at x = 1

[CAS.Command.details] More details
  [CAS.Command.computation] Candidates
    Endpoints and real roots of the derivative in the interval (not proof): 4
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bound on the interval attained at the point
        Proposition: (∀ x ∈ Set.Icc (-1) 2, -2 ≤ x ^ 3 - 3 * x) ∧ 1 ∈ Set.Icc (-1) 2 ∧ (fun x ↦ x ^ 3 - 3 * x) 1 = -2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [minimize x in [-1, 2]] (x^3 - 3*x)

set_option linter.style.longLine false in
/--
info: #cas [maximize x in [-3, 3]]
Domain: x ∈ [-3, 3]
Input (polynomial): (x^3 - 3*x)
Output (exact maximum on the interval): max = 18 at x = 3

[CAS.Command.details] More details
  [CAS.Command.computation] Candidates
    Endpoints and real roots of the derivative in the interval (not proof): 4
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bound on the interval attained at the point
        Proposition: (∀ x ∈ Set.Icc (-3) 3, x ^ 3 - 3 * x ≤ 18) ∧ 3 ∈ Set.Icc (-3) 3 ∧ (fun x ↦ x ^ 3 - 3 * x) 3 = 18
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [maximize x in [-3, 3]] (x^3 - 3*x)

/--
info: #cas [minimize x in [1/2, 3/2]]
Domain: x ∈ [1/2, 3/2]
Input (polynomial): (x^5 - 5*x)
Output (exact minimum on the interval): min = -4 at x = 1

[CAS.Command.details] More details
  [CAS.Command.computation] Candidates
    Endpoints and real roots of the derivative in the interval (not proof): 3
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bound on the interval attained at the point
        Proposition: (∀ x ∈ Set.Icc (1 / 2) (3 / 2), -4 ≤ x ^ 5 - 5 * x) ∧
          1 ∈ Set.Icc (1 / 2) (3 / 2) ∧ (fun x ↦ x ^ 5 - 5 * x) 1 = -4
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [minimize x in [1/2, 3/2]] (x^5 - 5*x)

set_option linter.style.longLine false in
/--
info: #cas [maximize x in [-1, 1]]
Domain: x ∈ [-1, 1]
Input (polynomial): (1 - x^2)
Output (exact maximum on the interval): max = 1 at x = 0

[CAS.Command.details] More details
  [CAS.Command.computation] Candidates
    Endpoints and real roots of the derivative in the interval (not proof): 3
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bound on the interval attained at the point
        Proposition: (∀ x ∈ Set.Icc (-1) 1, 1 - x ^ 2 ≤ 1) ∧ 0 ∈ Set.Icc (-1) 1 ∧ (fun x ↦ 1 - x ^ 2) 0 = 1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [maximize x in [-1, 1]] (1 - x^2)

/--
info: #cas [minimize x in [1, 2]]
Domain: x ∈ [1, 2]
Input (polynomial): (x)
Output (exact minimum on the interval): min = 1 at x = 1

[CAS.Command.details] More details
  [CAS.Command.computation] Candidates
    Endpoints and real roots of the derivative in the interval (not proof): 2
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bound on the interval attained at the point
        Proposition: (∀ x ∈ Set.Icc 1 2, 1 ≤ x) ∧ 1 ∈ Set.Icc 1 2 ∧ (fun x ↦ x) 1 = 1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [minimize x in [1, 2]] (x)

/--
info: #cas [minimize x in [0, 1]]
Domain: x ∈ [0, 1]
Input (polynomial): (5)
Output (exact minimum on the interval): min = 5 at x = 0

[CAS.Command.details] More details
  [CAS.Command.computation] Candidates
    Endpoints and real roots of the derivative in the interval (not proof): 2
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bound on the interval attained at the point
        Proposition: (∀ x ∈ Set.Icc 0 1, 5 ≤ 5) ∧ 0 ∈ Set.Icc 0 1 ∧ (fun x ↦ 5) 0 = 5
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [minimize x in [0, 1]] (5)

/-! ### Certified enclosures at irrational critical points -/
set_option linter.style.longLine false in
/--
info: #cas [minimize x in [0, 1]]
Domain: x ∈ [0, 1]
Input (polynomial): (x^4 - x)
Output (certified enclosure of the minimum on the interval): min ∈ [-0.473, -0.472], witness x = 0.62996 with value ≤ -0.472

[CAS.Command.details] More details
  [CAS.Command.computation] Candidates
    Endpoints and real roots of the derivative in the interval (not proof): 3
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bound on the interval and a witness value
        Proposition: (∀ x ∈ Set.Icc 0 1, -473 / 10 ^ 3 ≤ x ^ 4 - x) ∧
          62996 / 10 ^ 5 ∈ Set.Icc 0 1 ∧ (fun x ↦ x ^ 4 - x) (62996 / 10 ^ 5) ≤ -472 / 10 ^ 3
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [minimize x in [0, 1]] (x^4 - x)

set_option linter.style.longLine false in
/--
info: #cas [minimize x in [0, 2]]
Domain: x ∈ [0, 2]
Input (polynomial): (x^3 - 2*x)
Output (certified enclosure of the minimum on the interval): min ∈ [-1.089, -1.088], witness x = 0.8165 with value ≤ -1.088

[CAS.Command.details] More details
  [CAS.Command.computation] Candidates
    Endpoints and real roots of the derivative in the interval (not proof): 3
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bound on the interval and a witness value
        Proposition: (∀ x ∈ Set.Icc 0 2, -1089 / 10 ^ 3 ≤ x ^ 3 - 2 * x) ∧
          8165 / 10 ^ 4 ∈ Set.Icc 0 2 ∧ (fun x ↦ x ^ 3 - 2 * x) (8165 / 10 ^ 4) ≤ -1088 / 10 ^ 3
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [minimize x in [0, 2]] (x^3 - 2*x)

set_option linter.style.longLine false in
/--
info: #cas (digits := 4) [maximize x in [0, 1]]
Domain: x ∈ [0, 1]
Input (polynomial): (x - x^3)
Output (certified enclosure of the maximum on the interval): max ∈ [0.3849, 0.3850], witness x = 0.57735 with value ≥ 0.3849

[CAS.Command.details] More details
  [CAS.Command.computation] Candidates
    Endpoints and real roots of the derivative in the interval (not proof): 3
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bound on the interval and a witness value
        Proposition: (∀ x ∈ Set.Icc 0 1, x - x ^ 3 ≤ 3850 / 10 ^ 4) ∧
          57735 / 10 ^ 5 ∈ Set.Icc 0 1 ∧ 3849 / 10 ^ 4 ≤ (fun x ↦ x - x ^ 3) (57735 / 10 ^ 5)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (digits := 4) [maximize x in [0, 1]] (x - x^3)

set_option linter.style.longLine false in
/--
info: #cas [maximize x in [0, 1]]
Domain: x ∈ [0, 1]
Input (polynomial): (x * (1 - x) * (x + 1))
Output (certified enclosure of the maximum on the interval): max ∈ [0.384, 0.385], witness x = 0.57735 with value ≥ 0.384

[CAS.Command.details] More details
  [CAS.Command.computation] Candidates
    Endpoints and real roots of the derivative in the interval (not proof): 3
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bound on the interval and a witness value
        Proposition: (∀ x ∈ Set.Icc 0 1, x * (1 - x) * (x + 1) ≤ 385 / 10 ^ 3) ∧
          57735 / 10 ^ 5 ∈ Set.Icc 0 1 ∧ 384 / 10 ^ 3 ≤ (fun x ↦ x * (1 - x) * (x + 1)) (57735 / 10 ^ 5)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [maximize x in [0, 1]] (x * (1 - x) * (x + 1))

set_option linter.style.longLine false in
/--
info: #cas [minimize x in [-2, 2]]
Domain: x ∈ [-2, 2]
Input (polynomial): (x^4 - 3*x^2 + x)
Output (certified enclosure of the minimum on the interval): min ∈ [-3.514, -3.513], witness x = -1.30084 with value ≤ -3.513

[CAS.Command.details] More details
  [CAS.Command.computation] Candidates
    Endpoints and real roots of the derivative in the interval (not proof): 5
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Bound on the interval and a witness value
        Proposition: (∀ x ∈ Set.Icc (-2) 2, -3514 / 10 ^ 3 ≤ x ^ 4 - 3 * x ^ 2 + x) ∧
          -130084 / 10 ^ 5 ∈ Set.Icc (-2) 2 ∧ (fun x ↦ x ^ 4 - 3 * x ^ 2 + x) (-130084 / 10 ^ 5) ≤ -3513 / 10 ^ 3
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [minimize x in [-2, 2]] (x^4 - 3*x^2 + x)

/-! ### Refusals -/
/--
error: minimize needs rational endpoints a < b
-/
#guard_msgs in
#cas [minimize x in [1, 0]] (x)

/--
error: minimize needs a polynomial in x with rational coefficients
-/
#guard_msgs in
#cas [minimize x in [0, 1]] (exp x)

/--
error: minimize accepts between 1 and 6 digits
-/
#guard_msgs in
#cas (digits := 7) [minimize x in [0, 1]] (x^4 - x)

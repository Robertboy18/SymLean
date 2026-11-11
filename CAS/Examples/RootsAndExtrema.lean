/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Roots, extrema and Gamma values: `#cas [findRoot]`, `#cas [minimize]`, `#cas (gamma q)`

Each command below runs in the build inside `#guard_msgs`, which checks its report; each report's
theorem is kernel-checked when the command runs. `findRoot` certifies a unique simple root in a
decimal interval from FloatLib-backed interval evaluation (certified numerics); `minimize` and
`maximize` give exact global extrema of polynomials at rational points and certified enclosures
otherwise; the call `gamma q` gives exact values at integers and half-integers. The refusals
show a double root, a triple root, a sign change across a pole, unbounded polynomials and an
argument with no closed form.

The last section has the corresponding goals for bare `cas`.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

-- FindRoot
set_option linter.style.longLine false in
/--
info: #cas [findRoot x in [0, 1]]
Domain: x ∈ [0, 1]
Input (equation in ℝ): (cos x = x)
Output (certified simple root): x = 0.7390851332 ± 10^-10

[CAS.Command.details] More details
  [CAS.Command.computation] Certified root
    Sign change found by interval sampling and bisection (not proof)
    Unique root in [0.7390851331, 0.7390851333], within 10^-10 of 0.7390851332: endpoint signs and a derivative of one sign, checked by the kernel
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Unique root in the interval
        Proposition: ∃! x, x ∈ Set.Icc (7390851331 / 10 ^ 10) (7390851333 / 10 ^ 10) ∧ Real.cos x = x
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [findRoot x in [0, 1]] (cos x = x)

/--
info: #cas [findRoot x in [1, 2]]
Domain: x ∈ [1, 2]
Input (scalar ℝ): (x^2 - 2)
Output (certified simple root): x = 1.4142135624 ± 10^-10

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [findRoot x in [1, 2]] (x^2 - 2)

/--
info: #cas (digits := 20) [findRoot x in [0, 2]]
Domain: x ∈ [0, 2]
Input (scalar ℝ): (exp x - 3)
Output (certified simple root): x = 1.09861228866810969140 ± 10^-20

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (digits := 20) [findRoot x in [0, 2]] (exp x - 3)

/--
info: #cas [findRoot x in [0, 1]]
Domain: x ∈ [0, 1]
Input (scalar ℝ): (x * exp x - 1)
Output (certified simple root): x = 0.5671432904 ± 10^-10

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [findRoot x in [0, 1]] (x * exp x - 1)

/--
info: #cas [findRoot x in [1, 3]]
Domain: x ∈ [1, 3]
Input (scalar ℝ): (log x + x - 2)
Output (certified simple root): x = 1.5571455990 ± 10^-10

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [findRoot x in [1, 3]] (log x + x - 2)

/--
info: #cas [findRoot x in [2, 4]]
Domain: x ∈ [2, 4]
Input (scalar ℝ): (sin x)
Output (certified simple root): x = 3.1415926536 ± 10^-10

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [findRoot x in [2, 4]] (sin x)

set_option linter.style.longLine false in
/--
info: #cas [findRoot x in [0, 10^200]]
Domain: x ∈ [0, 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
Input (scalar ℝ): (x - 1)
Output (certified simple root): x = 1.0000000000 ± 10^-10

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [findRoot x in [0, 10^200]] (x - 1)

set_option linter.style.longLine false in
/--
error: findRoot: no sign change of the expression at 65 equally spaced points of [-1, 1]; a root of even multiplicity, or two roots closer than the sample spacing, has no certificate here
-/
#guard_msgs (error, drop info) in
#cas [findRoot x in [-1, 1]] (x^2)

set_option linter.style.longLine false in
/--
error: findRoot: the sign change could not be narrowed below [-1/34359738368, 7/274877906944] (interval evaluation does not decide the sign near the root); ask for fewer digits
-/
#guard_msgs (error, drop info) in
#cas [findRoot x in [-1, 1]] (x^3)

set_option linter.style.longLine false in
/--
error: findRoot: the derivative cannot be evaluated on [9999999999/10000000000, 10000000001/10000000000], where the sign changes; the expression may have a singularity there rather than a root
-/
#guard_msgs (error, drop info) in
#cas [findRoot x in [0, 2]] (1 / (x - 1))

-- Minimize and Maximize
/--
info: #cas [minimize x]
Domain: x ∈ ℝ
Input (polynomial): (x^2 - 2*x + 4)
Output (exact global minimum): min = 3 at x = 1

[CAS.Command.details] More details
  [CAS.Command.computation] Critical points
    Real roots of the derivative from the root list (not proof): 1
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Global bound attained at the point
        Proposition: (∀ (x : ℝ), 3 ≤ x ^ 2 - 2 * x + 4) ∧ (fun x ↦ x ^ 2 - 2 * x + 4) 1 = 3
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [minimize x] (x^2 - 2*x + 4)

set_option linter.style.longLine false in
/--
info: #cas [minimize x]
Domain: x ∈ ℝ
Input (polynomial): (x^4 - x)
Output (certified enclosure of the global minimum): min ∈ [-0.473, -0.472] near x = 0.62996

[CAS.Command.details] More details
  [CAS.Command.computation] Critical points
    Real roots of the derivative from the root list (not proof): 1
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Global bound and a nearby value
        Proposition: (∀ (x : ℝ), -473 / 10 ^ 3 ≤ x ^ 4 - x) ∧ (fun x ↦ x ^ 4 - x) (62996 / 10 ^ 5) ≤ -472 / 10 ^ 3
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [minimize x] (x^4 - x)

/--
info: #cas [maximize x]
Domain: x ∈ ℝ
Input (polynomial): (3 + 2*x - x^2)
Output (exact global maximum): max = 4 at x = 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [maximize x] (3 + 2*x - x^2)

/--
info: #cas [minimize x]
Domain: x ∈ ℝ
Input (polynomial): (x^4 - x^3)
Output (exact global minimum): min = -27/256 at x = 3/4

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [minimize x] (x^4 - x^3)

/--
info: #cas [minimize x]
Domain: x ∈ ℝ
Input (polynomial): (x^4 - 3*x^2 + x)
Output (certified enclosure of the global minimum): min ∈ [-3.514, -3.513] near x = -1.30084

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [minimize x] (x^4 - 3*x^2 + x)

/--
info: #cas (digits := 4) [maximize x]
Domain: x ∈ ℝ
Input (polynomial): (1 - x^4 + x)
Output (certified enclosure of the global maximum): max ∈ [1.4724, 1.4725] near x = 0.629961

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (digits := 4) [maximize x] (1 - x^4 + x)

/--
info: #cas [minimize x]
Domain: x ∈ ℝ
Input (polynomial): (7)
Output (exact global minimum): min = 7 at x = 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [minimize x] (7)

set_option linter.style.longLine false in
/--
error: minimize: the polynomial is unbounded below (degree 3, leading coefficient 1), so it has no minimum
-/
#guard_msgs (error, drop info) in
#cas [minimize x] (x^3 - x)

set_option linter.style.longLine false in
/--
error: maximize: the polynomial is unbounded above (degree 2, leading coefficient 1), so it has no maximum
-/
#guard_msgs (error, drop info) in
#cas [maximize x] (x^2)

/--
error: minimize needs a polynomial in x with rational coefficients
-/
#guard_msgs (error, drop info) in
#cas [minimize x] (sin x)

-- Gamma
/--
info: #cas (gamma (7/2))
Domain: ℝ
Input (rational number): 7/2
Output (exact value of Γ): 15√π/8

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Gamma by a closed formula
        Proposition: Real.Gamma (7 / 2) = 15 * √Real.pi / 8
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (gamma (7/2))

/--
info: #cas (gamma 5)
Domain: ℝ
Input (rational number): 5
Output (exact value of Γ): 24

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (gamma 5)

/--
info: #cas (gamma (5/2))
Domain: ℝ
Input (rational number): 5/2
Output (exact value of Γ): 3√π/4

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (gamma (5/2))

/--
info: #cas (gamma (1/2))
Domain: ℝ
Input (rational number): 1/2
Output (exact value of Γ): √π

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (gamma (1/2))

/--
info: #cas (gamma (-3/2))
Domain: ℝ
Input (rational number): -3/2
Output (exact value of Γ): 4√π/3

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (gamma (-3/2))

/--
info: #cas (gamma (-3))
Domain: ℝ
Input (rational number): -3
Output (exact value of Γ): 0 (Mathlib's value at the pole -3; Mathematica: ComplexInfinity)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (gamma (-3))

/--
error: gamma: exact values are computed at integers and half-integers; `1/3` is neither
-/
#guard_msgs (error, drop info) in
#cas (gamma (1/3))

/-! ## Bare `cas` -/

namespace CAS.Examples.RootsAndExtrema

/-- The root of `cos x = x` in `[0, 1]` exists, by the `findRoot` certificate. -/
example : ∃ x : ℝ, Real.cos x = x ∧ 0 ≤ x ∧ x ≤ 1 := by cas

example : ∃ x ∈ Set.Icc (0 : ℝ) 1, x * Real.exp x = 1 := by cas

/-- Uniqueness on the whole interval needs a derivative of one sign on it. -/
example : ∃! x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧ Real.cos x = x := by cas

/-- Strict bounds are kept away from the root interval. -/
example : ∃ x : ℝ, Real.sin x = 0 ∧ 3 < x ∧ x < 4 := by cas

/-- A global polynomial bound with a fractional constant: the minimum of `x ^ 4 - x ^ 3`. -/
example : ∀ x : ℝ, (-27 : ℝ) / 256 ≤ x ^ 4 - x ^ 3 := by cas

example : Real.Gamma (7 / 2) = 15 * √Real.pi / 8 := by cas

example : Real.Gamma (-1 / 2) = -2 * √Real.pi := by cas

example : Real.Gamma 5 = 24 := by cas

/-- Mathlib's value at a pole. -/
example : Real.Gamma (-2) = 0 := by cas

example : True := by
  fail_if_success have : ∃ x : ℝ, Real.exp x = 0 ∧ 0 ≤ x ∧ x ≤ 1 := by cas
  fail_if_success have : ∃! x : ℝ, x ∈ Set.Icc (-4 : ℝ) 4 ∧ Real.sin x = 0 := by cas
  fail_if_success have : ∀ x : ℝ, (-26 : ℝ) / 256 ≤ x ^ 4 - x ^ 3 := by cas
  fail_if_success have : Real.Gamma (7 / 2) = 15 * √Real.pi / 4 := by cas
  trivial

end CAS.Examples.RootsAndExtrema

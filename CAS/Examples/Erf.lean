/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# The error function

Each command below runs in the build inside `#guard_msgs`, which checks its report; each report's
theorem is kernel-checked when the command runs.

`CAS.erf x = 2 / √π ∫₀ˣ e^(-t²) dt` (`CAS.Analysis.SpecialFunctions.Erf`; Mathlib v4.35 has no
error function, this is the definition of Mathlib PR #34053). `#cas [N d] (erf q)` proves
`lo ≤ CAS.erf q ∧ CAS.erf q ≤ hi ∧ hi - lo ≤ 1 / 10 ^ d` at a rational `|q| ≤ 10` (denominator at
most 1000, `1 ≤ d ≤ 30`). `#cas [integrate x]` of a Gaussian `c e^(-α x² + β x + γ)` (rational, `α >
0`) proves the derivative of its primitive in `erf` and its integral over every `[a, b]`.
`#cas [derive x]` differentiates sums of `c * erf (A x + B)`. Every other argument of `N`,
integrand and expression reaches the existing handlers, as the last checks show; in a section
with a variable named `erf`, `N` refuses the call.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/-! ### Digits -/
set_option linter.style.longLine false in
/--
info: #cas [N 10]
Domain: error function erf x = 2/√π ∫₀ˣ e^(-t²) dt at a rational point
Input (scalar ℝ): (erf (1/2))
Output (decimal enclosure of width at most 10^-10, with 10 terms of the series): [0.52049987781, 0.52049987782]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of erf 1/2
        Proposition: 0.52049987781 ≤ CAS.erf (1 / 2) ∧
          CAS.erf (1 / 2) ≤ 0.52049987782 ∧ 0.52049987782 - 0.52049987781 ≤ 1 / 10 ^ 10
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.erfCheck_sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 10] (erf (1/2))

set_option linter.style.longLine false in
/--
info: #cas [N 30]
Domain: error function erf x = 2/√π ∫₀ˣ e^(-t²) dt at a rational point
Input (scalar ℝ): (erf 1)
Output (decimal enclosure of width at most 10^-30, with 30 terms of the series): [0.8427007929497148693412206350826, 0.8427007929497148693412206350827]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of erf 1
        Proposition: 0.8427007929497148693412206350826 ≤ CAS.erf 1 ∧
          CAS.erf 1 ≤ 0.8427007929497148693412206350827 ∧
            0.8427007929497148693412206350827 - 0.8427007929497148693412206350826 ≤ 1 / 10 ^ 30
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.erfCheck_sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 30] (erf 1)

set_option linter.style.longLine false in
/--
info: #cas [N 20]
Domain: error function erf x = 2/√π ∫₀ˣ e^(-t²) dt at a rational point
Input (scalar ℝ): (erf (-3))
Output (decimal enclosure of width at most 10^-20, with 57 terms of the series): [-0.999977909503001414559, -0.999977909503001414558]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of erf -3
        Proposition: -0.999977909503001414559 ≤ CAS.erf (-3) ∧
          CAS.erf (-3) ≤ -0.999977909503001414558 ∧ -0.999977909503001414558 + 0.999977909503001414559 ≤ 1 / 10 ^ 20
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.erfCheck_sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 20] (erf (-3))

set_option linter.style.longLine false in
/--
info: #cas [N 10]
Domain: error function erf x = 2/√π ∫₀ˣ e^(-t²) dt at a rational point
Input (scalar ℝ): (erf 10)
Output (decimal enclosure of width at most 10^-10, with 294 terms of the series): [0.99999999999, 1.00000000001]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of erf 10
        Proposition: 0.99999999999 ≤ CAS.erf 10 ∧
          CAS.erf 10 ≤ 1.00000000001 ∧ 1.00000000001 - 0.99999999999 ≤ 1 / 10 ^ 10
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.erfCheck_sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 10] (erf 10)

/--
info: #cas [N 5]
Domain: error function erf x = 2/√π ∫₀ˣ e^(-t²) dt at a rational point
Input (scalar ℝ): (erf 0)
Output (exact value): 0

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of erf 0
        Proposition: 0 ≤ CAS.erf 0 ∧ CAS.erf 0 ≤ 0 ∧ 0 - 0 ≤ 1 / 10 ^ 5
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.erfCheck_sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 5] (erf 0)

/-! ### Refusals: the limits -/
/--
error: erf accepts rational points with |q| ≤ 10 and a denominator of at most 1000
-/
#guard_msgs in
#cas [N 10] (erf 11)

/--
error: erf accepts at most 30 digits
-/
#guard_msgs in
#cas [N 31] (erf 1)

/--
error: erf accepts rational points with |q| ≤ 10 and a denominator of at most 1000
-/
#guard_msgs in
#cas [N 10] (erf (1/1001))

/--
error: erf: a power has an exponent over 64
-/
#guard_msgs in
#cas [N 10] (erf (2 ^ 1000000000))

/-! ### Gaussian integrals -/
set_option linter.style.longLine false in
/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (c e ^ (-α x ^ 2 + β x + γ), α > 0): (exp (-x ^ 2))
Output (scalar ℝ; antiderivative (with the interval integrals)): 1/2*sqrt(pi)*erf(x)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Integral of the input
        Proposition: ∀ (a b : ℝ),
          ∫ (x : ℝ) in a..b, Real.exp (-x ^ 2) = 1 / 2 * √Real.pi * CAS.erf b - 1 / 2 * √Real.pi * CAS.erf a
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.integral_gaussian_eq
      [CAS.explanation.checkedStep] Derivative of the primitive
        Proposition: ∀ (x : ℝ), HasDerivAt (fun x ↦ 1 / 2 * √Real.pi * CAS.erf x) (Real.exp (-x ^ 2)) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.hasDerivAt_gaussianPrimitive
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [integrate x] (exp (-x ^ 2))

set_option linter.style.longLine false in
/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (c e ^ (-α x ^ 2 + β x + γ), α > 0): (2 * exp (-x ^ 2))
Output (scalar ℝ; antiderivative (with the interval integrals)): sqrt(pi)*erf(x)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Integral of the input
        Proposition: ∀ (a b : ℝ), ∫ (x : ℝ) in a..b, 2 * Real.exp (-x ^ 2) = √Real.pi * CAS.erf b - √Real.pi * CAS.erf a
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.integral_gaussian_eq
      [CAS.explanation.checkedStep] Derivative of the primitive
        Proposition: ∀ (x : ℝ), HasDerivAt (fun x ↦ √Real.pi * CAS.erf x) (2 * Real.exp (-x ^ 2)) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.hasDerivAt_gaussianPrimitive
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [integrate x] (2 * exp (-x ^ 2))

set_option linter.style.longLine false in
/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (c e ^ (-α x ^ 2 + β x + γ), α > 0): (exp (-x ^ 2 / 2))
Output (scalar ℝ; antiderivative (with the interval integrals)): 1/2*sqrt(pi)/sqrt(1/2)*erf(sqrt(1/2)*x)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Integral of the input
        Proposition: ∀ (a b : ℝ),
          ∫ (x : ℝ) in a..b, Real.exp (-x ^ 2 / 2) =
            1 / 2 * (√Real.pi / √(1 / 2)) * CAS.erf (√(1 / 2) * b) -
              1 / 2 * (√Real.pi / √(1 / 2)) * CAS.erf (√(1 / 2) * a)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.integral_gaussian_eq
      [CAS.explanation.checkedStep] Derivative of the primitive
        Proposition: ∀ (x : ℝ),
          HasDerivAt (fun x ↦ 1 / 2 * (√Real.pi / √(1 / 2)) * CAS.erf (√(1 / 2) * x)) (Real.exp (-x ^ 2 / 2)) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.hasDerivAt_gaussianPrimitive
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [integrate x] (exp (-x ^ 2 / 2))

set_option linter.style.longLine false in
/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (c e ^ (-α x ^ 2 + β x + γ), α > 0): (exp (-4 * x ^ 2))
Output (scalar ℝ; antiderivative (with the interval integrals)): 1/2*sqrt(pi)/2*erf(2*x)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Integral of the input
        Proposition: ∀ (a b : ℝ),
          ∫ (x : ℝ) in a..b, Real.exp (-4 * x ^ 2) =
            1 / 2 * (√Real.pi / 2) * CAS.erf (2 * b) - 1 / 2 * (√Real.pi / 2) * CAS.erf (2 * a)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.integral_gaussian_eq
      [CAS.explanation.checkedStep] Derivative of the primitive
        Proposition: ∀ (x : ℝ), HasDerivAt (fun x ↦ 1 / 2 * (√Real.pi / 2) * CAS.erf (2 * x)) (Real.exp (-4 * x ^ 2)) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.hasDerivAt_gaussianPrimitive
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [integrate x] (exp (-4 * x ^ 2))

set_option linter.style.longLine false in
/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (c e ^ (-α x ^ 2 + β x + γ), α > 0): (3 * exp (-2 * x ^ 2 + x + 1))
Output (scalar ℝ; antiderivative (with the interval integrals)): 3/2*sqrt(pi)*exp(9/8)/sqrt(2)*erf(sqrt(2)*(x - 1/4))

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Integral of the input
        Proposition: ∀ (a b : ℝ),
          ∫ (x : ℝ) in a..b, 3 * Real.exp (-2 * x ^ 2 + x + 1) =
            3 / 2 * (√Real.pi * Real.exp (9 / 8) / √2) * CAS.erf (√2 * (b - 1 / 4)) -
              3 / 2 * (√Real.pi * Real.exp (9 / 8) / √2) * CAS.erf (√2 * (a - 1 / 4))
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.integral_gaussian_eq
      [CAS.explanation.checkedStep] Derivative of the primitive
        Proposition: ∀ (x : ℝ),
          HasDerivAt (fun x ↦ 3 / 2 * (√Real.pi * Real.exp (9 / 8) / √2) * CAS.erf (√2 * (x - 1 / 4)))
            (3 * Real.exp (-2 * x ^ 2 + x + 1)) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.hasDerivAt_gaussianPrimitive
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [integrate x] (3 * exp (-2 * x ^ 2 + x + 1))

set_option linter.style.longLine false in
/--
info: #cas [integrate]
Domain: t ∈ ℝ
Input (c e ^ (-α x ^ 2 + β x + γ), α > 0): (exp (-(t - 1) ^ 2))
Output (scalar ℝ; antiderivative (with the interval integrals)): 1/2*sqrt(pi)*erf(t - 1)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Integral of the input
        Proposition: ∀ (a b : ℝ),
          ∫ (t : ℝ) in a..b, Real.exp (-(t - 1) ^ 2) =
            1 / 2 * √Real.pi * CAS.erf (b - 1) - 1 / 2 * √Real.pi * CAS.erf (a - 1)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.integral_gaussian_eq
      [CAS.explanation.checkedStep] Derivative of the primitive
        Proposition: ∀ (t : ℝ), HasDerivAt (fun t ↦ 1 / 2 * √Real.pi * CAS.erf (t - 1)) (Real.exp (-(t - 1) ^ 2)) t
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.hasDerivAt_gaussianPrimitive
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [integrate] (exp (-(t - 1) ^ 2))

/-! ### Derivatives -/
/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (sum of c * erf (A x + B)): (erf x)
Output (scalar ℝ; derivative): 2/sqrt(pi)*exp(-x^2)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Derivative of the input
        Proposition: ∀ (x : ℝ), HasDerivAt (fun x ↦ CAS.erf x) (2 / √Real.pi * Real.exp (-x ^ 2)) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.hasDerivAt_erf
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [derive x] (erf x)

set_option linter.style.longLine false in
/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (sum of c * erf (A x + B)): (2 * erf (3 * x + 1) - erf (x / 2))
Output (scalar ℝ; derivative): 12/sqrt(pi)*exp(-(3*x + 1)^2) - exp(-(x/2)^2)/sqrt(pi)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Derivative of the input
        Proposition: ∀ (x : ℝ),
          HasDerivAt (fun x ↦ 2 * CAS.erf (3 * x + 1) - CAS.erf (x / 2))
            (12 / √Real.pi * Real.exp (-(3 * x + 1) ^ 2) - Real.exp (-(x / 2) ^ 2) / √Real.pi) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.hasDerivAt_erf
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [derive x] (2 * erf (3 * x + 1) - erf (x / 2))

/--
info: #cas [derive]
Domain: y ∈ ℝ
Input (sum of c * erf (A x + B)): (erf (1 - y) / 3)
Output (scalar ℝ; derivative): -(2/3/sqrt(pi)*exp(-(1 - y)^2))

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Derivative of the input
        Proposition: ∀ (y : ℝ),
          HasDerivAt (fun y ↦ CAS.erf (1 - y) / 3) (-(2 / 3 / √Real.pi * Real.exp (-(1 - y) ^ 2))) y
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.hasDerivAt_erf
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [derive] (erf (1 - y) / 3)

set_option linter.style.longLine false in
/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (sum of c * erf (A x + B)): (erf (Real.exp 1 * x))
Output (scalar ℝ; derivative): 1*2/sqrt(pi)*exp(-(e*x)^2)*e*1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Derivative of the input
        Proposition: ∀ (x : ℝ),
          HasDerivAt (fun x ↦ CAS.erf (Real.exp 1 * x))
            (1 * (2 / √Real.pi * Real.exp (-(Real.exp 1 * x) ^ 2) * (Real.exp 1 * 1))) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.hasDerivAt_erf
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [derive x] (erf (Real.exp 1 * x))

set_option linter.style.longLine false in
/--
info: #cas [derive]
Domain: x ∈ ℝ
Input (sum of c * erf (A x + B)): (erf (Real.sqrt 2 * x) / 2)
Output (scalar ℝ; derivative): 1/2*2/sqrt(pi)*exp(-(sqrt(2)*x)^2)*sqrt(2)*1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Derivative of the input
        Proposition: ∀ (x : ℝ),
          HasDerivAt (fun x ↦ CAS.erf (√2 * x) / 2) (1 / 2 * (2 / √Real.pi * Real.exp (-(√2 * x) ^ 2) * (√2 * 1))) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.hasDerivAt_erf
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [derive] (erf (Real.sqrt 2 * x) / 2)

/-! ### Other inputs reach the existing handlers -/
/--
info: #cas [N 5]
Domain: closed real expression
Input (scalar ℝ): (pi)
Output (first 5 significant digits, truncated): 3.1415

[CAS.Command.details] More details
  [CAS.Command.computation] Certified numerical evaluation
    Working precision: 56 bits, 29 series terms, 51 logarithm terms
    Guarantee: every printed digit is a digit of the real value, truncated toward zero
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Certified decimal digits
        Proposition: 31415 / 10 ^ 4 ≤ Real.pi ∧ Real.pi < (31415 + 1) / 10 ^ 4
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.DigitsEval.eval_sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 5] (pi)

/-! The reports of the existing integrator and derivative name auxiliary declarations of this
module, so only their outputs are checked. -/
/-- Output (scalar ℝ; antiderivative): -1/2*exp(-x^2) -/
#guard_msgs (info, substring := true) in
#cas [integrate x] (x * exp (-x ^ 2))

/-- Output (scalar ℝ): -2*x*exp(-x^2) -/
#guard_msgs (info, substring := true) in
#cas [derive x] (exp (-x ^ 2))

/-! ### Inside a section with `variable`s the integrand reaches the existing integrators -/
section

variable (exp : ℝ → ℝ)

set_option linter.style.longLine false in
/--
error: the checked integrator found no supported antiderivative in coordinate 'x'. Try an equivalent supported form. For a `HasDerivAt` identity, use `cas` or `cas using h`. To check a known primitive `F` of an ordinary interval-integral identity, use `cas [integrate primitive := F]` or `cas [integrate primitive := F using h]`; the domain conditions must hold throughout the interval `Set.uIcc a b`
-/
#guard_msgs in
#cas [integrate x] (Real.exp (-x ^ 2))

end

/-! ### Inside a section with a local `erf`, `N` refuses the call -/
section

variable (erf : ℝ → ℝ)

set_option linter.style.longLine false in
/--
error: `erf` is a variable of the section, which hides the function `erf` of `#cas`; rename the variable to evaluate the function
-/
#guard_msgs in
#cas [N 5] (erf 1)

end

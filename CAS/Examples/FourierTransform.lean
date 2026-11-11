/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Fourier transforms of Gaussians

Each command below runs in the build inside `#guard_msgs`, which checks its report; each report's
theorem is kernel-checked when the command runs.

`#cas [fourierTransform x ξ] f` takes `f = c e ^ (-α x ^ 2 + β x + γ)` with rational `c ≠ 0`,
`α > 0`, `β`, `γ` and proves `∀ ξ : ℝ, 𝓕 (fun x : ℝ ↦ ((f : ℝ) : ℂ)) ξ = F` in Mathlib's convention
`𝓕 f ξ = ∫ x, e ^ (-2 π i x ξ) f x` (Mathematica's `FourierParameters -> {0, -2 Pi}`), with
`F = c √(π / α) e ^ (β ^ 2 / (4 α) + γ - π ^ 2 ξ ^ 2 / α) e ^ (-i π β ξ / α)`, `√(π / α)` printed
as `√(b π / a)` for `α = a / b` in lowest terms (`√π`, `√(2 π)`, `√(π / 3)`, `√(2 π / 3)` below)
and `c = -1` as a negation. The integrand of the theorem is the input as written. Symbolic
parameters (also `π`), `α ≤ 0`, exponents of degree over 2 and the resource limits of
`#cas [laplace t s]` are refused, as the last checks show.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/-! ### Transforms -/
set_option linter.style.longLine false in
/--
info: #cas [fourierTransform x ξ]
Domain: ξ ∈ ℝ
Input (c e ^ (-α x ^ 2 + β x + γ), α > 0): (exp (-x ^ 2))
Output (Fourier transform 𝓕 f ξ = ∫ e ^ (-2 π i x ξ) f x dx (Mathlib)): sqrt(pi)*exp(-(pi^2*ξ^2))

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Fourier transform
        Proposition: ∀ (ξ : ℝ),
          FourierTransform.fourier (fun x ↦ ↑(Real.exp (-x ^ 2))) ξ = ↑(√Real.pi * Real.exp (-(Real.pi ^ 2 * ξ ^ 2)))
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [fourierTransform x ξ] (exp (-x ^ 2))

set_option linter.style.longLine false in
/--
info: #cas [fourierTransform x ξ]
Domain: ξ ∈ ℝ
Input (c e ^ (-α x ^ 2 + β x + γ), α > 0): (exp (-(x ^ 2) / 2) / 2)
Output (Fourier transform 𝓕 f ξ = ∫ e ^ (-2 π i x ξ) f x dx (Mathlib)): 1/2*sqrt(2*pi)*exp(-(2*pi^2*ξ^2))

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Fourier transform
        Proposition: ∀ (ξ : ℝ),
          FourierTransform.fourier (fun x ↦ ↑(Real.exp (-x ^ 2 / 2) / 2)) ξ =
            ↑(1 / 2 * √(2 * Real.pi) * Real.exp (-(2 * (Real.pi ^ 2 * ξ ^ 2))))
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [fourierTransform x ξ] (exp (-(x ^ 2) / 2) / 2)

set_option linter.style.longLine false in
/--
info: #cas [fourierTransform x ξ]
Domain: ξ ∈ ℝ
Input (c e ^ (-α x ^ 2 + β x + γ), α > 0): (3 * exp (-(x ^ 2) + 2 * x))
Output (Fourier transform 𝓕 f ξ = ∫ e ^ (-2 π i x ξ) f x dx (Mathlib)): 3*sqrt(pi)*exp(1 - pi^2*ξ^2)*exp(-(2*pi*ξ)*i)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Fourier transform
        Proposition: ∀ (ξ : ℝ),
          FourierTransform.fourier (fun x ↦ ↑(3 * Real.exp (-x ^ 2 + 2 * x))) ξ =
            ↑(3 * √Real.pi * Real.exp (1 - Real.pi ^ 2 * ξ ^ 2)) * Complex.exp (-↑(2 * (Real.pi * ξ)) * Complex.I)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [fourierTransform x ξ] (3 * exp (-(x ^ 2) + 2 * x))

set_option linter.style.longLine false in
/--
info: #cas [fourierTransform x ξ]
Domain: ξ ∈ ℝ
Input (c e ^ (-α x ^ 2 + β x + γ), α > 0): (exp (-(x - 1) ^ 2))
Output (Fourier transform 𝓕 f ξ = ∫ e ^ (-2 π i x ξ) f x dx (Mathlib)): sqrt(pi)*exp(-(pi^2*ξ^2))*exp(-(2*pi*ξ)*i)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Fourier transform
        Proposition: ∀ (ξ : ℝ),
          FourierTransform.fourier (fun x ↦ ↑(Real.exp (-(x - 1) ^ 2))) ξ =
            ↑(√Real.pi * Real.exp (-(Real.pi ^ 2 * ξ ^ 2))) * Complex.exp (-↑(2 * (Real.pi * ξ)) * Complex.I)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [fourierTransform x ξ] (exp (-(x - 1) ^ 2))

set_option linter.style.longLine false in
/--
info: #cas [fourierTransform x ξ]
Domain: ξ ∈ ℝ
Input (c e ^ (-α x ^ 2 + β x + γ), α > 0): (exp (-(x ^ 2) / 2 + x / 2))
Output (Fourier transform 𝓕 f ξ = ∫ e ^ (-2 π i x ξ) f x dx (Mathlib)): sqrt(2*pi)*exp(1/8 - 2*pi^2*ξ^2)*exp(-(pi*ξ)*i)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Fourier transform
        Proposition: ∀ (ξ : ℝ),
          FourierTransform.fourier (fun x ↦ ↑(Real.exp (-x ^ 2 / 2 + x / 2))) ξ =
            ↑(√(2 * Real.pi) * Real.exp (1 / 8 - 2 * (Real.pi ^ 2 * ξ ^ 2))) * Complex.exp (-↑(Real.pi * ξ) * Complex.I)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [fourierTransform x ξ] (exp (-(x ^ 2) / 2 + x / 2))

set_option linter.style.longLine false in
/--
info: #cas [fourierTransform x ξ]
Domain: ξ ∈ ℝ
Input (c e ^ (-α x ^ 2 + β x + γ), α > 0): (exp (-(x ^ 2) / 2 - x / 2))
Output (Fourier transform 𝓕 f ξ = ∫ e ^ (-2 π i x ξ) f x dx (Mathlib)): sqrt(2*pi)*exp(1/8 - 2*pi^2*ξ^2)*exp(pi*ξ*i)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Fourier transform
        Proposition: ∀ (ξ : ℝ),
          FourierTransform.fourier (fun x ↦ ↑(Real.exp (-x ^ 2 / 2 - x / 2))) ξ =
            ↑(√(2 * Real.pi) * Real.exp (1 / 8 - 2 * (Real.pi ^ 2 * ξ ^ 2))) * Complex.exp (↑(Real.pi * ξ) * Complex.I)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [fourierTransform x ξ] (exp (-(x ^ 2) / 2 - x / 2))

set_option linter.style.longLine false in
/--
info: #cas [fourierTransform x ξ]
Domain: ξ ∈ ℝ
Input (c e ^ (-α x ^ 2 + β x + γ), α > 0): (-2 * exp (-(3 / 2) * x ^ 2 - x / 3 + 1))
Output (Fourier transform 𝓕 f ξ = ∫ e ^ (-2 π i x ξ) f x dx (Mathlib)): -2*sqrt(2*pi/3)*exp(55/54 - 2/3*pi^2*ξ^2)*exp(2/9*pi*ξ*i)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Fourier transform
        Proposition: ∀ (ξ : ℝ),
          FourierTransform.fourier (fun x ↦ ↑(-2 * Real.exp (-(3 / 2) * x ^ 2 - x / 3 + 1))) ξ =
            ↑(-2 * √(2 * Real.pi / 3) * Real.exp (55 / 54 - 2 / 3 * (Real.pi ^ 2 * ξ ^ 2))) *
              Complex.exp (↑(2 / 9 * (Real.pi * ξ)) * Complex.I)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [fourierTransform x ξ] (-2 * exp (-(3 / 2) * x ^ 2 - x / 3 + 1))

set_option linter.style.longLine false in
/--
info: #cas [fourierTransform x ξ]
Domain: ξ ∈ ℝ
Input (c e ^ (-α x ^ 2 + β x + γ), α > 0): (-exp (-3 * x ^ 2))
Output (Fourier transform 𝓕 f ξ = ∫ e ^ (-2 π i x ξ) f x dx (Mathlib)): -(sqrt(pi/3)*exp(-(1/3*pi^2*ξ^2)))

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Fourier transform
        Proposition: ∀ (ξ : ℝ),
          FourierTransform.fourier (fun x ↦ ↑(-Real.exp (-3 * x ^ 2))) ξ =
            ↑(-(√(Real.pi / 3) * Real.exp (-(1 / 3 * (Real.pi ^ 2 * ξ ^ 2)))))
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [fourierTransform x ξ] (-exp (-3 * x ^ 2))

set_option linter.style.longLine false in
/--
info: #cas [fourierTransform x ξ]
Domain: ξ ∈ ℝ
Input (c e ^ (-α x ^ 2 + β x + γ), α > 0): (-1 * exp (-(5 / 7) * x ^ 2 + 2 * x - 1))
Output (Fourier transform 𝓕 f ξ = ∫ e ^ (-2 π i x ξ) f x dx (Mathlib)): -(sqrt(7*pi/5)*exp(2/5 - 7/5*pi^2*ξ^2))*exp(-(14/5*pi*ξ)*i)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Fourier transform
        Proposition: ∀ (ξ : ℝ),
          FourierTransform.fourier (fun x ↦ ↑(-1 * Real.exp (-(5 / 7) * x ^ 2 + 2 * x - 1))) ξ =
            ↑(-(√(7 * Real.pi / 5) * Real.exp (2 / 5 - 7 / 5 * (Real.pi ^ 2 * ξ ^ 2)))) *
              Complex.exp (-↑(14 / 5 * (Real.pi * ξ)) * Complex.I)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [fourierTransform x ξ] (-1 * exp (-(5 / 7) * x ^ 2 + 2 * x - 1))

/-! ### Refused -/
set_option linter.style.longLine false in
/--
error: fourierTransform: expected c * exp (-α x ^ 2 + β x + γ) with rational c, α, β, γ and α > 0 (parameters are not supported)
-/
#guard_msgs in
#cas [fourierTransform x ξ] (exp (-pi * x ^ 2))

set_option linter.style.longLine false in
/--
error: fourierTransform: expected c * exp (-α x ^ 2 + β x + γ) with rational c, α, β, γ and α > 0 (parameters are not supported)
-/
#guard_msgs in
#cas [fourierTransform x ξ] (exp (x ^ 2))

set_option linter.style.longLine false in
/--
error: fourierTransform: expected c * exp (-α x ^ 2 + β x + γ) with rational c, α, β, γ and α > 0 (parameters are not supported)
-/
#guard_msgs in
#cas [fourierTransform x ξ] (exp (-x))

set_option linter.style.longLine false in
/--
error: fourierTransform: expected c * exp (-α x ^ 2 + β x + γ) with rational c, α, β, γ and α > 0 (parameters are not supported)
-/
#guard_msgs in
#cas [fourierTransform x ξ] (exp (-x ^ 3))

set_option linter.style.longLine false in
/--
error: fourierTransform: expected c * exp (-α x ^ 2 + β x + γ) with rational c, α, β, γ and α > 0 (parameters are not supported)
-/
#guard_msgs in
#cas [fourierTransform x ξ] (exp (x ^ 2 * (x ^ 2 - x - 1)))

set_option linter.style.longLine false in
/--
error: fourierTransform: expected c * exp (-α x ^ 2 + β x + γ) with rational c, α, β, γ and α > 0 (parameters are not supported)
-/
#guard_msgs in
#cas [fourierTransform x ξ] (exp ((x ^ 2 - x / 2 - 1) ^ 2))

set_option linter.style.longLine false in
/--
error: fourierTransform: expected c * exp (-α x ^ 2 + β x + γ) with rational c, α, β, γ and α > 0 (parameters are not supported)
-/
#guard_msgs in
#cas [fourierTransform x ξ] (exp (-x ^ 2) * cos x)

/--
error: fourierTransform: the coefficient c is 0
-/
#guard_msgs in
#cas [fourierTransform x ξ] (0 * exp (-x ^ 2))

/--
error: fourierTransform: tanh is not supported
-/
#guard_msgs in
#cas [fourierTransform x ξ] (tanh x)

/--
error: fourierTransform: a decimal literal has a power of ten over 256
-/
#guard_msgs in
#cas [fourierTransform x ξ] (exp (-x ^ 2 + 1e-300 * x))

/--
error: fourierTransform: the variables x and ξ must be different
-/
#guard_msgs in
#cas [fourierTransform x x] (exp (-x ^ 2))

section

variable (exp : ℝ → ℝ)

/--
error: fourierTransform is not supported in a section with `variable`s
-/
#guard_msgs in
#cas [fourierTransform x ξ] (exp (-x ^ 2))

end

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Inverse Laplace transforms

Each command below runs in the build inside `#guard_msgs`, which checks its report; each report's
theorem is kernel-checked when the command runs.

`#cas [inverseLaplace s t] F` (Mathematica's `InverseLaplaceTransform[F, s, t]`) takes a proper
rational function `F` with rational coefficients, finds `f`, a sum of terms `c tⁿ e^(a t) g (t)`
with `g` one of `1`, `cos`, `sin`, `cosh`, `sinh` and of terms over the roots of factors without
closed form, and proves
`∀ s : ℝ, σ < s → IntegrableOn (fun t ↦ exp (-(s * t)) * f t) (Ioi 0) ∧
∫ t in Ioi 0, exp (-(s * t)) * f t = F s`, with `F` as written: `f` is an inverse transform of `F`
(uniqueness is not part of the theorem; Mathlib has no Lerch theorem). The denominator is factored
over the factors written in the input, or over `ℚ` with `CASHex.Factor`. A factor of degree three
or more goes to the root splitter: its rational roots and the quadratics that remain give exact
terms, and the parts without closed form keep their roots as enclosures that the kernel checks.
`σ` covers every real zero of every written divisor of `F`, cancelled ones included, and the real
parts of the enclosed roots. Improper `F`, parameters, repeated factors whose roots are only
enclosed and inputs in a section with `variable`s are refused, as the last checks show.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/-! ### Real poles -/
set_option linter.style.longLine false in
/--
info: #cas [inverseLaplace s t]
Domain: s > 2
Input (proper rational function of s): (1 / (s - 2))
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)): exp(2*t)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Inverse Laplace transform
        Proposition: ∀ (s : ℝ),
          2 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * Real.exp (2 * t)) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * Real.exp (2 * t) = 1 / (s - 2)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [inverseLaplace s t] (1 / (s - 2))

set_option linter.style.longLine false in
/--
info: #cas [inverseLaplace s t]
Domain: s > 1
Input (proper rational function of s): (1 / ((s - 1) * (s + 2)))
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)): 1/3*exp(t) - 1/3*exp(-2*t)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Inverse Laplace transform
        Proposition: ∀ (s : ℝ),
          1 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (1 / 3 * Real.exp t - 1 / 3 * Real.exp (-2 * t)))
                (Set.Ioi 0) MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (1 / 3 * Real.exp t - 1 / 3 * Real.exp (-2 * t)) =
                1 / ((s - 1) * (s + 2))
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [inverseLaplace s t] (1 / ((s - 1) * (s + 2)))

set_option linter.style.longLine false in
/--
info: #cas [inverseLaplace s t]
Domain: s > 1
Input (proper rational function of s): (1 / (s - 1) ^ 3)
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)): 1/2*t^2*exp(t)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Inverse Laplace transform
        Proposition: ∀ (s : ℝ),
          1 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (1 / 2 * (t ^ 2 * Real.exp t))) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (1 / 2 * (t ^ 2 * Real.exp t)) = 1 / (s - 1) ^ 3
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [inverseLaplace s t] (1 / (s - 1) ^ 3)

set_option linter.style.longLine false in
/--
info: #cas [inverseLaplace s t]
Domain: s > 1
Input (proper rational function of s): (1 / (s ^ 2 - 1))
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)): -(1/2*exp(-t)) + 1/2*exp(t)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Inverse Laplace transform
        Proposition: ∀ (s : ℝ),
          1 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (-(1 / 2 * Real.exp (-t)) + 1 / 2 * Real.exp t))
                (Set.Ioi 0) MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (-(1 / 2 * Real.exp (-t)) + 1 / 2 * Real.exp t) =
                1 / (s ^ 2 - 1)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [inverseLaplace s t] (1 / (s ^ 2 - 1))

set_option linter.style.longLine false in
/--
info: #cas [inverseLaplace s t]
Domain: s > √2
Input (proper rational function of s): (1 / (s ^ 2 - 2))
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)): sinh(sqrt(2)*t)/sqrt(2)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Inverse Laplace transform
        Proposition: ∀ (s : ℝ),
          √2 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (Real.sinh (√2 * t) / √2)) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (Real.sinh (√2 * t) / √2) = 1 / (s ^ 2 - 2)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [inverseLaplace s t] (1 / (s ^ 2 - 2))

/-! ### Complex poles -/
set_option linter.style.longLine false in
/--
info: #cas [inverseLaplace s t]
Domain: s > 0
Input (proper rational function of s): (1 / (s ^ 2 + 4))
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)): 1/2*sin(2*t)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Inverse Laplace transform
        Proposition: ∀ (s : ℝ),
          0 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (1 / 2 * Real.sin (2 * t))) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (1 / 2 * Real.sin (2 * t)) = 1 / (s ^ 2 + 4)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [inverseLaplace s t] (1 / (s ^ 2 + 4))

set_option linter.style.longLine false in
/--
info: #cas [inverseLaplace s t]
Domain: s > 0
Input (proper rational function of s): (s / (s ^ 2 + 4))
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)): cos(2*t)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Inverse Laplace transform
        Proposition: ∀ (s : ℝ),
          0 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * Real.cos (2 * t)) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * Real.cos (2 * t) = s / (s ^ 2 + 4)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [inverseLaplace s t] (s / (s ^ 2 + 4))

set_option linter.style.longLine false in
/--
info: #cas [inverseLaplace s t]
Domain: s > 0
Input (proper rational function of s): (1 / (s ^ 2 + 2))
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)): sin(sqrt(2)*t)/sqrt(2)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Inverse Laplace transform
        Proposition: ∀ (s : ℝ),
          0 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (Real.sin (√2 * t) / √2)) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (Real.sin (√2 * t) / √2) = 1 / (s ^ 2 + 2)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [inverseLaplace s t] (1 / (s ^ 2 + 2))

set_option linter.style.longLine false in
/--
info: #cas [inverseLaplace s t]
Domain: s > -1
Input (proper rational function of s): ((2 * s + 3) / ((s + 1) * (s ^ 2 + 2 * s + 5)))
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)): 1/4*exp(-t) - 1/4*exp(-t)*cos(2*t) + exp(-t)*sin(2*t)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Inverse Laplace transform
        Proposition: ∀ (s : ℝ),
          -1 < s →
            MeasureTheory.IntegrableOn
                (fun t ↦
                  Real.exp (-(s * t)) *
                    (1 / 4 * Real.exp (-t) - 1 / 4 * (Real.exp (-t) * Real.cos (2 * t)) +
                      Real.exp (-t) * Real.sin (2 * t)))
                (Set.Ioi 0) MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0,
                  Real.exp (-(s * t)) *
                    (1 / 4 * Real.exp (-t) - 1 / 4 * (Real.exp (-t) * Real.cos (2 * t)) +
                      Real.exp (-t) * Real.sin (2 * t)) =
                (2 * s + 3) / ((s + 1) * (s ^ 2 + 2 * s + 5))
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [inverseLaplace s t] ((2 * s + 3) / ((s + 1) * (s ^ 2 + 2 * s + 5)))

set_option linter.style.longLine false in
/--
info: #cas [inverseLaplace s t]
Domain: s > 0
Input (proper rational function of s): (1 / (s ^ 2 + 1) ^ 2)
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)): 1/2*sin(t) - 1/2*t*cos(t)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Inverse Laplace transform
        Proposition: ∀ (s : ℝ),
          0 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (1 / 2 * Real.sin t - 1 / 2 * (t * Real.cos t)))
                (Set.Ioi 0) MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (1 / 2 * Real.sin t - 1 / 2 * (t * Real.cos t)) =
                1 / (s ^ 2 + 1) ^ 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [inverseLaplace s t] (1 / (s ^ 2 + 1) ^ 2)

set_option linter.style.longLine false in
/--
info: #cas [inverseLaplace s t]
Domain: s > 0
Input (proper rational function of s): (1 / (s * (s ^ 2 + 1)))
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)): 1 - cos(t)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Inverse Laplace transform
        Proposition: ∀ (s : ℝ),
          0 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (1 - Real.cos t)) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (1 - Real.cos t) = 1 / (s * (s ^ 2 + 1))
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [inverseLaplace s t] (1 / (s * (s ^ 2 + 1)))

set_option linter.style.longLine false in
/--
info: #cas [inverseLaplace s t]
Domain: s > -1
Input (proper rational function of s): ((s + 3) / (s ^ 2 + 5 + 2 * s))
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)): exp(-t)*cos(2*t) + exp(-t)*sin(2*t)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Inverse Laplace transform
        Proposition: ∀ (s : ℝ),
          -1 < s →
            MeasureTheory.IntegrableOn
                (fun t ↦ Real.exp (-(s * t)) * (Real.exp (-t) * Real.cos (2 * t) + Real.exp (-t) * Real.sin (2 * t)))
                (Set.Ioi 0) MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0,
                  Real.exp (-(s * t)) * (Real.exp (-t) * Real.cos (2 * t) + Real.exp (-t) * Real.sin (2 * t)) =
                (s + 3) / (s ^ 2 + 5 + 2 * s)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [inverseLaplace s t] ((s + 3) / (s ^ 2 + 5 + 2 * s))

/-! ### Decimal coefficients -/
set_option linter.style.longLine false in
/--
info: #cas [inverseLaplace s t]
Domain: s > 1/4
Input (proper rational function of s): (0.5 / (s - 0.25))
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)): 1/2*exp(1/4*t)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Inverse Laplace transform
        Proposition: ∀ (s : ℝ),
          1 / 4 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (1 / 2 * Real.exp (1 / 4 * t))) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (1 / 2 * Real.exp (1 / 4 * t)) = 0.5 / (s - 0.25)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [inverseLaplace s t] (0.5 / (s - 0.25))

/-! ### A cancelled factor: σ covers the written divisors -/
set_option linter.style.longLine false in
/--
info: #cas [inverseLaplace s t]
Domain: s > 2
Input (proper rational function of s): ((s - 2) / ((s - 2) * (s + 1)))
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)): exp(-t)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Inverse Laplace transform
        Proposition: ∀ (s : ℝ),
          2 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * Real.exp (-t)) (Set.Ioi 0) MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * Real.exp (-t) = (s - 2) / ((s - 2) * (s + 1))
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [inverseLaplace s t] ((s - 2) / ((s - 2) * (s + 1)))

/-! ### Irrational real roots with one centre: σ is the largest bound -/
/--
info: #cas [inverseLaplace s t]
Domain: s > √3
Input (proper rational function of s): (1 / ((s ^ 2 - 2) * (s ^ 2 - 3)))
-/
#guard_msgs (info, substring := true) in
#cas [inverseLaplace s t] (1 / ((s ^ 2 - 2) * (s ^ 2 - 3)))

/-! ### Factors of degree three or more -/

-- The root splitter finds the rational root `-1` of `s ^ 3 + 1` and solves the quadratic
-- `s ^ 2 - s + 1` that remains, so every term is exact.
/--
info: #cas [inverseLaplace s t]
Domain: s > 1/2
Input (proper rational function of s): (1 / (s ^ 3 + 1))
-/
#guard_msgs (info, substring := true) in
#cas [inverseLaplace s t] (1 / (s ^ 3 + 1))

-- `s ^ 3 - 2` has no rational root, so its roots are known by enclosures that the kernel checks:
-- the real root and a pair of complex roots. `σ` is the upper end of the enclosure of the real
-- root.
/--
info: #cas [inverseLaplace s t]
Domain: s > 1.25992106
Input (proper rational function of s): (1 / (s ^ 3 - 2))
-/
#guard_msgs (info, substring := true) in
#cas [inverseLaplace s t] (1 / (s ^ 3 - 2))

-- An exact term for `s + 1` beside the terms over the enclosed roots of `s ^ 3 - 2`.
/--
info: #cas [inverseLaplace s t]
Domain: s > 1.25992106
Input (proper rational function of s): (1 / ((s ^ 3 - 2) * (s + 1)))
-/
#guard_msgs (info, substring := true) in
#cas [inverseLaplace s t] (1 / ((s ^ 3 - 2) * (s + 1)))

-- Without `CASHex.Factor` the quartic `s ^ 4 + 4` stays whole, with two pairs of enclosed complex
-- roots; with it, Hex splits the quartic into two quadratics (see `CASHex/Examples.lean`).
/--
Input (proper rational function of s): (1 / (s ^ 4 + 4))
-/
#guard_msgs (info, substring := true) in
#cas [inverseLaplace s t] (1 / (s ^ 4 + 4))

/-! ### Refusals -/
set_option linter.style.longLine false in
/--
error: inverseLaplace: the factor s^3 - 2 is repeated and its roots are known only by enclosures, which is not supported
-/
#guard_msgs in
#cas [inverseLaplace s t] (1 / (s ^ 3 - 2) ^ 2)

set_option linter.style.longLine false in
/--
error: inverseLaplace: F is not proper; its polynomial part (Dirac deltas and their derivatives) is not supported
-/
#guard_msgs in
#cas [inverseLaplace s t] (s ^ 2 / (s + 1))

set_option linter.style.longLine false in
/--
error: inverseLaplace: expected a proper rational function of s with rational coefficients (parameters are not supported)
-/
#guard_msgs in
#cas [inverseLaplace s t] (1 / (s - a))

/--
error: inverseLaplace: the variables s and t must be different
-/
#guard_msgs in
#cas [inverseLaplace s s] (1 / s)

/--
error: inverseLaplace: a divisor is itself a quotient; write F with polynomial divisors
-/
#guard_msgs in
#cas [inverseLaplace s t] (1 / ((s ^ 2 - 1) / (s - 1)))

/--
error: inverseLaplace: a power has an exponent over 64
-/
#guard_msgs in
#cas [inverseLaplace s t] (1 / (1 + s) ^ 1000000)

set_option linter.style.longLine false in
/--
error: inverseLaplace: the input has degree over 32 before simplification (in a numerator or a denominator of a subexpression)
-/
#guard_msgs in
#cas [inverseLaplace s t] ((1 / (s + 1) + 1 / (s + 2)) ^ 32)

/--
error: inverseLaplace: the constants of the input may need more than 4096 bits
-/
#guard_msgs in
#cas [inverseLaplace s t] ((1 / 2 ^ 31 + 1 / 3 ^ 31) ^ 64 / (s - 1))

/--
error: inverseLaplace: a coefficient has more than 1024 bits
-/
#guard_msgs in
#cas [inverseLaplace s t] ((s ^ 32 + 1) / (s + 4294967296 ^ 64))

/-! ### Inside a section with `variable`s -/
section

variable (exp : ℝ → ℝ)

/--
error: inverseLaplace is not supported in a section with `variable`s
-/
#guard_msgs in
#cas [inverseLaplace s t] (1 / (s + 3))

end

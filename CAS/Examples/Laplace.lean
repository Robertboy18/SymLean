/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Laplace transforms

Each command below runs in the build inside `#guard_msgs`, which checks its report; each report's
theorem is kernel-checked when the command runs.

`#cas [laplace t s] f` (Mathematica's `LaplaceTransform[f, t, s]`) takes a sum of terms
`c tⁿ e ^ (a t) g (b t)` with `g` one of `1`, `cos`, `sin`, `cosh`, `sinh` and rational `a`, `b`,
`c` and proves `∀ s : ℝ, σ < s → IntegrableOn (fun t ↦ exp (-(s t)) f t) (Ioi 0) ∧
∫ t in Ioi 0, exp (-(s t)) f t = F` with `σ` the largest bound of a term with a nonzero
coefficient (`a`, and `a + |b|` for `cosh`, `sinh`) and `F` a sum of rational functions of `s`, one
per term. The integrand of the theorem is the input as written. Symbolic parameters, `tanh`,
powers `tⁿ` with `n > 8`, more than 8 terms, inputs of more than 600 syntax nodes (the arguments
of `sinh`, `cosh`, `tan` counted twice), literals of more than 320 characters, constants of more
than 1024 bits, constant powers and decimal literals with an exponent over 256 and inputs in a
section with `variable`s are refused, as the last checks show.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/-! ### Transforms -/
set_option linter.style.longLine false in
/--
info: #cas [laplace t s]
Domain: s > 0
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): 1
Output (Laplace transform): 1/s

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (s : ℝ),
          0 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * 1) (Set.Ioi 0) MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * 1 = 1 / s
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace t s] 1

set_option linter.style.longLine false in
/--
info: #cas [laplace t s]
Domain: s > 2
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): (3 * t ^ 2 * exp (2 * t) + cos (5 * t))
Output (Laplace transform): 6/(s - 2)^3 + s/(s^2 + 25)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (s : ℝ),
          2 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (3 * t ^ 2 * Real.exp (2 * t) + Real.cos (5 * t)))
                (Set.Ioi 0) MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (3 * t ^ 2 * Real.exp (2 * t) + Real.cos (5 * t)) =
                6 / (s - 2) ^ 3 + s / (s ^ 2 + 25)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace t s] (3 * t ^ 2 * exp (2 * t) + cos (5 * t))

set_option linter.style.longLine false in
/--
info: #cas [laplace t s]
Domain: s > 0
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): (t * sin (2 * t))
Output (Laplace transform): 4*s/(s^2 + 4)^2

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (s : ℝ),
          0 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (t * Real.sin (2 * t))) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (t * Real.sin (2 * t)) = 4 * s / (s ^ 2 + 4) ^ 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace t s] (t * sin (2 * t))

set_option linter.style.longLine false in
/--
info: #cas [laplace t s]
Domain: s > 0
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): (exp (-t) - 2 * t ^ 3)
Output (Laplace transform): 1/(s + 1) - 12/s^4

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (s : ℝ),
          0 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (Real.exp (-t) - 2 * t ^ 3)) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (Real.exp (-t) - 2 * t ^ 3) = 1 / (s + 1) - 12 / s ^ 4
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace t s] (exp (-t) - 2 * t ^ 3)

set_option linter.style.longLine false in
/--
info: #cas [laplace t s]
Domain: s > 1/2
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): (t ^ 2 * exp (t / 2) * cos (3 * t))
Output (Laplace transform): (2*(s - 1/2)^3 - 54*(s - 1/2))/((s - 1/2)^2 + 9)^3

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (s : ℝ),
          1 / 2 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (t ^ 2 * Real.exp (t / 2) * Real.cos (3 * t)))
                (Set.Ioi 0) MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (t ^ 2 * Real.exp (t / 2) * Real.cos (3 * t)) =
                (2 * (s - 1 / 2) ^ 3 - 54 * (s - 1 / 2)) / ((s - 1 / 2) ^ 2 + 9) ^ 3
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace t s] (t ^ 2 * exp (t / 2) * cos (3 * t))

set_option linter.style.longLine false in
/--
info: #cas [laplace t s]
Domain: s > 0
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): (2 * t * exp (-3 * t) * sin t - 5)
Output (Laplace transform): 4*(s + 3)/((s + 3)^2 + 1)^2 - 5/s

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (s : ℝ),
          0 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (2 * t * Real.exp (-3 * t) * Real.sin t - 5))
                (Set.Ioi 0) MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (2 * t * Real.exp (-3 * t) * Real.sin t - 5) =
                4 * (s + 3) / ((s + 3) ^ 2 + 1) ^ 2 - 5 / s
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace t s] (2 * t * exp (-3 * t) * sin t - 5)

set_option linter.style.longLine false in
/--
info: #cas [laplace t s]
Domain: s > 2
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): (exp (2 * t) * cos (3 * t) - exp (2 * t) * sin (3 * t) / 3)
Output (Laplace transform): (s - 2)/((s - 2)^2 + 9) - 1/((s - 2)^2 + 9)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (s : ℝ),
          2 < s →
            MeasureTheory.IntegrableOn
                (fun t ↦
                  Real.exp (-(s * t)) * (Real.exp (2 * t) * Real.cos (3 * t) - Real.exp (2 * t) * Real.sin (3 * t) / 3))
                (Set.Ioi 0) MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0,
                  Real.exp (-(s * t)) *
                    (Real.exp (2 * t) * Real.cos (3 * t) - Real.exp (2 * t) * Real.sin (3 * t) / 3) =
                (s - 2) / ((s - 2) ^ 2 + 9) - 1 / ((s - 2) ^ 2 + 9)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace t s] (exp (2 * t) * cos (3 * t) - exp (2 * t) * sin (3 * t) / 3)

set_option linter.style.longLine false in
/--
info: #cas [laplace t s]
Domain: s > 0
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): (t ^ 3 * cos (2 * t))
Output (Laplace transform): (6*s^4 - 144*s^2 + 96)/(s^2 + 4)^4

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (s : ℝ),
          0 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (t ^ 3 * Real.cos (2 * t))) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (t ^ 3 * Real.cos (2 * t)) =
                (6 * s ^ 4 - 144 * s ^ 2 + 96) / (s ^ 2 + 4) ^ 4
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace t s] (t ^ 3 * cos (2 * t))

set_option linter.style.longLine false in
/--
info: #cas [laplace t s]
Domain: s > -3/2
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): (exp (-(3 / 2) * t) * sin (-2 * t))
Output (Laplace transform): -(2/((s + 3/2)^2 + 4))

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (s : ℝ),
          -(3 / 2) < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (Real.exp (-(3 / 2) * t) * Real.sin (-2 * t)))
                (Set.Ioi 0) MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (Real.exp (-(3 / 2) * t) * Real.sin (-2 * t)) =
                -(2 / ((s + 3 / 2) ^ 2 + 4))
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace t s] (exp (-(3 / 2) * t) * sin (-2 * t))

set_option linter.style.longLine false in
/--
info: #cas [laplace x p]
Domain: p > -1
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): (x ^ 8 * exp (-x))
Output (Laplace transform): 40320/(p + 1)^9

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (p : ℝ),
          -1 < p →
            MeasureTheory.IntegrableOn (fun x ↦ Real.exp (-(p * x)) * (x ^ 8 * Real.exp (-x))) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (x : ℝ) in Set.Ioi 0, Real.exp (-(p * x)) * (x ^ 8 * Real.exp (-x)) = 40320 / (p + 1) ^ 9
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace x p] (x ^ 8 * exp (-x))

/-! ### Hyperbolic functions: `σ = a + |b|` -/
/--
info: #cas [laplace t s]
Domain: s > 3
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): (cosh (3 * t))
Output (Laplace transform): s/(s^2 - 9)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (s : ℝ),
          3 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * Real.cosh (3 * t)) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * Real.cosh (3 * t) = s / (s ^ 2 - 9)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace t s] (cosh (3 * t))

set_option linter.style.longLine false in
/--
info: #cas [laplace t s]
Domain: s > 3
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): (exp (2 * t) * sinh t)
Output (Laplace transform): 1/((s - 2)^2 - 1)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (s : ℝ),
          3 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (Real.exp (2 * t) * Real.sinh t)) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (Real.exp (2 * t) * Real.sinh t) = 1 / ((s - 2) ^ 2 - 1)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace t s] (exp (2 * t) * sinh t)

set_option linter.style.longLine false in
/--
info: #cas [laplace t s]
Domain: s > 2
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): (t * sinh (-2 * t))
Output (Laplace transform): -(4*s/(s^2 - 4)^2)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (s : ℝ),
          2 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (t * Real.sinh (-2 * t))) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (t * Real.sinh (-2 * t)) = -(4 * s / (s ^ 2 - 4) ^ 2)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace t s] (t * sinh (-2 * t))

set_option linter.style.longLine false in
/--
info: #cas [laplace t s]
Domain: s > 1
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): (t ^ 2 * exp (-t) * cosh (t / 2) - 3 * sinh t)
Output (Laplace transform): (2*(s + 1)^3 + 3/2*(s + 1))/((s + 1)^2 - 1/4)^3 - 3/(s^2 - 1)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (s : ℝ),
          1 < s →
            MeasureTheory.IntegrableOn
                (fun t ↦ Real.exp (-(s * t)) * (t ^ 2 * Real.exp (-t) * Real.cosh (t / 2) - 3 * Real.sinh t))
                (Set.Ioi 0) MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0,
                  Real.exp (-(s * t)) * (t ^ 2 * Real.exp (-t) * Real.cosh (t / 2) - 3 * Real.sinh t) =
                (2 * (s + 1) ^ 3 + 3 / 2 * (s + 1)) / ((s + 1) ^ 2 - 1 / 4) ^ 3 - 3 / (s ^ 2 - 1)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace t s] (t ^ 2 * exp (-t) * cosh (t / 2) - 3 * sinh t)

/-! ### `sinh` written with exponentials, as the reader writes it -/
set_option linter.style.longLine false in
/--
info: #cas [laplace t s]
Domain: s > 3
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): ((exp (3 * t) - exp (-(3 * t))) / 2)
Output (Laplace transform): 3/(s^2 - 9)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (s : ℝ),
          3 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * ((Real.exp (3 * t) - Real.exp (-(3 * t))) / 2))
                (Set.Ioi 0) MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * ((Real.exp (3 * t) - Real.exp (-(3 * t))) / 2) =
                3 / (s ^ 2 - 9)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace t s] ((exp (3 * t) - exp (-(3 * t))) / 2)

/-! ### A term with coefficient `0` imposes no condition on `s` -/
set_option linter.style.longLine false in
/--
info: #cas [laplace t s]
Domain: s > 0
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): (0 * exp (5 * t) + cos t)
Output (Laplace transform): s/(s^2 + 1)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (s : ℝ),
          0 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (0 * Real.exp (5 * t) + Real.cos t)) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (0 * Real.exp (5 * t) + Real.cos t) = s / (s ^ 2 + 1)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace t s] (0 * exp (5 * t) + cos t)

/-! ### Rates that are `0` after arithmetic -/
/--
info: #cas [laplace t s]
Domain: s > 0
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): (exp (t * 0))
Output (Laplace transform): 1/s

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (s : ℝ),
          0 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * Real.exp (t * 0)) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * Real.exp (t * 0) = 1 / s
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace t s] (exp (t * 0))

set_option linter.style.longLine false in
/--
info: #cas [laplace t s]
Domain: s > 0
Input (terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh): (exp ((1 - 1) * t) * cos t)
Output (Laplace transform): s/(s^2 + 1)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Laplace transform
        Proposition: ∀ (s : ℝ),
          0 < s →
            MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (Real.exp ((1 - 1) * t) * Real.cos t)) (Set.Ioi 0)
                MeasureTheory.volume ∧
              ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(s * t)) * (Real.exp ((1 - 1) * t) * Real.cos t) = s / (s ^ 2 + 1)
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [laplace t s] (exp ((1 - 1) * t) * cos t)

/-! ### Refusals -/
set_option linter.style.longLine false in
/--
error: laplace: expected a sum of terms c tⁿ e ^ (a t) g (b t) with g one of cos, sin, cosh, sinh, or c tⁿ e ^ (a t), with rational a, b, c and b ≠ 0 (parameters are not supported)
-/
#guard_msgs in
#cas [laplace t s] (cosh (t * 0))

set_option linter.style.longLine false in
/--
error: laplace: expected a sum of terms c tⁿ e ^ (a t) g (b t) with g one of cos, sin, cosh, sinh, or c tⁿ e ^ (a t), with rational a, b, c and b ≠ 0 (parameters are not supported)
-/
#guard_msgs in
#cas [laplace t s] (cosh t * cos t)

/--
error: laplace: tanh is not supported
-/
#guard_msgs in
#cas [laplace t s] (tanh t)

set_option linter.style.longLine false in
/--
error: laplace: expected a sum of terms c tⁿ e ^ (a t) g (b t) with g one of cos, sin, cosh, sinh, or c tⁿ e ^ (a t), with rational a, b, c and b ≠ 0 (parameters are not supported)
-/
#guard_msgs in
#cas [laplace t s] (exp (t ^ 2))

set_option linter.style.longLine false in
/--
error: laplace: expected a sum of terms c tⁿ e ^ (a t) g (b t) with g one of cos, sin, cosh, sinh, or c tⁿ e ^ (a t), with rational a, b, c and b ≠ 0 (parameters are not supported)
-/
#guard_msgs in
#cas [laplace t s] (exp (a * t))

/--
error: laplace accepts powers t ^ n with n ≤ 8
-/
#guard_msgs in
#cas [laplace t s] (t ^ 9)

/--
error: laplace: the variables t and s must be different
-/
#guard_msgs in
#cas [laplace t t] (exp t)

/--
error: laplace accepts at most 8 terms
-/
#guard_msgs in
#cas [laplace t s] (1 + t + t ^ 2 + t ^ 3 + t ^ 4 + t ^ 5 + t ^ 6 + t ^ 7 + t ^ 8)

set_option linter.style.longLine false in
/--
error: laplace: expected a sum of terms c tⁿ e ^ (a t) g (b t) with g one of cos, sin, cosh, sinh, or c tⁿ e ^ (a t), with rational a, b, c and b ≠ 0 (parameters are not supported)
-/
#guard_msgs in
#cas [laplace t s] (2 ^ 100000 * t)

set_option linter.style.longLine false in
/--
error: laplace: expected a sum of terms c tⁿ e ^ (a t) g (b t) with g one of cos, sin, cosh, sinh, or c tⁿ e ^ (a t), with rational a, b, c and b ≠ 0 (parameters are not supported)
-/
#guard_msgs in
#cas [laplace t s] (2 ^ 257 * t)

/--
error: laplace: a decimal literal has a power of ten over 256
-/
#guard_msgs in
#cas [laplace t s] (1e-300 * t)

set_option linter.style.longLine false in
/--
error: laplace: expected a sum of terms c tⁿ e ^ (a t) g (b t) with g one of cos, sin, cosh, sinh, or c tⁿ e ^ (a t), with rational a, b, c and b ≠ 0 (parameters are not supported)
-/
#guard_msgs in
#cas [laplace t s] (2 ^ 256 * 2 ^ 256 * 2 ^ 256 * 2 ^ 256 * t)

set_option linter.style.longLine false in
/--
error: laplace: a literal has more than 320 characters
-/
#guard_msgs in
#cas [laplace t s] (100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 * t)

set_option linter.style.longLine false in
/--
error: laplace: the input is too large (more than 600 syntax nodes, the arguments of sinh, cosh and tan counted twice)
-/
#guard_msgs in
#cas [laplace t s] (sinh (sinh (sinh (sinh (sinh (sinh (sinh (sinh (sinh (sinh t))))))))))

set_option linter.style.longLine false in
/--
error: laplace: the input is too large (more than 600 syntax nodes, the arguments of sinh, cosh and tan counted twice)
-/
#guard_msgs in
#cas [laplace t s] (tan (tan (tan (tan (tan (tan (tan (tan (tan (tan t))))))))))

section

variable (exp : ℝ → ℝ)

/--
error: laplace is not supported in a section with `variable`s
-/
#guard_msgs in
#cas [laplace t s] (exp t)

end

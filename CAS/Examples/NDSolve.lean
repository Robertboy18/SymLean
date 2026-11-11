/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Certified numerical solutions of differential equations

Each command below runs in the build inside `#guard_msgs`, which checks its report; each report's
theorem is kernel-checked when the command runs.

`#cas (digits := d) [ndsolve y t in [t₀, T], y t₀ = y₀ (, at [τ, …])] (y' = f)` (Mathematica's
`NDSolve`) takes a polynomial `f` in `t` and `y` with rational coefficients and proves that a
solution of `y' = f (t, y)`, `y t₀ = y₀` exists on `[t₀, T]` (`IsIntegralCurveOn` on `Icc t₀ T`),
that it is unique there (`Set.EqOn`), and that every solution lies in the printed interval at each
output time (by default `T`), an interval of width at most `10 ^ (-d)` (default `d = 6`). The
kernel checks the pieces of a piecewise Taylor approximation (`CAS.Calculus.NDSolve.check_sound`):
residual bounds, one-sided Lipschitz bounds of `f` in tubes around the pieces and the Grönwall
bounds that keep every solution in the tubes. Dissipative problems (`y' = -10 y`) keep their
accuracy because the bound is one-sided. A solution that leaves every tube, as when it blows up,
makes the command refuse. Inputs that are not polynomial, degrees over 4 in `t` or `y`, more than
20 monomials, `|t₀|, |T|, |y₀| > 100`, `T - t₀ > 20`, more than 8 output times, `d > 15` and inputs
in a section with `variable`s are refused, as the last checks show.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/-! ### Values -/
set_option linter.style.longLine false in
/--
info: #cas [ndsolve y t in [0, 1], y 0 = 1]
Domain: t ∈ [0, 1]
Input (polynomial initial value problem): (y' = y), y 0 = 1
Output (certified enclosures of width at most 10^-6; the solution exists and is unique on [0, 1] (4 pieces)): y(1) ∈ [2.7182818, 2.7182819]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Existence, uniqueness and enclosures
        Proposition: (∃ y, y 0 = 1 ∧ IsIntegralCurveOn y (fun t y ↦ y) (Set.Icc 0 1)) ∧
          (∀ (y z : ℝ → ℝ),
              y 0 = 1 →
                IsIntegralCurveOn y (fun t y ↦ y) (Set.Icc 0 1) →
                  z 0 = 1 → IsIntegralCurveOn z (fun t y ↦ y) (Set.Icc 0 1) → Set.EqOn y z (Set.Icc 0 1)) ∧
            ∀ (y : ℝ → ℝ),
              y 0 = 1 →
                IsIntegralCurveOn y (fun t y ↦ y) (Set.Icc 0 1) →
                  2.7182818 ≤ y 1 ∧ y 1 ≤ 2.7182819 ∧ 2.7182819 - 2.7182818 ≤ 1 / 10 ^ 6
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [ndsolve y t in [0, 1], y 0 = 1] (y' = y)

set_option linter.style.longLine false in
/--
info: #cas [ndsolve y t in [0, 1], y 0 = 1/2, at [1/2, 1]]
Domain: t ∈ [0, 1]
Input (polynomial initial value problem): (y' = y ^ 2 + t), y 0 = 1/2
Output (certified enclosures of width at most 10^-6; the solution exists and is unique on [0, 1] (6 pieces)): y(1/2) ∈ [0.8242620, 0.8242621], y(1) ∈ [2.1278712, 2.1278713]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Existence, uniqueness and enclosures
        Proposition: (∃ y, y 0 = 1 / 2 ∧ IsIntegralCurveOn y (fun t y ↦ y ^ 2 + t) (Set.Icc 0 1)) ∧
          (∀ (y z : ℝ → ℝ),
              y 0 = 1 / 2 →
                IsIntegralCurveOn y (fun t y ↦ y ^ 2 + t) (Set.Icc 0 1) →
                  z 0 = 1 / 2 → IsIntegralCurveOn z (fun t y ↦ y ^ 2 + t) (Set.Icc 0 1) → Set.EqOn y z (Set.Icc 0 1)) ∧
            ∀ (y : ℝ → ℝ),
              y 0 = 1 / 2 →
                IsIntegralCurveOn y (fun t y ↦ y ^ 2 + t) (Set.Icc 0 1) →
                  (0.8242620 ≤ y (1 / 2) ∧ y (1 / 2) ≤ 0.8242621 ∧ 0.8242621 - 0.8242620 ≤ 1 / 10 ^ 6) ∧
                    2.1278712 ≤ y 1 ∧ y 1 ≤ 2.1278713 ∧ 2.1278713 - 2.1278712 ≤ 1 / 10 ^ 6
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [ndsolve y t in [0, 1], y 0 = 1/2, at [1/2, 1]] (y' = y ^ 2 + t)

set_option linter.style.longLine false in
/--
info: #cas (digits := 10) [ndsolve y t in [0, 3], y 0 = 0, at [1, 2, 3]]
Domain: t ∈ [0, 3]
Input (polynomial initial value problem): (y' = 1 - y ^ 2), y 0 = 0
Output (certified enclosures of width at most 10^-10; the solution exists and is unique on [0, 3] (12 pieces)): y(1) ∈ [0.76159415595, 0.76159415596], y(2) ∈ [0.96402758007, 0.96402758008], y(3) ∈ [0.99505475368, 0.99505475369]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Existence, uniqueness and enclosures
        Proposition: (∃ y, y 0 = 0 ∧ IsIntegralCurveOn y (fun t y ↦ 1 - y ^ 2) (Set.Icc 0 3)) ∧
          (∀ (y z : ℝ → ℝ),
              y 0 = 0 →
                IsIntegralCurveOn y (fun t y ↦ 1 - y ^ 2) (Set.Icc 0 3) →
                  z 0 = 0 → IsIntegralCurveOn z (fun t y ↦ 1 - y ^ 2) (Set.Icc 0 3) → Set.EqOn y z (Set.Icc 0 3)) ∧
            ∀ (y : ℝ → ℝ),
              y 0 = 0 →
                IsIntegralCurveOn y (fun t y ↦ 1 - y ^ 2) (Set.Icc 0 3) →
                  (0.76159415595 ≤ y 1 ∧ y 1 ≤ 0.76159415596 ∧ 0.76159415596 - 0.76159415595 ≤ 1 / 10 ^ 10) ∧
                    (0.96402758007 ≤ y 2 ∧ y 2 ≤ 0.96402758008 ∧ 0.96402758008 - 0.96402758007 ≤ 1 / 10 ^ 10) ∧
                      0.99505475368 ≤ y 3 ∧ y 3 ≤ 0.99505475369 ∧ 0.99505475369 - 0.99505475368 ≤ 1 / 10 ^ 10
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (digits := 10) [ndsolve y t in [0, 3], y 0 = 0, at [1, 2, 3]] (y' = 1 - y ^ 2)

set_option linter.style.longLine false in
/--
info: #cas [ndsolve x s in [-1, 1], x (-1) = 2, at [-1, 0, 1]]
Domain: s ∈ [-1, 1]
Input (polynomial initial value problem): (x' = s * x - x ^ 2), x (-1) = 2
Output (certified enclosures of width at most 10^-6; the solution exists and is unique on [-1, 1] (14 pieces)): x(-1) ∈ [2.0000000, 2.0000000], x(0) ∈ [0.4952166, 0.4952167], x(1) ∈ [0.5129370, 0.5129371]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Existence, uniqueness and enclosures
        Proposition: (∃ x, x (-1) = 2 ∧ IsIntegralCurveOn x (fun s x ↦ s * x - x ^ 2) (Set.Icc (-1) 1)) ∧
          (∀ (x z : ℝ → ℝ),
              x (-1) = 2 →
                IsIntegralCurveOn x (fun s x ↦ s * x - x ^ 2) (Set.Icc (-1) 1) →
                  z (-1) = 2 →
                    IsIntegralCurveOn z (fun s x ↦ s * x - x ^ 2) (Set.Icc (-1) 1) → Set.EqOn x z (Set.Icc (-1) 1)) ∧
            ∀ (x : ℝ → ℝ),
              x (-1) = 2 →
                IsIntegralCurveOn x (fun s x ↦ s * x - x ^ 2) (Set.Icc (-1) 1) →
                  (2.0000000 ≤ x (-1) ∧ x (-1) ≤ 2.0000000 ∧ 2.0000000 - 2.0000000 ≤ 1 / 10 ^ 6) ∧
                    (0.4952166 ≤ x 0 ∧ x 0 ≤ 0.4952167 ∧ 0.4952167 - 0.4952166 ≤ 1 / 10 ^ 6) ∧
                      0.5129370 ≤ x 1 ∧ x 1 ≤ 0.5129371 ∧ 0.5129371 - 0.5129370 ≤ 1 / 10 ^ 6
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [ndsolve x s in [-1, 1], x (-1) = 2, at [-1, 0, 1]] (x' = s * x - x ^ 2)

set_option linter.style.longLine false in
/--
info: #cas [ndsolve y t in [0, 1], y 0 = 0]
Domain: t ∈ [0, 1]
Input (polynomial initial value problem): (y' = t), y 0 = 0
Output (certified enclosures of width at most 10^-6; the solution exists and is unique on [0, 1] (4 pieces)): y(1) ∈ [0.5000000, 0.5000000]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Existence, uniqueness and enclosures
        Proposition: (∃ y, y 0 = 0 ∧ IsIntegralCurveOn y (fun t y ↦ t) (Set.Icc 0 1)) ∧
          (∀ (y z : ℝ → ℝ),
              y 0 = 0 →
                IsIntegralCurveOn y (fun t y ↦ t) (Set.Icc 0 1) →
                  z 0 = 0 → IsIntegralCurveOn z (fun t y ↦ t) (Set.Icc 0 1) → Set.EqOn y z (Set.Icc 0 1)) ∧
            ∀ (y : ℝ → ℝ),
              y 0 = 0 →
                IsIntegralCurveOn y (fun t y ↦ t) (Set.Icc 0 1) →
                  0.5000000 ≤ y 1 ∧ y 1 ≤ 0.5000000 ∧ 0.5000000 - 0.5000000 ≤ 1 / 10 ^ 6
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [ndsolve y t in [0, 1], y 0 = 0] (y' = t)

set_option linter.style.longLine false in
/--
info: #cas (digits := 8) [ndsolve y t in [-1/2, 3/4], y (-1/2) = -3/7, at [0, 3/4]]
Domain: t ∈ [-1/2, 3/4]
Input (polynomial initial value problem): (y' = t ^ 2 - y / 3), y (-1/2) = -3/7
Output (certified enclosures of width at most 10^-8; the solution exists and is unique on [-1/2, 3/4] (8 pieces)): y(0) ∈ [-0.325987844, -0.325987843], y(3/4) ∈ [-0.121621874, -0.121621873]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Existence, uniqueness and enclosures
        Proposition: (∃ y,
            y (-(1 / 2)) = -(3 / 7) ∧ IsIntegralCurveOn y (fun t y ↦ t ^ 2 - y / 3) (Set.Icc (-(1 / 2)) (3 / 4))) ∧
          (∀ (y z : ℝ → ℝ),
              y (-(1 / 2)) = -(3 / 7) →
                IsIntegralCurveOn y (fun t y ↦ t ^ 2 - y / 3) (Set.Icc (-(1 / 2)) (3 / 4)) →
                  z (-(1 / 2)) = -(3 / 7) →
                    IsIntegralCurveOn z (fun t y ↦ t ^ 2 - y / 3) (Set.Icc (-(1 / 2)) (3 / 4)) →
                      Set.EqOn y z (Set.Icc (-(1 / 2)) (3 / 4))) ∧
            ∀ (y : ℝ → ℝ),
              y (-(1 / 2)) = -(3 / 7) →
                IsIntegralCurveOn y (fun t y ↦ t ^ 2 - y / 3) (Set.Icc (-(1 / 2)) (3 / 4)) →
                  (-0.325987844 ≤ y 0 ∧ y 0 ≤ -0.325987843 ∧ -0.325987843 + 0.325987844 ≤ 1 / 10 ^ 8) ∧
                    -0.121621874 ≤ y (3 / 4) ∧ y (3 / 4) ≤ -0.121621873 ∧ -0.121621873 + 0.121621874 ≤ 1 / 10 ^ 8
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (digits := 8) [ndsolve y t in [-1/2, 3/4], y (-1/2) = -3/7, at [0, 3/4]] (y' = t ^ 2 - y / 3)

/-! ### A dissipative problem and a long interval -/
set_option linter.style.longLine false in
/--
info: #cas (digits := 12) [ndsolve y t in [0, 1], y 0 = 1]
Domain: t ∈ [0, 1]
Input (polynomial initial value problem): (y' = -10 * y), y 0 = 1
Output (certified enclosures of width at most 10^-12; the solution exists and is unique on [0, 1] (15 pieces)): y(1) ∈ [0.0000453999297, 0.0000453999298]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Existence, uniqueness and enclosures
        Proposition: (∃ y, y 0 = 1 ∧ IsIntegralCurveOn y (fun t y ↦ -10 * y) (Set.Icc 0 1)) ∧
          (∀ (y z : ℝ → ℝ),
              y 0 = 1 →
                IsIntegralCurveOn y (fun t y ↦ -10 * y) (Set.Icc 0 1) →
                  z 0 = 1 → IsIntegralCurveOn z (fun t y ↦ -10 * y) (Set.Icc 0 1) → Set.EqOn y z (Set.Icc 0 1)) ∧
            ∀ (y : ℝ → ℝ),
              y 0 = 1 →
                IsIntegralCurveOn y (fun t y ↦ -10 * y) (Set.Icc 0 1) →
                  453999297e-13 ≤ y 1 ∧ y 1 ≤ 453999298e-13 ∧ 453999298e-13 - 453999297e-13 ≤ 1 / 10 ^ 12
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (digits := 12) [ndsolve y t in [0, 1], y 0 = 1] (y' = -10 * y)

set_option linter.style.longLine false in
/--
info: #cas (digits := 8) [ndsolve y t in [0, 10], y 0 = 1/10]
Domain: t ∈ [0, 10]
Input (polynomial initial value problem): (y' = y * (1 - y)), y 0 = 1/10
Output (certified enclosures of width at most 10^-8; the solution exists and is unique on [0, 10] (13 pieces)): y(10) ∈ [0.999591567, 0.999591568]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Existence, uniqueness and enclosures
        Proposition: (∃ y, y 0 = 1 / 10 ∧ IsIntegralCurveOn y (fun t y ↦ y * (1 - y)) (Set.Icc 0 10)) ∧
          (∀ (y z : ℝ → ℝ),
              y 0 = 1 / 10 →
                IsIntegralCurveOn y (fun t y ↦ y * (1 - y)) (Set.Icc 0 10) →
                  z 0 = 1 / 10 →
                    IsIntegralCurveOn z (fun t y ↦ y * (1 - y)) (Set.Icc 0 10) → Set.EqOn y z (Set.Icc 0 10)) ∧
            ∀ (y : ℝ → ℝ),
              y 0 = 1 / 10 →
                IsIntegralCurveOn y (fun t y ↦ y * (1 - y)) (Set.Icc 0 10) →
                  0.999591567 ≤ y 10 ∧ y 10 ≤ 0.999591568 ∧ 0.999591568 - 0.999591567 ≤ 1 / 10 ^ 8
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (digits := 8) [ndsolve y t in [0, 10], y 0 = 1/10] (y' = y * (1 - y))

/-! ### Refusals -/
/--
error: ndsolve: no certified step at t = 49841/50000; the solution may blow up there
-/
#guard_msgs in
#cas [ndsolve y t in [0, 2], y 0 = 1] (y' = y ^ 2)

/--
error: ndsolve: f must be a polynomial in t and y with rational coefficients
-/
#guard_msgs in
#cas [ndsolve y t in [0, 1], y 0 = 1] (y' = sin y)

/--
error: ndsolve: f must be a polynomial in t and y with rational coefficients
-/
#guard_msgs in
#cas [ndsolve y t in [0, 1], y 0 = 1] (y' = 1 / y)

/--
error: ndsolve accepts degree at most 4 in y
-/
#guard_msgs in
#cas [ndsolve y t in [0, 1], y 0 = 1] (y' = y ^ 5)

/--
error: ndsolve: the initial condition must be at t₀ = 0
-/
#guard_msgs in
#cas [ndsolve y t in [0, 1], y 1 = 1] (y' = y)

/--
error: ndsolve: expected t₀ < T
-/
#guard_msgs in
#cas [ndsolve y t in [1, 0], y 1 = 1] (y' = y)

/--
error: ndsolve: the output time 2 is not in [0, 1]
-/
#guard_msgs in
#cas [ndsolve y t in [0, 1], y 0 = 1, at [2]] (y' = y)

/--
error: ndsolve accepts between 1 and 15 digits
-/
#guard_msgs in
#cas (digits := 16) [ndsolve y t in [0, 1], y 0 = 1] (y' = y)

/--
error: ndsolve accepts T - t₀ ≤ 20
-/
#guard_msgs in
#cas [ndsolve y t in [0, 30], y 0 = 1] (y' = -y)

/--
error: ndsolve: expected an equation y' = f
-/
#guard_msgs in
#cas [ndsolve y t in [0, 1], y 0 = 1] (z' = y)

/--
error: ndsolve: the list of output times is empty
-/
#guard_msgs in
#cas [ndsolve y t in [0, 1], y 0 = 0, at []] (y' = 0)

/--
error: ndsolve: a power has an exponent over 64
-/
#guard_msgs in
#cas [ndsolve y t in [0, 1], y 0 = 1] (y' = (1 + y) ^ 1000000)

set_option linter.style.longLine false in
/--
error: ndsolve: the input has degree over 16 before simplification (in a numerator or a denominator of a subexpression)
-/
#guard_msgs in
#cas [ndsolve y t in [0, 1], y 0 = 1] (y' = ((((1 + y) ^ 64) ^ 64) ^ 64) ^ 0)

/--
error: ndsolve: f must be a polynomial in t and y with rational coefficients
-/
#guard_msgs in
#cas [ndsolve y t in [0, 1], y 0 = 1] (y' = (t ^ 16 + y) / (t + (4294967296 * y) ^ 16))

/--
error: ndsolve accepts degree at most 4 in y
-/
#guard_msgs in
#cas [ndsolve y t in [0, 1], y 0 = 1] (y' = t * (y ^ 15 + 1) + (y + 4294967296 ^ 64))

/--
error: ndsolve: a power has an exponent over 64
-/
#guard_msgs in
#cas [ndsolve y t in [0, 2 ^ 1000000000], y 0 = 1] (y' = y)

/-! ### Inside a section with `variable`s -/
section

variable (exp : ℝ → ℝ)

/--
error: ndsolve is not supported in a section with `variable`s
-/
#guard_msgs in
#cas [ndsolve y t in [0, 1], y 0 = 1] (y' = y)

end

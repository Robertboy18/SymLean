/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Linear differential equations of order one and two

`#cas [dsolve y x] (equation)` solves a linear equation with rational constant coefficients and a
right side made of terms `xᵏ e ^ (a x) cos (b x)`, `xᵏ e ^ (a x) sin (b x)`; the equations here
have order one or two. The theorem says that the family is exactly the set of solutions: for every
`y` with differentiable derivatives below the order (`y` differentiable, for order one), `y` solves
the equation if and only if it has the stated form. With initial values the answer is the single
solution. Each command runs in the build inside `#guard_msgs`, which checks its report.

The outputs are `c₁ e ^ (-x) + c₂ e ^ (-2x)`; `c₁ e ^ x + c₂ x e ^ x`;
`c₁ e ^ (-x) cos (2x) + c₂ e ^ (-x) sin (2x)`; `c₁ e ^ (√2 x) + c₂ e ^ (-√2 x)`;
`-x cos x / 2 + c₁ cos x + c₂ sin x` (resonance raises the degree); `-x e ^ x + c₁ e ^ x +
c₂ e ^ (2x)`; `e ^ x (cos x / 17 + 4 sin x / 17) + c₁ cos (√2 x / 2) + c₂ sin (√2 x / 2)`;
`-1/4 + x/2 + c₁ e ^ (-2x)`; `cos x`; `sinh (√2 x) / √2`; and
`-x cos (2x) / 4 + sin (2x) / 8`. The first theorem is

`∀ (y : ℝ → ℝ), (∀ k < 2, Differentiable ℝ (iteratedDeriv k y)) → ((∀ (x : ℝ),`
`iteratedDeriv 2 y x + 3 * deriv y x + 2 * y x = 0) ↔ ∃ c₁ c₂, ∀ (x : ℝ),`
`y x = c₁ * Real.exp (-x) + c₂ * Real.exp (-(2 * x)))`,

and the ninth `∀ (y : ℝ → ℝ), (∀ k < 2, Differentiable ℝ (iteratedDeriv k y)) →`
`((∀ (x : ℝ), iteratedDeriv 2 y x + y x = 0) ∧ y 0 = 1 ∧ deriv y 0 = 0 ↔`
`∀ (x : ℝ), y x = Real.cos x)`. Second-order equations with coefficients depending on `x`, such
as `y'' + x y = 0`, are refused; higher orders are in `DSolveOrder.lean` and `DSolveRoot.lean`.

The compiled theorem is the general solution of the harmonic oscillator from the library
statement the command instantiates.
-/

public section

namespace CAS.Examples.DSolve

open CAS.LinearODE

/-- The solutions of `y'' + y = 0` with a differentiable derivative are the span of `cos x` and
`sin x`. -/
example (y : ℝ → ℝ)
    (hy : ∀ k < degQ [(CharRoot.pair 0 1 1, 1)], Differentiable ℝ (iteratedDeriv k y)) :
    (∀ x, rLop (degQ [(CharRoot.pair 0 1 1, 1)])
        (fun k ↦ (charQ [(CharRoot.pair 0 1 1, 1)] k : ℝ)) y x = 0) ↔
      y ∈ Submodule.span ℝ {f | f ∈ basisList [(CharRoot.pair 0 1 1, 1)]} :=
  rLop_eq_zero_iff _ (by decide) (nodup_of_separated (p := 8) (by decide +kernel)) hy

end CAS.Examples.DSolve

end

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 2 with constant coefficients): (y'' + 3*y' + 2*y = 0)
Output (order 2, characteristic roots: -1, -2): y(x) = c₁*exp(-x) + c₂*exp(-(2*x))

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The general solution, and every solution has this form
        Proposition: ∀ (y : ℝ → ℝ),
          (∀ k < 2, Differentiable ℝ (iteratedDeriv k y)) →
            ((∀ (x : ℝ), iteratedDeriv 2 y x + 3 * deriv y x + 2 * y x = 0) ↔
              ∃ c₁ c₂, ∀ (x : ℝ), y x = c₁ * Real.exp (-x) + c₂ * Real.exp (-(2 * x)))
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [dsolve y x] (y'' + 3*y' + 2*y = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 2 with constant coefficients): (y'' - 2*y' + y = 0)
Output (order 2, characteristic roots: 1 (multiplicity 2)): y(x) = c₁*exp(x) + c₂*x*exp(x)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The general solution, and every solution has this form
        Proposition: ∀ (y : ℝ → ℝ),
          (∀ k < 2, Differentiable ℝ (iteratedDeriv k y)) →
            ((∀ (x : ℝ), iteratedDeriv 2 y x - 2 * deriv y x + y x = 0) ↔
              ∃ c₁ c₂, ∀ (x : ℝ), y x = c₁ * Real.exp x + c₂ * (x * Real.exp x))
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [dsolve y x] (y'' - 2*y' + y = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 2 with constant coefficients): (y'' + 2*y' + 5*y = 0)
Output (order 2, characteristic roots: -1 ± 2 i): y(x) = c₁*exp(-x)*cos(2*x) + c₂*exp(-x)*sin(2*x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y'' + 2*y' + 5*y = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 2 with constant coefficients): (y'' - 2*y = 0)
Output (order 2, characteristic roots: ±√2): y(x) = c₁*exp(sqrt(2)*x) + c₂*exp(-(sqrt(2)*x))

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y'' - 2*y = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 2 with constant coefficients): (y'' + y = sin x)
Output (order 2, characteristic roots: ±i): y(x) = -(1/2*x*cos(x)) + c₁*cos(x) + c₂*sin(x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y'' + y = sin x)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 2 with constant coefficients): (y'' - 3*y' + 2*y = exp x)
Output (order 2, characteristic roots: 1, 2): y(x) = exp(x)*-x + c₁*exp(x) + c₂*exp(2*x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y'' - 3*y' + 2*y = exp x)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 2 with constant coefficients): (2*y'' + y = cos x * exp x)
Output (order 2, characteristic roots: ±1/2√2 i): y(x) = exp(x)*(1/17*cos(x) + 4/17*sin(x)) +
c₁*cos(1/2*sqrt(2)*x) + c₂*sin(1/2*sqrt(2)*x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (2*y'' + y = cos x * exp x)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 1 with constant coefficients): (y' + 2*y = x)
Output (order 1, characteristic roots: -2): y(x) = -(1/4) + 1/2*x + c₁*exp(-(2*x))

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The general solution, and every solution has this form
        Proposition: ∀ (y : ℝ → ℝ),
          Differentiable ℝ y →
            ((∀ (x : ℝ), deriv y x + 2 * y x = x) ↔
              ∃ c₁, ∀ (x : ℝ), y x = -(1 / 4) + 1 / 2 * x + c₁ * Real.exp (-(2 * x)))
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [dsolve y x] (y' + 2*y = x)

/--
info: #cas [dsolve y x, y 0 = 1, y' 0 = 0]
Domain: x ∈ ℝ
Input (linear equation of order 2 with constant coefficients): (y'' + y = 0)
Output (order 2, characteristic roots: ±i): y(x) = cos(x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x, y 0 = 1, y' 0 = 0] (y'' + y = 0)

/--
info: #cas [dsolve y x, y 0 = 0, y' 0 = 1]
Domain: x ∈ ℝ
Input (linear equation of order 2 with constant coefficients): (y'' - 2*y = 0)
Output (order 2, characteristic roots: ±√2): y(x) = sinh(sqrt(2)*x)/sqrt(2)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x, y 0 = 0, y' 0 = 1] (y'' - 2*y = 0)

/--
info: #cas [dsolve y x, y 0 = 0, y' 0 = 0]
Domain: x ∈ ℝ
Input (linear equation of order 2 with constant coefficients): (y'' + 4*y = sin (2*x))
Output (order 2, characteristic roots: ±2 i): y(x) = -(1/4*x*cos(2*x)) + 1/4*sin(2*x)/2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x, y 0 = 0, y' 0 = 0] (y'' + 4*y = sin (2*x))


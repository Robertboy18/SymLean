/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Linear differential equations of higher order and with a variable coefficient

`#cas [dsolve y x] (equation)` solves a linear equation of any order with rational constant
coefficients, with exact characteristic roots when `CAS.Command.RootSplit` splits the
characteristic polynomial into linear and quadratic factors and with enclosures otherwise, and a
first-order equation `y' + p(x) y = q(x)` when the checked integrator finds the two primitives of
the integrating factor. Each command runs in the build inside `#guard_msgs`, which checks its
report.

The outputs are `c₁ e ^ x + c₂ e ^ (2x) + c₃ e ^ (3x)`;
`c₁ e ^ x + e ^ (-x/2) (c₂ cos (√3 x / 2) + c₃ sin (√3 x / 2))`;
`c₁ e ^ x + c₂ e ^ (-x) + c₃ cos x + c₄ sin x`; `(c₁ + c₃ x) cos x + (c₂ + c₄ x) sin x`;
`c₁ e ^ (r₁ x) + ⋯ + c₄ e ^ (r₄ x)` with enclosures of the roots `r₁, …, r₄` of
`r ^ 4 - 5 r ^ 2 + 6`; `-x ^ 2 / 2 + c₁ + c₂ e ^ x + c₃ e ^ (-x)`; `cos x / 5` plus the
combination of `e ^ (Re z x) cos (Im z x)` and `e ^ (Re z x) sin (Im z x)` over enclosures of two
roots `z` of `r ^ 4 + 4`; `e ^ x / 3 + 2/3 e ^ (-x/2) cos (√3 x / 2)`; `sin x`;
`(e ^ (x ^ 2) / 2 + C) e ^ (-x ^ 2)`; `(e ^ (sin x) + C) e ^ (-sin x)`; `e ^ (x ^ 2)`; and
`c₁ e ^ x + e ^ (-x / 2469134) (c₂ cos (β x) + c₃ sin (β x))` with
`β = √6096622709955 / 2469134`. The first theorem is

`∀ (y : ℝ → ℝ), (∀ k < 3, Differentiable ℝ (iteratedDeriv k y)) → ((∀ (x : ℝ),`
`iteratedDeriv 3 y x - 6 * iteratedDeriv 2 y x + 11 * deriv y x = 6 * y x) ↔ ∃ c₁ c₂ c₃, ∀ (x : ℝ),`
`y x = c₁ * Real.exp x + c₂ * Real.exp (2 * x) + c₃ * Real.exp (3 * x))`

and the eighth `∀ (y : ℝ → ℝ), (∀ k < 3, Differentiable ℝ (iteratedDeriv k y)) →`
`((∀ (x : ℝ), iteratedDeriv 3 y x = y x) ∧ y 0 = 1 ∧ deriv y 0 = 0 ∧ iteratedDeriv 2 y 0 = 0 ↔`
`∀ (x : ℝ), y x = 1 / 3 * Real.exp x +`
`2 / 3 * (Real.exp (-(1 / 2 * x)) * Real.cos (1 / 2 * √3 * x)))`. In the last command the
characteristic polynomial is `(X - 1) (X ^ 2 + X / 1234567 + 1)`, split by the quadratic formula
with or without `CASHex`. Without `CASHex` the splitter looks for no quadratic factors of a
quartic without rational roots, so `X ^ 4 - 5 X ^ 2 + 6` and `X ^ 4 + 4` keep their roots as
enclosures; with `CASHex` its factor provider splits them and the roots are exact.
`y'''' + y = 0` and `y''''' - y = 0`, where `X ^ 4 + 1` and `X ^ 4 + X ^ 3 + X ^ 2 + X + 1` are
irreducible over `ℚ`, are in `CAS.Examples.DSolveRoot`; `y' + x y = 1` is refused, since
its integrating factor `e ^ (x ^ 2 / 2)` has no elementary primitive.

The compiled theorem is the general solution of `y'''' + 2 y'' + y = 0` from the library
statement the command instantiates, with the roots `±i` of multiplicity two.
-/

public section

namespace CAS.Examples.DSolveOrder

open CAS.LinearODE

/-- The solutions of `y'''' + 2 y'' + y = 0` are the span of `cos x`, `sin x`, `x cos x`,
`x sin x`. -/
example (y : ℝ → ℝ)
    (hy : ∀ k < degQ [(CharRoot.pair 0 1 1, 2)], Differentiable ℝ (iteratedDeriv k y)) :
    (∀ x, rLop (degQ [(CharRoot.pair 0 1 1, 2)])
        (fun k ↦ (charQ [(CharRoot.pair 0 1 1, 2)] k : ℝ)) y x = 0) ↔
      y ∈ Submodule.span ℝ {f | f ∈ basisList [(CharRoot.pair 0 1 1, 2)]} :=
  rLop_eq_zero_iff _ (by decide) (nodup_of_separated (p := 8) (by decide +kernel)) hy

end CAS.Examples.DSolveOrder

end

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 3 with constant coefficients): (y''' - 6*y'' + 11*y' - 6*y = 0)
Output (order 3, characteristic roots: 1, 2, 3): y(x) = c₁*exp(x) + c₂*exp(2*x) + c₃*exp(3*x)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The general solution, and every solution has this form
        Proposition: ∀ (y : ℝ → ℝ),
          (∀ k < 3, Differentiable ℝ (iteratedDeriv k y)) →
            ((∀ (x : ℝ), iteratedDeriv 3 y x - 6 * iteratedDeriv 2 y x + 11 * deriv y x = 6 * y x) ↔
              ∃ c₁ c₂ c₃, ∀ (x : ℝ), y x = c₁ * Real.exp x + c₂ * Real.exp (2 * x) + c₃ * Real.exp
(3 * x))
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [dsolve y x] (y''' - 6*y'' + 11*y' - 6*y = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 3 with constant coefficients): (y''' - y = 0)
Output (order 3, characteristic roots: 1, -1/2 ± 1/2√3 i): y(x) = c₁*exp(x) +
c₂*exp(-(1/2*x))*cos(1/2*sqrt(3)*x) + c₃*exp(-(1/2*x))*sin(1/2*sqrt(3)*x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y''' - y = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 4 with constant coefficients): (y'''' - y = 0)
Output (order 4, characteristic roots: 1, -1, ±i): y(x) = c₁*exp(x) + c₂*exp(-x) + c₃*cos(x) +
c₄*sin(x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y'''' - y = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 4 with constant coefficients): (y'''' + 2*y'' + y = 0)
Output (order 4, characteristic roots: ±i (multiplicity 2)): y(x) = c₁*cos(x) + c₂*sin(x) +
c₃*x*cos(x) + c₄*x*sin(x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y'''' + 2*y'' + y = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 4 with constant coefficients): (y'''' - 5*y'' + 6*y = 0)
Output (order 4, the roots of r^4 - 5 r^2 + 6 = 0: r₁ ∈ (-1.73205082, -1.73205080), r₂ ∈
(-1.41421357, -1.41421355), r₃ ∈ (1.41421355, 1.41421357), r₄ ∈ (1.73205080, 1.73205082)): y(x) =
c₁*exp(r₁*x) + c₂*exp(r₂*x) + c₃*exp(r₃*x) + c₄*exp(r₄*x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y'''' - 5*y'' + 6*y = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 3 with constant coefficients): (y''' - y' = x)
Output (order 3, characteristic roots: 0, 1, -1): y(x) = -(1/2*x^2) + c₁ + c₂*exp(x) + c₃*exp(-x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y''' - y' = x)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 4 with constant coefficients): (y'''' + 4*y = Real.cos x)
Output (order 4, the roots of r^4 + 4 = 0: z₁ = α ± iβ, α ∈ [-1.00000002, -0.99999998], β ∈
[0.99999998, 1.00000002], z₂ = α ± iβ, α ∈ [0.99999998, 1.00000002], β ∈ [0.99999998, 1.00000002]):
y(x) = 1/5*cos(x) + c₁*exp(re(z₁)*x)*cos(im(z₁)*x) + c₂*exp(re(z₁)*x)*sin(im(z₁)*x) +
c₃*exp(re(z₂)*x)*cos(im(z₂)*x) + c₄*exp(re(z₂)*x)*sin(im(z₂)*x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y'''' + 4*y = Real.cos x)

/--
info: #cas [dsolve y x, y 0 = 1, y' 0 = 0, y'' 0 = 0]
Domain: x ∈ ℝ
Input (linear equation of order 3 with constant coefficients): (y''' - y = 0)
Output (order 3, characteristic roots: 1, -1/2 ± 1/2√3 i): y(x) = 1/3*exp(x) +
2/3*exp(-(1/2*x))*cos(1/2*sqrt(3)*x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x, y 0 = 1, y' 0 = 0, y'' 0 = 0] (y''' - y = 0)

/--
info: #cas [dsolve y x, y 0 = 0, y' 0 = 1, y'' 0 = 0]
Domain: x ∈ ℝ
Input (linear equation of order 3 with constant coefficients): (y''' + y' = 0)
Output (order 3, characteristic roots: 0, ±i): y(x) = sin(x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x, y 0 = 0, y' 0 = 1, y'' 0 = 0] (y''' + y' = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order one with a variable coefficient): (y' + 2*x*y = x)
Output (integrating factor e ^ P): y(x) = (1/2*exp(x^2) + C)*exp(-x^2)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y' + 2*x*y = x)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order one with a variable coefficient): (y' + Real.cos x * y = Real.cos x)
Output (integrating factor e ^ P): y(x) = (exp(sin(x)) + C)*exp(-sin(x))

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y' + Real.cos x * y = Real.cos x)

/--
info: #cas [dsolve y x, y 0 = 1]
Domain: x ∈ ℝ
Input (linear equation of order one with a variable coefficient): (y' - 2*x*y = 0)
Output (integrating factor e ^ P): y(x) = exp(x^2)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x, y 0 = 1] (y' - 2*x*y = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 3 with constant coefficients): (y''' - (1234566/1234567) * y'' +
(1234566/1234567) * y' - y = 0)
Output (order 3, characteristic roots: 1, -1/2469134 ± 1/2469134√6096622709955 i)
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y''' - (1234566/1234567) * y'' + (1234566/1234567) * y' - y = 0)

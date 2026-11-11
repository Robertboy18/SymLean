/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Characteristic roots without closed form

When `CAS.Command.RootSplit` leaves a factor of the characteristic polynomial of a
constant-coefficient equation without closed form (an irreducible factor of degree three or more,
or without `CASHex` a factor of degree four or more without rational roots), `#cas [dsolve y x]`
names its roots by certified enclosures:
`AlgRoot.real R lo hi` is the real root of `R` in `(lo, hi)` and `AlgRoot.complex R u v ρ` the
complex root within `ρ` of `u + v i`. The theorem binds them by `let`, states the enclosures and
the equation `R (r) = 0` of each, and gives the general solution in them. Each command runs in
the build inside `#guard_msgs`, which checks its report.

The roots are: for `r ^ 4 + 1`, `z₁ = α₁ ± i β₁` with `α₁ ∈ [-0.70710680, -0.70710676]`,
`β₁ ∈ [0.70710676, 0.70710680]` and `z₂` with `α₂, β₂ ∈ [0.70710676, 0.70710680]`; for `r ^ 3 - 2`,
`r₁ ∈ (1.25992104, 1.25992106)` and `α ∈ [-0.62996054, -0.62996050]`,
`β ∈ [1.09112362, 1.09112366]`; for `r ^ 3 - 3 r + 1` three real roots near `-1.87938524`,
`0.34729636`, `1.53208889`; for `r ^ 5 - 1` the root `1` and the two pairs of
`r ^ 4 + r ^ 3 + r ^ 2 + r + 1` near `-0.80901699 ± 0.58778525 i` and
`0.30901699 ± 0.95105652 i`; for `r ^ 5 - r - 1` a real root near `1.16730398` and two pairs;
for `r ^ 4 + 5 r ^ 2 + 6 = (r ^ 2 + 2) (r ^ 2 + 3)` the pairs near `±1.41421356 i` and
`±1.73205081 i`, which are exact with `CASHex`. With the right side `e ^ x` the particular solution
is `-e ^ x`. The first theorem is

`let z₁ := AlgRoot.complex [1, 0, 0, 0, 1] (-0.70710678) 0.70710678 2e-8;`
`let z₂ := AlgRoot.complex [1, 0, 0, 0, 1] 0.70710678 0.70710678 2e-8;`
`(z₁.re ∈ Set.Icc (-0.70710680) (-0.70710676) ∧ z₁.im ∈ Set.Icc 0.70710676 0.70710680 ∧`
`z₁ ^ 4 + 1 = 0) ∧ (z₂.re ∈ Set.Icc 0.70710676 0.70710680 ∧ z₂.im ∈ Set.Icc 0.70710676 0.70710680`
`∧ z₂ ^ 4 + 1 = 0) ∧ ∀ (y : ℝ → ℝ), (∀ k < 4, Differentiable ℝ (iteratedDeriv k y)) →`
`((∀ (x : ℝ), iteratedDeriv 4 y x + y x = 0) ↔ ∃ c₁ c₂ c₃ c₄, ∀ (x : ℝ),`
`y x = c₁ * (Real.exp (z₁.re * x) * Real.cos (z₁.im * x)) +`
`c₂ * (Real.exp (z₁.re * x) * Real.sin (z₁.im * x)) + c₃ * (Real.exp (z₂.re * x) *`
`Real.cos (z₂.im * x)) + c₄ * (Real.exp (z₂.re * x) * Real.sin (z₂.im * x)))`.

Initial values are refused in this case, since the constants would solve a linear system with
these roots as entries.

The compiled theorem is the enclosure of the real root of `r ^ 3 - 2`, from the sign change of
`r ^ 3 - 2` between the endpoints.
-/

public section

namespace CAS.Examples.DSolveRoot

open CAS

/-- The real root of `r ^ 3 - 2` lies in `(1.25992104, 1.25992106)`. -/
example : AlgRoot.real [-2, 0, 0, 1] 1.25992104 1.25992106 ∈
    Set.Ioo ((1.25992104 : ℚ) : ℝ) ((1.25992106 : ℚ) : ℝ) :=
  (AlgRoot.real_spec _ (by norm_num) (by norm_num [CAS.Polynomial.coeffEvalRat])).1

end CAS.Examples.DSolveRoot

end

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 4 with constant coefficients): (y'''' + y = 0)
Output (order 4, the roots of r^4 + 1 = 0: z₁ = α ± iβ, α ∈ [-0.70710680, -0.70710676], β ∈
[0.70710676, 0.70710680], z₂ = α ± iβ, α ∈ [0.70710676, 0.70710680], β ∈ [0.70710676, 0.70710680]):
y(x) = c₁*exp(re(z₁)*x)*cos(im(z₁)*x) + c₂*exp(re(z₁)*x)*sin(im(z₁)*x) +
c₃*exp(re(z₂)*x)*cos(im(z₂)*x) + c₄*exp(re(z₂)*x)*sin(im(z₂)*x)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The roots of the characteristic factor without closed form,
by certified enclosures, and the general solution
        Proposition: let z₁ := CAS.AlgRoot.complex [1, 0, 0, 0, 1] (-0.70710678) 0.70710678
2e-8;
        let z₂ := CAS.AlgRoot.complex [1, 0, 0, 0, 1] 0.70710678 0.70710678 2e-8;
        (z₁.re ∈ Set.Icc (-0.70710680) (-0.70710676) ∧ z₁.im ∈ Set.Icc 0.70710676 0.70710680 ∧ z₁ ^
4 + 1 = 0) ∧
          (z₂.re ∈ Set.Icc 0.70710676 0.70710680 ∧ z₂.im ∈ Set.Icc 0.70710676 0.70710680 ∧ z₂ ^ 4 +
1 = 0) ∧
            ∀ (y : ℝ → ℝ),
              (∀ k < 4, Differentiable ℝ (iteratedDeriv k y)) →
                ((∀ (x : ℝ), iteratedDeriv 4 y x + y x = 0) ↔
                  ∃ c₁ c₂ c₃ c₄,
                    ∀ (x : ℝ),
                      y x =
                        c₁ * (Real.exp (z₁.re * x) * Real.cos (z₁.im * x)) +
                              c₂ * (Real.exp (z₁.re * x) * Real.sin (z₁.im * x)) +
                            c₃ * (Real.exp (z₂.re * x) * Real.cos (z₂.im * x)) +
                          c₄ * (Real.exp (z₂.re * x) * Real.sin (z₂.im * x)))
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [dsolve y x] (y'''' + y = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 3 with constant coefficients): (y''' - 2 * y = 0)
Output (order 3, the roots of r^3 - 2 = 0: r₁ ∈ (1.25992104, 1.25992106), z₁ = α ± iβ, α ∈
[-0.62996054, -0.62996050], β ∈ [1.09112362, 1.09112366]): y(x) = c₁*exp(r₁*x) +
c₂*exp(re(z₁)*x)*cos(im(z₁)*x) + c₃*exp(re(z₁)*x)*sin(im(z₁)*x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y''' - 2 * y = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 3 with constant coefficients): (y''' - 3 * y' + y = 0)
Output (order 3, the roots of r^3 - 3 r + 1 = 0: r₁ ∈ (-1.87938525, -1.87938523), r₂ ∈ (0.34729635,
0.34729637), r₃ ∈ (1.53208888, 1.53208890)): y(x) = c₁*exp(r₁*x) + c₂*exp(r₂*x) + c₃*exp(r₃*x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y''' - 3 * y' + y = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 5 with constant coefficients): (y''''' - y = 0)
Output (order 5, characteristic roots: 1 and the roots of r^4 + r^3 + r^2 + r + 1 = 0: z₁ = α ± iβ,
α ∈ [-0.80901701, -0.80901697], β ∈ [0.58778523, 0.58778527], z₂ = α ± iβ, α ∈ [0.30901697,
0.30901701], β ∈ [0.95105650, 0.95105654]): y(x) = c₁*exp(x) + c₂*exp(re(z₁)*x)*cos(im(z₁)*x) +
c₃*exp(re(z₁)*x)*sin(im(z₁)*x) + c₄*exp(re(z₂)*x)*cos(im(z₂)*x) + c₅*exp(re(z₂)*x)*sin(im(z₂)*x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y''''' - y = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 5 with constant coefficients): (y''''' - y' - y = 0)
Output (order 5, the roots of r^5 - r - 1 = 0: r₁ ∈ (1.16730397, 1.16730399), z₁ = α ± iβ, α ∈
[-0.76488445, -0.76488441], β ∈ [0.35247153, 0.35247157], z₂ = α ± iβ, α ∈ [0.18123242, 0.18123246],
β ∈ [1.08395408, 1.08395412]): y(x) = c₁*exp(r₁*x) + c₂*exp(re(z₁)*x)*cos(im(z₁)*x) +
c₃*exp(re(z₁)*x)*sin(im(z₁)*x) + c₄*exp(re(z₂)*x)*cos(im(z₂)*x) + c₅*exp(re(z₂)*x)*sin(im(z₂)*x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y''''' - y' - y = 0)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 3 with constant coefficients): (y''' - 2 * y = exp x)
Output (order 3, the roots of r^3 - 2 = 0: r₁ ∈ (1.25992104, 1.25992106), z₁ = α ± iβ, α ∈
[-0.62996054, -0.62996050], β ∈ [1.09112362, 1.09112366]): y(x) = exp(x)*-1 + c₁*exp(r₁*x) +
c₂*exp(re(z₁)*x)*cos(im(z₁)*x) + c₃*exp(re(z₁)*x)*sin(im(z₁)*x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y''' - 2 * y = exp x)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order 4 with constant coefficients): (y'''' + 5*y'' + 6*y = 0)
Output (order 4, the roots of r^4 + 5 r^2 + 6 = 0: z₁ = α ± iβ
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y'''' + 5*y'' + 6*y = 0)

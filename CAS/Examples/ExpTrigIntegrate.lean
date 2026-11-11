/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Primitives of `xᵏ e ^ (a x) cos (b x)` with symbolic parameters

`#cas [integrate x] f` integrates sums of terms `c xᵏ e ^ (a x) cos (b x)` and
`c xᵏ e ^ (a x) sin (b x)` with symbolic `a` and `b`, also without the exponential or without the
trigonometric factor, by the planner's coupled recurrence for polynomial amplitudes
(`CAS.Integration.ExponentialTrig`). The primitive is `e ^ (a x) (P x sin (b x) + Q x cos (b x))`
for polynomials `P` and `Q` whose coefficients are rational functions of `a` and `b`, and the
report lists their denominators as conditions: `a ^ 2 + b ^ 2 ≠ 0`, or `a ≠ 0` and `b ≠ 0` when
one factor is missing. `#cas [dsolve y x]` uses the same primitives for `y' + p y = q` with a
symbolic constant `p`. Each command runs in the build inside `#guard_msgs`, which checks its
report.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
Output (scalar ℝ; antiderivative): exp(a*x)*(a*sin(n*x) - n*cos(n*x))/(a^2 + n^2)
Conditions: a^2 + n^2 ≠ 0
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (exp (a * x) * sin (n * x))

/--
Output (scalar ℝ; antiderivative): exp(a*x)*(n*sin(n*x) + a*cos(n*x))/(a^2 + n^2)
Conditions: a^2 + n^2 ≠ 0
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (exp (a * x) * cos (n * x))

/--
Output (scalar ℝ; antiderivative): exp(a*x)*(x^2*a^2 - 2*x*a + 2)/a^3
Conditions: a ≠ 0
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (x ^ 2 * exp (a * x))

/--
Output (scalar ℝ; antiderivative): (sin(n*x) - x*n*cos(n*x))/n^2
Conditions: n ≠ 0
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (x * sin (n * x))

/-- Output (scalar ℝ; antiderivative): exp(x)*(1/2*x*sin(x) + (-1/2*x + 1/2)*cos(x)) -/
#guard_msgs (info, substring := true) in
#cas [integrate x] (x * exp x * sin x)

/--
Output (scalar ℝ; antiderivative): exp(a*x)*((x*a^3 + x*a*b^2 - a^2 + b^2)*sin(b*x) +
(-(x*a^2*b) - x*b^3 + 2*a*b)*cos(b*x))/(a^2 + b^2)^2
Conditions: a^2 + b^2 ≠ 0
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (exp (a * x) * sin (b * x) * x)

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order one with symbolic coefficients): (y' + a * y = sin (n * x))
Output (integrating factor e ^ (p x)): y(x) = (exp(a*x)*(a*sin(n*x) - n*cos(n*x))/(a^2 + n^2) +
C)*exp(-(a*x))

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y' + a * y = sin (n * x))

/--
info: #cas [dsolve y x]
Domain: x ∈ ℝ
Input (linear equation of order one with symbolic coefficients): (y' + k * y = exp (2 * x))
Output (integrating factor e ^ (p x)): y(x) = (exp((k + 2)*x)/(k + 2) + C)*exp(-(k*x))

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [dsolve y x] (y' + k * y = exp (2 * x))


/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Certified numerical integration

`#cas [nintegrate x in [a, b]] f` returns a decimal value of the integral with a proved error bound
`10 ^ (-d)`, `d = 6` unless `(digits := d)` is given. The commands run in the build in
`NIntegrateReports.lean`, each inside `#guard_msgs`, which checks its report.

The six commands use the batch Simpson certificate, one kernel check for all panels:
`0.746824 ± 10^-6` (16 panels), `0.785398 ± 10^-6` (16 panels), `0.45969770 ± 10^-8`
(16 panels), `0.38629436 ± 10^-8` (32 panels), `8.3891 ± 10^-4` and `1.718282 ± 10^-6` (8
panels). Ten digits of `∫ exp` need 64 panels and about 65 s of kernel checking, too long for the
build, which runs six. The statement for the rational integrand is
`|(∫ (x : ℝ) in 0..1, 1 / (1 + x ^ 2)) - 785398 / 10 ^ 6| ≤ 1 / 10 ^ 6`. The square root is not
smooth at `0`, so the batch route does not apply; `NIntegrateSingular.lean` integrates it after
the substitution `x = u ^ 2`.

The compiled theorem is eight decimals of `∫ sin` through the batch certificate, whose validity
side condition `simp` checks. The Gaussian integral through bare `cega` is
`gaussian_integral_approx` in `CEGA/GaussianIntegral.lean`.
-/

public section

namespace CAS.Examples.NIntegrate

open CAS CAS.Continuum Verified.Expr in
/-- Eight decimals of `∫ x in 0..1, sin x = 1 - cos 1` from 16 panels in one kernel check. -/
theorem sin_eight_decimals :
    |(∫ x in (0 : ℝ)..1, Real.sin x) - 45969770 / 10 ^ 8| ≤ 1 / 10 ^ 8 := by
  have h := BatchSimpson.of_integralCheck_abs (p := ⟨66, 32, 57⟩) (f := .sin (.var 0))
    (d := (Verified.Expr.sin (.var 0)).symbolicDerivative 4) (a := 0) (b := 1) (N := 16)
    (c := 45969770 / 10 ^ 8) (ε := 1 / 10 ^ 8)
    (by intro k hk x _; interval_cases k <;> simp [iteratedDiff, diff]) (by cega)
  simpa [univariateEval] using h

end CAS.Examples.NIntegrate

end

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Fourier coefficients of products, and sine and cosine series on `[0, L]`

`#cas [fourier x n] f` takes products of polynomials, exponentials and trigonometric functions,
as sums of terms `c xʲ e ^ (a x) cos (k x)` and `c xʲ e ^ (a x) sin (k x)`, and gives `a₀`, `aₙ`,
`bₙ` on `[-π, π]` as exact functions of `n` with a proof; when a term `xʲ cos (k x)` or
`xʲ sin (k x)` has no exponential factor the value at `n = k` comes out separately, unless the
formula for general `n` gives it too. `#cas [fourierSin x n L] f` and
`#cas [fourierCos x n L] f` give the coefficients of the sine and cosine series on `[0, L]` for sums
of terms `c xʲ e ^ (a x)`, with `π` allowed in the coefficients and `L` a positive rational number
or rational multiple of `π`. Each command runs in the build inside `#guard_msgs`, which checks its
report.

The outputs are: `a₀ = 2`, `a₁ = -1/2`, `aₙ = 2 (-1) ^ (n + 1) / ((n + 1) (n - 1))` for
`n ≥ 2`, `bₙ = 0`; for `x ^ 2 e ^ x`, `a₀ = 2 ((π ^ 2 + 2) sinh π - 2 π cosh π) / π` and `aₙ`,
`bₙ` rational functions of `n` over `π (n ^ 2 + 1) ^ 3` with `sinh π`, `cosh π`; `aₙ = 0`,
`b₂ = -1/4`, `bₙ = 2 (-1) ^ (n + 1) n / ((n + 2) (n - 2))`;
`a₀ = -4 sinh π / (5 π)`,
`aₙ = 4 (-1) ^ n (n ^ 2 - 5) sinh π / (π ((n + 2) ^ 2 + 1) ((n - 2) ^ 2 + 1))`,
`bₙ = 8 (-1) ^ n n sinh π / (π ((n - 2) ^ 2 + 1) ((n + 2) ^ 2 + 1))`;
`b₁ = (4 π ^ 2 - 3) / 12`, `b₃ = 5/24`,
`bₙ = 2 (-1) ^ n n (n ^ 4 - 6 n ^ 2 + 37) / ((n - 1) ^ 2 (n + 1) ^ 2 (n + 3) (n - 3))`
otherwise, `a₀ = aₙ = 0`; the sine series of `x (π - x)` on `[0, π]` has
`bₙ = 4 (1 - (-1) ^ n) / (n ^ 3 π)` and its cosine series `a₀ = π ^ 2 / 3`,
`aₙ = -2 (1 + (-1) ^ n) / n ^ 2`; on `[0, 1]`, `x` has `bₙ = 2 (-1) ^ (n + 1) / (n π)`; on
`[0, 2]`, `x ^ 2` has `a₀ = 8/3`, `aₙ = 16 (-1) ^ n / (n ^ 2 π ^ 2)`; and on `[0, π]`, `e ^ x`
has `bₙ = 2 n (1 - (-1) ^ n e ^ π) / (π (n ^ 2 + 1))`. The sixth theorem is

`∀ (n : ℕ), 0 < n → 2 / Real.pi * ∫ (x : ℝ) in 0..Real.pi, x * (Real.pi - x) * Real.sin (↑n * x) =`
`4 * (1 - (-1) ^ n) / (↑n ^ 3 * Real.pi)`.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [fourier x n]
Domain: x ∈ [-π, π], n ≥ 1
Input (scalar ℝ): (x * sin x)
Output (Fourier coefficients): a₀ = 2, aₙ = if n = 1 then -(1/2) else 2*(-1)^(n + 1)/((n + 1)*(n -
1)), bₙ = 0

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The Fourier coefficients on [-π, π], by integration by parts
        Proposition: 1 / Real.pi * ∫ (x : ℝ) in -Real.pi..Real.pi, x * Real.sin x = 2 ∧
          (∀ (n : ℕ),
              0 < n →
                1 / Real.pi * ∫ (x : ℝ) in -Real.pi..Real.pi, x * Real.sin x * Real.cos (↑n * x) =
                  if n = 1 then -(1 / 2) else 2 * (-1) ^ (n + 1) / ((↑n + 1) * (↑n - 1))) ∧
            ∀ (n : ℕ), 0 < n → 1 / Real.pi * ∫ (x : ℝ) in -Real.pi..Real.pi, x * Real.sin x *
Real.sin (↑n * x) = 0
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [fourier x n] (x * sin x)

/--
info: #cas [fourier x n]
Domain: x ∈ [-π, π], n ≥ 1
Input (scalar ℝ): (x^2 * exp x)
Output (Fourier coefficients): a₀ = 2*((pi^2 + 2)*sinh(pi) - 2*pi*cosh(pi))/pi, aₙ =
2*(-1)^n*((n^4*pi^2 + 2*n^2*pi^2 - 6*n^2 + pi^2 + 2)*sinh(pi) + (2*n^4*pi - 2*pi)*cosh(pi))/(pi*(n^2
+ 1)^3), bₙ = 2*(-1)^(n + 1)*n*((n^4*pi^2 + 2*n^2*pi^2 - 2*n^2 + pi^2 + 6)*sinh(pi) + (-(4*n^2*pi) -
4*pi)*cosh(pi))/(pi*(n^2 + 1)^3)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fourier x n] (x^2 * exp x)

/--
info: #cas [fourier x n]
Domain: x ∈ [-π, π], n ≥ 1
Input (scalar ℝ): (x * cos (2 * x))
Output (Fourier coefficients): a₀ = 0, aₙ = 0, bₙ = if n = 2 then -(1/4) else 2*(-1)^(n + 1)*n/((n +
2)*(n - 2))

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fourier x n] (x * cos (2 * x))

/--
info: #cas [fourier x n]
Domain: x ∈ [-π, π], n ≥ 1
Input (scalar ℝ): (exp x * sin (2 * x))
Output (Fourier coefficients): a₀ = -(4/5*sinh(pi)/pi), aₙ = 4*(-1)^n*(n^2 - 5)*sinh(pi)/(pi*((n +
2)^2 + 1)*((n - 2)^2 + 1)), bₙ = 8*(-1)^n*n*sinh(pi)/(pi*((n - 2)^2 + 1)*((n + 2)^2 + 1))

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fourier x n] (exp x * sin (2 * x))

/--
info: #cas [fourier x n]
Domain: x ∈ [-π, π], n ≥ 1
Input (scalar ℝ): (x ^ 2 * sin x + x * cos (3 * x))
Output (Fourier coefficients): a₀ = 0, aₙ = 0, bₙ = if n = 1 then 1/12*(4*pi^2 - 3) else if n = 3
then 5/24 else 2*(-1)^n*n*(n^4 - 6*n^2 + 37)/((n - 1)^2*(n + 1)^2*(n + 3)*(n - 3))

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fourier x n] (x ^ 2 * sin x + x * cos (3 * x))

/--
info: #cas [fourierSin x n pi]
Domain: x ∈ [0, pi], n ≥ 1
Input (scalar ℝ): (x * (pi - x))
Output (sine series coefficients): bₙ = 4*(1 - (-1)^n)/(n^3*pi)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fourierSin x n pi] (x * (pi - x))

/--
info: #cas [fourierCos x n pi]
Domain: x ∈ [0, pi], n ≥ 1
Input (scalar ℝ): (x * (pi - x))
Output (cosine series coefficients): a₀ = 1/3*pi^2, aₙ = -(2*(1 + (-1)^n)/n^2)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fourierCos x n pi] (x * (pi - x))

/--
info: #cas [fourierSin x n 1]
Domain: x ∈ [0, 1], n ≥ 1
Input (scalar ℝ): (x)
Output (sine series coefficients): bₙ = 2*(-1)^(n + 1)/(n*pi)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fourierSin x n 1] (x)

/--
info: #cas [fourierCos x n 2]
Domain: x ∈ [0, 2], n ≥ 1
Input (scalar ℝ): (x ^ 2)
Output (cosine series coefficients): a₀ = 8/3, aₙ = 16*(-1)^n/(n^2*pi^2)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fourierCos x n 2] (x ^ 2)

/--
info: #cas [fourierSin x n pi]
Domain: x ∈ [0, pi], n ≥ 1
Input (scalar ℝ): (exp x)
Output (sine series coefficients): bₙ = 2*n*(1 - (-1)^n*exp(pi))/(pi*(n^2 + 1))

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fourierSin x n pi] (exp x)


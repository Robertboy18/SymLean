/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Fourier coefficients on `[-π, π]`

`#cas [fourier x n] f` gives `a₀ = 1/π ∫ f`, `aₙ = 1/π ∫ f (x) cos (n x)` and
`bₙ = 1/π ∫ f (x) sin (n x)` for every `n ≥ 1` as exact functions of `n`, with a proof of the three
equations, for `f` a sum of products of polynomials, exponentials `e ^ (a x)`, sines and cosines
with integer frequencies. The proof writes `f` as a sum of terms `c xʲ e ^ (a x) cos (k x)` and
`c xʲ e ^ (a x) sin (k x)` and integrates them by parts (`CAS.FourierProduct.fourier_of_eq`).
When a term `c xʲ cos (k x)` or `c xʲ sin (k x)` has `k ≥ 1`, the coefficients at `n = k` come
out separately, as an `if`, unless the formula for general `n` gives them too. Each command runs
in the build inside `#guard_msgs`, which checks its report.

The outputs are `bₙ = 2 (-1) ^ (n + 1) / n` (and `a₀ = aₙ = 0`); `a₀ = 2 π ^ 2 / 3`,
`aₙ = 4 (-1) ^ n / n ^ 2`; `a₀ = 2 sinh π / π`, `aₙ = 2 (-1) ^ n sinh π / (π (n ^ 2 + 1))`,
`bₙ = 2 (-1) ^ (n + 1) n sinh π / (π (n ^ 2 + 1))`; `a₂ = 3` and `aₙ = 0` otherwise,
`b₁ = 2 π ^ 2 - 15` and `bₙ = 2 (-1) ^ n (6 + 2 n ^ 2 - n ^ 2 π ^ 2) / n ^ 3` otherwise;
`a₀ = 2 (3 π ^ 4 + 5 π ^ 2 + 15) / 15`, `aₙ = 4 (-1) ^ n (2 n ^ 2 π ^ 2 + n ^ 2 - 12) / n ^ 4`,
`bₙ = 2 (-1) ^ (n + 1) (n ^ 2 π ^ 2 + n ^ 2 - 6) / n ^ 3`; `b₁ = 3/4`, `b₃ = -1/4`; `a₀ = 1`,
`a₂ = 1/2`, `b₁ = -1/2`, `b₅ = 1/2`; for `sin x ^ 10`, `a₀ = 63/128`, `a₂ = -105/256`,
`a₄ = 15/64`, `a₆ = -45/512`, `a₈ = 5/256`, `a₁₀ = -1/512`; and for `x sin x ^ 10`,
`bₙ = 7257600 (-1) ^ n / (n (n ^ 2 - 4) (n ^ 2 - 16) (n ^ 2 - 36) (n ^ 2 - 64) (n ^ 2 - 100))`
for `n` other than `2, 4, 6, 8, 10`, whose values come out separately. The first report shows the
theorem in full.

More products, such as `x sin x` and `e ^ x sin (2 x)`, and the sine and cosine series on `[0, L]`
are in `FourierProduct.lean`.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [fourier x n]
Domain: x ∈ [-π, π], n ≥ 1
Input (scalar ℝ): (x)
Output (Fourier coefficients): a₀ = 0, aₙ = 0, bₙ = 2*(-1)^(n + 1)/n

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] The Fourier coefficients on [-π, π], by integration by parts
        Proposition: 1 / Real.pi * ∫ (x : ℝ) in -Real.pi..Real.pi, x = 0 ∧
          (∀ (n : ℕ), 0 < n → 1 / Real.pi * ∫ (x : ℝ) in -Real.pi..Real.pi, x * Real.cos (↑n * x) =
0) ∧
            ∀ (n : ℕ),
              0 < n → 1 / Real.pi * ∫ (x : ℝ) in -Real.pi..Real.pi, x * Real.sin (↑n * x) = 2 * (-1)
^ (n + 1) / ↑n
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [fourier x n] (x)

/--
info: #cas [fourier x n]
Domain: x ∈ [-π, π], n ≥ 1
Input (scalar ℝ): (x^2)
Output (Fourier coefficients): a₀ = 2/3*pi^2, aₙ = 4*(-1)^n/n^2, bₙ = 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fourier x n] (x^2)

/--
info: #cas [fourier x n]
Domain: x ∈ [-π, π], n ≥ 1
Input (scalar ℝ): (exp x)
Output (Fourier coefficients): a₀ = 2*sinh(pi)/pi, aₙ = 2*(-1)^n*sinh(pi)/(pi*(n^2 + 1)), bₙ =
2*(-1)^(n + 1)*n*sinh(pi)/(pi*(n^2 + 1))

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fourier x n] (exp x)

/--
info: #cas [fourier x n]
Domain: x ∈ [-π, π], n ≥ 1
Input (scalar ℝ): (x^3 - 2*x + 3*cos (2*x) + sin x)
Output (Fourier coefficients): a₀ = 0, aₙ = if n = 2 then 3 else 0, bₙ = if n = 1 then 2*pi^2 - 15
else 2*(-1)^n*(-(n^2*pi^2) + 2*n^2 + 6)/n^3

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fourier x n] (x^3 - 2*x + 3*cos (2*x) + sin x)

/--
info: #cas [fourier x n]
Domain: x ∈ [-π, π], n ≥ 1
Input (scalar ℝ): (1 + x + x^2 + x^3 + x^4)
Output (Fourier coefficients): a₀ = 2/15*(3*pi^4 + 5*pi^2 + 15), aₙ = 4*(-1)^n*(2*n^2*pi^2 + n^2 -
12)/n^4, bₙ = 2*(-1)^(n + 1)*(n^2*pi^2 + n^2 - 6)/n^3

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fourier x n] (1 + x + x^2 + x^3 + x^4)

/--
info: #cas [fourier x n]
Domain: x ∈ [-π, π], n ≥ 1
Input (scalar ℝ): (sin x ^ 3)
Output (Fourier coefficients): a₀ = 0, aₙ = 0, bₙ = if n = 3 then -(1/4) else if n = 1 then 3/4 else
0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fourier x n] (sin x ^ 3)

/--
info: #cas [fourier x n]
Domain: x ∈ [-π, π], n ≥ 1
Input (scalar ℝ): (cos x ^ 2 + sin (2 * x) * cos (3 * x))
Output (Fourier coefficients): a₀ = 1, aₙ = if n = 2 then 1/2 else 0, bₙ = if n = 5 then 1/2 else if
n = 1 then -(1/2) else 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fourier x n] (cos x ^ 2 + sin (2 * x) * cos (3 * x))

/--
info: #cas [fourier x n]
Domain: x ∈ [-π, π], n ≥ 1
Input (scalar ℝ): (sin x ^ 10)
Output (Fourier coefficients): a₀ = 63/128, aₙ = if n = 10 then -(1/512) else if n = 8 then 5/256
else if n = 6 then -(45/512) else if n = 4 then 15/64 else if n = 2 then -(105/256) else 0, bₙ = 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fourier x n] (sin x ^ 10)

/--
info: #cas [fourier x n]
Domain: x ∈ [-π, π], n ≥ 1
Input (scalar ℝ): (x * sin x ^ 10)
Output (Fourier coefficients): a₀ = 0, aₙ = 0, bₙ = if n = 10 then -(7381/2580480) else if n = 8
then 4609/258048 else if n = 6 then -(3069/57344) else if n = 4 then 319/3584 else if n = 2 then
-(77/1024) else 7257600*(-1)^n/(n*(n + 10)*(n - 10)*(n + 8)*(n - 8)*(n + 6)*(n - 6)*(n + 4)*(n -
4)*(n + 2)*(n - 2))

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fourier x n] (x * sin x ^ 10)


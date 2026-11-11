/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Taylor series and limits

`#cas [series x a n] f` prints the Taylor polynomial of degree `n` at a rational point with exact
coefficients and proves the expansion with a little-o remainder; `#cas [limit x → a] f` computes
limits, for quotients through the leading terms of numerator and denominator. Each command runs in
the build inside `#guard_msgs`, which checks its report.

The series are `1 + x + 1/2*x^2 + 1/6*x^3 + 1/24*x^4 + 1/120*x^5 + 1/720*x^6 + o(x^6)`,
`x - 1/6*x^3 + 1/120*x^5 - 1/5040*x^7 + o(x^7)`, `1 + x + x^2 + x^3 + x^4 + x^5 + o(x^5)`,
`x - 1 - 1/2*(x - 1)^2 + 1/3*(x - 1)^3 - 1/4*(x - 1)^4 + o((x - 1)^4)`,
`1/100 + 50*(x - 1/10000) - 125000*(x - 1/10000)^2 + o((x - 1/10000)^2)`,
`1 + x + 1/2*x^2 - 1/8*x^4 - 1/15*x^5 - 1/240*x^6 + o(x^6)`, `x - 1/3*x^3 + 1/5*x^5 + o(x^5)` and,
at the centre `-1/2`, `2/3 + 4/9*(x + 1/2) + 8/27*(x + 1/2)^2 + o((x + 1/2)^2)`; for the sine the
checked statement is

`(fun x ↦ Real.sin x - (x - 1 / 6 * x ^ 3 + 1 / 120 * x ^ 5 - 1 / 5040 * x ^ 7)) =o[nhds 0]`
`fun x ↦ x ^ 7`.

The limits are `1`, `1/2`, `2`, `1/2`, `1`, `sin(1)`, `1/100` and `2/3`, the first stated as
`Filter.Tendsto (fun x ↦ Real.sin x / x) (nhdsWithin 0 {0}ᶜ) (nhds 1)`. The last three are limits
at points of continuity, such as `Tendsto (fun x ↦ Real.sin x) (nhds 1) (nhds (Real.sin 1))`; the
points `1/10000` and `-1/2` are written as fractions.

The coefficients are the exact derivatives at the centre. The domain checker certifies them at the
centre alone, and the theorems extend their validity to a neighbourhood, so the square root
expands at `1/10000`. A quotient whose denominator vanishes at the centre has a Laurent series
(`CAS.Examples.Laurent`); Puiseux expansions are not available.

The compiled theorem below is the first limit, from the leading terms `1 · x` of `sin x` and of
`x`; the validity of the derivatives is checked by `simp`, and the coefficients by `cega`.
-/

public section

namespace CAS.Examples.Series

open Filter Topology CAS Verified.Expr

/-- `sin x / x → 1` as `x → 0`. -/
example :
    Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by
  have h := tendsto_div_of_check (.sin (.var 0)) (.var 0) 1 0
    (by intro k hk x _; interval_cases k <;> simp [iteratedDiff, diff])
    (by intro k hk x _; interval_cases k <;> simp [iteratedDiff, diff])
    1 1 1 (by cega)
  simpa [univariateEval] using h

end CAS.Examples.Series

end

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [series x 0 6]
Domain: x → 0
Input (scalar ℝ): (exp x)
Output (Taylor polynomial with exact coefficients): 1 + x + 1/2*x^2 + 1/6*x^3 + 1/24*x^4 + 1/120*x^5
+ 1/720*x^6 + o(x^6)

[CAS.Command.details] More details
  [CAS.Command.computation] Checked coefficients
    Coefficients of (x - 0)^0, …, ^6: [1, 1, 1/2, 1/6, 1/24, 1/120, 1/720]
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Taylor expansion with a little-o remainder
        Proposition: (fun x ↦
            Real.exp x -
              (1 + x + 1 / 2 * x ^ 2 + 1 / 6 * x ^ 3 + 1 / 24 * x ^ 4 + 1 / 120 * x ^ 5 + 1 / 720 *
x ^ 6)) =o[nhds 0]
          fun x ↦ x ^ 6
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [series x 0 6] (exp x)

/--
info: #cas [series x 0 7]
Domain: x → 0
Input (scalar ℝ): (sin x)
Output (Taylor polynomial with exact coefficients): x - 1/6*x^3 + 1/120*x^5 - 1/5040*x^7 + o(x^7)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [series x 0 7] (sin x)

/--
info: #cas [series x 0 5]
Domain: x → 0
Input (scalar ℝ): (1 / (1 - x))
Output (Taylor polynomial with exact coefficients): 1 + x + x^2 + x^3 + x^4 + x^5 + o(x^5)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [series x 0 5] (1 / (1 - x))

/--
info: #cas [series x 1 4]
Domain: x → 1
Input (scalar ℝ): (log x)
Output (Taylor polynomial with exact coefficients): x - 1 - 1/2*(x - 1)^2 + 1/3*(x - 1)^3 - 1/4*(x -
1)^4 + o((x - 1)^4)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [series x 1 4] (log x)

/--
info: #cas [series x 1/10000 2]
Domain: x → 1/10000
Input (scalar ℝ): (sqrt x)
Output (Taylor polynomial with exact coefficients): 1/100 + 50*(x - 1/10000) - 125000*(x -
1/10000)^2 + o((x - 1/10000)^2)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [series x 1/10000 2] (sqrt x)

/--
info: #cas [series x 0 6]
Domain: x → 0
Input (scalar ℝ): (exp (sin x))
Output (Taylor polynomial with exact coefficients): 1 + x + 1/2*x^2 - 1/8*x^4 - 1/15*x^5 - 1/240*x^6
+ o(x^6)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [series x 0 6] (exp (sin x))

/--
info: #cas [series x 0 5]
Domain: x → 0
Input (scalar ℝ): (atan x)
Output (Taylor polynomial with exact coefficients): x - 1/3*x^3 + 1/5*x^5 + o(x^5)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [series x 0 5] (atan x)

/--
info: #cas [series x -1/2 2]
Domain: x → -1/2
Input (scalar ℝ): (1 / (1 - x))
Output (Taylor polynomial with exact coefficients): 2/3 + 4/9*(x + 1/2) + 8/27*(x + 1/2)^2 +
o((x + 1/2)^2)

[CAS.Command.details] More details
-/
#guard_msgs (info, whitespace := lax, substring := true) in
#cas [series x -1/2 2] (1 / (1 - x))

/--
info: #cas [limit x → 0]
Domain: x → 0, x ≠ 0
Input (scalar ℝ): (sin x / x)
Output (exact limit): 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → 0] (sin x / x)

/--
info: #cas [limit x → 0]
Domain: x → 0, x ≠ 0
Input (scalar ℝ): ((1 - cos x) / x^2)
Output (exact limit): 1/2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → 0] ((1 - cos x) / x^2)

/--
info: #cas [limit x → 1]
Domain: x → 1, x ≠ 1
Input (scalar ℝ): ((x^2 - 1) / (x - 1))
Output (exact limit): 2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → 1] ((x^2 - 1) / (x - 1))

/--
info: #cas [limit x → 0]
Domain: x → 0, x ≠ 0
Input (scalar ℝ): ((exp x - 1 - x) / x^2)
Output (exact limit): 1/2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → 0] ((exp x - 1 - x) / x^2)

/--
info: #cas [limit x → 1]
Domain: x → 1, x ≠ 1
Input (scalar ℝ): (log x / (x - 1))
Output (exact limit): 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → 1] (log x / (x - 1))

/--
info: #cas [limit x → 1]
Domain: x → 1
Input (scalar ℝ): (sin x)
Output (limit, the value at the point): sin(1)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → 1] (sin x)

/--
info: #cas [limit x → 1/10000]
Domain: x → 1/10000
Input (scalar ℝ): (sqrt x)
Output (limit, the value at the point): 1/100

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → 1/10000] (sqrt x)

/--
info: #cas [limit x → -1/2]
Domain: x → -1/2
Input (scalar ℝ): (1 / (1 - x))
Output (limit, the value at the point): 2/3

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [limit x → -1/2] (1 / (1 - x))

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Requested digits in CEGA queries

The option `(digits := d)` makes every box enclosure try the precision-parametric evaluator
`DigitsEval.eval` first, at the working precision for `d` decimal digits, before the planner's
routes. The default policy has no digit request and runs the planner unchanged. The calculator
reads `π` as `Real.pi`.

The first theorem is closed by `cega (digits := d) [enclose]` on the closed expression. The
other two state their bounds with decimal literals: bare `cega` reads each literal as the exact
rational it denotes, and the evaluator rounds quotients relative to their magnitude, so a bound
of `1e-27` keeps every digit of the decimal it is compared with.
-/

public section

namespace CAS.Examples.CEGA.Digits

/-- Fifty digits of `π`, beyond the twenty digits of the default `π` enclosure. -/
theorem pi_fifty_digits :
    (31415926535897932384626433832795028841971693993751 / 10 ^ 49 : ℝ) ≤ Real.pi ∧
      Real.pi ≤ 31415926535897932384626433832795028841971693993752 / 10 ^ 49 := by
  cega (digits := 52) [enclose] Real.pi

/-- Twenty-seven decimals of `e`. -/
theorem e_decimal_digits : |Real.exp 1 - 2.718281828459045235360287471| < 1e-27 := by
  cega (digits := 30)

/-- Twenty-six decimals of `π`, within `1e-24`. -/
theorem pi_decimal_digits : |Real.pi - 3.14159265358979323846264338| < 1e-24 := by
  cega (digits := 30)

end CAS.Examples.CEGA.Digits

end

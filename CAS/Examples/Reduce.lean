/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Polynomial and rational inequalities

`#cas [reduce x]` solves a polynomial or rational inequality in one real variable exactly: the
solution set is a union of intervals whose endpoints are the real roots, rational roots exactly and
the others as `ρ j`, a real number located in an interval of width `10 ^ (-20)`. Each command
runs in the build inside `#guard_msgs`, which checks its report.

The outputs are `x < 1 ∨ 2 < x`; `ρ0 < x < ρ1, where ρ0 = -1.41421356237309504880…,
ρ1 = 1.41421356237309504880…`; `-1 ≤ x ≤ 0 ∨ 1 ≤ x`; `x ≤ -2 ∨ x = 1`; `True`;
`x < -2 ∨ 1 < x`; and `x < ρ0, where ρ0 = 1.16730397826141868425…`. Rational roots enter the
theorem as rationals, and with no irrational root there is no `ρ`: the first theorem is
`∀ (x : ℝ), 0 < x ^ 2 - 3 * x + 2 ↔ x < 1 ∨ 2 < x`. The second is

`∃ ρ, ((-141421356237309504881 / 10 ^ 20 < ρ 0 ∧ ρ 0 < -141421356237309504880 / 10 ^ 20) ∧`
`141421356237309504880 / 10 ^ 20 < ρ 1 ∧ ρ 1 < 141421356237309504881 / 10 ^ 20) ∧`
`∀ (x : ℝ), x ^ 2 < 2 ↔ ρ 0 < x ∧ x < ρ 1`,

and the rational inequality is stated for the quotient,
`∀ (x : ℝ), 0 < (x - 1) / (x + 2) ↔ x < -2 ∨ 1 < x`. At `x = -2` Lean's quotient is `0`, so the
endpoint is excluded as it should be. The quartic `(x - 1) (x - 2) (x - 3) (x - 4) > 0` gives
`x < 1 ∨ 2 < x < 3 ∨ 4 < x`.

`#cas [solve x]` takes an equation of any degree. `x ^ 3 - 2 = 0` gives `x = ρ0` with `ρ0` the
root of `x^3 - 2` in an interval of width `10 ^ (-8)`, and the theorem names it exactly as
`AlgRoot.real`; `x ^ 2 = 2` gives `x = √2 ∨ x = -√2`. Bare `cas` proves the sign of a polynomial
on a closed interval from the same root list, with the endpoints as cell boundaries, so a zero at
an endpoint or a double root inside the interval does not stop it.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [reduce x]
Domain: x ∈ ℝ
Input (polynomial relation): (x^2 - 3*x + 2 > 0)
Output (equivalent condition on the real roots): x < 1 ∨ 2 < x

[CAS.Command.details] More details
  [CAS.Command.computation] Certified roots
    2 real roots of the polynomial, 1 cell; cuts [0, 3/2, 3]; signs [true, false, true]
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Solution set for every real value
        Proposition: ∀ (x : ℝ), 0 < x ^ 2 - 3 * x + 2 ↔ x < 1 ∨ 2 < x
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [reduce x] (x^2 - 3*x + 2 > 0)

/--
info: #cas [reduce x]
Domain: x ∈ ℝ
Input (polynomial relation): (x^2 < 2)
Output (equivalent condition on the real roots): ρ0 < x < ρ1, where ρ0 = -1.41421356237309504880…,
ρ1 = 1.41421356237309504880…

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [reduce x] (x^2 < 2)

/--
info: #cas [reduce x]
Domain: x ∈ ℝ
Input (polynomial relation): (x^3 - x ≥ 0)
Output (equivalent condition on the real roots): -1 ≤ x ≤ 0 ∨ 1 ≤ x

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [reduce x] (x^3 - x ≥ 0)

/--
info: #cas [reduce x]
Domain: x ∈ ℝ
Input (polynomial relation): ((x - 1)^2 * (x + 2) ≤ 0)
Output (equivalent condition on the real roots): x ≤ -2 ∨ x = 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [reduce x] ((x - 1)^2 * (x + 2) ≤ 0)

/--
info: #cas [reduce x]
Domain: x ∈ ℝ
Input (polynomial relation): (x^2 + 1 > 0)
Output (equivalent condition on the real roots): True

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [reduce x] (x^2 + 1 > 0)

/--
info: #cas [reduce x]
Domain: x ∈ ℝ
Input (rational relation): ((x - 1) / (x + 2) > 0)
Output (equivalent condition on the real roots): x < -2 ∨ 1 < x

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [reduce x] ((x - 1) / (x + 2) > 0)

/--
info: #cas [reduce x]
Domain: x ∈ ℝ
Input (polynomial relation): (x^5 - x - 1 < 0)
Output (equivalent condition on the real roots): x < ρ0, where ρ0 = 1.16730397826141868425…

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [reduce x] (x^5 - x - 1 < 0)


/--
info: #cas [reduce x]
Domain: x ∈ ℝ
Input (polynomial relation): ((x - 1) * (x - 2) * (x - 3) * (x - 4) > 0)
Output (equivalent condition on the real roots): x < 1 ∨ 2 < x < 3 ∨ 4 < x

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [reduce x] ((x - 1) * (x - 2) * (x - 3) * (x - 4) > 0)

/-! ## Equations of any degree -/

/--
info: #cas [solve x]
Domain: x ∈ ℝ
Input (real relation): (x ^ 3 - 2 = 0)
Output (equivalent real solution predicate): x = ρ0
ρ0: the root of x^3 - 2 in (1.25992104, 1.25992105)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x] (x ^ 3 - 2 = 0)

/--
info: #cas [solve x]
Domain: x ∈ ℝ
Input (real relation): (x ^ 2 = 2)
Output (equivalent real solution predicate): x = sqrt(2) ∨ x = -sqrt(2)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x] (x ^ 2 = 2)

/--
info: #cas [solve x]
Domain: x ∈ ℝ
Input (real relation): (x = 1)
Output (equivalent real solution predicate): x = 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x] (x = 1)

/--
info: #cas [solve x]
Domain: x ∈ ℝ
Input (real relation): x = 1
Output (equivalent real solution predicate): x = 1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [solve x] x = 1

/-! ## Signs on an interval -/

/-- The minimum `0` of `x ^ 2 + x` on `[0, 2]` is at the endpoint `0`. -/
example : ∀ x ∈ Set.Icc (0 : ℝ) 2, 0 ≤ x ^ 2 + x := by cas

public section

namespace CAS.Examples.Reduce

/-- `-x ^ 3 + 6 x ^ 2 - 9 x + 4 = (x - 1) ^ 2 (4 - x)` touches `0` at the interior point `1`. -/
theorem nonneg_touching_on_Icc : ∀ x ∈ Set.Icc (0 : ℝ) 3, 0 ≤ -x ^ 3 + 6 * x ^ 2 - 9 * x + 4 := by
  cas

end CAS.Examples.Reduce

end

/-- info: 'CAS.Examples.Reduce.nonneg_touching_on_Icc' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CAS.Examples.Reduce.nonneg_touching_on_Icc

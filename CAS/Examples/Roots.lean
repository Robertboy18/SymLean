/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# All real roots of a polynomial

`#cas [roots x] (p = q)` lists every real solution of a polynomial equation with rational
coefficients, of any degree, with rational solutions given exactly and the others by certified
decimals, and proves that the list is complete. Each command runs in the build inside `#guard_msgs`,
which checks its report.

The outputs are `2.09455148154232659148` (Wallis's cubic), `1.16730397826141868425`,
`-2, 1, -1.41421356237309504880, 1.41421356237309504880` (the rational roots `-2` and the double
root `1` are split off before the cover), `no real solutions`, the two square roots of `2` to 40
decimals, `1, 2, 3, 4` for a product of four linear factors, and the exact roots `±1/10^15` and
`±1/10^20` of `x^2 = 1/10^30` and `x^2 = 1/10^40`, which are read off narrow isolating intervals.
For the cubic the checked theorem is

`(∃! x, x ∈ Set.Ioo (209455148154232659148 / 10 ^ 20) (209455148154232659149 / 10 ^ 20)`
`∧ x ^ 3 - 2 * x - 5 = 0) ∧ ∀ (x : ℝ), x ^ 3 - 2 * x - 5 = 0 → x ∈ Set.Ioo … …`.

The compiled theorem below is the same statement for the quintic `x ^ 5 - x - 1`, whose root
the classical formula cannot express, with the certificate that the command finds: no rational
root, the quintic itself as the polynomial to cover, the Cauchy bound `3` from
`x ^ 5 = x + 1`, and a cover of `[-3, 3]` by six root-free cells and one refined root cell. `cega`
evaluates the single Boolean check in the kernel, which multiplies out the identities and checks
each cell.
-/

public section

namespace CAS.Examples.Roots

open CAS CAS.Polynomial.RealRoot

/-- `x ^ 5 - x - 1` has exactly one real root, `1.1673…`. -/
theorem quintic_roots :
    (∃! x : ℝ, x ∈ Set.Ioo (11673 / 10000 : ℝ) (11674 / 10000) ∧ x ^ 5 - x - 1 = 0) ∧
      ∀ x : ℝ, x ^ 5 - x - 1 = 0 → x ∈ Set.Ioo (11673 / 10000 : ℝ) (11674 / 10000) := by
  have h := of_exprRootCheck (expr := .sub (.sub (.pow (.var 0) 5) (.var 0)) (.nat 1))
    (cert :=
      { content := 1, roots := [], quotient := [-1, -1, 0, 0, 0, 1],
        bound := ⟨1, 5, [(-1, fun _ ↦ 1), (-1, fun _ ↦ 0)]⟩,
        cells := [(-3 / 2, .free), (-9 / 8, .free), (-3 / 4, .free), (0, .free), (3 / 4, .free),
          (3 / 2, .root .increasing (11673 / 10000) (11674 / 10000)), (3, .free)] })
    (intervals := [(11673 / 10000, 11674 / 10000)]) (points := []) (by cega)
  simpa using h

end CAS.Examples.Roots

end

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [roots x]
Domain: x ∈ ℝ
Input (polynomial equation): (x^3 - 2*x - 5 = 0)
Output (the only real solution, by 20 decimals, truncated): 2.09455148154232659148

[CAS.Command.details] More details
  [CAS.Command.computation] Certified isolation
    Square-free polynomial of degree 3, Cauchy bound 8, 6 cells
    Guarantee: the listed solutions are distinct, each rational is a solution, each decimal interval
contains exactly one solution, and there are no other real solutions
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Complete list of real solutions
        Proposition: (∃! x,
            x ∈ Set.Ioo (209455148154232659148 / 10 ^ 20) (209455148154232659149 / 10 ^ 20) ∧ x ^ 3
- 2 * x - 5 = 0) ∧
          ∀ (x : ℝ),
            x ^ 3 - 2 * x - 5 = 0 → x ∈ Set.Ioo (209455148154232659148 / 10 ^ 20)
(209455148154232659149 / 10 ^ 20)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Polynomial.RealRoot.of_exprRootCheck
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [roots x] (x^3 - 2*x - 5 = 0)

/--
info: #cas [roots x]
Domain: x ∈ ℝ
Input (polynomial equation): (x^5 - x - 1)
Output (the only real solution, by 20 decimals, truncated): 1.16730397826141868425

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [roots x] (x^5 - x - 1)

/--
info: #cas [roots x]
Domain: x ∈ ℝ
Input (polynomial equation): ((x - 1)^2 * (x + 2) * (x^2 - 2))
Output (all 4 real solutions; enclosed ones by 20 decimals, truncated): -2, 1,
-1.41421356237309504880, 1.41421356237309504880

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [roots x] ((x - 1)^2 * (x + 2) * (x^2 - 2))

/--
info: #cas [roots x]
Domain: x ∈ ℝ
Input (polynomial equation): (x^2 + 1)
Output (complete list of real solutions): no real solutions

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [roots x] (x^2 + 1)

/--
info: #cas (digits := 40) [roots x]
Domain: x ∈ ℝ
Input (polynomial equation): (x^2 = 2)
Output (all 2 real solutions; enclosed ones by 40 decimals, truncated):
-1.4142135623730950488016887242096980785696, 1.4142135623730950488016887242096980785696

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (digits := 40) [roots x] (x^2 = 2)

/--
info: #cas [roots x]
Domain: x ∈ ℝ
Input (polynomial equation): ((x-1)*(x-2)*(x-3)*(x-4) = 0)
Output (all 4 real solutions): 1, 2, 3, 4

[CAS.Command.details] More details
  [CAS.Command.computation] Certified isolation
    4 rational roots split off; the remaining factor is constant
-/
#guard_msgs (info, substring := true) in
#cas [roots x] ((x-1)*(x-2)*(x-3)*(x-4) = 0)

/--
info: #cas [roots x]
Domain: x ∈ ℝ
Input (polynomial equation): (x^2 = 1/10^30)
Output (all 2 real solutions): -1/1000000000000000, 1/1000000000000000

[CAS.Command.details] More details
  [CAS.Command.computation] Certified isolation
    2 rational roots split off; the remaining factor is constant
-/
#guard_msgs (info, substring := true) in
#cas [roots x] (x^2 = 1/10^30)

/--
info: #cas [roots x]
Domain: x ∈ ℝ
Input (polynomial equation): (x^2 = 1/10^40)
Output (all 2 real solutions): -1/100000000000000000000, 1/100000000000000000000

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [roots x] (x^2 = 1/10^40)

/-- info: 'CAS.Examples.Roots.quintic_roots' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CAS.Examples.Roots.quintic_roots

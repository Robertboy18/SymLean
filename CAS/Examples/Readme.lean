/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# The outputs that the README prints

Each `#guard_msgs` below pins an output that `README.md` quotes or describes, so that a change of
the output fails the build: the conditional answer of `#cas [simplify]` and the hypothesis
`x * x - 1 ≠ 0` of its theorem, the report of `#cas [roots x]` with the root and the proposition
the kernel checked, the refusal of Fateman's integral `∫₋₁¹ 1 / x²` with its values, the refusal
on SymPy's integrand `√(2 - x) √(1 / (2 - x))`, and `cas` on `x / x = 1`, which needs `x ≠ 0` and
names it when it is missing. The axioms of the fast-profile theorem `fast_rows` are pinned in
`tests/cega/Readme.lean`, since `cega.nativeCertificates` puts native axioms into the module that
uses it.
-/

set_option linter.hashCommand false

/-! ## `#cas [simplify]`: the answer, its condition and the hypothesis of its theorem -/

/--
info: #cas [simplify]
Domain: x ∈ ℝ
Input (scalar ℝ): ((x ^ 4 - 1) / (x ^ 2 - 1))
Output (scalar ℝ): x^2 + 1
Conditions: x^2 - 1 ≠ 0

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked symbolic computation
    Raw checked nonzero requirements: x^2 - 1
    Guarantee: these assumptions justify conditional rewrites and preserve real evaluation
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the simplified form
        Proposition: ∀ (x : ℝ), x * x - 1 ≠ 0 → (x ^ 4 - 1) / (x ^ 2 - 1) = x ^ 2 + 1
-/
#guard_msgs (info, substring := true) in
#cas [simplify] ((x ^ 4 - 1) / (x ^ 2 - 1))

/-! ## `#cas [roots x]`: the root, and what the kernel checked -/

/--
info: #cas [roots x]
Domain: x ∈ ℝ
Input (polynomial equation): (x ^ 5 - x - 1 = 0)
Output (the only real solution, by 20 decimals, truncated): 1.16730397826141868425

[CAS.Command.details] More details
  [CAS.Command.computation] Certified isolation
    Square-free polynomial of degree 5, Cauchy bound 3, 7 cells
    Guarantee: the listed solutions are distinct, each rational is a solution, each decimal
    interval contains exactly one solution, and there are no other real solutions
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Complete list of real solutions
        Proposition: (∃! x,
            x ∈ Set.Ioo (116730397826141868425 / 10 ^ 20) (116730397826141868426 / 10 ^ 20) ∧
            x ^ 5 - x - 1 = 0) ∧
          ∀ (x : ℝ), x ^ 5 - x - 1 = 0 →
          x ∈ Set.Ioo (116730397826141868425 / 10 ^ 20) (116730397826141868426 / 10 ^ 20)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Polynomial.RealRoot.of_exprRootCheck
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs (whitespace := lax) in
#cas [roots x] (x ^ 5 - x - 1 = 0)

/-! ## The refusals on the integrals of the README's "Why" -/

/--
error: `cas` did not prove the value -2 of the integral: it could not prove that the conditions of
the primitive -(1/x) hold on the interval (x ≠ 0). Where they fail, the difference of the
primitive's values at the endpoints need not be the integral. For a numerical value use `#cas
[nintegrate x in [-1, 1]] (1 / x ^ 2)`.
-/
#guard_msgs (whitespace := lax) in
#cas [integrate x in [-1, 1]] (1 / x ^ 2)

/--
error: the checked integrator found no supported antiderivative in coordinate 'x', so the
integral has no exact value here. For a numerical value use `#cas [nintegrate x in [0, 1]] (sqrt
(2 - x) * sqrt (1 / (2 - x)))`.
-/
#guard_msgs (whitespace := lax) in
#cas [integrate x in [0, 1]] (sqrt (2 - x) * sqrt (1 / (2 - x)))

/-! ## `cas` on `x / x = 1` -/

@[expose] public section

namespace CAS.Examples.Readme

/-- `x / x = 1` for real `x ≠ 0`, the hypothesis `hx` taken from the context. -/
theorem div_self_of_ne (x : ℝ) (hx : x ≠ 0) : x / x = 1 := by
  cas

/-- info: 'CAS.Examples.Readme.div_self_of_ne' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms div_self_of_ne

end CAS.Examples.Readme

end

-- Without `hx`, `cas` fails and names the missing hypothesis `x ≠ 0`.
/--
error: cas could not close this ordinary arithmetic goal.
This goal contains branch-sensitive operations and may need nonzero denominator hypotheses. Put
those facts in the local context; pass one explicit fact as `cas using h` when needed. The
corresponding `#cas [simplify]` report shows the exact generated conditions. Detected candidate
conditions: x ≠ 0.
-/
#guard_msgs (error, whitespace := lax, substring := true) in
example (x : ℝ) : x / x = 1 := by
  cas

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Headline theorems of `#cas` reports

The first checked step of a `#cas` report states its result about the input as written, in
Mathlib's terms: for `simplify` the identity of the input with its simplified form, for `derive x`
the `HasDerivAt` statement of the displayed derivative under the checked conditions, for `grad`
the `HasGradientAt` statement of the displayed gradient, for `integrate x` the integral of the
input over every interval from `a` to `b`, and for `enclose` the certified bounds for every point
`x ∈ Set.Icc a b` of the box or for the closed expression. The digits, the Gaussian integrals and
the derivatives of `erf` open with their theorems in the same way. The `Theorem:` line of the step
names the lemma its proof applies: the lemma that transports the statement from the checked
certificate, whose reflected statements follow it, and for `erf` the theorem of the backend. The
rule tree of a derivative shows only under `set_option cas.verbose true`. The hypotheses of the
statement are the checked conditions, which the `Conditions` line prints in its display form: the
hypothesis `0 < 2 * x + 2` of the derivative of `sqrt (2 * x + 2)` reads `x + 1 > 0` there.

The statement names a function such as `Real.tan`, `|x|` or `Real.sinh` in the input exactly where
the user applied it, so that a form written out stays written out, and in the result where the
result has its form and the input applies the function somewhere. The `Output` line follows the
rule of the result. A condition on a polynomial is printed in descending powers, and a negated term
after `+` or `-` as a subtraction or an addition, by a rewrite that the kernel checks with the
step. The base and the exponent of a power whose exponent is not a natural number print with their
type when they are closed numeric terms, numerals combined by `+`, `-`, `*`, `/`, `^` and casts, as
in `x ^ (3 / 2 : ℝ)` and `x ^ (2 ^ 2 / 3 ^ 2 : ℝ)`, since a pasted `x ^ (3 / 2)` would be a natural
power, and so do the powers inside such a term, as in `x ^ ((4 : ℝ) ^ (1 / 2 : ℝ) : ℝ)`. Each
command runs in the build inside `#guard_msgs`, which checks its whole report. The last section
prints terms whose casts hide operations that real arithmetic would read otherwise.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [simplify]
Domain: x ∈ ℝ
Input (scalar ℝ): (x + x)
Output (scalar ℝ): 2*x

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked symbolic computation
    Raw checked nonzero requirements: (none)
    Guarantee: these assumptions justify conditional rewrites and preserve real evaluation
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the simplified form
        Proposition: ∀ (x : ℝ), x + x = 2 * x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.eq_of_simplifyFinDisplayRoute
      [CAS.explanation.checkedStep] Simplification under generated rewrite assumptions
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ (𝕏[0].add 𝕏[0]).simplifyFinDisplayRoute.nonzero →
            CAS.Verified.Expr.eval ρ (𝕏[0].add 𝕏[0]).simplifyFinDisplayRoute.rhs =
              CAS.Verified.Expr.eval ρ (𝕏[0].add 𝕏[0]).simplifyFinDisplayRoute.lhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.SideClaimRoute.sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] pre-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] base normalization: structural: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: trig: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: algebra: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: factor-common: attempted
        checked
      [CAS.explanation.plannerStep] post-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: fraction-normal-form: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: rational-side: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-square: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-numeral: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-product-collect: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: common-add-factor: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: unit-ratio: attempted
        side-conditioned
      [CAS.explanation.plannerStep] direct: univariate-rational-canonical: attempted
        side-conditioned
-/
#guard_msgs in
#cas [simplify] (x + x)

set_option linter.style.longLine false in
/--
info: #cas [enclose x in [0, 1]]
Domain: x ∈ [0, 1] ⊆ ℝ
Input (scalar map ℝ → ℝ): (x ^ 2 - x)
Output (certified interval in ℝ): [-1/4, 0]
Upper bound: 0
Absolute bound: 1/4
Center and radius: -1/8 ± 1/8

[CAS.Command.details] More details
  Coordinates: x
  Certified domain: x ∈ [0, 1] ⊆ ℝ
  [CAS.Command.computation] Certified numerical guarantee
    Guarantee: the input lies in the output interval throughout the box
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of the input
        Proposition: ∀ x ∈ Set.Icc 0 1, -1 / 4 ≤ x ^ 2 - x ∧ x ^ 2 - x ≤ 0
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.mem_of_enclosedOn_box
      [CAS.explanation.checkedStep] Upper bound of the input
        Proposition: ∀ x ∈ Set.Icc 0 1, x ^ 2 - x ≤ 0
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.le_of_boundOn_box
      [CAS.explanation.checkedStep] Absolute bound of the input
        Proposition: ∀ x ∈ Set.Icc 0 1, |x ^ 2 - x| ≤ 1 / 4
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.abs_le_of_boundOn_abs_box
      [CAS.explanation.checkedStep] Center and radius of the input
        Proposition: ∀ x ∈ Set.Icc 0 1, |x ^ 2 - x + 1 / 8| ≤ 1 / 8
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.abs_sub_le_of_approxOn_box
      [CAS.explanation.checkedStep] Certified enclosure
        Proposition: CAS.Certificate.EnclosedOn (CAS.Exact.exprFn ((𝕏[0].pow 2).sub 𝕏[0]))
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 0 1 ⋯].get coordinate)
          (↑(-1) / ↑4) (↑0 / ↑1)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.enclosedOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified upper bound
        Proposition: CAS.Certificate.BoundOn (CAS.Exact.exprFn ((𝕏[0].pow 2).sub 𝕏[0]))
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 0 1 ⋯].get coordinate)
          (↑0 / ↑1)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified absolute bound
        Proposition: CAS.Certificate.BoundOn (fun x ↦ |CAS.Exact.exprFn ((𝕏[0].pow 2).sub 𝕏[0]) x|)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 0 1 ⋯].get coordinate)
          (↑1 / ↑4)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_abs_of_interval_eq
      [CAS.explanation.checkedStep] Certified center and radius
        Proposition: CAS.Certificate.ApproxOn (CAS.Exact.exprFn ((𝕏[0].pow 2).sub 𝕏[0])) (fun x ↦ ↑(-1) / ↑8)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 0 1 ⋯].get coordinate)
          (↑1 / ↑8)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.approxOn_center_of_interval_eq
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] affine arithmetic: succeeded
-/
#guard_msgs in
#cas [enclose x in [0, 1]] (x ^ 2 - x)

set_option linter.style.longLine false in
/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (sqrt (2 * x + 2))
Output (scalar ℝ): 1/sqrt(2*x + 2)
Conditions: x + 1 > 0

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Analytic domain conditions
    Raw checked nonzero requirements: (none)
    Raw checked positivity requirements: 2*x + 2
  [CAS.Command.computation] Partial derivative in x
    [CAS.Command.computation] 1. Apply symbolic differentiation rules
      raw result: (0*x + 2*1 + 0)/(2*sqrt(2*x + 2))
    [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
      normalized result: 1/sqrt(2*x + 2)
    [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
      displayed result: 1/sqrt(2*x + 2)
      additional nonzero requirements: (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Derivative of the input
        Proposition: ∀ (x : ℝ), 0 < 2 * x + 2 → HasDerivAt (fun x ↦ √(2 * x + 2)) (1 / √(2 * x + 2)) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.hasDerivAt_of_displayRoute
      [CAS.explanation.checkedStep] Partial derivative in x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0
              (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt).rawDerivative =
          CAS.Verified.Expr.diff 0 (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Partial derivative in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Partial derivative in x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 0
                    (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt)).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt)).rhs =
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 0
                    (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Partial derivative in x: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^1),
          CAS.Verified.Expr.ValidAt x.ofLp (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt)).nonzero →
              (fderiv ℝ
                    (fun y ↦
                      CAS.Verified.Expr.eval y.ofLp
                        (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt)
                    x)
                  (EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 0
                        (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt)).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [derive x] (sqrt (2 * x + 2))

set_option linter.style.longLine false in
/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (sqrt (2 * x + 2))
Output (scalar ℝ): 1/sqrt(2*x + 2)
Conditions: x + 1 > 0

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Analytic domain conditions
    Raw checked nonzero requirements: (none)
    Raw checked positivity requirements: 2*x + 2
  [CAS.Command.computation] Partial derivative in x
    [CAS.Command.computation] 1. Apply symbolic differentiation rules
      raw result: (0*x + 2*1 + 0)/(2*sqrt(2*x + 2))
      [CAS.Command.computation] square-root chain rule
        input: sqrt(2*x + 2)
        raw derivative: (0*x + 2*1 + 0)/(2*sqrt(2*x + 2))
        representation: indexed DiffDerivation node
        [CAS.Command.computation] sum rule
          input: 2*x + 2
          raw derivative: 0*x + 2*1 + 0
          representation: indexed DiffDerivation node
          [CAS.Command.computation] product rule
            input: 2*x
            raw derivative: 0*x + 2*1
            representation: indexed DiffDerivation node
            [CAS.Command.computation] constant rule
              input: 2
              raw derivative: 0
              representation: indexed DiffDerivation node
            [CAS.Command.computation] variable rule
              input: x
              raw derivative: 1
              representation: indexed DiffDerivation node
          [CAS.Command.computation] constant rule
            input: 2
            raw derivative: 0
            representation: indexed DiffDerivation node
    [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
      normalized result: 1/sqrt(2*x + 2)
    [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
      displayed result: 1/sqrt(2*x + 2)
      additional nonzero requirements: (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Derivative of the input
        Proposition: ∀ (x : ℝ), 0 < 2 * x + 2 → HasDerivAt (fun x ↦ √(2 * x + 2)) (1 / √(2 * x + 2)) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.hasDerivAt_of_displayRoute
      [CAS.explanation.checkedStep] Partial derivative in x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0
              (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt).rawDerivative =
          CAS.Verified.Expr.diff 0 (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Partial derivative in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Partial derivative in x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 0
                    (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt)).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt)).rhs =
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 0
                    (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Partial derivative in x: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^1),
          CAS.Verified.Expr.ValidAt x.ofLp (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt)).nonzero →
              (fderiv ℝ
                    (fun y ↦
                      CAS.Verified.Expr.eval y.ofLp
                        (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt)
                    x)
                  (EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 0
                        (((CAS.Verified.Expr.nat 2).mul 𝕏[0]).add (CAS.Verified.Expr.nat 2)).sqrt)).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
set_option cas.verbose true in
#cas [derive x] (sqrt (2 * x + 2))

set_option linter.style.longLine false in
/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (x * exp x)
Output (scalar ℝ; antiderivative): exp(x)*(x - 1)

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked antiderivative computation
    [CAS.Command.computation] 1. Differentiate the proposed primitive
      Raw derivative: exp(x)*1*(x - 1) + exp(x)*(1 + 0)
    [CAS.Command.computation] 2. Form the derivative residual
      Raw residual: exp(x)*1*(x - 1) + exp(x)*(1 + 0) - x*exp(x)
      Definition: CAS.IntegrationCheck.residual
    [CAS.Command.computation] 3. Check the residual normal form
      Checked residual normal form: 0
      Certificate condition: checked residual normal form = 0
    [CAS.Command.computation] 4. Record analytic domain requirements
      Certificate nonzero requirements (compacted): (none)
      Certificate positivity requirements (compacted): (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Integral of the input
        Proposition: ∀ (a b : ℝ), ∫ (x : ℝ) in a..b, x * Real.exp x = Real.exp b * (b - 1) - Real.exp a * (a - 1)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_of_line
      [CAS.explanation.checkedStep] Primitive derivative in x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0
              (𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1))))).rawDerivative =
          CAS.Verified.Expr.diff 0 (𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1))))
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Primitive derivative in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  (𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1))))).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  (𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1))))).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Primitive derivative in x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 0
                    (𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1)))))).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      (𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1)))))).rhs =
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 0
                    (𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1))))).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Primitive derivative in x: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^1),
          CAS.Verified.Expr.ValidAt x.ofLp (𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1)))) →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      (𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1)))))).nonzero →
              (fderiv ℝ (fun y ↦ CAS.Verified.Expr.eval y.ofLp (𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1)))))
                    x)
                  (EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 0
                        (𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1)))))).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
      [CAS.explanation.checkedStep] Residual route reaches zero
        Proposition: (CAS.IntegrationCheck.route 0 (𝕏[0].mul 𝕏[0].exp)
              { candidate := 𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1))), routeZero := ⋯ }.candidate).rhs =
          0
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.routeZero
      [CAS.explanation.checkedStep] Symbolic antiderivative identity under the displayed requirements
        Proposition: ∀ (x : ℝ^1),
          { candidate := 𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1))), routeZero := ⋯ }.requirements.Holds
              x.ofLp →
            CAS.Verified.Expr.eval x.ofLp
                (CAS.Verified.Expr.diff 0
                  { candidate := 𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1))), routeZero := ⋯ }.candidate) =
              CAS.Verified.Expr.eval x.ofLp (𝕏[0].mul 𝕏[0].exp)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.eval_diff_eq
      [CAS.explanation.checkedStep] Coordinate-line derivative theorem
        Proposition: ∀ (x : ℝ^1) (t : ℝ),
          { candidate := 𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1))), routeZero := ⋯ }.requirements.Holds
              (x.ofLp + t • (EuclideanSpace.single 0 1).ofLp) →
            HasDerivAt
              (fun s ↦
                CAS.Verified.Expr.eval (x + s • EuclideanSpace.single 0 1).ofLp
                  { candidate := 𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1))), routeZero := ⋯ }.candidate)
              (CAS.Verified.Expr.eval (x + t • EuclideanSpace.single 0 1).ofLp (𝕏[0].mul 𝕏[0].exp)) t
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.hasDerivAt_eval_add_smul_single
      [CAS.explanation.checkedStep] Coordinate-line fundamental theorem of calculus
        Proposition: ∀ (x : ℝ^1) (a b : ℝ),
          (∀ t ∈ Set.uIcc a b,
              { candidate := 𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1))), routeZero := ⋯ }.requirements.Holds
                (x.ofLp + t • (EuclideanSpace.single 0 1).ofLp)) →
            ∫ (t : ℝ) in a..b, CAS.Verified.Expr.eval (x + t • EuclideanSpace.single 0 1).ofLp (𝕏[0].mul 𝕏[0].exp) =
              CAS.Verified.Expr.eval (x + b • EuclideanSpace.single 0 1).ofLp
                  { candidate := 𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1))), routeZero := ⋯ }.candidate -
                CAS.Verified.Expr.eval (x + a • EuclideanSpace.single 0 1).ofLp
                  { candidate := 𝕏[0].exp.mul (𝕏[0].add (CAS.Verified.Expr.int (-1))), routeZero := ⋯ }.candidate
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_eval_add_smul_single
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] direct: ordered-sparse-polynomial: attempted
        checked
      [CAS.explanation.plannerStep] direct: pythagorean: attempted
        checked
      [CAS.explanation.plannerStep] direct: algebra: attempted
        checked
      [CAS.explanation.plannerStep] direct: pythagorean: attempted
        checked
      [CAS.explanation.plannerStep] direct: algebra: attempted
        checked
-/
#guard_msgs in
#cas [integrate x] (x * exp x)

set_option linter.style.longLine false in
/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (1 / (x ^ 6 + 3 * x ^ 4 + 4 * x ^ 3 + 2 * x ^ 2 + 5 * x + 3))
Output (scalar ℝ): -((6*x^5 + 12*x^3 + 12*x^2 + 4*x + 5)/(x^6 + 3*x^4 + 4*x^3 + 2*x^2 + 5*x + 3)^2)
Conditions: x^6 + 3*x^4 + 4*x^3 + 2*x^2 + 5*x + 3 ≠ 0

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Analytic domain conditions
    Raw checked nonzero requirements: x^6 + 3*x^4 + 4*x^3 + 2*x^2 + 5*x + 3
    Raw checked positivity requirements: (none)
  [CAS.Command.computation] Partial derivative in x
    [CAS.Command.computation] 1. Apply symbolic differentiation rules
      raw result: (0*(x^6 + 3*x^4 + 4*x^3 + 2*x^2 + 5*x + 3) - 1*(6*x^5*1 + 0*x^4 + 3*4*x^3*1 + 0*x^3 + 4*3*x^2*1 + 0*x^2 + 2*2*x^1*1 + 0*x + 5*1 + 0))/(x^6 + 3*x^4 + 4*x^3 + 2*x^2 + 5*x + 3)^2
    [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
      normalized result: -((6*x^5 + 12*x^3 + 12*x^2 + 4*x + 5)/(x^6 + 3*x^4 + 4*x^3 + 2*x^2 + 5*x + 3)^2)
    [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
      displayed result: -((6*x^5 + 12*x^3 + 12*x^2 + 4*x + 5)/(x^6 + 3*x^4 + 4*x^3 + 2*x^2 + 5*x + 3)^2)
      additional nonzero requirements: (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Derivative of the input
        Proposition: ∀ (x : ℝ),
          x ^ 6 + 3 * x ^ 4 + 4 * x ^ 3 + 2 * x ^ 2 + 5 * x + 3 ≠ 0 →
            HasDerivAt (fun x ↦ 1 / (x ^ 6 + 3 * x ^ 4 + 4 * x ^ 3 + 2 * x ^ 2 + 5 * x + 3))
              (-((6 * x ^ 5 + 12 * x ^ 3 + 12 * x ^ 2 + 4 * x + 5) /
                  (x ^ 6 + 3 * x ^ 4 + 4 * x ^ 3 + 2 * x ^ 2 + 5 * x + 3) ^ 2))
              x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.hasDerivAt_of_displayRoute
      [CAS.explanation.checkedStep] Partial derivative in x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0
              ((CAS.Verified.Expr.nat 1).div
                ((((((𝕏[0].pow 6).add ((CAS.Verified.Expr.nat 3).mul (𝕏[0].pow 4))).add
                              ((CAS.Verified.Expr.nat 4).mul (𝕏[0].pow 3))).add
                          ((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 2))).add
                      ((CAS.Verified.Expr.nat 5).mul 𝕏[0])).add
                  (CAS.Verified.Expr.nat 3)))).rawDerivative =
          CAS.Verified.Expr.diff 0
            ((CAS.Verified.Expr.nat 1).div
              ((((((𝕏[0].pow 6).add ((CAS.Verified.Expr.nat 3).mul (𝕏[0].pow 4))).add
                            ((CAS.Verified.Expr.nat 4).mul (𝕏[0].pow 3))).add
                        ((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 2))).add
                    ((CAS.Verified.Expr.nat 5).mul 𝕏[0])).add
                (CAS.Verified.Expr.nat 3)))
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Partial derivative in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  ((CAS.Verified.Expr.nat 1).div
                    ((((((𝕏[0].pow 6).add ((CAS.Verified.Expr.nat 3).mul (𝕏[0].pow 4))).add
                                  ((CAS.Verified.Expr.nat 4).mul (𝕏[0].pow 3))).add
                              ((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 2))).add
                          ((CAS.Verified.Expr.nat 5).mul 𝕏[0])).add
                      (CAS.Verified.Expr.nat 3)))).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  ((CAS.Verified.Expr.nat 1).div
                    ((((((𝕏[0].pow 6).add ((CAS.Verified.Expr.nat 3).mul (𝕏[0].pow 4))).add
                                  ((CAS.Verified.Expr.nat 4).mul (𝕏[0].pow 3))).add
                              ((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 2))).add
                          ((CAS.Verified.Expr.nat 5).mul 𝕏[0])).add
                      (CAS.Verified.Expr.nat 3)))).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Partial derivative in x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 0
                    ((CAS.Verified.Expr.nat 1).div
                      ((((((𝕏[0].pow 6).add ((CAS.Verified.Expr.nat 3).mul (𝕏[0].pow 4))).add
                                    ((CAS.Verified.Expr.nat 4).mul (𝕏[0].pow 3))).add
                                ((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 2))).add
                            ((CAS.Verified.Expr.nat 5).mul 𝕏[0])).add
                        (CAS.Verified.Expr.nat 3))))).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      ((CAS.Verified.Expr.nat 1).div
                        ((((((𝕏[0].pow 6).add ((CAS.Verified.Expr.nat 3).mul (𝕏[0].pow 4))).add
                                      ((CAS.Verified.Expr.nat 4).mul (𝕏[0].pow 3))).add
                                  ((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 2))).add
                              ((CAS.Verified.Expr.nat 5).mul 𝕏[0])).add
                          (CAS.Verified.Expr.nat 3))))).rhs =
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 0
                    ((CAS.Verified.Expr.nat 1).div
                      ((((((𝕏[0].pow 6).add ((CAS.Verified.Expr.nat 3).mul (𝕏[0].pow 4))).add
                                    ((CAS.Verified.Expr.nat 4).mul (𝕏[0].pow 3))).add
                                ((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 2))).add
                            ((CAS.Verified.Expr.nat 5).mul 𝕏[0])).add
                        (CAS.Verified.Expr.nat 3)))).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Partial derivative in x: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^1),
          CAS.Verified.Expr.ValidAt x.ofLp
              ((CAS.Verified.Expr.nat 1).div
                ((((((𝕏[0].pow 6).add ((CAS.Verified.Expr.nat 3).mul (𝕏[0].pow 4))).add
                              ((CAS.Verified.Expr.nat 4).mul (𝕏[0].pow 3))).add
                          ((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 2))).add
                      ((CAS.Verified.Expr.nat 5).mul 𝕏[0])).add
                  (CAS.Verified.Expr.nat 3))) →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      ((CAS.Verified.Expr.nat 1).div
                        ((((((𝕏[0].pow 6).add ((CAS.Verified.Expr.nat 3).mul (𝕏[0].pow 4))).add
                                      ((CAS.Verified.Expr.nat 4).mul (𝕏[0].pow 3))).add
                                  ((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 2))).add
                              ((CAS.Verified.Expr.nat 5).mul 𝕏[0])).add
                          (CAS.Verified.Expr.nat 3))))).nonzero →
              (fderiv ℝ
                    (fun y ↦
                      CAS.Verified.Expr.eval y.ofLp
                        ((CAS.Verified.Expr.nat 1).div
                          ((((((𝕏[0].pow 6).add ((CAS.Verified.Expr.nat 3).mul (𝕏[0].pow 4))).add
                                        ((CAS.Verified.Expr.nat 4).mul (𝕏[0].pow 3))).add
                                    ((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 2))).add
                                ((CAS.Verified.Expr.nat 5).mul 𝕏[0])).add
                            (CAS.Verified.Expr.nat 3))))
                    x)
                  (EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 0
                        ((CAS.Verified.Expr.nat 1).div
                          ((((((𝕏[0].pow 6).add ((CAS.Verified.Expr.nat 3).mul (𝕏[0].pow 4))).add
                                        ((CAS.Verified.Expr.nat 4).mul (𝕏[0].pow 3))).add
                                    ((CAS.Verified.Expr.nat 2).mul (𝕏[0].pow 2))).add
                                ((CAS.Verified.Expr.nat 5).mul 𝕏[0])).add
                            (CAS.Verified.Expr.nat 3))))).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [derive x] (1 / (x ^ 6 + 3 * x ^ 4 + 4 * x ^ 3 + 2 * x ^ 2 + 5 * x + 3))

set_option linter.style.longLine false in
/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (tan x)
Output (scalar ℝ): 1/cos(x)^2
Conditions: cos(x) ≠ 0

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Analytic domain conditions
    Raw checked nonzero requirements: cos(x)
    Raw checked positivity requirements: (none)
  [CAS.Command.computation] Partial derivative in x
    [CAS.Command.computation] 1. Apply symbolic differentiation rules
      raw result: (cos(x)*1*cos(x) - sin(x)*-sin(x)*1)/cos(x)^2
    [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
      normalized result: 1/cos(x)^2
    [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
      displayed result: 1/cos(x)^2
      additional nonzero requirements: (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Derivative of the input
        Proposition: ∀ (x : ℝ), Real.cos x ≠ 0 → HasDerivAt (fun x ↦ Real.tan x) (1 / Real.cos x ^ 2) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.hasDerivAt_of_displayRoute
      [CAS.explanation.checkedStep] Partial derivative in x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].sin.div 𝕏[0].cos)).rawDerivative =
          CAS.Verified.Expr.diff 0 (𝕏[0].sin.div 𝕏[0].cos)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Partial derivative in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].sin.div 𝕏[0].cos)).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].sin.div 𝕏[0].cos)).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Partial derivative in x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].sin.div 𝕏[0].cos))).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].sin.div 𝕏[0].cos))).rhs =
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].sin.div 𝕏[0].cos)).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Partial derivative in x: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^1),
          CAS.Verified.Expr.ValidAt x.ofLp (𝕏[0].sin.div 𝕏[0].cos) →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].sin.div 𝕏[0].cos))).nonzero →
              (fderiv ℝ (fun y ↦ CAS.Verified.Expr.eval y.ofLp (𝕏[0].sin.div 𝕏[0].cos)) x) (EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].sin.div 𝕏[0].cos))).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [derive x] (tan x)

set_option linter.style.longLine false in
/--
info: #cas [simplify]
Domain: x ∈ ℝ
Input (scalar ℝ): (tan x * cos x)
Output (scalar ℝ): sin(x)
Conditions: cos(x) ≠ 0

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked symbolic computation
    Raw checked nonzero requirements: cos(x)
    Guarantee: these assumptions justify conditional rewrites and preserve real evaluation
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the simplified form
        Proposition: ∀ (x : ℝ), Real.cos x ≠ 0 → Real.tan x * Real.cos x = Real.sin x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.eq_of_simplifyFinDisplayRoute
      [CAS.explanation.checkedStep] Simplification under generated rewrite assumptions
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ ((𝕏[0].sin.div 𝕏[0].cos).mul 𝕏[0].cos).simplifyFinDisplayRoute.nonzero →
            CAS.Verified.Expr.eval ρ ((𝕏[0].sin.div 𝕏[0].cos).mul 𝕏[0].cos).simplifyFinDisplayRoute.rhs =
              CAS.Verified.Expr.eval ρ ((𝕏[0].sin.div 𝕏[0].cos).mul 𝕏[0].cos).simplifyFinDisplayRoute.lhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.SideClaimRoute.sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] pre-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] base normalization: structural: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: trig: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: algebra: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: factor-common: attempted
        checked
      [CAS.explanation.plannerStep] post-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: fraction-normal-form: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: rational-side: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-square: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-numeral: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-product-collect: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: common-add-factor: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: unit-ratio: attempted
        side-conditioned
-/
#guard_msgs in
#cas [simplify] (tan x * cos x)

set_option linter.style.longLine false in
/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (sinh x)
Output (scalar ℝ): 1/2*(exp(x) + exp(-x))

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Analytic domain conditions
    Raw checked nonzero requirements: 2
    Raw checked positivity requirements: (none)
  [CAS.Command.computation] Partial derivative in x
    [CAS.Command.computation] 1. Apply symbolic differentiation rules
      raw result: ((exp(x)*1 - exp(-x)*-1)*2 - (exp(x) - exp(-x))*0)/2^2
    [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
      normalized result: 1/2*(exp(x) + exp(-x))
    [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
      displayed result: 1/2*(exp(x) + exp(-x))
      additional nonzero requirements: (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Derivative of the input
        Proposition: ∀ (x : ℝ), HasDerivAt (fun x ↦ Real.sinh x) (1 / 2 * (Real.exp x + Real.exp (-x))) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.hasDerivAt_of_displayRoute
      [CAS.explanation.checkedStep] Partial derivative in x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0
              ((𝕏[0].exp.sub 𝕏[0].neg.exp).div (CAS.Verified.Expr.nat 2))).rawDerivative =
          CAS.Verified.Expr.diff 0 ((𝕏[0].exp.sub 𝕏[0].neg.exp).div (CAS.Verified.Expr.nat 2))
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Partial derivative in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  ((𝕏[0].exp.sub 𝕏[0].neg.exp).div (CAS.Verified.Expr.nat 2))).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  ((𝕏[0].exp.sub 𝕏[0].neg.exp).div (CAS.Verified.Expr.nat 2))).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Partial derivative in x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 0
                    ((𝕏[0].exp.sub 𝕏[0].neg.exp).div (CAS.Verified.Expr.nat 2)))).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      ((𝕏[0].exp.sub 𝕏[0].neg.exp).div (CAS.Verified.Expr.nat 2)))).rhs =
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 0
                    ((𝕏[0].exp.sub 𝕏[0].neg.exp).div (CAS.Verified.Expr.nat 2))).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Partial derivative in x: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^1),
          CAS.Verified.Expr.ValidAt x.ofLp ((𝕏[0].exp.sub 𝕏[0].neg.exp).div (CAS.Verified.Expr.nat 2)) →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      ((𝕏[0].exp.sub 𝕏[0].neg.exp).div (CAS.Verified.Expr.nat 2)))).nonzero →
              (fderiv ℝ
                    (fun y ↦ CAS.Verified.Expr.eval y.ofLp ((𝕏[0].exp.sub 𝕏[0].neg.exp).div (CAS.Verified.Expr.nat 2)))
                    x)
                  (EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 0
                        ((𝕏[0].exp.sub 𝕏[0].neg.exp).div (CAS.Verified.Expr.nat 2)))).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [derive x] (sinh x)

set_option linter.style.longLine false in
/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (|x|)
Output (scalar ℝ): x/|x|
Conditions: x^2 > 0

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Analytic domain conditions
    Raw checked nonzero requirements: (none)
    Raw checked positivity requirements: x^2
  [CAS.Command.computation] Partial derivative in x
    [CAS.Command.computation] 1. Apply symbolic differentiation rules
      raw result: 2*x^1*1/(2*|x|)
    [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
      normalized result: x/|x|
    [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
      displayed result: x/|x|
      additional nonzero requirements: (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Derivative of the input
        Proposition: ∀ (x : ℝ), 0 < x ^ 2 → HasDerivAt (fun x ↦ |x|) (x / |x|) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.hasDerivAt_of_displayRoute
      [CAS.explanation.checkedStep] Partial derivative in x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].pow 2).sqrt).rawDerivative =
          CAS.Verified.Expr.diff 0 (𝕏[0].pow 2).sqrt
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Partial derivative in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].pow 2).sqrt).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].pow 2).sqrt).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Partial derivative in x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].pow 2).sqrt)).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].pow 2).sqrt)).rhs =
              CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].pow 2).sqrt).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Partial derivative in x: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^1),
          CAS.Verified.Expr.ValidAt x.ofLp (𝕏[0].pow 2).sqrt →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].pow 2).sqrt)).nonzero →
              (fderiv ℝ (fun y ↦ CAS.Verified.Expr.eval y.ofLp (𝕏[0].pow 2).sqrt) x) (EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].pow 2).sqrt)).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [derive x] (|x|)

set_option linter.style.longLine false in
/--
info: #cas [grad x, y]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (x * y)
Output (vector ℝ^2; order x, y): (y, x)

[CAS.Command.details] More details
  Variables and component order: x, y
  [CAS.Command.computation] Analytic domain conditions
    Raw checked nonzero requirements: (none)
    Raw checked positivity requirements: (none)
  [CAS.Command.computation] Checked gradient computation
    [CAS.Command.computation] Gradient component ∂_x
      Output: y
      [CAS.Command.computation] Partial derivative in x
        [CAS.Command.computation] 1. Apply symbolic differentiation rules
          raw result: 1*y + x*0
        [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
          normalized result: y
        [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
          displayed result: y
          additional nonzero requirements: (none)
    [CAS.Command.computation] Gradient component ∂_y
      Output: x
      [CAS.Command.computation] Partial derivative in y
        [CAS.Command.computation] 1. Apply symbolic differentiation rules
          raw result: 0*y + x*1
        [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
          normalized result: x
        [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
          displayed result: x
          additional nonzero requirements: (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Gradient of the input
        Proposition: ∀ (x y : ℝ), HasGradientAt (fun p ↦ p.ofLp 0 * p.ofLp 1) !₂[y, x] !₂[x, y]
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.hasGradientAt_of_closedGradient
      [CAS.explanation.checkedStep] Gradient component ∂_x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1])).rawDerivative =
          CAS.Verified.Expr.diff 0 (𝕏[0].mul 𝕏[1])
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Gradient component ∂_x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1])).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1])).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Gradient component ∂_x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1]))).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1]))).rhs =
              CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1])).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Gradient component ∂_x: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^2),
          CAS.Verified.Expr.ValidAt x.ofLp (𝕏[0].mul 𝕏[1]) →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1]))).nonzero →
              (fderiv ℝ (fun y ↦ CAS.Verified.Expr.eval y.ofLp (𝕏[0].mul 𝕏[1])) x) (EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].mul 𝕏[1]))).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
      [CAS.explanation.checkedStep] Gradient component ∂_y: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 1 (𝕏[0].mul 𝕏[1])).rawDerivative =
          CAS.Verified.Expr.diff 1 (𝕏[0].mul 𝕏[1])
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Gradient component ∂_y: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 1 (𝕏[0].mul 𝕏[1])).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 1 (𝕏[0].mul 𝕏[1])).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Gradient component ∂_y: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 2 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute (CAS.Verified.Expr.DiffDerivation.build 1 (𝕏[0].mul 𝕏[1]))).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute (CAS.Verified.Expr.DiffDerivation.build 1 (𝕏[0].mul 𝕏[1]))).rhs =
              CAS.Verified.Expr.eval ρ (CAS.Verified.Expr.DiffDerivation.build 1 (𝕏[0].mul 𝕏[1])).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Gradient component ∂_y: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^2),
          CAS.Verified.Expr.ValidAt x.ofLp (𝕏[0].mul 𝕏[1]) →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 1 (𝕏[0].mul 𝕏[1]))).nonzero →
              (fderiv ℝ (fun y ↦ CAS.Verified.Expr.eval y.ofLp (𝕏[0].mul 𝕏[1])) x) (EuclideanSpace.single 1 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute (CAS.Verified.Expr.DiffDerivation.build 1 (𝕏[0].mul 𝕏[1]))).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
      [CAS.explanation.checkedStep] Analytic gradient assembly
        Proposition: ∀ (x : ℝ^2),
          CAS.Verified.Expr.ValidAt x.ofLp (𝕏[0].mul 𝕏[1]) →
            (WithLp.toLp 2 fun i ↦ CAS.Verified.Expr.eval x.ofLp ((∇ₛ (𝕏[0].mul 𝕏[1])) i)) =
              gradient (fun y ↦ CAS.Verified.Expr.eval y.ofLp (𝕏[0].mul 𝕏[1])) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.closedGradient_eval_eq_gradient
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [grad x, y] (x * y)

set_option linter.style.longLine false in
/--
info: #cas [N 10]
Domain: error function erf x = 2/√π ∫₀ˣ e^(-t²) dt at a rational point
Input (scalar ℝ): (erf (1/2))
Output (decimal enclosure of width at most 10^-10, with 10 terms of the series): [0.52049987781, 0.52049987782]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of erf 1/2
        Proposition: 0.52049987781 ≤ CAS.erf (1 / 2) ∧
          CAS.erf (1 / 2) ≤ 0.52049987782 ∧ 0.52049987782 - 0.52049987781 ≤ 1 / 10 ^ 10
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.erfCheck_sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 10] (erf (1/2))

set_option linter.style.longLine false in
/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (c e ^ (-α x ^ 2 + β x + γ), α > 0): (exp (-x ^ 2))
Output (scalar ℝ; antiderivative (with the interval integrals)): 1/2*sqrt(pi)*erf(x)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Integral of the input
        Proposition: ∀ (a b : ℝ),
          ∫ (x : ℝ) in a..b, Real.exp (-x ^ 2) = 1 / 2 * √Real.pi * CAS.erf b - 1 / 2 * √Real.pi * CAS.erf a
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.integral_gaussian_eq
      [CAS.explanation.checkedStep] Derivative of the primitive
        Proposition: ∀ (x : ℝ), HasDerivAt (fun x ↦ 1 / 2 * √Real.pi * CAS.erf x) (Real.exp (-x ^ 2)) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.hasDerivAt_gaussianPrimitive
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [integrate x] (exp (-x ^ 2))

/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (sum of c * erf (A x + B)): (erf x)
Output (scalar ℝ; derivative): 2/sqrt(pi)*exp(-x^2)

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Derivative of the input
        Proposition: ∀ (x : ℝ), HasDerivAt (fun x ↦ CAS.erf x) (2 / √Real.pi * Real.exp (-x ^ 2)) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.hasDerivAt_erf
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [derive x] (erf x)

set_option linter.style.longLine false in
/--
info: #cas [enclose]
Domain: closed real expression
Input (scalar ℝ): (sqrt 2)
Output (certified interval in ℝ): [181/128, 5793/4096]
Upper bound: 5793/4096
Absolute bound: 5793/4096
Center and radius: 11585/8192 ± 1/8192

[CAS.Command.details] More details
  Coordinates: none
  Certified domain: closed real expression
  [CAS.Command.computation] Certified numerical guarantee
    Guarantee: the real value lies in the output interval
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of the input
        Proposition: 181 / 128 ≤ √2 ∧ √2 ≤ 5793 / 4096
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.mem_of_enclosedOn_box
      [CAS.explanation.checkedStep] Upper bound of the input
        Proposition: √2 ≤ 5793 / 4096
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.le_of_boundOn_box
      [CAS.explanation.checkedStep] Absolute bound of the input
        Proposition: |√2| ≤ 5793 / 4096
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.abs_le_of_boundOn_abs_box
      [CAS.explanation.checkedStep] Center and radius of the input
        Proposition: |√2 - 11585 / 8192| ≤ 1 / 8192
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.abs_sub_le_of_approxOn_box
      [CAS.explanation.checkedStep] Certified enclosure
        Proposition: CAS.Certificate.EnclosedOn (CAS.Exact.exprFn (CAS.Verified.Expr.nat 2).sqrt)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦ [].get coordinate) (↑181 / ↑128) (↑5793 / ↑4096)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.enclosedOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified upper bound
        Proposition: CAS.Certificate.BoundOn (CAS.Exact.exprFn (CAS.Verified.Expr.nat 2).sqrt)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦ [].get coordinate) (↑5793 / ↑4096)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified absolute bound
        Proposition: CAS.Certificate.BoundOn (fun x ↦ |CAS.Exact.exprFn (CAS.Verified.Expr.nat 2).sqrt x|)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦ [].get coordinate) (↑5793 / ↑4096)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_abs_of_interval_eq
      [CAS.explanation.checkedStep] Certified center and radius
        Proposition: CAS.Certificate.ApproxOn (CAS.Exact.exprFn (CAS.Verified.Expr.nat 2).sqrt) (fun x ↦ ↑11585 / ↑8192)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦ [].get coordinate) (↑1 / ↑8192)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.approxOn_center_of_interval_eq
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] square-root range: succeeded
-/
#guard_msgs in
#cas [enclose] (sqrt 2)

/-! ## Function names

The input `tan x + sin x / cos x` applies `tan` once and writes the other quotient out, and its
statement keeps both as written. The input `sin x / cos x` applies no function of the table, so
neither its statement nor its `Output` line names `Real.tan`, and `sqrt (x ^ 2)` keeps its root. -/

set_option linter.style.longLine false in
/--
info: #cas [simplify]
Domain: x ∈ ℝ
Input (scalar ℝ): (tan x + sin x / cos x)
Output (scalar ℝ): 2*sin(x)/cos(x)

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked symbolic computation
    Raw checked nonzero requirements: (none)
    Guarantee: these assumptions justify conditional rewrites and preserve real evaluation
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the simplified form
        Proposition: ∀ (x : ℝ), Real.tan x + Real.sin x / Real.cos x = 2 * Real.sin x / Real.cos x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.eq_of_simplifyFinDisplayRoute
      [CAS.explanation.checkedStep] Simplification under generated rewrite assumptions
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              ((𝕏[0].sin.div 𝕏[0].cos).add (𝕏[0].sin.div 𝕏[0].cos)).simplifyFinDisplayRoute.nonzero →
            CAS.Verified.Expr.eval ρ ((𝕏[0].sin.div 𝕏[0].cos).add (𝕏[0].sin.div 𝕏[0].cos)).simplifyFinDisplayRoute.rhs =
              CAS.Verified.Expr.eval ρ ((𝕏[0].sin.div 𝕏[0].cos).add (𝕏[0].sin.div 𝕏[0].cos)).simplifyFinDisplayRoute.lhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.SideClaimRoute.sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] pre-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] base normalization: structural: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: trig: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: algebra: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: factor-common: attempted
        checked
      [CAS.explanation.plannerStep] post-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: fraction-normal-form: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: rational-side: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-square: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-numeral: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-product-collect: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: common-add-factor: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: unit-ratio: attempted
        side-conditioned
-/
#guard_msgs in
#cas [simplify] (tan x + sin x / cos x)

set_option linter.style.longLine false in
/--
info: #cas [simplify]
Domain: x ∈ ℝ
Input (scalar ℝ): (sin x / cos x)
Output (scalar ℝ): sin(x)/cos(x)

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked symbolic computation
    Raw checked nonzero requirements: (none)
    Guarantee: these assumptions justify conditional rewrites and preserve real evaluation
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the simplified form
        Proposition: ∀ (x : ℝ), Real.sin x / Real.cos x = Real.sin x / Real.cos x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.eq_of_simplifyFinDisplayRoute
      [CAS.explanation.checkedStep] Simplification under generated rewrite assumptions
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ (𝕏[0].sin.div 𝕏[0].cos).simplifyFinDisplayRoute.nonzero →
            CAS.Verified.Expr.eval ρ (𝕏[0].sin.div 𝕏[0].cos).simplifyFinDisplayRoute.rhs =
              CAS.Verified.Expr.eval ρ (𝕏[0].sin.div 𝕏[0].cos).simplifyFinDisplayRoute.lhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.SideClaimRoute.sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] pre-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] base normalization: structural: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: trig: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: algebra: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: factor-common: attempted
        checked
      [CAS.explanation.plannerStep] post-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: fraction-normal-form: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: rational-side: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-square: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-numeral: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-product-collect: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: common-add-factor: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: unit-ratio: attempted
        side-conditioned
-/
#guard_msgs in
#cas [simplify] (sin x / cos x)

/--
info: #cas [simplify]
Domain: x ∈ ℝ
Input (scalar ℝ): (sqrt (x ^ 2))
Output (scalar ℝ): sqrt(x^2)

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked symbolic computation
    Raw checked nonzero requirements: (none)
    Guarantee: these assumptions justify conditional rewrites and preserve real evaluation
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the simplified form
        Proposition: ∀ (x : ℝ), √(x ^ 2) = √(x * x)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.eq_of_simplifyFinDisplayRoute
      [CAS.explanation.checkedStep] Simplification under generated rewrite assumptions
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ (𝕏[0].pow 2).sqrt.simplifyFinDisplayRoute.nonzero →
            CAS.Verified.Expr.eval ρ (𝕏[0].pow 2).sqrt.simplifyFinDisplayRoute.rhs =
              CAS.Verified.Expr.eval ρ (𝕏[0].pow 2).sqrt.simplifyFinDisplayRoute.lhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.SideClaimRoute.sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] pre-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] base normalization: structural: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: trig: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: algebra: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: factor-common: attempted
        checked
      [CAS.explanation.plannerStep] post-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: fraction-normal-form: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: rational-side: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-square: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-numeral: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-product-collect: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: common-add-factor: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: unit-ratio: attempted
        side-conditioned
-/
#guard_msgs in
#cas [simplify] (sqrt (x ^ 2))

/-! ## Casts in printed terms

The printer drops a cast only when every operation under it means the same in the target type. A
subtraction in `ℕ`, a division or a remainder in `ℕ` or `ℤ` and a logarithm of a real variable
read in `ℂ` stay typed groups, which the display normal form does not rewrite by the rules of real
arithmetic. The text of a group is a Lean term with the operator tree of the input: a right
operand at the level of its operator keeps its parentheses, and an operation that truncates in
another type is a group of its own. A function of another library that has the name of a function
of the printer prints with its full name, and the name of a constant that is not an identifier
prints with Lean's escapes. -/

/-- info: (n - (m - k) : ℕ) + x*(a/b : ℤ) - (log(x) : ℝ) -/
#guard_msgs in
run_elab do
  let e ← Lean.Elab.Term.elabTermAndSynthesize (← `(fun (n m k : ℕ) (a b : ℤ) (x : ℝ) ↦
    ((((n - (m - k) : ℕ) : ℝ) + x * ((a / b : ℤ) : ℝ) : ℝ) : ℂ) - ((Real.log x : ℝ) : ℂ))) none
  Lean.Meta.lambdaTelescope (← Lean.instantiateMVars e) fun _ body ↦ do
    Lean.logInfo (← CAS.Command.renderTerm body)

/-- A constant whose name is not an identifier. -/
def «a-b» : ℕ := 2

/--
info: (1 + (2 - 3) - 0 : ℕ)
---
info: (2*(3/2)/1 : ℕ)
---
info: (2*(3/2)/1 : ℤ)
---
info: (a%b : ℕ) + (c%d : ℤ)
---
info: ((n - m : ℕ)/k : ℤ)
---
info: Nat.sqrt(8)
---
info: «a-b»^2
-/
#guard_msgs in
run_elab do
  for term in #[← `(((1 + (2 - 3) - 0 : ℕ) : ℝ)), ← `(((2 * (3 / 2) / 1 : ℕ) : ℝ)),
      ← `(((2 * (3 / 2) / 1 : ℤ) : ℝ)),
      ← `(fun (a b : ℕ) (c d : ℤ) ↦ ((a % b : ℕ) : ℝ) + ((c % d : ℤ) : ℝ)),
      ← `(fun (n m : ℕ) (k : ℤ) ↦ ((((n - m : ℕ) : ℤ) / k : ℤ) : ℝ)),
      ← `(((Nat.sqrt 8 : ℕ) : ℝ)), ← `(((«a-b» : ℕ) : ℝ) ^ 2)] do
    let e ← Lean.Elab.Term.elabTermAndSynthesize term none
    Lean.Meta.lambdaTelescope (← Lean.instantiateMVars e) fun _ body ↦ do
      Lean.logInfo (← CAS.Command.renderTerm body)

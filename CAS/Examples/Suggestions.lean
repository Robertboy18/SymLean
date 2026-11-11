/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Suggestions of `#cas` reports

Under `set_option cas.suggest true` a report also offers its first checked statement as an
`example` to paste in place of the command, proved by `cas`, or for an enclosure with a
configuration by `cega` with that configuration. The suggestion costs a second proof of the
statement, so it is off by default. It follows the report, and it is offered only when the binders
and the type of the example, elaborated here as the `example` command elaborates them, with the
variables of the section, are the statement, and the whole example elaborates without errors
here to a declaration of the statement with no `sorry`. Each pinned suggestion is followed by its
pasted copy. Gradients and the digits and derivatives of `erf` have none, since `cas` does not
prove their statements. The powers print the types of their closed numeric operands, also of a
power inside such an operand. The last three cases run in sections under `open Real`. With a local
notation for `Real.sin` the report and the suggestion print with it. With a section variable `sin`
the suggestion names `Real.sin` in full, since the printer avoids the name of the variable, while
the `Proposition:` line of the report, printed without the variables of the section, reads
`sin x`. A section variable that clashes with no name leaves the suggestion as it is. Each pasted
copy elaborates within its section.
-/

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
---
info: Try this:
  [apply] example (x : ℝ) : x + x = 2 * x := by cas
-/
#guard_msgs in
set_option cas.suggest true in
#cas [simplify] (x + x)

example (x : ℝ) : x + x = 2 * x := by cas

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
---
info: Try this:
  [apply] example (x : ℝ) (h : Real.cos x ≠ 0) :
      HasDerivAt (fun x ↦ Real.tan x) (1 / Real.cos x ^ 2) x := by
    cas
-/
#guard_msgs in
set_option cas.suggest true in
#cas [derive x] (tan x)

example (x : ℝ) (h : Real.cos x ≠ 0) :
    HasDerivAt (fun x ↦ Real.tan x) (1 / Real.cos x ^ 2) x := by
  cas

set_option linter.style.longLine false in
/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (x ^ (3/2 : ℝ))
Output (scalar ℝ): 3/2*sqrt(x)
Conditions: x > 0

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Analytic domain conditions
    Raw checked nonzero requirements: 2
    Raw checked positivity requirements: x
  [CAS.Command.computation] Partial derivative in x
    [CAS.Command.computation] 1. Apply symbolic differentiation rules
      raw result: 1*3/2*x^(3/2 - 1) + (0*2 - 3*0)/2^2*x^(3/2)*log(x)
    [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
      normalized result: 3/2*x^(1/2)
    [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
      displayed result: 3/2*sqrt(x)
      additional nonzero requirements: (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Derivative of the input
        Proposition: ∀ (x : ℝ), 0 < x → HasDerivAt (fun x ↦ x ^ (3 / 2 : ℝ)) (3 / 2 * √x) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.hasDerivAt_of_displayRoute
      [CAS.explanation.checkedStep] Partial derivative in x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0
              (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat 2)))).rawDerivative =
          CAS.Verified.Expr.diff 0 (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat 2)))
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Partial derivative in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat 2)))).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat 2)))).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Partial derivative in x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 0
                    (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat 2))))).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat 2))))).rhs =
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 0
                    (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat 2)))).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Partial derivative in x: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^1),
          CAS.Verified.Expr.ValidAt x.ofLp (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat 2))) →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat 2))))).nonzero →
              (fderiv ℝ
                    (fun y ↦
                      CAS.Verified.Expr.eval y.ofLp
                        (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat 2))))
                    x)
                  (EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 0
                        (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat 2))))).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
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
      [CAS.explanation.plannerStep] post-normalization: pythagorean: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-product-collect: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: common-add-factor: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: unit-ratio: attempted
        side-conditioned
---
info: Try this:
  [apply] example (x : ℝ) (h : 0 < x) : HasDerivAt (fun x ↦ x ^ (3 / 2 : ℝ)) (3 / 2 * √x) x := by cas
-/
#guard_msgs in
set_option cas.suggest true in
#cas [derive x] (x ^ (3/2 : ℝ))

example (x : ℝ) (h : 0 < x) : HasDerivAt (fun x ↦ x ^ (3 / 2 : ℝ)) (3 / 2 * √x) x := by cas

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
---
info: Try this:
  [apply] example (a b : ℝ) :
      ∫ (x : ℝ) in a..b, x * Real.exp x = Real.exp b * (b - 1) - Real.exp a * (a - 1) := by
    cas
-/
#guard_msgs in
set_option cas.suggest true in
#cas [integrate x] (x * exp x)

example (a b : ℝ) :
    ∫ (x : ℝ) in a..b, x * Real.exp x = Real.exp b * (b - 1) - Real.exp a * (a - 1) := by
  cas

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
---
info: Try this:
  [apply] example (x : ℝ) (h : x ∈ Set.Icc 0 1) : -1 / 4 ≤ x ^ 2 - x ∧ x ^ 2 - x ≤ 0 := by cas
-/
#guard_msgs in
set_option cas.suggest true in
#cas [enclose x in [0, 1]] (x ^ 2 - x)

example (x : ℝ) (h : x ∈ Set.Icc 0 1) : -1 / 4 ≤ x ^ 2 - x ∧ x ^ 2 - x ≤ 0 := by cas

set_option linter.style.longLine false in
/--
info: #cas (prec := 16) [enclose]
Domain: closed real expression
Input (scalar ℝ): (sqrt 2)
Output (certified interval in ℝ): [92681/65536, 46341/32768]
Upper bound: 46341/32768
Absolute bound: 46341/32768
Center and radius: 185363/131072 ± 1/131072

[CAS.Command.details] More details
  Coordinates: none
  Certified domain: closed real expression
  [CAS.Command.computation] Certified numerical guarantee
    Guarantee: the real value lies in the output interval
    Precision policy: exp order 16, sqrt digits 16, log terms 16, subdivision depth 2
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of the input
        Proposition: 92681 / 65536 ≤ √2 ∧ √2 ≤ 46341 / 32768
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.mem_of_enclosedOn_box
      [CAS.explanation.checkedStep] Upper bound of the input
        Proposition: √2 ≤ 46341 / 32768
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.le_of_boundOn_box
      [CAS.explanation.checkedStep] Absolute bound of the input
        Proposition: |√2| ≤ 46341 / 32768
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.abs_le_of_boundOn_abs_box
      [CAS.explanation.checkedStep] Center and radius of the input
        Proposition: |√2 - 185363 / 131072| ≤ 1 / 131072
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.abs_sub_le_of_approxOn_box
      [CAS.explanation.checkedStep] Certified enclosure
        Proposition: CAS.Certificate.EnclosedOn (CAS.Exact.exprFn (CAS.Verified.Expr.nat 2).sqrt)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦ [].get coordinate) (↑92681 / ↑65536)
          (↑46341 / ↑32768)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.enclosedOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified upper bound
        Proposition: CAS.Certificate.BoundOn (CAS.Exact.exprFn (CAS.Verified.Expr.nat 2).sqrt)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦ [].get coordinate) (↑46341 / ↑32768)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified absolute bound
        Proposition: CAS.Certificate.BoundOn (fun x ↦ |CAS.Exact.exprFn (CAS.Verified.Expr.nat 2).sqrt x|)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦ [].get coordinate) (↑46341 / ↑32768)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_abs_of_interval_eq
      [CAS.explanation.checkedStep] Certified center and radius
        Proposition: CAS.Certificate.ApproxOn (CAS.Exact.exprFn (CAS.Verified.Expr.nat 2).sqrt)
          (fun x ↦ ↑185363 / ↑131072) (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦ [].get coordinate)
          (↑1 / ↑131072)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.approxOn_center_of_interval_eq
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] square-root range: succeeded
---
info: Try this:
  [apply] example : 92681 / 65536 ≤ √2 ∧ √2 ≤ 46341 / 32768 := by cega (prec := 16)
-/
#guard_msgs in
set_option cas.suggest true in
#cas (prec := 16) [enclose] (sqrt 2)

example : 92681 / 65536 ≤ √2 ∧ √2 ≤ 46341 / 32768 := by cega (prec := 16)

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
---
info: Try this:
  [apply] example (a b : ℝ) :
      ∫ (x : ℝ) in a..b, Real.exp (-x ^ 2) =
        1 / 2 * √Real.pi * CAS.erf b - 1 / 2 * √Real.pi * CAS.erf a := by
    cas
-/
#guard_msgs in
set_option cas.suggest true in
#cas [integrate x] (exp (-x ^ 2))

example (a b : ℝ) :
    ∫ (x : ℝ) in a..b, Real.exp (-x ^ 2) =
      1 / 2 * √Real.pi * CAS.erf b - 1 / 2 * √Real.pi * CAS.erf a := by
  cas

/--
info: #cas [simplify]
Domain: x ∈ ℝ
Input (scalar ℝ): (x ^ ((2 ^ 2 / 3 ^ 2) : ℝ))
Output (scalar ℝ): x^(4/9)

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked symbolic computation
    Raw checked nonzero requirements: (none)
    Guarantee: these assumptions justify conditional rewrites and preserve real evaluation
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the simplified form
        Proposition: ∀ (x : ℝ), x ^ (2 ^ 2 / 3 ^ 2 : ℝ) = x ^ (4 / 9 : ℝ)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.eq_of_simplifyFinDisplayRoute
      [CAS.explanation.checkedStep] Simplification under generated rewrite assumptions
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (𝕏[0].rpow
                    (((CAS.Verified.Expr.nat 2).pow 2).div
                      ((CAS.Verified.Expr.nat 3).pow 2))).simplifyFinDisplayRoute.nonzero →
            CAS.Verified.Expr.eval ρ
                (𝕏[0].rpow
                      (((CAS.Verified.Expr.nat 2).pow 2).div
                        ((CAS.Verified.Expr.nat 3).pow 2))).simplifyFinDisplayRoute.rhs =
              CAS.Verified.Expr.eval ρ
                (𝕏[0].rpow
                      (((CAS.Verified.Expr.nat 2).pow 2).div
                        ((CAS.Verified.Expr.nat 3).pow 2))).simplifyFinDisplayRoute.lhs
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
---
info: Try this:
  [apply] example (x : ℝ) : x ^ (2 ^ 2 / 3 ^ 2 : ℝ) = x ^ (4 / 9 : ℝ) := by cas
-/
#guard_msgs in
set_option cas.suggest true in
#cas [simplify] (x ^ ((2 ^ 2 / 3 ^ 2) : ℝ))

example (x : ℝ) : x ^ (2 ^ 2 / 3 ^ 2 : ℝ) = x ^ (4 / 9 : ℝ) := by cas

set_option linter.style.longLine false in
/--
info: #cas [simplify]
Domain: x ∈ ℝ
Input (scalar ℝ): (x ^ ((4 : ℝ) ^ (1 / 2 : ℝ)))
Output (scalar ℝ): x^2

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked symbolic computation
    Raw checked nonzero requirements: (none)
    Guarantee: these assumptions justify conditional rewrites and preserve real evaluation
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the simplified form
        Proposition: ∀ (x : ℝ), x ^ ((4 : ℝ) ^ (1 / 2 : ℝ) : ℝ) = x ^ 2
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.eq_of_simplifyFinDisplayRoute
      [CAS.explanation.checkedStep] Simplification under generated rewrite assumptions
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (𝕏[0].rpow
                    ((CAS.Verified.Expr.nat 4).rpow
                      ((CAS.Verified.Expr.nat 1).div (CAS.Verified.Expr.nat 2)))).simplifyFinDisplayRoute.nonzero →
            CAS.Verified.Expr.eval ρ
                (𝕏[0].rpow
                      ((CAS.Verified.Expr.nat 4).rpow
                        ((CAS.Verified.Expr.nat 1).div (CAS.Verified.Expr.nat 2)))).simplifyFinDisplayRoute.rhs =
              CAS.Verified.Expr.eval ρ
                (𝕏[0].rpow
                      ((CAS.Verified.Expr.nat 4).rpow
                        ((CAS.Verified.Expr.nat 1).div (CAS.Verified.Expr.nat 2)))).simplifyFinDisplayRoute.lhs
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
---
info: Try this:
  [apply] example (x : ℝ) : x ^ ((4 : ℝ) ^ (1 / 2 : ℝ) : ℝ) = x ^ 2 := by cas
-/
#guard_msgs in
set_option cas.suggest true in
#cas [simplify] (x ^ ((4 : ℝ) ^ (1 / 2 : ℝ)))

example (x : ℝ) : x ^ ((4 : ℝ) ^ (1 / 2 : ℝ) : ℝ) = x ^ 2 := by cas

section
open Real

local notation "sn" a:max => Real.sin a

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
        Proposition: ∀ (x : ℝ), cos x ≠ 0 → tan x * cos x = sn x
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
---
info: Try this:
  [apply] example (x : ℝ) (h : cos x ≠ 0) : tan x * cos x = sn x := by cas
-/
#guard_msgs in
set_option cas.suggest true in
#cas [simplify] (tan x * cos x)

example (x : ℝ) (h : cos x ≠ 0) : tan x * cos x = sn x := by cas

end

section
open Real

variable (sin : ℝ → ℝ)

/--
info: #cas [simplify]
Domain: x ∈ ℝ
Input (scalar ℝ): (Real.sin x)
Output (scalar ℝ): sin(x)

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked symbolic computation
    Raw checked nonzero requirements: (none)
    Guarantee: these assumptions justify conditional rewrites and preserve real evaluation
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the simplified form
        Proposition: ∀ (x : ℝ), sin x = sin x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.eq_of_simplifyFinDisplayRoute
      [CAS.explanation.checkedStep] Simplification under generated rewrite assumptions
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ 𝕏[0].sin.simplifyFinDisplayRoute.nonzero →
            CAS.Verified.Expr.eval ρ 𝕏[0].sin.simplifyFinDisplayRoute.rhs =
              CAS.Verified.Expr.eval ρ 𝕏[0].sin.simplifyFinDisplayRoute.lhs
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
---
info: Try this:
  [apply] example (x : ℝ) : Real.sin x = Real.sin x := by cas
-/
#guard_msgs in
set_option cas.suggest true in
#cas [simplify] (Real.sin x)

example (x : ℝ) : Real.sin x = Real.sin x := by cas

end

section
open Real

variable (c : ℝ)

/--
info: #cas [simplify]
Domain: x ∈ ℝ
Input (scalar ℝ): (Real.sin x)
Output (scalar ℝ): sin(x)

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked symbolic computation
    Raw checked nonzero requirements: (none)
    Guarantee: these assumptions justify conditional rewrites and preserve real evaluation
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the simplified form
        Proposition: ∀ (x : ℝ), sin x = sin x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.eq_of_simplifyFinDisplayRoute
      [CAS.explanation.checkedStep] Simplification under generated rewrite assumptions
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ 𝕏[0].sin.simplifyFinDisplayRoute.nonzero →
            CAS.Verified.Expr.eval ρ 𝕏[0].sin.simplifyFinDisplayRoute.rhs =
              CAS.Verified.Expr.eval ρ 𝕏[0].sin.simplifyFinDisplayRoute.lhs
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
---
info: Try this:
  [apply] example (x : ℝ) : sin x = sin x := by cas
-/
#guard_msgs in
set_option cas.suggest true in
#cas [simplify] (Real.sin x)

example (x : ℝ) : sin x = sin x := by cas

end

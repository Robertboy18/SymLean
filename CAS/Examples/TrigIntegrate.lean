/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Antiderivatives of trigonometric integrands

`#cas [integrate x] f` integrates a rational function of `sin u` and `cos u`, for one phase `u`
linear in `x`, by the planner's case for one trigonometric phase (`CAS.Integration.Bioche`). A
polynomial in `sin u` and `cos u` is integrated monomial by monomial: an odd power by the
substitution `t = cos u` or `t = sin u`, and two even powers by `sin u ^ 2 = 1 - cos u ^ 2` and the
reduction formula of `cos u ^ (2 * m)`. A quotient goes through the substitution that Bioche's rules
choose from its symmetries: `t = cos u` for `sin x ^ 3 / cos x ^ 2`, and `t = tan u` for `tan x ^ 2`
and `1 / (1 + cos x ^ 2)`. A quotient with none of the three symmetries, such as `1 / (2 + cos x)`,
goes through the tangent half-angle substitution `t = sin u / (1 + cos u)`. Each command proves
`HasDerivAt F (f x) x` at every `x` where the checked conditions hold, and the `Conditions` line
prints those conditions in display form. Each runs in the build inside `#guard_msgs`, which checks
its report.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/-! ### Polynomials in `sin u` and `cos u` -/

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (sin x ^ 2 * cos x ^ 2)
Output (scalar ℝ; antiderivative): 1/8*x + 1/8*sin(x)*cos(x) - 1/4*sin(x)*cos(x)^3

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (sin x ^ 2 * cos x ^ 2)

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (sin (2*x) ^ 2)
Output (scalar ℝ; antiderivative): 1/2*x - 1/4*sin(2*x)*cos(2*x)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (sin (2*x) ^ 2)

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (sin (x/2) ^ 4)
Output (scalar ℝ; antiderivative): 3/8*x - 5/4*sin(1/2*x)*cos(1/2*x) + 1/2*sin(1/2*x)*cos(1/2*x)^3

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (sin (x/2) ^ 4)

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (cos x ^ 6)
Output (scalar ℝ; antiderivative): 5/16*x + 5/16*sin(x)*cos(x) + 5/24*sin(x)*cos(x)^3 +
1/6*sin(x)*cos(x)^5

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (cos x ^ 6)

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (sin x ^ 3 * cos x ^ 2)
Output (scalar ℝ; antiderivative): -(1/3*cos(x)^3) + 1/5*cos(x)^5

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] (sin x ^ 3 * cos x ^ 2)

/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): ((sin x + cos x) ^ 2)
Output (scalar ℝ; antiderivative): x + sin(x)^2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integrate x] ((sin x + cos x) ^ 2)

/-! ### Quotients, by Bioche's rules -/

/-- Output (scalar ℝ; antiderivative): tan(x) - x -/
#guard_msgs (info, substring := true) in
#cas [integrate x] (tan x ^ 2)

set_option linter.style.longLine false in
/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (sin x ^ 2 / cos x ^ 2)
Output (scalar ℝ; antiderivative): sin(x)/cos(x) - x
Conditions: cos(x) ≠ 0

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked antiderivative computation
    [CAS.Command.computation] 1. Differentiate the proposed primitive
      Raw derivative: (cos(x)*1*cos(x) - sin(x)*-sin(x)*1)/cos(x)^2 - 1
    [CAS.Command.computation] 2. Form the derivative residual
      Raw residual: (cos(x)*1*cos(x) - sin(x)*-sin(x)*1)/cos(x)^2 - 1 - sin(x)^2/cos(x)^2
      Definition: CAS.IntegrationCheck.residual
    [CAS.Command.computation] 3. Check the residual normal form
      Checked residual normal form: 0
      Certificate condition: checked residual normal form = 0
    [CAS.Command.computation] 4. Record analytic domain requirements
      Certificate nonzero requirements (compacted): cos(x)
      Certificate positivity requirements (compacted): (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Integral of the input
        Proposition: ∀ (a b : ℝ),
          (∀ x ∈ Set.uIcc a b, Real.cos x ≠ 0) →
            ∫ (x : ℝ) in a..b, Real.sin x ^ 2 / Real.cos x ^ 2 =
              Real.sin b / Real.cos b - b - (Real.sin a / Real.cos a - a)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_of_line
      [CAS.explanation.checkedStep] Primitive derivative in x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0 ((𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg)).rawDerivative =
          CAS.Verified.Expr.diff 0 ((𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Primitive derivative in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0 ((𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg)).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0 ((𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg)).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Primitive derivative in x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 0 ((𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg))).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0 ((𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg))).rhs =
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 0 ((𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg)).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Primitive derivative in x: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^1),
          CAS.Verified.Expr.ValidAt x.ofLp ((𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg) →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0 ((𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg))).nonzero →
              (fderiv ℝ (fun y ↦ CAS.Verified.Expr.eval y.ofLp ((𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg)) x)
                  (EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 0 ((𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg))).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
      [CAS.explanation.checkedStep] Residual route reaches zero
        Proposition: (CAS.IntegrationCheck.route 0 ((𝕏[0].sin.pow 2).div (𝕏[0].cos.pow 2))
              { candidate := (𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg, routeZero := ⋯ }.candidate).rhs =
          0
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.routeZero
      [CAS.explanation.checkedStep] Symbolic antiderivative identity under the displayed requirements
        Proposition: ∀ (x : ℝ^1),
          { candidate := (𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg, routeZero := ⋯ }.requirements.Holds x.ofLp →
            CAS.Verified.Expr.eval x.ofLp
                (CAS.Verified.Expr.diff 0
                  { candidate := (𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg, routeZero := ⋯ }.candidate) =
              CAS.Verified.Expr.eval x.ofLp ((𝕏[0].sin.pow 2).div (𝕏[0].cos.pow 2))
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.eval_diff_eq
      [CAS.explanation.checkedStep] Coordinate-line derivative theorem
        Proposition: ∀ (x : ℝ^1) (t : ℝ),
          { candidate := (𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg, routeZero := ⋯ }.requirements.Holds
              (x.ofLp + t • (EuclideanSpace.single 0 1).ofLp) →
            HasDerivAt
              (fun s ↦
                CAS.Verified.Expr.eval (x + s • EuclideanSpace.single 0 1).ofLp
                  { candidate := (𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg, routeZero := ⋯ }.candidate)
              (CAS.Verified.Expr.eval (x + t • EuclideanSpace.single 0 1).ofLp ((𝕏[0].sin.pow 2).div (𝕏[0].cos.pow 2)))
              t
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.hasDerivAt_eval_add_smul_single
      [CAS.explanation.checkedStep] Coordinate-line fundamental theorem of calculus
        Proposition: ∀ (x : ℝ^1) (a b : ℝ),
          (∀ t ∈ Set.uIcc a b,
              { candidate := (𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg, routeZero := ⋯ }.requirements.Holds
                (x.ofLp + t • (EuclideanSpace.single 0 1).ofLp)) →
            ∫ (t : ℝ) in a..b,
                CAS.Verified.Expr.eval (x + t • EuclideanSpace.single 0 1).ofLp
                  ((𝕏[0].sin.pow 2).div (𝕏[0].cos.pow 2)) =
              CAS.Verified.Expr.eval (x + b • EuclideanSpace.single 0 1).ofLp
                  { candidate := (𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg, routeZero := ⋯ }.candidate -
                CAS.Verified.Expr.eval (x + a • EuclideanSpace.single 0 1).ofLp
                  { candidate := (𝕏[0].sin.div 𝕏[0].cos).add 𝕏[0].neg, routeZero := ⋯ }.candidate
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
-/
#guard_msgs in
#cas [integrate x] (sin x ^ 2 / cos x ^ 2)

/-- Output (scalar ℝ; antiderivative): -log(cos(x)) -/
#guard_msgs (info, substring := true) in
#cas [integrate x] (tan x)

/-- Output (scalar ℝ; antiderivative): 1/2/cos(x)^2 + log(cos(x)) -/
#guard_msgs (info, substring := true) in
#cas [integrate x] (tan x ^ 3)

set_option linter.style.longLine false in
/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (1 / (sin x * cos x))
Output (scalar ℝ; antiderivative): log(sin(x)/cos(x))
Conditions: sin(x) ≠ 0; cos(x) ≠ 0

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked antiderivative computation
    [CAS.Command.computation] 1. Differentiate the proposed primitive
      Raw derivative: (cos(x)*1*cos(x) - sin(x)*-sin(x)*1)/cos(x)^2/(sin(x)/cos(x))
    [CAS.Command.computation] 2. Form the derivative residual
      Raw residual: (cos(x)*1*cos(x) - sin(x)*-sin(x)*1)/cos(x)^2/(sin(x)/cos(x)) - 1/(sin(x)*cos(x))
      Definition: CAS.IntegrationCheck.residual
    [CAS.Command.computation] 3. Check the residual normal form
      Checked residual normal form: 0
      Certificate condition: checked residual normal form = 0
    [CAS.Command.computation] 4. Record analytic domain requirements
      Certificate nonzero requirements (compacted): sin(x)/cos(x), sin(x), cos(x)
      Certificate positivity requirements (compacted): (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Integral of the input
        Proposition: ∀ (a b : ℝ),
          (∀ x ∈ Set.uIcc a b, Real.sin x / Real.cos x ≠ 0 ∧ Real.sin x ≠ 0 ∧ Real.cos x ≠ 0) →
            ∫ (x : ℝ) in a..b, 1 / (Real.sin x * Real.cos x) =
              Real.log (Real.sin b / Real.cos b) - Real.log (Real.sin a / Real.cos a)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_of_line
      [CAS.explanation.checkedStep] Primitive derivative in x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].sin.div 𝕏[0].cos).log).rawDerivative =
          CAS.Verified.Expr.diff 0 (𝕏[0].sin.div 𝕏[0].cos).log
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Primitive derivative in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].sin.div 𝕏[0].cos).log).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].sin.div 𝕏[0].cos).log).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Primitive derivative in x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].sin.div 𝕏[0].cos).log)).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].sin.div 𝕏[0].cos).log)).rhs =
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].sin.div 𝕏[0].cos).log).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Primitive derivative in x: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^1),
          CAS.Verified.Expr.ValidAt x.ofLp (𝕏[0].sin.div 𝕏[0].cos).log →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].sin.div 𝕏[0].cos).log)).nonzero →
              (fderiv ℝ (fun y ↦ CAS.Verified.Expr.eval y.ofLp (𝕏[0].sin.div 𝕏[0].cos).log) x)
                  (EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 0 (𝕏[0].sin.div 𝕏[0].cos).log)).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
      [CAS.explanation.checkedStep] Residual route reaches zero
        Proposition: (CAS.IntegrationCheck.route 0 ((CAS.Verified.Expr.nat 1).div (𝕏[0].sin.mul 𝕏[0].cos))
              { candidate := (𝕏[0].sin.div 𝕏[0].cos).log, routeZero := ⋯ }.candidate).rhs =
          0
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.routeZero
      [CAS.explanation.checkedStep] Symbolic antiderivative identity under the displayed requirements
        Proposition: ∀ (x : ℝ^1),
          { candidate := (𝕏[0].sin.div 𝕏[0].cos).log, routeZero := ⋯ }.requirements.Holds x.ofLp →
            CAS.Verified.Expr.eval x.ofLp
                (CAS.Verified.Expr.diff 0 { candidate := (𝕏[0].sin.div 𝕏[0].cos).log, routeZero := ⋯ }.candidate) =
              CAS.Verified.Expr.eval x.ofLp ((CAS.Verified.Expr.nat 1).div (𝕏[0].sin.mul 𝕏[0].cos))
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.eval_diff_eq
      [CAS.explanation.checkedStep] Coordinate-line derivative theorem
        Proposition: ∀ (x : ℝ^1) (t : ℝ),
          { candidate := (𝕏[0].sin.div 𝕏[0].cos).log, routeZero := ⋯ }.requirements.Holds
              (x.ofLp + t • (EuclideanSpace.single 0 1).ofLp) →
            HasDerivAt
              (fun s ↦
                CAS.Verified.Expr.eval (x + s • EuclideanSpace.single 0 1).ofLp
                  { candidate := (𝕏[0].sin.div 𝕏[0].cos).log, routeZero := ⋯ }.candidate)
              (CAS.Verified.Expr.eval (x + t • EuclideanSpace.single 0 1).ofLp
                ((CAS.Verified.Expr.nat 1).div (𝕏[0].sin.mul 𝕏[0].cos)))
              t
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.hasDerivAt_eval_add_smul_single
      [CAS.explanation.checkedStep] Coordinate-line fundamental theorem of calculus
        Proposition: ∀ (x : ℝ^1) (a b : ℝ),
          (∀ t ∈ Set.uIcc a b,
              { candidate := (𝕏[0].sin.div 𝕏[0].cos).log, routeZero := ⋯ }.requirements.Holds
                (x.ofLp + t • (EuclideanSpace.single 0 1).ofLp)) →
            ∫ (t : ℝ) in a..b,
                CAS.Verified.Expr.eval (x + t • EuclideanSpace.single 0 1).ofLp
                  ((CAS.Verified.Expr.nat 1).div (𝕏[0].sin.mul 𝕏[0].cos)) =
              CAS.Verified.Expr.eval (x + b • EuclideanSpace.single 0 1).ofLp
                  { candidate := (𝕏[0].sin.div 𝕏[0].cos).log, routeZero := ⋯ }.candidate -
                CAS.Verified.Expr.eval (x + a • EuclideanSpace.single 0 1).ofLp
                  { candidate := (𝕏[0].sin.div 𝕏[0].cos).log, routeZero := ⋯ }.candidate
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
-/
#guard_msgs in
#cas [integrate x] (1 / (sin x * cos x))

/-- Output (scalar ℝ; antiderivative): cos(x) + 1/cos(x) -/
#guard_msgs (info, substring := true) in
#cas [integrate x] (sin x ^ 3 / cos x ^ 2)

set_option linter.style.longLine false in
/--
info: #cas [integrate x]
Domain: x ∈ ℝ
Input (scalar ℝ): (1 / (sin x ^ 2 * cos x ^ 2))
Output (scalar ℝ; antiderivative): sin(x)/cos(x) - 1/(sin(x)/cos(x))
Conditions: sin(x) ≠ 0; cos(x) ≠ 0

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Checked antiderivative computation
    [CAS.Command.computation] 1. Differentiate the proposed primitive
      Raw derivative: (cos(x)*1*cos(x) - sin(x)*-sin(x)*1)/cos(x)^2 + (0*sin(x)/cos(x) + 1*(cos(x)*1*cos(x) - sin(x)*-sin(x)*1)/cos(x)^2)/(sin(x)/cos(x))^2
    [CAS.Command.computation] 2. Form the derivative residual
      Raw residual: (cos(x)*1*cos(x) - sin(x)*-sin(x)*1)/cos(x)^2 + (0*sin(x)/cos(x) + 1*(cos(x)*1*cos(x) - sin(x)*-sin(x)*1)/cos(x)^2)/(sin(x)/cos(x))^2 - 1/(sin(x)^2*cos(x)^2)
      Definition: CAS.IntegrationCheck.residual
    [CAS.Command.computation] 3. Check the residual normal form
      Checked residual normal form: 0
      Certificate condition: checked residual normal form = 0
    [CAS.Command.computation] 4. Record analytic domain requirements
      Certificate nonzero requirements (compacted): sin(x)/cos(x), cos(x), sin(x)
      Certificate positivity requirements (compacted): (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Integral of the input
        Proposition: ∀ (a b : ℝ),
          (∀ x ∈ Set.uIcc a b, Real.sin x / Real.cos x ≠ 0 ∧ Real.cos x ≠ 0 ∧ Real.sin x ≠ 0) →
            ∫ (x : ℝ) in a..b, 1 / (Real.sin x ^ 2 * Real.cos x ^ 2) =
              Real.sin b / Real.cos b - 1 / (Real.sin b / Real.cos b) -
                (Real.sin a / Real.cos a - 1 / (Real.sin a / Real.cos a))
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_of_line
      [CAS.explanation.checkedStep] Primitive derivative in x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0
              ((𝕏[0].sin.div 𝕏[0].cos).add ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos)))).rawDerivative =
          CAS.Verified.Expr.diff 0
            ((𝕏[0].sin.div 𝕏[0].cos).add ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos)))
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Primitive derivative in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  ((𝕏[0].sin.div 𝕏[0].cos).add
                    ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos)))).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  ((𝕏[0].sin.div 𝕏[0].cos).add
                    ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos)))).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Primitive derivative in x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 0
                    ((𝕏[0].sin.div 𝕏[0].cos).add ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos))))).nonzero →
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      ((𝕏[0].sin.div 𝕏[0].cos).add ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos))))).rhs =
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 0
                    ((𝕏[0].sin.div 𝕏[0].cos).add
                      ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos)))).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Primitive derivative in x: analytic semantics of the displayed result
        Proposition: ∀ (x : ℝ^1),
          CAS.Verified.Expr.ValidAt x.ofLp
              ((𝕏[0].sin.div 𝕏[0].cos).add ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos))) →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      ((𝕏[0].sin.div 𝕏[0].cos).add
                        ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos))))).nonzero →
              (fderiv ℝ
                    (fun y ↦
                      CAS.Verified.Expr.eval y.ofLp
                        ((𝕏[0].sin.div 𝕏[0].cos).add ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos))))
                    x)
                  (EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 0
                        ((𝕏[0].sin.div 𝕏[0].cos).add ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos))))).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
      [CAS.explanation.checkedStep] Residual route reaches zero
        Proposition: (CAS.IntegrationCheck.route 0
              ((CAS.Verified.Expr.nat 1).div ((𝕏[0].sin.pow 2).mul (𝕏[0].cos.pow 2)))
              { candidate := (𝕏[0].sin.div 𝕏[0].cos).add ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos)),
                  routeZero := ⋯ }.candidate).rhs =
          0
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.routeZero
      [CAS.explanation.checkedStep] Symbolic antiderivative identity under the displayed requirements
        Proposition: ∀ (x : ℝ^1),
          { candidate := (𝕏[0].sin.div 𝕏[0].cos).add ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos)),
                    routeZero := ⋯ }.requirements.Holds
              x.ofLp →
            CAS.Verified.Expr.eval x.ofLp
                (CAS.Verified.Expr.diff 0
                  { candidate := (𝕏[0].sin.div 𝕏[0].cos).add ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos)),
                      routeZero := ⋯ }.candidate) =
              CAS.Verified.Expr.eval x.ofLp ((CAS.Verified.Expr.nat 1).div ((𝕏[0].sin.pow 2).mul (𝕏[0].cos.pow 2)))
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.eval_diff_eq
      [CAS.explanation.checkedStep] Coordinate-line derivative theorem
        Proposition: ∀ (x : ℝ^1) (t : ℝ),
          { candidate := (𝕏[0].sin.div 𝕏[0].cos).add ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos)),
                    routeZero := ⋯ }.requirements.Holds
              (x.ofLp + t • (EuclideanSpace.single 0 1).ofLp) →
            HasDerivAt
              (fun s ↦
                CAS.Verified.Expr.eval (x + s • EuclideanSpace.single 0 1).ofLp
                  { candidate := (𝕏[0].sin.div 𝕏[0].cos).add ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos)),
                      routeZero := ⋯ }.candidate)
              (CAS.Verified.Expr.eval (x + t • EuclideanSpace.single 0 1).ofLp
                ((CAS.Verified.Expr.nat 1).div ((𝕏[0].sin.pow 2).mul (𝕏[0].cos.pow 2))))
              t
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.IntegrationCheck.AntiderivativeCert.hasDerivAt_eval_add_smul_single
      [CAS.explanation.checkedStep] Coordinate-line fundamental theorem of calculus
        Proposition: ∀ (x : ℝ^1) (a b : ℝ),
          (∀ t ∈ Set.uIcc a b,
              { candidate := (𝕏[0].sin.div 𝕏[0].cos).add ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos)),
                      routeZero := ⋯ }.requirements.Holds
                (x.ofLp + t • (EuclideanSpace.single 0 1).ofLp)) →
            ∫ (t : ℝ) in a..b,
                CAS.Verified.Expr.eval (x + t • EuclideanSpace.single 0 1).ofLp
                  ((CAS.Verified.Expr.nat 1).div ((𝕏[0].sin.pow 2).mul (𝕏[0].cos.pow 2))) =
              CAS.Verified.Expr.eval (x + b • EuclideanSpace.single 0 1).ofLp
                  { candidate := (𝕏[0].sin.div 𝕏[0].cos).add ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos)),
                      routeZero := ⋯ }.candidate -
                CAS.Verified.Expr.eval (x + a • EuclideanSpace.single 0 1).ofLp
                  { candidate := (𝕏[0].sin.div 𝕏[0].cos).add ((CAS.Verified.Expr.int (-1)).div (𝕏[0].sin.div 𝕏[0].cos)),
                      routeZero := ⋯ }.candidate
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
-/
#guard_msgs in
#cas [integrate x] (1 / (sin x ^ 2 * cos x ^ 2))

/-- Output (scalar ℝ; antiderivative): 2*atan(2*sin(x)/cos(x)/sqrt(8))/sqrt(8) -/
#guard_msgs (info, substring := true) in
#cas [integrate x] (1 / (1 + cos x ^ 2))

/-! ### Other quotients, by the tangent half-angle substitution -/

/-- Output (scalar ℝ; antiderivative): 4*atan(2*sin(x)/(1 + cos(x))/sqrt(12))/sqrt(12) -/
#guard_msgs (info, substring := true) in
#cas [integrate x] (1 / (2 + cos x))

/-- Output (scalar ℝ; antiderivative): 1/2*atan(1/2*sin(x)/(1 + cos(x))) -/
#guard_msgs (info, substring := true) in
#cas [integrate x] (1 / (5 + 3 * cos x))

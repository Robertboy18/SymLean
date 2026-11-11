/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Tactic.DerivativeBridge

/-!
# Checked identities between ordinary real expressions

The checked identity route of bare `cas`. `closeRealIdentity` proves an ordinary equality
`lhs = rhs` between real terms, and `closeReflectedEquality` proves a goal that is already
reflected, `Verified.Expr.eval ρ a = Verified.Expr.eval ρ b` or `Verified.Expr.eval ρ a = 0`, as
the fallback of the raw symbolic route.
The route proves exactly the identities of the checked normal form: polynomial and rational
algebra, the square-root and logarithm passes, the real-power algebra of
`CAS.ClosedForm.Pipeline.Passes.RealPower` (`a ^ p * a ^ q = a ^ (p + q)`,
`(a ^ p) ^ q = a ^ (p * q)`, `(a * b) ^ p = a ^ p * b ^ p`, `a ^ (b - 1) = a ^ b / a`,
`a ^ (-b) = 1 / a ^ b`, `a ^ (2 : ℝ) = a ^ 2`, `√a = a ^ (1/2 : ℝ)`), and exponential
recombination (`exp a * exp b = exp (a + b)`, `exp u ^ 2 = exp (2 * u)`). An identity that
holds only under a positivity condition fails, naming the condition, when neither the context
nor the `using` evidence proves it.

## Main definitions

* `closeRealIdentity`: an ordinary real equality, by `DerivativeBridge.closeRealEqualityGoal`.
* `closeReflectedEquality`: a reflected equality, in the goal's own environment.

## Implementation notes

We reflect both sides over one shared table of atoms (every maximal subterm that is not an
operation of the checked language, such as a variable, a cast, or a norm), and the kernel runs
the side-conditioned normalizer `CAS.Verified.Expr.sideConditionPipeline` of
`CAS/ClosedForm/Pipeline/Configured.lean` on the difference of the two reflections. The run is
certified by `decide +kernel` and becomes an equality through
`CAS.Verified.Expr.eval_eq_of_sideConditionPipeline_run_essential`
(`DerivativeBridge.certifyZeroDifference`). When the pipeline does not reduce the difference to
zero, the multivariate canonical form `Verified.Expr.Alg.canonicalForm` of
`CAS/ClosedForm/Canonical.lean` is run on it in the same way
(`DerivativeBridge.certifyCanonicalZeroDifference`): it cancels the polynomial gcd of numerator
and denominator over the atoms and canonicalizes the arguments of the elementary functions
bottom-up, so that `(x^4 - y^4) / (x^2 - y^2) = x^2 + y^2` closes under `x^2 - y^2 ≠ 0` and
`exp ((x^2 - y^2) / (x - y)) = exp (x + y)` under `x - y ≠ 0`. Its gcd comes from untrusted
code, and the canonical form uses it only when the check `Canonical.Reduction.valid` accepts it.

The conditions the normalizer recorded (nonvanishing denominators and cancelled factors, positive
bases of real powers and square roots) are discharged from the local context by
`DerivativeBridge.closeValidity`, with the evidence of a `using` clause when one is supplied.
Finally each reflection is identified with its ordinary term by the lowering bridge, and the
proof `lhs = rhs` is assembled and checked before it is assigned; the shared core is
`DerivativeBridge.closeRealEqualityGoal`, which the derivative finisher uses as well. For a
reflected goal we introduce no atoms: the pipeline runs on `a - b` in the goal's own
environment, and the recorded conditions are discharged the same way.
-/

public meta section

namespace CAS.Tactic.Identity

open Lean Elab Tactic Meta
open DerivativeBridge KernelReadBack

/--
Close the main goal, an ordinary equality `lhs = rhs` between real terms, with the checked
side-conditioned normalizer, or with the multivariate canonical form when the normalizer does not
reduce the difference to zero (`DerivativeBridge.closeRealEqualityGoal`). Analytic conditions
recorded by the normalizer are proved from the local context, or from `evidence?` when
supplied; the goal is left unchanged on failure.
-/
def closeRealIdentity (operation : String) (evidence? : Option (TSyntax `term)) :
    TacticM Unit := withMainContext do
  closeRealEqualityGoal operation (← getMainGoal) evidence?
  replaceMainGoal []

/-- The environment and expression of an evaluation `Verified.Expr.eval ρ e`. -/
private def evaluationArguments? (term : Expr) : Option (Expr × Expr) :=
  let term := term.consumeMData
  if term.isAppOfArity ``Verified.Expr.eval 3 then
    some (term.getAppArgs[1]!, term.getAppArgs[2]!)
  else
    none

/-- Prove `Verified.Expr.eval ρ (Verified.Expr.nat 0) = 0`. -/
private def evaluationOfZero (operation : String) (environment index : Expr) : MetaM Expr := do
  let zero ← mkAppOptM ``Verified.Expr.nat #[some index, some (toExpr (0 : Nat))]
  let evaluation ← mkAppM ``Verified.Expr.eval #[environment, zero]
  let zeroReal ← mkAppOptM ``OfNat.ofNat #[some (mkConst ``Real), some (mkRawNatLit 0), none]
  let goal ← mkFreshExprSyntheticOpaqueMVar (← mkEq evaluation zeroReal)
  let remaining ←
    try
      withSuppressedMessagesMeta <| runTacticOnGoal goal.mvarId!
        (← `(tactic| simp only [Verified.Expr.eval, Nat.cast_zero]))
    catch _ =>
      throwError "{operation} internal error: the evaluation of the literal zero did not reduce"
  unless remaining.isEmpty do
    throwError "{operation} internal error: the evaluation of the literal zero did not reduce"
  instantiateMVars goal

/--
Close the main goal, a reflected equality `Verified.Expr.eval ρ a = Verified.Expr.eval ρ b`,
`Verified.Expr.eval ρ a = 0`, or `0 = Verified.Expr.eval ρ a` over a `Fin` index type, with the
checked side-conditioned normalizer run on `a - b` in the goal's own environment, and with the
multivariate canonical form when that leaves a residual (`DerivativeBridge.certifyZeroDifference`).
This is the fallback of the raw symbolic route when the unconditional normalizer, the fraction
normal form, and the canonical form of `symbolic_eq` do not reach zero, for example when the
identity needs the real-power or elementary passes. The recorded conditions are discharged
from the local context, or from `evidence?`; the goal is left unchanged on failure.
-/
def closeReflectedEquality (operation : String) (evidence? : Option (TSyntax `term)) :
    TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (_, lhs, rhs) := target.consumeMData.eq?
    | throwError "{operation} reflected route expected an equality"
  let (environment, reflectedLhs, reflectedRhs, zeroSide) ←
    match evaluationArguments? lhs, evaluationArguments? rhs with
    | some (environment, a), some (environment', b) => do
        unless ← isDefEq environment environment' do
          throwError "{operation} reflected route: the two sides use different environments"
        pure (environment, a, b, none)
    | some (environment, a), none => do
        unless rhs.consumeMData.zero? ∨ (← isDefEq rhs (← mkAppOptM ``OfNat.ofNat
            #[some (mkConst ``Real), some (mkRawNatLit 0), none])) do
          throwError "{operation} reflected route expected an evaluation or the literal zero"
        let index := (← whnf (← inferType a)).appArg!
        let zero ← mkAppOptM ``Verified.Expr.nat #[some index, some (toExpr (0 : Nat))]
        pure (environment, a, zero, some false)
    | none, some (environment, b) => do
        unless lhs.consumeMData.zero? ∨ (← isDefEq lhs (← mkAppOptM ``OfNat.ofNat
            #[some (mkConst ``Real), some (mkRawNatLit 0), none])) do
          throwError "{operation} reflected route expected an evaluation or the literal zero"
        let index := (← whnf (← inferType b)).appArg!
        let zero ← mkAppOptM ``Verified.Expr.nat #[some index, some (toExpr (0 : Nat))]
        pure (environment, zero, b, some true)
    | none, none =>
        throwError "{operation} reflected route expected an evaluation of a checked expression"
  let index ← KernelReadBack.finIndexOfType (← inferType reflectedLhs)
  let (claim, sideGoal) ←
    certifyZeroDifference operation index environment reflectedLhs reflectedRhs
  closeValidity operation sideGoal evidence?
  let claim ← instantiateMVars claim
  let proof ←
    match zeroSide with
    | none => pure claim
    | some false => mkEqTrans claim (← evaluationOfZero operation environment index)
    | some true => mkEqTrans (← mkEqSymm (← evaluationOfZero operation environment index)) claim
  let proof ← instantiateMVars proof
  if proof.hasMVar ∨ proof.hasSorry then
    throwError "{operation} produced incomplete identity evidence"
  unless ← isTypeCorrect proof do
    throwError "{operation} produced ill-typed identity evidence"
  unless ← isDefEq (← inferType proof) target do
    throwError "{operation} produced evidence for a different reflected equality"
  goal.assign proof
  replaceMainGoal []

end CAS.Tactic.Identity

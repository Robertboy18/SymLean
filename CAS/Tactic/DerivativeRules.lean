/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import CAS.Tactic.KernelReadBack
public meta import CAS.Tactic.KernelReadBack
public meta import CAS.Tactic.ProofCarrier

/-!
# Extending scalar differentiation with checked theorems

`@[cas_deriv]` registers a theorem whose conclusion is `HasDerivAt`. These rules work with
ordinary Lean functions, so adding a function does not require changing the reflected grammar.
Mathlib supplies the arithmetic and chain rules. Scalar fields and codomains are inferred from
the goal; in particular, the same route handles real and complex derivatives.

## Main definitions

* `derive?` proves `HasDerivAt f D x` and returns the computed value `D` with its proof.
* `hasRule` tells whether a registered rule concludes a derivative of a given function head.

## Implementation notes

`derive?` leaves the value `D` as a metavariable that the rules assign, and the caller compares
it with a stated value afterwards. The search works backwards with backtracking on each
`HasDerivAt` goal: it tries an assumption, the local `HasDerivAt` hypotheses, the registered
rules, the rules for `Real.exp`, `Real.sin`, `Real.cos`, `Real.sinh`, `Real.cosh` and their
complex counterparts, and the arithmetic rule of the head (`HasDerivAt.add`, `HasDerivAt.mul`,
`HasDerivAt.pow` and similar). When none applies, we split the application `outer (inner t)`
syntactically rather than ask unification to invent a composition, prove the inner derivative
first, and combine the two by `HasDerivAt.comp`. Rule premises must be proved, the premises
other than derivatives by a fixed list of closing tactics such as `positivity` and `nlinarith`.
Registration adds no analytic assumption and no evaluation axiom. The search has a work budget
(`cas.maxDerivativeSteps`), restores the proof state if it cannot finish, and returns only a
completed proof (`ProofCarrier.checkCompletedProof`). The rules are Mathlib's or the user's; the
search order is ours.
-/

public meta section

namespace CAS.Tactic.DerivativeRules

open Lean Meta Elab Tactic

/-- Trace the derivative rule search: the rules tried on each `HasDerivAt` goal and the error of
each rule that fails. -/
initialize registerTraceClass `cas.derivativeRules

private initialize registry : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    name := `CAS.Tactic.DerivativeRules.registry
    addImportedFn := fun states ↦ states.foldl (fun names state ↦
      state.foldl (fun names name ↦
        if names.contains name then names else names.push name) names) #[]
    addEntryFn := fun names name ↦ if names.contains name then names else names.push name
  }

private def conclusion : Expr → Expr
  | .forallE _ _ body _ => conclusion body
  | type => type.consumeMData

/-- Register an analytic derivative theorem for ordinary functions. A definition of the
current module whose rule is registered stays folded until the rules have been tried, so the
rule applies to it rather than to its unfolded body. -/
syntax (name := casDerivRuleAttr) "cas_deriv" : attr

initialize registerBuiltinAttribute {
  name := `casDerivRuleAttr
  descr := "register a checked HasDerivAt theorem for CAS differentiation"
  add := fun name _ kind ↦ do
    unless kind == .global do throwAttrMustBeGlobal `cas_deriv kind
    let info ← getConstInfo name
    -- A module exports its theorems as axioms, and in a module file the handler sees that view
    -- of the theorems of the current module and of the imported ones.
    unless (info.isTheorem || info.isAxiom) &&
        (conclusion info.type).isAppOfArity ``HasDerivAt 10 do
      throwError "@[cas_deriv] requires a theorem whose conclusion is HasDerivAt"
    modifyEnv fun env ↦ registry.addEntry env name
}

/-- Whether a registered `@[cas_deriv]` theorem concludes `HasDerivAt f _ _` for a function `f`
headed by the constant `name`. -/
def hasRule (name : Name) : MetaM Bool := do
  let env ← getEnv
  for rule in registry.getState env do
    let some info := env.find? rule
      | continue
    if (conclusion info.type).getAppArgs[7]!.eta.getAppFn.isConstOf name then
      return true
  return false

/-- The largest number of recursive steps of the rule search for one derivative (the `@[cas_deriv]`
rules and the analytic rules); past it the search fails with an error that names the option. -/
register_option cas.maxDerivativeSteps : Nat := {
  defValue := 512
  descr := "maximum recursive steps in CAS analytic derivative rule search"
}

private def applicationBody (function binder : Expr) : MetaM Expr := do
  let function ← withTransparency .reducible <| whnf function
  return (← Core.betaReduce (mkApp function binder)).consumeMData

private def rulesFor (function point : Expr) : MetaM (Array Name) := do
  withLocalDeclD `t (← inferType point) fun binder ↦ do
    let body ← applicationBody function binder
    if body == binder then return #[``hasDerivAt_id']
    unless body.containsFVar binder.fvarId! do return #[``hasDerivAt_const]
    let head := body.getAppFn
    if head.isConstOf ``HAdd.hAdd then return #[``HasDerivAt.add]
    if head.isConstOf ``HSub.hSub then return #[``HasDerivAt.sub]
    if head.isConstOf ``HMul.hMul then return #[``HasDerivAt.mul]
    if head.isConstOf ``HDiv.hDiv then return #[``HasDerivAt.div]
    if head.isConstOf ``Neg.neg then return #[``HasDerivAt.neg]
    if head.isConstOf ``Inv.inv then return #[``HasDerivAt.inv]
    if body.isAppOfArity ``HPow.hPow 6 && body.getAppArgs[1]!.isConstOf ``Nat then
      return #[``HasDerivAt.pow]
    return #[]

private def analyticRules : Array Name :=
  #[``Real.hasDerivAt_exp, ``Real.hasDerivAt_sin, ``Real.hasDerivAt_cos,
    ``Real.hasDerivAt_sinh, ``Real.hasDerivAt_cosh,
    ``Complex.hasDerivAt_exp, ``Complex.hasDerivAt_sin, ``Complex.hasDerivAt_cos,
    ``Complex.hasDerivAt_sinh, ``Complex.hasDerivAt_cosh]

private def proveDerivative : Nat → MVarId → StateT Nat TacticM Unit
  | 0, _ => throwError "CAS derivative rules reached their recursion limit"
  | depth + 1, goal => goal.withContext do
      if ← goal.isAssigned then return
      let remaining ← get
      if remaining = 0 then throwError "CAS derivative rules exhausted cas.maxDerivativeSteps"
      set (remaining - 1)
      let target ← instantiateMVars (← goal.getType)
      if ← goal.assumptionCore then return
      if target.isForall then
        let (_, next) ← goal.intro1
        proveDerivative depth next
        return
      unless target.isAppOfArity ``HasDerivAt 10 do
        let goals ← KernelReadBack.runTacticOnGoal goal
          (← `(tactic| first | assumption | positivity | (simp_all; done) |
            (norm_num; done) | linarith | nlinarith))
        unless goals.isEmpty do throwError "unproved derivative rule premise:{indentExpr target}"
        return
      for declaration in ← getLCtx do
        unless declaration.isImplementationDetail do
          if (conclusion declaration.type).isAppOfArity ``HasDerivAt 10 then
            let saved ← liftM (saveState : TacticM Tactic.SavedState)
            try
              let goals ← goal.apply (mkFVar declaration.fvarId)
              for subgoal in goals do proveDerivative depth subgoal
              return
            catch error =>
              saved.restore
              if error.isRuntime then throw error
      let arguments := target.getAppArgs
      let function := arguments[7]!
      let point := arguments[9]!
      let rules := (registry.getState (← getEnv)) ++ analyticRules ++
        (← rulesFor function point)
      trace[cas.derivativeRules] "Applicable derivative rules: {rules}"
      for name in rules do
        let saved ← liftM (saveState : TacticM Tactic.SavedState)
        try
          let goals ← goal.applyConst name
          for subgoal in goals do proveDerivative depth subgoal
          return
        catch error =>
          saved.restore
          if error.isRuntime then throw error
          if name.getPrefix == `HasDerivAt then
            trace[cas.derivativeRules] "{name}: {error.toMessageData}"
      -- Split the actual application, rather than asking unification to invent a composition.
      let composed ← withLocalDeclD `t (← inferType point) fun binder ↦ do
        let body ← applicationBody function binder
        unless body.isApp do return none
        let outer := body.appFn!
        let innerBody := body.appArg!
        if outer.containsFVar binder.fvarId! || innerBody == binder ||
            !innerBody.containsFVar binder.fvarId! then return none
        let inner ← mkLambdaFVars #[binder] innerBody
        return some (outer, inner)
      if let some (outer, inner) := composed then
        let innerPoint := mkApp inner point
        let innerValue ← mkFreshExprMVar (← inferType innerPoint)
        let outerValue ← mkFreshExprMVar (← inferType (mkApp outer innerPoint))
        let innerGoal ← mkFreshExprSyntheticOpaqueMVar
          (← mkAppM ``HasDerivAt #[inner, innerValue, point])
        let outerGoal ← mkFreshExprSyntheticOpaqueMVar
          (← mkAppM ``HasDerivAt #[outer, outerValue, innerPoint])
        proveDerivative depth innerGoal.mvarId!
        proveDerivative depth outerGoal.mvarId!
        -- Fix the inner function before checking its value at the point: that value alone
        -- cannot determine a function, particularly after reducing natural powers.
        let proof ← mkAppOptM ``HasDerivAt.comp
          #[none, none, some point, none, none, none, some inner, some outer,
            some (← instantiateMVars innerValue), some (← instantiateMVars outerValue),
            some (← instantiateMVars outerGoal), some (← instantiateMVars innerGoal)]
        unless ← isDefEq (← inferType proof) target do
          throwError "the derivative chain rule does not match the requested function"
        goal.assign proof
        return
      throwError "no analytic derivative rule matched:{indentExpr target}"

/-- Prove `HasDerivAt function derivative point` by analytic rules, returning the computed
value and its proof. The derivative value is inferred from the rules before any comparison with
an expected answer. Failure returns `none` and restores the tactic state. -/
def derive? (function point : Expr) : TacticM (Option (Expr × Expr)) :=
  ProofCarrier.restoringStateOnNone <| withMainContext do
    try
      let value ← mkFreshExprMVar (← inferType (mkApp function point))
      let goal ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HasDerivAt #[function, value, point])
      let budget := cas.maxDerivativeSteps.get (← getOptions)
      discard <| (proveDerivative 64 goal.mvarId!).run budget
      let proof ← ProofCarrier.checkCompletedProof "CAS analytic derivative rules" goal
      return some (← instantiateMVars value, proof)
    catch error =>
      if error.isRuntime then throw error
      trace[cas.derivativeRules] "{error.toMessageData}"
      return none

end CAS.Tactic.DerivativeRules

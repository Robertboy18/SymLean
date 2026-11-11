/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Tactic.DerivativeBridge
public meta import CAS.Tactic.DerivativeBridge

/-!
# Nested scalar derivative elimination

Nested ordinary real derivatives that depend on the differentiated variable are
rewritten inner-first through the checked scalar derivative bridge. Derivative
values independent of that variable remain arbitrary scalar coefficients. Every
rewrite carries a proof; unsupported varying derivatives or unmet analytic
conditions are reported by `eliminateInnerDerivatives`.

## Implementation notes

`eliminateInnerDerivatives` rewrites an inner `deriv g` as a function, which needs the analytic
conditions of `g` at every real point. We run it as a post-procedure of `simp`
(`innerDerivativeSimproc`), so the body of `g` is simplified before `deriv g` itself, and
derivative values already constant in the initial context are frozen before `simp` enters
them. Each rewrite is proved by `innerDerivativeFunction` from `scalarHasDerivAt`,
`HasDerivAt.deriv`, and function extensionality.

`eliminateNestedNear` works near the evaluation point
instead: validity of `g` at the point persists on a neighbourhood
(`Verified.Expr.deriv_eval_lineEmbed_eventuallyEq`), where `deriv g` agrees with the symbolic
derivative, and the outer derivative only depends on the function near the point
(`Filter.EventuallyEq.deriv_eq`). So `deriv (fun x ↦ deriv Real.sqrt x) x` is eliminated under
`0 < x`. The neighbourhood occurs only inside the proofs: each agreement is composed with the
continuity of the inner argument (`Filter.EventuallyEq.comp_tendsto`, `HasDerivAt.continuousAt`)
and the steps are chained by `Filter.EventuallyEq.trans`. The filter lemmas are Mathlib's; the
two elimination routes are ours.
-/

public meta section

namespace CAS.Tactic.DerivativeBridge

open Lean Elab Tactic Meta

/-- Whether `expression` contains a `deriv` application that mentions `binder`. -/
def containsVaryingDeriv (expression binder : Expr) : Bool :=
  (expression.find? fun term ↦
    term.getAppFn.consumeMData.isConstOf ``deriv &&
      term.containsFVar binder.fvarId!).isSome

/--
Prove `deriv g = fun s ↦ D s` for an ordinary function `g : ℝ → ℝ` whose body has no
remaining derivative depending on `s`, by reflection at an arbitrary point of the line.

Validity of the reflected body at every real point is required: `closeValidity` proves it at
an arbitrary point, so this only succeeds for bodies whose analytic conditions it proves there
(for example polynomials, trigonometric and exponential functions, and their sums and
products); `eliminateNestedNear` needs them at the evaluation point only. Nondefinitional
lowerings, such as the exponential forms of hyperbolic functions,
are transported through the same checked function equality as an ordinary derivative.
-/
def innerDerivativeFunction
    (operation : String) (function : Expr) (evidence? : Option (TSyntax `term)) :
    MetaM (Expr × Expr) := do
  let real := mkConst ``Real
  unless ← isDefEq (← inferType function) (← mkArrow real real) do
    throwError "{operation} nested derivative: the inner function is not of type ℝ → ℝ"
  withLocalDeclD `s real fun s ↦ do
    let body ← withTransparency .reducible <| whnf (mkApp function s)
    if containsVaryingDeriv body s then
      throwError "{operation} nested derivative: an inner derivative could not be eliminated"
    let derivative ← scalarHasDerivAt operation s body s evidence?
    let (hasDeriv, functionGoal?) ←
      transportToFunction derivative function fun g ↦
        mkAppM ``HasDerivAt #[g, derivative.value, s]
    closeMatchingGoals operation functionGoal? none derivative evidence?
    let pointwise ← mkAppM ``HasDerivAt.deriv #[hasDeriv]
    let equalityAt ← mkExpectedTypeHint pointwise
      (← mkEq (← mkAppM ``deriv #[function, s]) derivative.value)
    let equality ← mkFunExt (← mkLambdaFVars #[s] equalityAt)
    let replacement ← mkLambdaFVars #[s] derivative.value
    let derivFunction ← mkAppM ``deriv #[function]
    let equality ← mkExpectedTypeHint equality (← mkEq derivFunction replacement)
    return (replacement, equality)

/-- The simproc rewriting an unapplied `deriv g` for `g : ℝ → ℝ` to its evaluated
symbolic derivative function. Failures are recorded and leave the term unchanged. -/
def innerDerivativeSimproc
    (operation : String) (evidence? : Option (TSyntax `term))
    (failure : IO.Ref (Option MessageData)) : Simp.Simproc := fun e ↦ do
  unless e.getAppFn.consumeMData.isConstOf ``deriv && e.getAppNumArgs > 0 do
    return .continue
  -- Only the unapplied derivative `deriv g : ℝ → ℝ` is rewritten; applied occurrences
  -- reach this simproc through the extra-argument mechanism of the simproc index.
  let real := mkConst ``Real
  unless ← isDefEq (← inferType e) (← mkArrow real real) do
    return .continue
  let function := e.appArg!
  try
    -- Simp runs its procedures at reducible transparency; the bridge needs to unfold
    -- ordinary definitions such as `Fin.castAdd`.
    let (replacement, proof) ←
      withTransparency .default <| innerDerivativeFunction operation function evidence?
    return .visit { expr := replacement, proof? := some proof }
  catch error =>
    failure.set (some error.toMessageData)
    return .continue

/--
Rewrite nested `deriv` applications depending on `binder` inside the real term `body`
to ordinary syntax for their symbolic derivatives, inner-first.

Returns the rewritten body and a proof of `body = body'`, or `none` when `body` mentions
no varying derivative. Constant derivative values are opaque scalar parameters, even
when their underlying functions have no regularity hypotheses. Fails when a varying
nested derivative cannot be eliminated.
-/
def eliminateInnerDerivatives
    (operation : String) (binder body : Expr) (evidence? : Option (TSyntax `term)) :
    TacticM (Option (Expr × Expr)) := do
  unless containsVaryingDeriv body binder do
    return none
  let unfolding ← unfoldEvaluationTactic
  let { ctx, simprocs, .. } ← mkSimpContext unfolding (eraseLocal := false)
  let defaults ← Simp.getSimprocs
  let failure ← IO.mkRef (none : Option MessageData)
  let real := mkConst ``Real
  let pattern ← mkAppM ``deriv #[← mkFreshExprMVar (← mkArrow real real)]
  let keys ← withConfigWithKey ctx.indexConfig <| DiscrTree.mkPath pattern
  let custom : Simprocs :=
    ({} : Simprocs).addCore keys ``innerDerivativeSimproc true
      (.inl (innerDerivativeSimproc operation evidence? failure))
  let initialContext ← getLCtx
  -- Variables opened while simplifying an inner function must also remain variable.
  -- Only derivative values already constant in the initial context are frozen.
  let isConstantDerivative (term : Expr) : MetaM Bool := do
    unless term.getAppFn.consumeMData.isConstOf ``deriv &&
        !term.hasLooseBVars &&
        !(term.hasAnyFVar fun id ↦
          id == binder.fvarId! || (initialContext.find? id).isNone) do
      return false
    Elaboration.RealExpression.hasType term real
  let methods := Simp.mkDefaultMethodsCore (simprocs ++ #[defaults, custom])
  let methods := { methods with
    pre := fun term ↦ do
      if ← isConstantDerivative term then return .done { expr := term }
      methods.pre term
    dpre := fun term ↦ do
      if ← isConstantDerivative term then return .done term
      methods.dpre term }
  let (result, _) ←
    Simp.main body ctx (methods := methods)
  if containsVaryingDeriv result.expr binder then
    match ← failure.get with
    | some reason =>
        throwError
          "{operation} could not eliminate a nested derivative as a function, which needs \
           its analytic conditions at every point.\n{reason}"
    | none =>
        throwError
          "{operation} could not eliminate a nested derivative: only ordinary derivatives \
           of functions ℝ → ℝ are supported inside a differentiated body"
  return some (result.expr, ← result.getProof)

/-! ## Elimination near the evaluation point -/

/-- The outermost applied derivatives `deriv g a` in `expression` that mention `binder` and
have no loose bound variables. -/
private partial def outerVaryingDerivatives (arity : Nat) (binder expression : Expr)
    (found : Array Expr) : Array Expr :=
  let expression := expression.consumeMData
  if expression.isAppOfArity ``deriv arity && expression.containsFVar binder.fvarId! &&
      !expression.hasLooseBVars then
    if found.contains expression then found else found.push expression
  else
    let visit := outerVaryingDerivatives arity binder
    match expression with
    | .app function argument => visit argument (visit function found)
    | .lam _ type body _ | .forallE _ type body _ => visit body (visit type found)
    | .letE _ type value body _ => visit body (visit value (visit type found))
    | .proj _ _ projected => visit projected found
    | _ => found

/-- `Tendsto (fun binder ↦ argument) (𝓝 point) (𝓝 a₀)` with `a₀` the argument at the point,
from the checked derivative of the argument. -/
private def argumentTendsto (operation : String) (binder argument point : Expr)
    (evidence? : Option (TSyntax `term)) : MetaM Expr := do
  if argument.isFVar && argument.fvarId! == binder.fvarId! then
    return ← mkAppOptM ``Filter.tendsto_id #[none, some (← mkAppM ``nhds #[point])]
  let derivative ← scalarHasDerivAt operation binder argument point evidence?
  let function ← mkLambdaFVars #[binder] argument
  let (hasDeriv, functionGoal?) ← transportToFunction derivative function fun g ↦
    mkAppM ``HasDerivAt #[g, derivative.value, point]
  closeMatchingGoals operation functionGoal? none derivative evidence?
  let continuous ← mkAppM ``HasDerivAt.continuousAt #[← instantiateMVars hasDeriv]
  mkAppM ``ContinuousAt.tendsto #[continuous]

/-- Unfold the checked evaluator in `value`: the ordinary form and a proof of `value = form`. -/
private def unfoldEvaluatedValue (value : Expr) : TacticM (Expr × Expr) := do
  let { ctx, simprocs, .. } ← mkSimpContext (← unfoldEvaluationTactic) (eraseLocal := false)
  let (result, _) ← Simp.main value ctx (methods := Simp.mkDefaultMethodsCore simprocs)
  return (result.expr, ← result.getProof)

mutual

/-- A function `function'` without varying nested derivatives and a proof of
`function =ᶠ[𝓝 point] function'`, or `none` when `function` has no varying derivative. -/
private partial def eliminateNear (operation : String) (function point : Expr)
    (evidence? : Option (TSyntax `term)) : TacticM (Option (Expr × Expr)) := do
  let real := mkConst ``Real
  let neighbourhoods ← mkAppM ``nhds #[point]
  let arity := (← getConstInfo ``deriv).type.getNumHeadForalls
  let result? ← withLocalDeclD `t real fun binder ↦ do
    let body ← withTransparency .reducible <| whnf (mkApp function binder)
    let occurrences := outerVaryingDerivatives arity binder body #[]
    if occurrences.isEmpty then
      if containsVaryingDeriv body binder then
        throwError "{operation} cannot eliminate a nested derivative under a binder near the \
          point"
      return none
    let mut current := body
    let mut proof? : Option Expr := none
    for occurrence in occurrences do
      let arguments := occurrence.getAppArgs
      let inner := arguments[arguments.size - 2]!
      let argument := arguments[arguments.size - 1]!
      if inner.containsFVar binder.fvarId! then
        throwError "{operation} nested derivative: the inner function{indentExpr inner}\n\
          depends on the outer variable"
      if containsVaryingDeriv argument binder then
        throwError "{operation} nested derivative: a derivative evaluated at a varying \
          derivative is not supported"
      let (derivative, nearArgument) ←
        derivativeNear operation inner (argument.replaceFVar binder point) evidence?
      let composed ← mkAppM ``Filter.EventuallyEq.comp_tendsto
        #[nearArgument, ← argumentTendsto operation binder argument point evidence?]
      let replacement := (mkApp derivative argument).headBeta
      let abstracted ← kabstract current occurrence
      let next := abstracted.instantiate1 replacement
      let pointwise ← mkLambdaFVars #[binder] (← mkEq occurrence replacement)
      let rewritten ← mkLambdaFVars #[binder] (← mkEq current next)
      let step ← withLocalDeclD `h (← mkEq occurrence replacement) fun h ↦ do
        mkLambdaFVars #[binder, h] (← mkCongrArg (.lam `v real abstracted .default) h)
      let eventual ← mkAppOptM ``Filter.Eventually.mono
        #[none, some pointwise, some rewritten, some neighbourhoods, some composed, some step]
      let eventual ← mkExpectedTypeHint eventual (← mkAppM ``Filter.EventuallyEq
        #[neighbourhoods, ← mkLambdaFVars #[binder] current, ← mkLambdaFVars #[binder] next])
      proof? ← match proof? with
        | none => pure (some eventual)
        | some previous => some <$> mkAppM ``Filter.EventuallyEq.trans #[previous, eventual]
      current := next
    if containsVaryingDeriv current binder then
      throwError "{operation} could not eliminate every nested derivative near the point"
    let some proof := proof?
      | return none
    return some (← mkLambdaFVars #[binder] current, proof)
  let some (function', proof) := result?
    | return none
  let stated ← mkAppM ``Filter.EventuallyEq #[neighbourhoods, function, function']
  return some (function', ← mkExpectedTypeHint proof stated)

/-- The derivative `D` of `function` near `point`, in ordinary syntax, and a proof of
`deriv function =ᶠ[𝓝 point] D`. Validity of the reflected body is needed at `point` only. -/
private partial def derivativeNear (operation : String) (function point : Expr)
    (evidence? : Option (TSyntax `term)) : TacticM (Expr × Expr) := do
  let real := mkConst ``Real
  let neighbourhoods ← mkAppM ``nhds #[point]
  let (function', agreement?) ← match ← eliminateNear operation function point evidence? with
    | none => pure (function, none)
    | some (function', agreement) => pure (function', some agreement)
  let key ← withLocalDeclD `s real fun binder ↦ do
    let body ← withTransparency .reducible <| whnf (mkApp function' binder)
    let reflection ← RealExpression.reflectEmbedded operation #[binder] #[binder] body
    let k := reflection.parameterCount
    let index ← RealExpression.embeddedCoordinate 1 k 0
    applyBridge operation ``Verified.Expr.deriv_eval_lineEmbed_eventuallyEq
      #[some (toExpr k), some reflection.expression, some reflection.parameters, some point,
        some index, some (← mkEqRefl (mkNatLit 0))] 1 evidence?
  let arguments := (← instantiateMVars (← inferType key)).getAppArgs
  let reflected := arguments[3]!.appArg!
  let value := arguments[4]!
  let key ←
    if ← isDefEq function' reflected then
      mkExpectedTypeHint key
        (← mkAppM ``Filter.EventuallyEq #[neighbourhoods, ← mkAppM ``deriv #[function'], value])
    else
      let equality ← mkFreshExprSyntheticOpaqueMVar (← mkEq function' reflected)
      let derivative : Derivative :=
        { proof := key, function := reflected, value, pointCoordinates := #[point],
          parameters := #[] }
      closeMatchingGoals operation (some equality.mvarId!) none derivative evidence?
      let motive ← withLocalDeclD `f (← inferType function') fun f ↦ do
        mkLambdaFVars #[f]
          (← mkAppM ``Filter.EventuallyEq #[neighbourhoods, ← mkAppM ``deriv #[f], value])
      mkEqMPR (← mkCongrArg motive (← instantiateMVars equality)) key
  let key ← match agreement? with
    | none => pure key
    | some agreement =>
        mkAppM ``Filter.EventuallyEq.trans #[← mkAppM ``Filter.EventuallyEq.deriv #[agreement], key]
  let (derivative, unfolded) ← unfoldEvaluatedValue value
  let motive ← withLocalDeclD `F (← mkArrow real real) fun F ↦ do
    mkLambdaFVars #[F]
      (← mkAppM ``Filter.EventuallyEq #[neighbourhoods, ← mkAppM ``deriv #[function], F])
  return (derivative, ← mkEqMP (← mkCongrArg motive unfolded) key)

end

/--
Eliminate the varying nested derivatives of `function : ℝ → ℝ` near `point`.

Returns a function `function'` without varying nested derivatives and a proof of
`function =ᶠ[𝓝 point] function'`, or `none` when `function` has no varying derivative. Each
inner `deriv g a` is replaced by the symbolic derivative of `g` at `a`, which agrees with it
near `point` when the body of `g` is valid at the value of `a` at `point`; the argument `a`
must be differentiable at `point`. Only validity at the point is checked, by the same
side-condition closers as an ordinary derivative.
-/
def eliminateNestedNear (operation : String) (function point : Expr)
    (evidence? : Option (TSyntax `term)) : TacticM (Option (Expr × Expr)) :=
  eliminateNear operation function point evidence?

end CAS.Tactic.DerivativeBridge

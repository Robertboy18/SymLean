/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Tactic.DerivativeBridge.NestedScalar
public meta import CAS.Tactic.DerivativeBridge.NestedScalar
public import CAS.Tactic.DerivativeRegistry
public meta import CAS.Tactic.DerivativeRegistry

/-!
# Closed-form rewriting of derivative subterms in identities

Residual identities such as `deriv (deriv f) t - deriv (deriv g) x = 0`, or differences
of repeated `partialDeriv`s of an explicit function, are not a single derivative
statement, so the derivative frontends refuse them, and the ordinary arithmetic route
sees the derivative applications as opaque atoms. Bare `cas` therefore runs a pre-pass on
an ordinary equality, disequality, or order relation before the arithmetic route:

1. every maximal subterm of the goal that is an ordinary derivative of an explicit
   elementary function, namely `deriv f x` (nested derivatives included),
   and, with a Euclidean backend registered through `CAS.Tactic.DerivativeRegistry`, its
   coordinate derivatives on `ℝ^n` with a literal `n`, is proved
   equal to its checked closed form and the goal is rewritten with that equation;
2. when the arithmetic route then fails, the real-valued definitions of the current module
   occurring in the goal are unfolded, as the derivative frontends unfold them (imported
   definitions stay folded), and the route is retried.

## Implementation notes

Each equation is the theorem the derivative route of `cas` would prove for
`subterm = rhs` with `rhs` the evaluated symbolic derivative: the body is reflected
through `CAS.Tactic.DerivativeBridge`, the bridge theorem of
`CAS.Calculus.ParameterEmbedding` is applied, its validity obligation is
discharged by `closeValidity` (with the `using` evidence when given), and the evaluated
derivative is unfolded to ordinary syntax by the same `simp only` script the derivative
frontends use. Every rewrite is therefore a kernel-checked equation. Nested derivatives are
eliminated first, as functions by `eliminateInnerDerivatives` and, when the inner conditions
fail somewhere, near the point by `eliminateNestedNear` and `Filter.EventuallyEq.deriv_eq`. A
subterm of a registered Euclidean backend gets its equation from `DerivativeRegistry.equation`.
The derivative theorems are those of `CAS/Calculus/ParameterEmbedding.lean`, and the rewriting
pre-pass is ours.

The rewriting is all or nothing: when one derivative subterm cannot be closed, the goal
is left unchanged, and the caller reports the derivative that could not be closed together
with the outcome of the arithmetic route on the unchanged goal. A goal
that the arithmetic route already closes with its own simplification lemmas (for example
one whose only derivatives are Mathlib's total `deriv Real.log`) is therefore still
closed.
-/

public meta section

namespace CAS.Tactic.DerivativeRewrite

open Lean Elab Tactic Meta
open DerivativeBridge

/-- The name of the tactic in diagnostics. -/
def operation : String := "cas"

/-! ## Current-module definitions -/

/-- Real-valued definitions of the current module occurring in `target` that can be unfolded:
structure projections and instances are kept folded. -/
private def unfoldableLocalDefinitions (target : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  (← statedLocalDefinitions target).filterM fun name ↦ do
    if env.isProjectionFn name then
      return false
    return !(← isInstance name)

/--
Unfold the real-valued definitions of the current module occurring in the main goal, as the
derivative frontends do for the differentiated function and the stated derivative. Imported
definitions are never unfolded. The pass repeats while it makes progress, up to `fuel` times,
and reports whether the goal changed. The identity route runs it only as a retry after the
arithmetic route has failed on the goal as stated, since a definition may name an analytic
object (a supremum, an integral) that the arithmetic treats as an atom.
-/
def unfoldLocalRealDefinitions : (fuel : Nat := 16) → TacticM Bool
  | 0 =>
      pure false
  | fuel + 1 => do
      let unfolded ← withMainContext do
        let target ← instantiateMVars (← getMainTarget)
        let definitions ← unfoldableLocalDefinitions target
        if definitions.isEmpty then
          return false
        unfoldDefinitions definitions
        let rewritten ← withMainContext do instantiateMVars (← getMainTarget)
        return rewritten != target
      if unfolded then
        discard <| unfoldLocalRealDefinitions fuel
      return unfolded

/-! ## Recognising derivative subterms -/

/-- The function and point of an ordinary real derivative `deriv f x` with `f : ℝ → ℝ`. The
unapplied `deriv f` is not recognised: its last argument is the function, not a real point. -/
private def scalarDerivative? (expression : Expr) : MetaM (Option (Expr × Expr)) := do
  let expression := expression.consumeMData
  unless expression.getAppFn.consumeMData.isConstOf ``deriv do
    return none
  let arguments := expression.getAppArgs
  unless 2 ≤ arguments.size do
    return none
  let function := arguments[arguments.size - 2]!
  let point := arguments[arguments.size - 1]!
  let real := mkConst ``Real
  unless ← Elaboration.RealExpression.hasType point real do
    return none
  unless ← Elaboration.RealExpression.hasType function (← mkArrow real real) do
    return none
  return some (function, point)

/-- Whether `expression` is a derivative application the pre-pass rewrites. -/
private def isDerivativeTerm (expression : Expr) : TacticM Bool := do
  if expression.hasLooseBVars then
    return false
  if (← scalarDerivative? expression).isSome then
    return true
  return ← DerivativeRegistry.isTerm expression

/--
Collect the maximal derivative subterms of `expression`, without duplicates. Binders are not
entered: a derivative under a `fun` cannot be rewritten in place, and it is handled by the
nested-derivative elimination of the enclosing derivative when there is one.
-/
private def collectDerivativeTerms (expression : Expr) (found : Array Expr) :
    TacticM (Array Expr) := do
  let stripped := expression.consumeMData
  if ← isDerivativeTerm stripped then
    return if found.contains stripped then found else found.push stripped
  match expression with
  | .app function argument =>
      collectDerivativeTerms argument (← collectDerivativeTerms function found)
  | .proj _ _ body => collectDerivativeTerms body found
  | .mdata _ body => collectDerivativeTerms body found
  | _ => return found

/-! ## Closed forms -/

/-- Close the optional function-identification goal left by `transportToFunction`. -/
def closeFunctionGoal (functionGoal? : Option MVarId) : MetaM Unit := do
  let some functionGoal := functionGoal?
    | return
  let remaining ← mathlibCleanup (← unfoldEvaluation [functionGoal])
  unless remaining.isEmpty do
    throwError
      "{operation} could not identify the differentiated function with its reflected form"

/-- Unfold the checked evaluator in the computed derivative `value`, returning the ordinary
real term and the proof that it equals `value`. -/
private def unfoldValue (value : Expr) : TacticM (Expr × Expr) := do
  let unfolding ← unfoldEvaluationTactic
  let { ctx, simprocs, .. } ← mkSimpContext unfolding (eraseLocal := false)
  let defaults ← Simp.getSimprocs
  let (result, _) ←
    Simp.main value ctx (methods := Simp.mkDefaultMethodsCore (simprocs ++ #[defaults]))
  return (result.expr, ← result.getProof)

/-- Given `equation : lhs = value` with `lhs` definitionally the derivative subterm `term`,
return a proof of `term = value'` where `value'` is `value` in ordinary real syntax. -/
def finishEquation (term equation : Expr) : TacticM Expr := do
  let equationType ← instantiateMVars (← inferType equation)
  let some (_, _, value) := equationType.eq?
    | throwError "{operation} internal error: the derivative theorem is not an equality"
  let (unfolded, valueEquality) ← unfoldValue value
  let proof ← mkEqTrans equation valueEquality
  let statement ← mkEq term unfolded
  unless ← isDefEq (← inferType proof) statement do
    throwError
      "{operation} internal error: the closed form of{indentExpr term}\n\
       does not restate the derivative subterm"
  mkExpectedTypeHint proof statement

/-- Rewrite the nested derivatives inside a function `ℝ → ℝ`, returning the rewritten
function and the proof of the function equality when there was anything to rewrite. -/
private def eliminateNested (function : Expr) (evidence? : Option (TSyntax `term)) :
    TacticM (Expr × Option Expr) := do
  let real := mkConst ``Real
  withLocalDeclD `t real fun binder ↦ do
    let body ← withTransparency .reducible <| whnf (mkApp function binder)
    match ← eliminateInnerDerivatives operation binder body evidence? with
    | none => return (function, none)
    | some (rewrittenBody, proof) =>
        let rewrittenFunction ← mkLambdaFVars #[binder] rewrittenBody
        let equality ← mkFunExt (← mkLambdaFVars #[binder] proof)
        let equality ← mkExpectedTypeHint equality (← mkEq function rewrittenFunction)
        return (rewrittenFunction, some equality)

/-- A function `function'` without varying nested derivatives and a proof of
`deriv function point = deriv function' point`, when `function` has nested derivatives. The
equality comes from the function equality of `eliminateNested` or, when the inner conditions
fail somewhere, from the agreement of the two functions near `point`
(`eliminateNestedNear`, `Filter.EventuallyEq.deriv_eq`), which needs them at the point only. -/
private def eliminateNestedAt (function point : Expr) (evidence? : Option (TSyntax `term)) :
    TacticM (Expr × Option Expr) := do
  let real := mkConst ``Real
  try
    let (rewrittenFunction, functionEquality?) ← eliminateNested function evidence?
    let some functionEquality := functionEquality?
      | return (function, none)
    let motive ← withLocalDeclD `g (← mkArrow real real) fun g ↦ do
      mkLambdaFVars #[g] (← mkAppM ``deriv #[g, point])
    return (rewrittenFunction, some (← mkCongrArg motive functionEquality))
  catch everywhere =>
    let near? ← tryCatch (eliminateNestedNear operation function point evidence?) fun near ↦
      throwError
        "{operation} could not eliminate the nested derivatives.\n\
         With the inner conditions at every point:{indentD everywhere.toMessageData}\n\
         Near the point, with the inner conditions there:{indentD near.toMessageData}"
    let some (rewrittenFunction, agreement) := near?
      | throw everywhere
    return (rewrittenFunction, some (← mkAppM ``Filter.EventuallyEq.deriv_eq #[agreement]))

/-- The equation `deriv function point = closedForm` for an ordinary scalar derivative. -/
private def scalarEquation
    (term function point : Expr) (evidence? : Option (TSyntax `term)) : TacticM Expr := do
  let real := mkConst ``Real
  unless ← Elaboration.RealExpression.hasType point real do
    throwError "{operation} rewrites ordinary real derivatives only; the point is not real"
  let function ← withTransparency .reducible <| whnf function
  unless ← Elaboration.RealExpression.hasType function (← mkArrow real real) do
    let functionType ← inferType function
    throwError
      "{operation} rewrites derivatives of functions ℝ → ℝ; the differentiated function has \
       type{indentExpr functionType}"
  let (rewrittenFunction, nestedEquation?) ← eliminateNestedAt function point evidence?
  let derivative ←
    withLocalDeclD `t real fun binder ↦ do
      let body ← withTransparency .reducible <| whnf (mkApp rewrittenFunction binder)
      unless ← Elaboration.RealExpression.hasType body real do
        let codomain ← inferType body
        throwError
          "{operation} rewrites real-valued derivatives; the function codomain is\
           {indentExpr codomain}"
      scalarHasDerivAt operation binder body point evidence?
  let (hasDeriv, functionGoal?) ←
    transportToFunction derivative rewrittenFunction fun g ↦
      mkAppM ``HasDerivAt #[g, derivative.value, point]
  closeFunctionGoal functionGoal?
  let equation ← mkAppM ``HasDerivAt.deriv #[hasDeriv]
  let equation ←
    match nestedEquation? with
    | none => pure equation
    | some nestedEquation => mkEqTrans nestedEquation equation
  finishEquation term equation

/-- The checked equation `term = closedForm` for one derivative subterm. -/
private def closedFormEquation (term : Expr) (evidence? : Option (TSyntax `term)) :
    TacticM Expr := do
  if let some (function, point) ← scalarDerivative? term then
    return ← scalarEquation term function point evidence?
  if ← DerivativeRegistry.isTerm term then
    return ← DerivativeRegistry.equation term evidence?
  throwError "{operation} internal error: unrecognised derivative subterm{indentExpr term}"

/-- Rewrite every maximal derivative subterm of the main goal to its checked closed form. -/
private def rewriteDerivativeTerms (evidence? : Option (TSyntax `term)) : TacticM Unit := do
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  let terms ← withMainContext do collectDerivativeTerms target #[]
  if terms.isEmpty then
    return
  let equations ← withMainContext do
    terms.mapM fun term ↦ do
      try
        closedFormEquation term evidence?
      catch error =>
        throwError
          "the derivative subterm{indentExpr term}\ncould not be rewritten to a checked \
           closed form:{indentD error.toMessageData}"
  let mut goal ← getMainGoal
  for equation in equations do
    let target ← instantiateMVars (← goal.getType)
    let result ← goal.rewrite target equation
    unless result.mvarIds.isEmpty do
      throwError "{operation} internal error: rewriting a derivative subterm left auxiliary goals"
    goal ← goal.replaceTargetEq result.eNew result.eqProof
  replaceMainGoal [goal]

/--
Prepare an ordinary identity goal for the arithmetic route: rewrite every maximal derivative
subterm to its checked closed form. Definitions of the current module hiding a derivative's
body are unfolded by the reflection itself.

Returns `none` when every derivative subterm was rewritten (or there was none), and the
description of the failure otherwise; in that case the goal is left unchanged, so the
arithmetic route still runs on a goal whose derivative terms are opaque atoms.
-/
def prepareIdentity (evidence? : Option (TSyntax `term)) : TacticM (Option MessageData) := do
  let saved ← saveState
  try
    rewriteDerivativeTerms evidence?
    return none
  catch error =>
    saved.restore
    return some error.toMessageData

end CAS.Tactic.DerivativeRewrite

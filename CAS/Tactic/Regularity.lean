/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.Smoothness
public import CAS.Tactic.DerivativeBridge

/-!
# Reflection of ordinary regularity goals

A theorem-facing bridge from ordinary Mathlib regularity
statements about explicit elementary functions to the checked symbolic
language. It accepts

* `DifferentiableAt ℝ f x`, `DifferentiableOn ℝ f s`, and `Differentiable ℝ f`,
* `ContDiffAt ℝ n f x`, `ContDiffOn ℝ n f s`, and `ContDiff ℝ n f`,
* `ContinuousAt f x`, `ContinuousOn f s`, and `Continuous f`,
* `AnalyticAt ℝ f x` and `AnalyticOnNhd ℝ f s`,

for functions `f : ℝ → ℝ` and `f : ℝ^k → ℝ` with a literal dimension `k`, the
body written with the coordinate projections `q 0, …, q (k - 1)` and any
binder-independent real parameters. The smoothness order `n : WithTop ℕ∞` may be
a natural literal, `(⊤ : ℕ∞)`, a variable, or the analytic order. The scalar
`DifferentiableAt` shape is handled by the derivative frontend instead.

## Implementation notes

The body is reflected exactly as by the derivative frontends
(`CAS.Tactic.RealDeriv`): the
function argument occupies the first coordinates and every binder-independent real
subterm is frozen as a parameter, so the reflected function is definitionally the
user's function whenever reflection used only definitional lowerings. We then apply the bridge
theorem of `CAS/Calculus/Smoothness.lean` that `bridgeTheorem` selects for the predicate, in its
`lineEmbed` form on `ℝ` and its `paramEmbed` form on `ℝ^k`. The smoothness forms rest on
`Verified.Expr.contDiffAt_eval`, an induction over the expression with Mathlib's smoothness
lemmas, which hold for every order. Continuity, differentiability on a set, and analyticity are
read off them at the orders `0`, `1`, and `ω` (analyticity by `ContDiffAt.analyticAt`).
`DifferentiableAt` and `Differentiable` come from the derivative theorems of
`CAS/Calculus/ParameterEmbedding.lean`. The validity hypothesis is discharged by
`CAS.Tactic.DerivativeBridge.closeValidity`, with the user's `using` evidence when given. For
the predicates on a set or on the whole space the validity obligation is universally quantified
over the set or the space; for polynomial, exponential, and trigonometric bodies it is trivial,
and otherwise the same nonzero and positivity facts as for a derivative are required at every
point. After a nondefinitional lowering, `transportToFunction` proves the function equality by
unfolding the checked evaluator and running the Mathlib normalization script. The regularity
facts are Mathlib's; the reflection and the choice of bridge theorem are ours.

The tactic fails closed: a symbolic dimension, a non-real codomain, an
unsupported operation, or an unprovable domain condition leaves the goal unchanged
and the error names the obstruction.
-/

public meta section

namespace CAS.Tactic.Regularity

open Lean Elab Tactic Meta
open DerivativeBridge

/-- The regularity predicates accepted by the bridge. -/
inductive Predicate where
  /-- `DifferentiableAt ℝ f x`. -/
  | differentiableAt (point : Expr)
  /-- `Differentiable ℝ f`. -/
  | differentiable
  /-- `ContDiffAt ℝ n f x`. -/
  | contDiffAt (order point : Expr)
  /-- `ContDiffOn ℝ n f s`. -/
  | contDiffOn (order set : Expr)
  /-- `ContDiff ℝ n f`. -/
  | contDiff (order : Expr)
  /-- `ContinuousAt f x`. -/
  | continuousAt (point : Expr)
  /-- `ContinuousOn f s`. -/
  | continuousOn (set : Expr)
  /-- `Continuous f`. -/
  | continuous
  /-- `DifferentiableOn ℝ f s`. -/
  | differentiableOn (set : Expr)
  /-- `AnalyticAt ℝ f x`. -/
  | analyticAt (point : Expr)
  /-- `AnalyticOnNhd ℝ f s`. -/
  | analyticOnNhd (set : Expr)

/-- A recognised regularity goal. -/
structure Shape where
  /-- The regularity predicate and its point, set, or order data. -/
  predicate : Predicate
  /-- The function whose regularity is claimed. -/
  function : Expr
  /-- The domain type `E` of the function. -/
  domain : Expr
  /-- The position of the function among the arguments of the predicate. -/
  functionIndex : Nat

/-- The domain of a function whose regularity the bridge can certify. -/
inductive Domain where
  /-- Functions `ℝ → ℝ`, reflected along the affine coordinate line. -/
  | scalar
  /-- Functions `ℝ^dimension → ℝ` with a literal dimension, reflected through the parameter
  embedding. -/
  | euclidean (dimension : Nat)

/-- The predicates whose function is followed by at most a point or a set: the name, whether
the first argument is the scalar field `ℝ`, the number of arguments after the function, and the
predicate built from the last argument. -/
private def pointwisePredicates : List (Name × Bool × Nat × (Expr → Predicate)) :=
  [(``ContinuousAt, false, 1, .continuousAt), (``ContinuousOn, false, 1, .continuousOn),
   (``Continuous, false, 0, fun _ ↦ .continuous),
   (``DifferentiableOn, true, 1, .differentiableOn), (``AnalyticAt, true, 1, .analyticAt),
   (``AnalyticOnNhd, true, 1, .analyticOnNhd)]

/-- Recognise the regularity shape of a proposition about a real-valued function over the
scalar field `ℝ`, if any. -/
def shape? (target : Expr) : MetaM (Option Shape) := do
  let target := target.consumeMData
  let arguments := target.getAppArgs
  let real := mkConst ``Real
  let overReals (scalarField codomain : Expr) : MetaM Bool := do
    unless scalarField.consumeMData.isConstOf ``Real do
      return false
    isDefEqGuarded codomain real
  if target.isAppOfArity ``DifferentiableAt 12 then
    unless ← overReals arguments[0]! arguments[6]! do
      return none
    return some
      { predicate := .differentiableAt arguments[11]!, function := arguments[10]!
        domain := arguments[2]!, functionIndex := 10 }
  if target.isAppOfArity ``Differentiable 11 then
    unless ← overReals arguments[0]! arguments[6]! do
      return none
    return some
      { predicate := .differentiable, function := arguments[10]!
        domain := arguments[2]!, functionIndex := 10 }
  if target.isAppOfArity ``ContDiffAt 11 then
    unless ← overReals arguments[0]! arguments[5]! do
      return none
    return some
      { predicate := .contDiffAt arguments[8]! arguments[10]!, function := arguments[9]!
        domain := arguments[2]!, functionIndex := 9 }
  if target.isAppOfArity ``ContDiffOn 11 then
    unless ← overReals arguments[0]! arguments[5]! do
      return none
    return some
      { predicate := .contDiffOn arguments[8]! arguments[10]!, function := arguments[9]!
        domain := arguments[2]!, functionIndex := 9 }
  if target.isAppOfArity ``ContDiff 10 then
    unless ← overReals arguments[0]! arguments[5]! do
      return none
    return some
      { predicate := .contDiff arguments[8]!, function := arguments[9]!
        domain := arguments[2]!, functionIndex := 9 }
  for (name, overScalars, trailing, predicate) in pointwisePredicates do
    let arity := (← getConstInfo name).type.getNumHeadForalls
    unless target.isAppOfArity name arity do
      continue
    if overScalars && !arguments[0]!.consumeMData.isConstOf ``Real then
      return none
    let functionIndex := arity - 1 - trailing
    let function := arguments[functionIndex]!
    let .forallE _ domain codomain _ ← whnfR (← inferType function)
      | return none
    if codomain.hasLooseBVars then
      return none
    unless ← isDefEqGuarded codomain real do
      return none
    return some
      { predicate := predicate arguments[arity - 1]!, function, domain, functionIndex }
  return none

/-- Classify the domain of a recognised goal, failing closed with a message that names the
obstruction. -/
def resolveDomain (shape : Shape) : MetaM Domain := do
  if ← isDefEqGuarded shape.domain (mkConst ``Real) then
    return .scalar
  match ← euclideanDimension? shape.domain with
  | some (some dimension) => return .euclidean dimension
  | some none =>
      throwError
        "{operation} certifies regularity on ℝ^n only for a literal dimension n; the \
         function has domain{indentExpr shape.domain}\n\
         Restate the claim in a fixed dimension, or prove it from the coordinate lemmas."
  | none =>
      throwError
        "{operation} certifies regularity of functions ℝ → ℝ and ℝ^n → ℝ with a literal \
         dimension n; the function has domain{indentExpr shape.domain}"

/--
Whether a proposition is a regularity goal served by this bridge: one of the accepted predicates
for a real-valued function, except `DifferentiableAt` for a function on `ℝ`, which the
derivative frontend serves.
-/
def isRegularityGoal (target : Expr) : MetaM Bool := do
  let some shape ← shape? target
    | return false
  match shape.predicate with
  | .differentiableAt _ => return !(← isDefEqGuarded shape.domain (mkConst ``Real))
  | _ => return true

/-- Expose current-module definitions that conceal the dependence of the function on its
argument, so that the goal and the reflected body share one definitional presentation. -/
private def unfoldDependentLocalDefinitions : TacticM Unit :=
  unfoldLocalDefinitionsWhile do
    let target ← instantiateMVars (← getMainTarget)
    let some shape ← shape? target
      | return #[]
    unless ← Elaboration.RealExpression.hasType shape.function
        (← mkArrow shape.domain (mkConst ``Real)) do
      return #[]
    dependentLocalDefinitions shape.domain shape.function

/-- The bridge theorem of `CAS.Calculus.Smoothness` for a predicate, in the line
convention (`euclidean = false`) or the parameter-embedding convention. -/
private def bridgeTheorem (predicate : Predicate) (euclidean : Bool) : Name :=
  match predicate, euclidean with
  | .differentiableAt _, false => ``Verified.Expr.differentiableAt_eval_lineEmbed
  | .differentiable, false => ``Verified.Expr.differentiable_eval_lineEmbed
  | .contDiffAt _ _, false => ``Verified.Expr.contDiffAt_eval_lineEmbed
  | .contDiffOn _ _, false => ``Verified.Expr.contDiffOn_eval_lineEmbed
  | .contDiff _, false => ``Verified.Expr.contDiff_eval_lineEmbed
  | .continuousAt _, false => ``Verified.Expr.continuousAt_eval_lineEmbed
  | .continuousOn _, false => ``Verified.Expr.continuousOn_eval_lineEmbed
  | .continuous, false => ``Verified.Expr.continuous_eval_lineEmbed
  | .differentiableOn _, false => ``Verified.Expr.differentiableOn_eval_lineEmbed
  | .analyticAt _, false => ``Verified.Expr.analyticAt_eval_lineEmbed
  | .analyticOnNhd _, false => ``Verified.Expr.analyticOnNhd_eval_lineEmbed
  | .differentiableAt _, true => ``Verified.Expr.differentiableAt_eval_paramEmbed
  | .differentiable, true => ``Verified.Expr.differentiable_eval_paramEmbed
  | .contDiffAt _ _, true => ``Verified.Expr.contDiffAt_eval_paramEmbed
  | .contDiffOn _ _, true => ``Verified.Expr.contDiffOn_eval_paramEmbed
  | .contDiff _, true => ``Verified.Expr.contDiff_eval_paramEmbed
  | .continuousAt _, true => ``Verified.Expr.continuousAt_eval_paramEmbed
  | .continuousOn _, true => ``Verified.Expr.continuousOn_eval_paramEmbed
  | .continuous, true => ``Verified.Expr.continuous_eval_paramEmbed
  | .differentiableOn _, true => ``Verified.Expr.differentiableOn_eval_paramEmbed
  | .analyticAt _, true => ``Verified.Expr.analyticAt_eval_paramEmbed
  | .analyticOnNhd _, true => ``Verified.Expr.analyticOnNhd_eval_paramEmbed

/-- The smoothness order and the explicit point or set arguments of a predicate. -/
private def predicateArguments (predicate : Predicate) : Option Expr × Array Expr :=
  match predicate with
  | .differentiableAt point | .continuousAt point | .analyticAt point => (none, #[point])
  | .differentiable | .continuous => (none, #[])
  | .contDiffAt order point => (some order, #[point])
  | .contDiffOn order set => (some order, #[set])
  | .contDiff order => (some order, #[])
  | .continuousOn set | .differentiableOn set | .analyticOnNhd set => (none, #[set])

/-- Reflect the body of the function over `coordinates` (terms in the `binder`) and prove the
regularity statement for the reflected function. -/
private def reflectedProof
    (shape : Shape) (binder : Expr) (coordinates : Array Expr) (body : Expr)
    (dimension? : Option Nat) (evidence? : Option (TSyntax `term)) : MetaM Expr := do
  unless ← Elaboration.RealExpression.hasType body (mkConst ``Real) do
    let codomain ← inferType body
    throwError
      "{operation} certifies regularity of real-valued functions; the function codomain \
       is{indentExpr codomain}"
  let reflection ← RealExpression.reflectEmbedded operation #[binder] coordinates body
  let k := reflection.parameterCount
  let (order?, explicitArguments) := predicateArguments shape.predicate
  let dimensionArguments : Array (Option Expr) :=
    match dimension? with
    | some dimension => #[some (toExpr dimension), some (toExpr k)]
    | none => #[some (toExpr k)]
  let arguments :=
    dimensionArguments ++ order?.toArray.map some ++
      #[some reflection.expression, some reflection.parameters] ++ explicitArguments.map some
  applyBridge operation (bridgeTheorem shape.predicate dimension?.isSome) arguments 1 evidence?
    "regularity" m!"{operation} internal error: the regularity theorem has too few hypotheses"

/--
Transport a regularity proof about the reflected function to the user's function.

When the two are definitionally equal the proof is reused as is. Otherwise (after the
lowering of `abs`, `tan`, or a hyperbolic function) the function equality is proved by
unfolding the checked evaluator and the Mathlib normalisation script.
-/
private def transportToFunction (shape : Shape) (target proof : Expr) : MetaM Expr := do
  let proofType ← instantiateMVars (← inferType proof)
  let reflected := proofType.getAppArgs[shape.functionIndex]!
  if ← isDefEq shape.function reflected then
    return proof
  let equality ← mkFreshExprSyntheticOpaqueMVar (← mkEq shape.function reflected)
  let remaining ← mathlibCleanup (← unfoldEvaluation [equality.mvarId!])
  unless remaining.isEmpty do
    throwError
      "{operation} could not identify the stated function with its reflected form\
       {indentExpr shape.function}"
  let functionType ← inferType shape.function
  let motive ←
    withLocalDeclD `g functionType fun g ↦ do
      let arguments := target.getAppArgs.set! shape.functionIndex g
      mkLambdaFVars #[g] (mkAppN target.getAppFn arguments)
  let congruence ← mkCongrArg motive (← instantiateMVars equality)
  mkEqMPR congruence proof

/-- Assign the main goal with `proof`, requiring definitional agreement of types. -/
private def finish (proof : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let proofType ← instantiateMVars (← inferType proof)
  unless ← isDefEq proofType target do
    throwError
      "{operation} constructed a proof of{indentExpr proofType}\n\
       but the goal is{indentExpr target}"
  goal.assign (← instantiateMVars proof)
  replaceMainGoal []

private def closeShape (shape : Shape) (evidence? : Option (TSyntax `term)) : TacticM Unit := do
  let domain ← resolveDomain shape
  let target ← instantiateMVars (← getMainTarget)
  let real := mkConst ``Real
  let function ← withTransparency .reducible <| whnf shape.function
  let shape := { shape with function }
  let proof ←
    match domain with
    | .scalar =>
        withLocalDeclD `t real fun binder ↦ do
          let body ← withTransparency .reducible <| whnf (mkApp function binder)
          reflectedProof shape binder #[binder] body none evidence?
    | .euclidean dimension =>
        withLocalDeclD `q shape.domain fun binder ↦ do
          let body ← withTransparency .reducible <| whnf (mkApp function binder)
          let coordinates ← coordinateTerms binder dimension
          reflectedProof shape binder coordinates body (some dimension) evidence?
  let proof ← transportToFunction shape target proof
  finish proof

/--
Close a regularity goal about an explicit elementary function: `DifferentiableAt ℝ f x`,
`DifferentiableOn ℝ f s`, `Differentiable ℝ f`, `ContDiffAt ℝ n f x`, `ContDiffOn ℝ n f s`,
`ContDiff ℝ n f`, `ContinuousAt f x`, `ContinuousOn f s`, `Continuous f`, `AnalyticAt ℝ f x`,
or `AnalyticOnNhd ℝ f s` for `f : ℝ → ℝ` or `f : ℝ^k → ℝ` with a literal `k` and any
smoothness order `n`.
-/
def close (evidence? : Option (TSyntax `term) := none) : TacticM Unit := do
  unfoldDependentLocalDefinitions
  exposeCheckedExpressions operation
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some shape ← shape? target
      | throwError
          "{operation} expected a `DifferentiableAt`, `DifferentiableOn`, `Differentiable`, \
           `ContDiffAt`, `ContDiffOn`, `ContDiff`, `ContinuousAt`, `ContinuousOn`, \
           `Continuous`, `AnalyticAt`, or `AnalyticOnNhd` statement over ℝ about a real-valued \
           function"
    closeShape shape evidence?

end CAS.Tactic.Regularity

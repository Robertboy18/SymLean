/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import CAS.Tactic.DerivativeBridge.NestedScalar
public meta import CAS.Tactic.DerivativeBridge.NestedScalar
public import CAS.Tactic.DerivativeRules
public meta import CAS.Tactic.DerivativeRules
public import CAS.Tactic.Regularity

/-!
# Ordinary scalar derivative goals

A theorem-facing bridge from ordinary Mathlib syntax about scalar derivatives
to the checked symbolic derivative language. It accepts

* `deriv (fun t : ℝ ↦ body) x₀ = rhs` (and `rhs = deriv … x₀`),
* `iteratedDeriv n f x₀ = rhs` and `iteratedDerivWithin n f s x₀ = rhs` for a literal `n`,
* `HasDerivAt (fun t : ℝ ↦ body) f' x₀`,
* `HasDerivWithinAt (fun t : ℝ ↦ body) f' s x₀`, and
* `DifferentiableAt ℝ (fun t : ℝ ↦ body) x₀`,

where the function may also be a named function `ℝ → ℝ` (a lambda applied after
`show`, `unfold`, or `simp only`). Mathlib's derivative predicates require a normed scalar
field, so discrete domains such as `ℕ` and `ℤ` are not accepted.

## Implementation notes

`close` tries the routes in a fixed order. Iterated derivatives are expanded first. A matching
hypothesis and the theorem rules of `CAS/Tactic/DerivativeRules.lean` come next, and the value
the rules propose is compared with the stated one by a fixed list of closing tactics. Varying
nested derivatives are then eliminated, a `deriv` equality is offered to the Mathlib shortcuts,
and the body is finally reflected through `CAS/Tactic/DerivativeBridge.lean`. The
differentiation rules are classical, and the proofs rest on Mathlib's derivative lemmas and on
`Verified.Expr.hasDerivAt_eval_lineEmbed` (`CAS/Calculus/ParameterEmbedding.lean`); the route
order and the treatment of nested and iterated derivatives are ours.

For a goal such as

```lean
deriv (fun t : ℝ ↦ Real.sin t + a * t ^ 2) x = Real.cos x + 2 * a * x
```

the reifier assigns coordinate zero to `t`. Every real subterm independent of
`t` is frozen as a parameter coordinate, so parameters may be arbitrary
real-valued Lean terms, including casts from `ℕ`, `ℤ`, and `ℚ`. The resulting
expression is proved with `Verified.Expr.hasDerivAt_eval_lineEmbed`, whose
statement about the reflected function is definitionally the user's statement
for every definitional lowering; reflection itself is therefore not part of
the trusted base. The computed derivative is identified with the stated one by
`CAS.Tactic.DerivativeBridge.closeMatchingGoals`, which falls back to
the checked side-conditioned normalizer when Mathlib's normal forms differ (for
example when `(√u)² = u` is needed). A divisor independent of `t` is kept as the inverse of a
parameter (`exposeConstantDivisors`), so the certificate needs no nonzero fact for it.

Nested derivatives such as `deriv (fun x ↦ deriv (fun y ↦ Real.sin (a * y)) x) x₀`
are handled inner-first: each varying inner `deriv g` is rewritten to the ordinary
syntax of its symbolic derivative (`DerivativeBridge.eliminateInnerDerivatives`),
and the outer derivative is then reflected as usual. Rewriting `deriv g` as a function
needs the inner body's analytic conditions at every point. When they fail somewhere, as
for `Real.sqrt` or `Real.log`, the inner derivatives are replaced near the evaluation
point instead (`DerivativeBridge.eliminateNestedNear`), where they agree with the symbolic
derivative, and `Filter.EventuallyEq.deriv_eq` transfers the outer derivative; the
conditions are then checked at the point only. A fixed value such as `deriv u a`
in `fun t ↦ deriv u a * t` is a scalar coefficient and requires no regularity of `u`.

An iterated derivative `iteratedDeriv n f` with a literal order `n` is first rewritten to
`n` nested derivatives (`iteratedDeriv_succ`, `iteratedDeriv_zero`), and
`iteratedDerivWithin n f s x` to `iteratedDeriv n f x` by `iteratedDerivWithin_eq_iteratedDeriv`.
Its conditions `UniqueDiffOn ℝ s` and `x ∈ s` come from a hypothesis or are proved for `univ`, a
half-line or an interval with nonempty interior, and `ContDiffAt ℝ n f x` is proved by
`Regularity`.

Before reflection, `DerivativeRules` tries Mathlib's arithmetic and chain rules,
registered `@[cas_deriv]` theorems, and derivative families in the local context.
A current-module definition with a registered rule stays folded until these rules have
been tried; the other definitions of the current module are unfolded first.
This route accepts ordinary functions outside the reflected grammar, including
complex exponential and trigonometric functions. Each theorem's premises must
be proved; a branch condition is never inferred from a function's name.
The reflected fallback remains real-valued.

Before reifying a `deriv` equality, `closeDerivEq` recognises five function heads and
closes the goal with a Mathlib lemma instead of the reflective route: `abs` (via
`deriv_abs`), `Real.log` (`Real.deriv_log`), `Real.sinh` and `Real.cosh`
(`Real.deriv_sinh`, `Real.deriv_cosh`), and `Real.tan` (`Real.deriv_tan`). These lemmas
are stated for the totalized `deriv`, so they carry no domain hypothesis:
`deriv Real.log 0 = 0⁻¹` and `deriv Real.tan (π / 2) = 1 / Real.cos (π / 2) ^ 2` are
theorems of Mathlib (both sides are `0`), and `cas` proves them without any
validity check. Only these five bare heads are treated this way. For `abs` and `Real.log` the
lemma is applied by `convert` and the remaining goals are closed by `simp_all`; when some stay
open, the reflective route runs. For the other three, a stated right-hand side that is not
literally the lemma's, as in `deriv Real.tan x = 1 + Real.tan x ^ 2`, is identified with the
lemma's value by the checked identity core
(`DerivativeBridge.closeRealEqualityGoal`): `tan` is lowered to `sin / cos`, the difference
is brought to one fraction, and the Pythagorean pass rewrites its numerator to zero. That
identity records `cos x ≠ 0`, which has to come from the context or the `using` evidence,
since the two sides differ where the cosine vanishes. A composed function
such as `fun t ↦ Real.log (2 * t)` goes through reification and must satisfy
`Verified.Expr.ValidAt` at the evaluation point, so the same tactic refuses
`deriv (fun t ↦ Real.log (2 * t)) 0 = 2 / (2 * 0)` even though that statement is also
true in Lean. The asymmetry is deliberate: the reflective route certifies the classical
derivative, while the shortcuts restate a Mathlib fact verbatim.
-/

public meta section

namespace CAS.Tactic.RealDeriv

open Lean Elab Tactic Meta
open DerivativeBridge

/-- The scalar derivative goal shapes accepted by the derivative route of `cas`. -/
inductive Shape where
  /-- `deriv f x₀ = rhs`, or `rhs = deriv f x₀` when `reverse` is set. -/
  | derivEq (function point rhs : Expr) (reverse : Bool)
  /-- `HasDerivAt f f' x₀`. -/
  | hasDerivAt (function derivative point : Expr)
  /-- `HasDerivWithinAt f f' s x₀`. -/
  | hasDerivWithinAt (function derivative set point : Expr)
  /-- `DifferentiableAt 𝕜 f x₀` for a scalar function. -/
  | differentiableAt (function point : Expr)

namespace Shape

/-- The differentiated function of a recognised goal. -/
def function : Shape → Expr
  | .derivEq f _ _ _ | .hasDerivAt f _ _ | .hasDerivWithinAt f _ _ _
  | .differentiableAt f _ => f

/-- The stated derivative value of a recognised goal, if any. -/
def stated? : Shape → Option Expr
  | .derivEq _ _ rhs _ => some rhs
  | .hasDerivAt _ f' _ | .hasDerivWithinAt _ f' _ _ => some f'
  | .differentiableAt _ _ => none

/-- The evaluation point of a recognised goal. -/
def point : Shape → Expr
  | .derivEq _ x₀ _ _ | .hasDerivAt _ _ x₀ | .hasDerivWithinAt _ _ _ x₀
  | .differentiableAt _ x₀ => x₀

end Shape

private def derivApplication? (expression : Expr) : Option (Expr × Expr) :=
  let expression := expression.consumeMData
  if expression.getAppFn.consumeMData.isConstOf ``deriv then
    let arguments := expression.getAppArgs
    if h : 2 ≤ arguments.size then
      some (arguments[arguments.size - 2], arguments[arguments.size - 1])
    else
      none
  else
    none

/-- Recognise the scalar derivative shape of a proposition, if any. -/
def shape? (target : Expr) : Option Shape :=
  let target := target.consumeMData
  if target.isAppOfArity ``Eq 3 then
    let arguments := target.getAppArgs
    match derivApplication? arguments[1]!, derivApplication? arguments[2]! with
    | some (function, point), none => some (.derivEq function point arguments[2]! false)
    | none, some (function, point) => some (.derivEq function point arguments[1]! true)
    | _, _ => none
  else if target.isAppOfArity ``HasDerivAt 10 then
    let arguments := target.getAppArgs
    some (.hasDerivAt arguments[7]! arguments[8]! arguments[9]!)
  else if target.isAppOfArity ``HasDerivWithinAt 11 then
    let arguments := target.getAppArgs
    some (.hasDerivWithinAt arguments[7]! arguments[8]! arguments[9]! arguments[10]!)
  else if target.isAppOfArity ``DifferentiableAt 12 then
    let arguments := target.getAppArgs
    some (.differentiableAt arguments[10]! arguments[11]!)
  else
    none

/-- `iteratedDeriv n f x` or `iteratedDerivWithin n f s x` with a literal order `n ≥ 1`. -/
private def isIteratedDerivApplication (expression : Expr) : Bool :=
  let expression := expression.consumeMData
  if expression.isAppOfArity ``iteratedDeriv 8 ||
      expression.isAppOfArity ``iteratedDerivWithin 9 then
    let order := expression.getAppArgs[5]!.consumeMData
    match order.nat? <|> order.rawNatLit? with
    | some n => 0 < n
    | none => false
  else
    false

/-- Whether a proposition has one of the scalar derivative shapes, or is an equality with a side
`iteratedDeriv n f x` or `iteratedDerivWithin n f s x` for a literal order `n ≥ 1`. -/
def isScalarDerivativeGoal (target : Expr) : Bool :=
  let target := target.consumeMData
  (shape? target).isSome ||
    (target.isAppOfArity ``Eq 3 &&
      (isIteratedDerivApplication target.getAppArgs[1]! ||
        isIteratedDerivApplication target.getAppArgs[2]!))

/-! ## Iterated derivatives with a literal order -/

/-- Every subterm of `expression` without loose bound variables satisfying `test`, outermost
first. -/
private partial def closedSubterms (test : Expr → Bool) (expression : Expr)
    (found : Array Expr) : Array Expr :=
  let expression := expression.consumeMData
  let found :=
    if test expression && !expression.hasLooseBVars && !found.contains expression then
      found.push expression
    else
      found
  let visit := closedSubterms test
  match expression with
  | .app function argument => visit argument (visit function found)
  | .lam _ type body _ | .forallE _ type body _ => visit body (visit type found)
  | .letE _ type value body _ => visit body (visit value (visit type found))
  | .proj _ _ projected => visit projected found
  | _ => found

/-- Rewrite the main goal with `equality`, keeping the side goals of the rewrite. -/
private def rewriteMainGoal (equality : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let result ← goal.rewrite (← instantiateMVars (← goal.getType)) equality
  let rewritten ← goal.replaceTargetEq result.eNew result.eqProof
  replaceMainGoal (rewritten :: result.mvarIds)

/-- Close `goal` by `tactic`, failing with `description` otherwise. -/
private def closeSideGoal (goal : Expr) (tactic : TSyntax `tactic) (description : String) :
    TacticM Unit := do
  let remaining ← Tactic.run goal.mvarId! (Tactic.evalTactic tactic)
  unless remaining.isEmpty do
    throwError "{operation} could not prove {description}{indentExpr (← inferType goal)}"

/-- Rewrite every `iteratedDerivWithin n f s x` with a literal order `n` in the main goal to
`iteratedDeriv n f x` by `iteratedDerivWithin_eq_iteratedDeriv`. Its conditions `UniqueDiffOn ℝ s`
and `x ∈ s` come from a hypothesis or are proved for `univ`, the half-lines and the intervals with
nonempty interior, and `ContDiffAt ℝ n f x` is proved by `Regularity.close`. -/
private def expandIteratedDerivWithin (evidence? : Option (TSyntax `term)) :
    TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let arity := (← getConstInfo ``iteratedDerivWithin).type.getNumHeadForalls
  for occurrence in closedSubterms (·.isAppOfArity ``iteratedDerivWithin arity) target #[] do
    let arguments := occurrence.getAppArgs
    let order := arguments[arity - 4]!
    let some _ ← getNatValue? order
      | continue
    let transport ← mkAppOptM ``iteratedDerivWithin_eq_iteratedDeriv
      #[none, none, none, none, none, some order, some arguments[arity - 3]!,
        some arguments[arity - 2]!, some arguments[arity - 1]!]
    let (hypotheses, _, _) ← forallMetaTelescopeReducing (← inferType transport) (some 3)
    let goals ← hypotheses.mapM fun hypothesis ↦ do
      mkFreshExprSyntheticOpaqueMVar (← inferType hypothesis)
    closeSideGoal goals[0]! (← `(tactic| first
      | assumption | exact uniqueDiffOn_univ
      | exact isOpen_Ioi.uniqueDiffOn | exact isOpen_Iio.uniqueDiffOn
      | exact isOpen_Ioo.uniqueDiffOn | exact uniqueDiffOn_Ici _ | exact uniqueDiffOn_Iic _
      | exact uniqueDiffOn_Icc (by first | norm_num | assumption | linarith)
      | exact uniqueDiffOn_Ico (by first | norm_num | assumption | linarith)
      | exact uniqueDiffOn_Ioc (by first | norm_num | assumption | linarith)))
      "unique differentiability on the set"
    closeSideGoal goals[2]! (← `(tactic| first
      | exact Set.mem_univ _ | assumption
      | (simp only [Set.mem_Ioi, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc,
            Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic];
          first | assumption | positivity | (constructor <;> linarith) | linarith)))
      "that the point lies in the set"
    let remaining ← Tactic.run goals[1]!.mvarId! (Regularity.close evidence?)
    unless remaining.isEmpty do
      throwError "{operation} could not prove the smoothness{indentExpr (← inferType goals[1]!)}"
    rewriteMainGoal (← instantiateMVars (mkAppN transport goals))

/-- `iteratedDeriv n f = deriv (… (deriv f))` with `n` derivatives, from `iteratedDeriv_zero`
and `iteratedDeriv_succ`. -/
private def iteratedDerivEquality (n : Nat) (function : Expr) : MetaM Expr := do
  let mut nested := function
  let mut proof ← mkAppOptM ``iteratedDeriv_zero #[none, none, none, none, none, some function]
  let derivative ← withLocalDeclD `g (← inferType function) fun g ↦ do
    mkLambdaFVars #[g] (← mkAppM ``deriv #[g])
  for k in [0:n] do
    let succ ← mkAppOptM ``iteratedDeriv_succ
      #[none, none, none, none, none, some (toExpr k), some function]
    proof ← mkEqTrans succ (← mkCongrArg derivative proof)
    nested ← mkAppM ``deriv #[nested]
  mkExpectedTypeHint proof (← mkEq (← mkAppM ``iteratedDeriv #[toExpr n, function]) nested)

/-- Rewrite every `iteratedDeriv n f` with a literal order `n ≥ 1` in the main goal to `n`
nested derivatives of `f`. -/
private def expandIteratedDerivatives : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let arity := (← getConstInfo ``iteratedDeriv).type.getNumHeadForalls - 1
  for occurrence in closedSubterms (·.isAppOfArity ``iteratedDeriv arity) target #[] do
    let arguments := occurrence.getAppArgs
    let some n ← getNatValue? arguments[arity - 2]!
      | continue
    if n = 0 then
      continue
    rewriteMainGoal (← iteratedDerivEquality n arguments[arity - 1]!)

/-! ## Current-module definitions -/

/--
Expose local definitions that depend on the differentiated coordinate, together with
real-valued local definitions used in the stated derivative.

Repeating this pass handles chains of ordinary user definitions while imported
analytic functions and binder-independent coefficients remain opaque. The
goal and generated certificate then share the same definitional presentation.
With `keepRuled`, a definition with a registered `@[cas_deriv]` rule stays folded, so that the
rule can apply to it.
-/
private def unfoldDependentLocalDefinitions (keepRuled : Bool := false) : TacticM Unit :=
  unfoldLocalDefinitionsWhile do
    let target ← instantiateMVars (← getMainTarget)
    let some shape := shape? target
      | return #[]
    let real := mkConst ``Real
    unless ← Elaboration.RealExpression.hasType shape.function (← mkArrow real real) do
      return #[]
    let mut definitions ← dependentLocalDefinitions real shape.function
    if let some stated := shape.stated? then
      definitions := definitions ++ (← statedLocalDefinitions stated)
    unless keepRuled do
      return definitions
    let used := target.getUsedConstants
    definitions.filterM fun name ↦ return used.contains name && !(← DerivativeRules.hasRule name)

/--
Rewrite varying nested derivatives inside the differentiated function of the main goal
to ordinary syntax for their symbolic derivatives. Fixed derivative values remain
scalar coefficients.
-/
private def eliminateNestedDerivatives
    (function : Expr) (evidence? : Option (TSyntax `term)) : TacticM Unit := do
  let real := mkConst ``Real
  let rewrite? ←
    withLocalDeclD `t real fun binder ↦ do
      let body ← withTransparency .reducible <| whnf (mkApp function binder)
      match ← eliminateInnerDerivatives operation binder body evidence? with
      | none => return none
      | some (rewrittenBody, proof) =>
          let rewrittenFunction ← mkLambdaFVars #[binder] rewrittenBody
          let equality ← mkFunExt (← mkLambdaFVars #[binder] proof)
          let equality ← mkExpectedTypeHint equality (← mkEq function rewrittenFunction)
          return some equality
  let some equality := rewrite?
    | return
  let goal ← getMainGoal
  let result ← goal.rewrite (← instantiateMVars (← goal.getType)) equality
  unless result.mvarIds.isEmpty do
    throwError "{operation} internal error: rewriting nested derivatives left auxiliary goals"
  let goal ← goal.replaceTargetEq result.eNew result.eqProof
  replaceMainGoal [goal]

/--
Replace the differentiated function of the main goal by a function without varying nested
derivatives that agrees with it near the evaluation point (`eliminateNestedNear`). The goal is
transferred by `Filter.EventuallyEq.deriv_eq` or by the `congr_of_eventuallyEq` lemma of its
predicate, so the inner conditions are needed at the point only.
-/
private def eliminateNestedDerivativesNear (evidence? : Option (TSyntax `term)) :
    TacticM Unit := withMainContext do
  let some shape := shape? (← instantiateMVars (← getMainTarget))
    | throwError "{operation} internal error: the goal lost its derivative shape"
  let some (function, agreement) ←
      eliminateNestedNear operation shape.function shape.point evidence?
    | return
  let goal ← getMainGoal
  let next ← match shape with
    | .derivEq _ point rhs reverse =>
        let lhs ← mkAppM ``deriv #[function, point]
        let next ← mkFreshExprSyntheticOpaqueMVar
          (← if reverse then mkEq rhs lhs else mkEq lhs rhs)
        let agreesAtPoint ← mkAppM ``Filter.EventuallyEq.deriv_eq #[agreement]
        goal.assign (← if reverse then mkEqTrans next (← mkEqSymm agreesAtPoint)
          else mkEqTrans agreesAtPoint next)
        pure next
    | .hasDerivAt _ stated point =>
        let next ← mkFreshExprSyntheticOpaqueMVar
          (← mkAppM ``HasDerivAt #[function, stated, point])
        goal.assign (← mkAppM ``HasDerivAt.congr_of_eventuallyEq #[next, agreement])
        pure next
    | .hasDerivWithinAt _ stated set point =>
        let next ← mkFreshExprSyntheticOpaqueMVar
          (← mkAppM ``HasDerivWithinAt #[function, stated, set, point])
        let within ← mkAppM ``Filter.EventuallyEq.filter_mono
          #[agreement, ← mkAppOptM ``nhdsWithin_le_nhds #[none, none, some point, some set]]
        goal.assign (← mkAppM ``HasDerivWithinAt.congr_of_eventuallyEq
          #[next, within, ← mkAppM ``Filter.EventuallyEq.eq_of_nhds #[agreement]])
        pure next
    | .differentiableAt _ point =>
        let next ← mkFreshExprSyntheticOpaqueMVar
          (← mkAppM ``DifferentiableAt #[mkConst ``Real, function, point])
        goal.assign (← mkAppM ``DifferentiableAt.congr_of_eventuallyEq #[next, agreement])
        pure next
  replaceMainGoal [next.mvarId!]

private def ensureScalarFunction (function point : Expr) : MetaM Expr := do
  let real := mkConst ``Real
  unless ← Elaboration.RealExpression.hasType point real do
    let pointType ← inferType point
    throwError
      "{operation} supports ordinary scalar derivatives over ℝ; \
       the evaluation point has type{indentExpr pointType}"
  let function ← withTransparency .reducible <| whnf function
  unless ← Elaboration.RealExpression.hasType function (← mkArrow real real) do
    let functionType ← inferType function
    throwError
      "{operation} supports functions ℝ → ℝ; the differentiated function has type\
       {indentExpr functionType}\n\
       Naturals and integers may be used as parameters after coercion to ℝ. \
       For other scalar fields, supply a derivative theorem or register a `@[cas_deriv]` rule."
  return function

/-- A constant divisor is a scalar multiplier even when it is zero. Keep its inverse
as a parameter, so the derivative certificate does not require an unnecessary nonzero fact.
The usual function-conversion proof checks the resulting presentation. -/
private def exposeConstantDivisors (binder body : Expr) : MetaM Expr :=
  Meta.transform body (skipConstInApp := true) (pre := fun e ↦ do
    unless e.isAppOfArity ``HDiv.hDiv 6 do return .continue
    let args := e.getAppArgs
    unless args[0]!.isConstOf ``Real do return .continue
    if CAS.Elaboration.RealExpression.dependsOn args[5]! binder then
      return .continue
    let inverse ← mkAppM ``Inv.inv #[args[5]!]
    return .continue (some (← mkAppM ``HMul.hMul #[args[4]!, inverse])))

/--
Reflect the body of `function` and prove `HasDerivAt function D point` for the computed
derivative `D`, returning the proof together with the value goal `D = stated` (when a
stated derivative is given) and the optional function-identification goal.
-/
private def checkedHasDerivAt
    (function point : Expr) (stated? : Option Expr) (evidence? : Option (TSyntax `term)) :
    TacticM (Expr × Derivative × Option MVarId × Option MVarId) := do
  let real := mkConst ``Real
  withLocalDeclD `t real fun binder ↦ do
    let body ← withTransparency .reducible <| whnf (mkApp function binder)
    unless ← Elaboration.RealExpression.hasType body real do
      let codomain ← inferType body
      throwError
        "{operation} supports real-valued scalar functions; \
         the function codomain is{indentExpr codomain}"
    let body ← exposeConstantDivisors binder body
    let derivative ← scalarHasDerivAt operation binder body point evidence?
    let (proof, functionGoal?) ←
      transportToFunction derivative function fun g ↦
        mkAppM ``HasDerivAt #[g, derivative.value, point]
    let valueGoal? ←
      match stated? with
      | none => pure none
      | some stated =>
          let valueGoal ← mkFreshExprSyntheticOpaqueMVar (← mkEq derivative.value stated)
          pure (some valueGoal.mvarId!)
    return (proof, derivative, functionGoal?, valueGoal?)

/-- Assign the main goal with `proof`, requiring definitional agreement of types, and close
the derivative conversion goals. -/
private def finish
    (proof : Expr) (derivative : Derivative)
    (functionGoal? valueGoal? : Option MVarId) (evidence? : Option (TSyntax `term)) :
    TacticM Unit := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let proofType ← instantiateMVars (← inferType proof)
  unless ← isDefEq proofType target do
    throwError
      "{operation} constructed a proof of{indentExpr proofType}\n\
       but the goal is{indentExpr target}"
  closeMatchingGoals operation functionGoal? valueGoal? derivative evidence?
  goal.assign (← instantiateMVars proof)
  replaceMainGoal []

private def closeDirectDeriv
    (function point rhs : Expr) (reverse : Bool) (evidence? : Option (TSyntax `term)) :
    TacticM Bool := do
  let real := mkConst ``Real
  let expectedFunctionType ← mkArrow real real
  let absFunction ←
    Term.elabTermEnsuringType (← `(term| (abs : ℝ → ℝ))) (some expectedFunctionType)
  let directTotalProof? ←
    if ← isDefEqGuarded function absFunction then
      some <$> mkAppM ``deriv_abs #[point]
    else if ← isDefEqGuarded function (mkConst ``Real.log) then
      some <$> mkAppM ``Real.deriv_log #[point]
    else
      pure none
  if let some directProof := directTotalProof? then
    let saved ← saveState
    try
      let proof ← if reverse then mkAppM ``Eq.symm #[directProof] else pure directProof
      let remainingGoals := (← getGoals).drop 1
      let convertConfig := ({} : Convert.CheapConfig).toConfig
      let conversionGoals ←
        (← getMainGoal).convert proof false (some 1) convertConfig
      setGoals conversionGoals
      evalTactic (← `(tactic| all_goals simp_all))
      if (← getGoals).isEmpty then
        setGoals remainingGoals
        return true
      saved.restore
    catch _ =>
      saved.restore
  let directProof? ←
    if ← isDefEqGuarded function (mkConst ``Real.sinh) then
      some <$> mkAppM ``congrFun #[mkConst ``Real.deriv_sinh, point]
    else if ← isDefEqGuarded function (mkConst ``Real.cosh) then
      some <$> mkAppM ``congrFun #[mkConst ``Real.deriv_cosh, point]
    else if ← isDefEqGuarded function (mkConst ``Real.tan) then
      some <$> mkAppM ``Real.deriv_tan #[point]
    else
      pure none
  let some directProof := directProof?
    | return false
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let directProof ← instantiateMVars directProof
  let proof ← if reverse then mkEqSymm directProof else pure directProof
  let proof ←
    if ← isDefEq (← inferType proof) target then
      pure proof
    else
      -- The stated value differs from the lemma's (`1 + tan x ^ 2` for `1 / cos x ^ 2`): the
      -- two are identified by the checked identity core, whose recorded conditions (here
      -- `cos x ≠ 0`) are discharged from the context or the `using` evidence.
      let some (_, _, computed) := (← instantiateMVars (← inferType directProof)).eq?
        | throwError "{operation} internal error: the total derivative lemma is not an equality"
      let valueGoal ← mkFreshExprSyntheticOpaqueMVar (← mkEq computed rhs)
      try
        closeRealEqualityGoal operation valueGoal.mvarId! evidence?
      catch error =>
        throwError
          "{operation} obtained Mathlib's total derivative of {function}, but it does not match \
           the stated right-hand side{indentExpr rhs}\nChecked identity route:\
           {indentD error.toMessageData}"
      let identified ← mkEqTrans directProof (← instantiateMVars valueGoal)
      if reverse then mkEqSymm identified else pure identified
  unless ← isDefEq (← inferType proof) target do
    throwError
      "{operation} internal error: the identified total derivative does not match the goal"
  goal.assign proof
  setGoals ((← getGoals).drop 1)
  return true

private def closeDerivEq
    (function point rhs : Expr) (reverse : Bool) (evidence? : Option (TSyntax `term)) :
    TacticM Unit := do
  if ← closeDirectDeriv function point rhs reverse evidence? then
    return
  let function ← ensureScalarFunction function point
  let (hasDeriv, derivative, functionGoal?, valueGoal?) ←
    checkedHasDerivAt function point (some rhs) evidence?
  let some valueGoal := valueGoal?
    | throwError "{operation} internal error: missing derivative value goal"
  let proof ← mkEqTrans (← mkAppM ``HasDerivAt.deriv #[hasDeriv]) (mkMVar valueGoal)
  let proof ← if reverse then mkEqSymm proof else pure proof
  finish proof derivative functionGoal? (some valueGoal) evidence?

private def closeHasDerivAt
    (function stated point : Expr) (evidence? : Option (TSyntax `term)) : TacticM Unit := do
  let function ← ensureScalarFunction function point
  let (hasDeriv, derivative, functionGoal?, valueGoal?) ←
    checkedHasDerivAt function point (some stated) evidence?
  let some valueGoal := valueGoal?
    | throwError "{operation} internal error: missing derivative value goal"
  let proof ← mkAppM ``HasDerivAt.congr_deriv #[hasDeriv, mkMVar valueGoal]
  finish proof derivative functionGoal? (some valueGoal) evidence?

private def closeHasDerivWithinAt
    (function stated set point : Expr) (evidence? : Option (TSyntax `term)) :
    TacticM Unit := do
  let function ← ensureScalarFunction function point
  let (hasDeriv, derivative, functionGoal?, valueGoal?) ←
    checkedHasDerivAt function point (some stated) evidence?
  let some valueGoal := valueGoal?
    | throwError "{operation} internal error: missing derivative value goal"
  let congruent ← mkAppM ``HasDerivAt.congr_deriv #[hasDeriv, mkMVar valueGoal]
  let proof ←
    mkAppOptM ``HasDerivAt.hasDerivWithinAt
      #[none, none, none, none, none, none, none, none, some set, some congruent]
  finish proof derivative functionGoal? (some valueGoal) evidence?

private def closeDifferentiableAt
    (function point : Expr) (evidence? : Option (TSyntax `term)) : TacticM Unit := do
  let function ← ensureScalarFunction function point
  let (hasDeriv, derivative, functionGoal?, _) ←
    checkedHasDerivAt function point none evidence?
  let proof ← mkAppM ``HasDerivAt.differentiableAt #[hasDeriv]
  finish proof derivative functionGoal? none evidence?

/-- Reuse a stated derivative through Mathlib's projections. An abstract function is accepted
only when the context already contains the corresponding derivative theorem. -/
private def closeFromHypothesis (shape : Shape)
    (evidence? : Option (TSyntax `term)) : TacticM Unit := withMainContext do
  let mut goal ← getMainGoal
  if let some evidence := evidence? then
    let proof ← Term.withoutErrToSorry <| Term.elabTerm evidence none
    let proof ← ProofCarrier.checkCompletedProof operation proof
    unless ← isProp (← inferType proof) do
      throwError "{operation} requires a proof as side evidence"
    let (_, newGoal) ← goal.note (← mkFreshUserName `hcasDerivative) proof
    goal := newGoal
    replaceMainGoal [goal]
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    for decl in ← getLCtx do
      unless decl.isImplementationDetail do
        let source := mkFVar decl.fvarId
        let sourceType ← instantiateMVars decl.type
        -- Compare functions before derivative predicates: unfolding an unrelated
        -- `HasDerivAt` can otherwise expand large finite sums in its function.
        if let some sourceShape := shape? sourceType then
          unless ← withTransparency .reducible <|
              ProofCarrier.isDefEqReadOnly sourceShape.function shape.function do
            continue
        if ← isDefEqGuarded sourceType target then
          goal.assign source
          replaceMainGoal []
          return
        if let some (.hasDerivAt _ _ _) := shape? sourceType then
          let proof ← match shape with
            | .derivEq _ _ _ reverse =>
                let proof ← mkAppM ``HasDerivAt.deriv #[source]
                if reverse then mkEqSymm proof else pure proof
            | .hasDerivAt _ _ _ => pure source
            | .hasDerivWithinAt _ _ set _ =>
                mkAppOptM ``HasDerivAt.hasDerivWithinAt
                  #[none, none, none, none, none, none, none, none, some set, some source]
            | .differentiableAt _ _ =>
                mkAppM ``HasDerivAt.differentiableAt #[source]
          if ← isDefEqGuarded (← inferType proof) target then
            goal.assign proof
            replaceMainGoal []
            return
    throwError "no matching derivative hypothesis"

private def closeFromRules (shape : Shape)
    (evidence? : Option (TSyntax `term)) : TacticM Unit := withMainContext do
  if let some evidence := evidence? then
    let proof ← Term.withoutErrToSorry <| Term.elabTerm evidence none
    let proof ← ProofCarrier.checkCompletedProof operation proof
    unless ← isProp (← inferType proof) do
      throwError "{operation} requires a proof as side evidence"
    let (_, goal) ← (← getMainGoal).note (← mkFreshUserName `hcasDerivative) proof
    replaceMainGoal [goal]
  withMainContext do
    let point := match shape with
      | .derivEq _ point _ _ | .hasDerivAt _ _ point |
          .hasDerivWithinAt _ _ _ point | .differentiableAt _ point => point
    let some (value, derivative) ← DerivativeRules.derive? shape.function point
      | throwError "no analytic derivative rule matched the function"
    let derivative ← if let some stated := shape.stated? then do
        let equality ← mkFreshExprSyntheticOpaqueMVar (← mkEq value stated)
        let remaining ← KernelReadBack.withSuppressedMessagesMeta <|
          KernelReadBack.runTacticOnGoal equality.mvarId!
            (← `(tactic| first | rfl | (simp; done) | ring | (field_simp; ring) | norm_num))
        unless remaining.isEmpty do
          throwError "the analytic derivative does not match the stated value"
        mkAppM ``HasDerivAt.congr_deriv #[derivative, ← instantiateMVars equality]
      else pure derivative
    let proof ← match shape with
      | .derivEq _ _ _ reverse =>
          let proof ← mkAppM ``HasDerivAt.deriv #[derivative]
          if reverse then mkEqSymm proof else pure proof
      | .hasDerivAt _ _ _ => pure derivative
      | .hasDerivWithinAt _ _ set _ =>
          mkAppOptM ``HasDerivAt.hasDerivWithinAt
            #[none, none, none, none, none, none, none, none, some set, some derivative]
      | .differentiableAt _ _ => mkAppM ``HasDerivAt.differentiableAt #[derivative]
    unless ← ProofCarrier.assignExactProof operation proof do
      throwError "the analytic derivative proof does not match the original goal"

/-- The derivative shape of the main goal. -/
private def mainShape : TacticM Shape := withMainContext do
  let some shape := shape? (← instantiateMVars (← getMainTarget))
    | throwError
        "{operation} expected an equality with an ordinary `deriv` application or an \
         iterated derivative of literal order, or a `HasDerivAt`, `HasDerivWithinAt`, or \
         `DifferentiableAt` statement about a scalar function"
  return shape

/-- Close the main goal from a stated derivative or by the analytic rules. Returns the error of
the rules when neither applies, leaving the goal unchanged. -/
private def closeByTheorems (shape : Shape) (evidence? : Option (TSyntax `term)) :
    TacticM (Option Exception) := do
  if let .ok _ ← ProofCarrier.attemptClosingMainGoal "stated derivative"
      (closeFromHypothesis shape evidence?) then
    return none
  match ← ProofCarrier.attemptClosingMainGoal "analytic derivative rules"
      (closeFromRules shape evidence?) with
  | .ok _ => return none
  | .error error =>
      trace[cas.derivativeRules] "{error.toMessageData}"
      return some error

/-- Close the main goal by reflecting its differentiated function. -/
private def closeByReflection (evidence? : Option (TSyntax `term)) : TacticM Unit :=
  withMainContext do
    match ← mainShape with
    | .derivEq function point rhs reverse =>
        closeDerivEq function point rhs reverse evidence?
    | .hasDerivAt function stated point =>
        closeHasDerivAt function stated point evidence?
    | .hasDerivWithinAt function stated set point =>
        closeHasDerivWithinAt function stated set point evidence?
    | .differentiableAt function point =>
        closeDifferentiableAt function point evidence?

/--
Close a scalar derivative goal: an equality with an ordinary `deriv` application on one side,
or with `iteratedDeriv n f x` or `iteratedDerivWithin n f s x` for a literal order `n`, or a
`HasDerivAt`, `HasDerivWithinAt`, or `DifferentiableAt` statement.
Analytic theorem rules are tried first; real-valued reflection is the fallback.

Iterated derivatives are rewritten to nested ones first. Nested derivatives inside the
differentiated function are eliminated before reflection, as functions when the inner
conditions hold at every point and otherwise near the evaluation point. When the
differentiated function is
literally one of `abs`, `Real.log`, `Real.sinh`, `Real.cosh` or `Real.tan` in a `deriv`
equality, the corresponding total Mathlib derivative lemma is used directly and no
analytic domain condition is checked, unless the stated value has to be identified with the
lemma's by the checked identity core (see the module docstring).
-/
def close
    (evidence? : Option (TSyntax `term) := none) : TacticM Unit := do
  withMainContext do
    let goal ← getMainGoal
    -- Reduce let-bound propositions without opening binder-independent local coefficients.
    let target ← zetaReduce (← instantiateMVars (← goal.getType)) (zetaDelta := false)
    goal.change target >>= fun goal ↦ replaceMainGoal [goal]
  expandIteratedDerivWithin evidence?
  expandIteratedDerivatives
  unfoldDependentLocalDefinitions (keepRuled := true)
  exposeCheckedExpressions operation
  let mut shape ← mainShape
  let some error ← closeByTheorems shape evidence?
    | return
  let mut ruleError := error
  -- Definitions kept folded for their rules are unfolded once the rules have not applied.
  let folded ← instantiateMVars (← getMainTarget)
  unfoldDependentLocalDefinitions
  unless (← instantiateMVars (← getMainTarget)) == folded do
    exposeCheckedExpressions operation
    shape ← mainShape
    let some error ← closeByTheorems shape evidence?
      | return
    ruleError := error
  withMainContext do
    unless ← Elaboration.RealExpression.hasType shape.point (mkConst ``Real) do
      throwError "{operation} could not prove this scalar derivative with analytic rules:\
        {indentD ruleError.toMessageData}\nSupply a derivative theorem or a `@[cas_deriv]` rule."
  let nested ← withMainContext do
    withLocalDeclD `t (mkConst ``Real) fun binder ↦ do
      let body ← withTransparency .reducible <| whnf (mkApp shape.function binder)
      return containsVaryingDeriv body binder
  unless nested do
    closeByReflection evidence?
    return
  -- `try` restores the state before its handler runs.
  try
    withMainContext do
      eliminateNestedDerivatives shape.function evidence?
    closeByReflection evidence?
  catch everywhere =>
    try
      eliminateNestedDerivativesNear evidence?
      closeByReflection evidence?
    catch near =>
      throwError
        "{operation} could not differentiate the nested derivatives.\n\
         With the inner conditions at every point:{indentD everywhere.toMessageData}\n\
         Near the point, with the inner conditions there:{indentD near.toMessageData}"

end CAS.Tactic.RealDeriv

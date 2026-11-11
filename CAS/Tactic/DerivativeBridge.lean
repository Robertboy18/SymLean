/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import CAS.Calculus.ParameterEmbedding
public import CAS.ClosedForm.SideConditionCompaction
public meta import CAS.Expr.Substitution
public import CAS.Tactic.Assumptions
public import CAS.Tactic.RealExpression
public meta import CAS.Tactic.RealExpression
public meta import Lean.Meta.Tactic.Unfold
public import CAS.Tactic.AnalyticIdentities -- shake: keep: quoted tangent rewrites
/-!
# Shared bridge from ordinary derivative goals to checked symbolic derivatives

The proof-producing core of the scalar derivative frontend `CAS/Tactic/RealDeriv.lean`, also
used by the regularity route (`CAS/Tactic/Regularity.lean`), the derivative rewriting of bare
`cas` (`CAS/Tactic/DerivativeRewrite.lean`), the checked identity route
(`CAS/Tactic/Identity.lean`), and the Euclidean derivative backends registered through
`CAS/Tactic/DerivativeRegistry.lean`. Every step is checked, and unsupported or false goals fail
without assigning anything.

## Main definitions

* `scalarHasDerivAt` reflects the body of an ordinary function `ℝ → ℝ` and proves
  `HasDerivAt (fun s ↦ expr.eval (lineEmbed c s)) D x₀`.
* `applyBridge` instantiates a bridge theorem, and `closeValidity` proves its validity
  hypotheses.
* `closeMatchingGoals` identifies the computed derivative with the stated one.
* `certifyZeroDifference` certifies with the kernel that the checked side-conditioned
  normalizer reduces a difference to zero; the checked identity route of bare `cas` shares it.
* The companion `CAS/Tactic/DerivativeBridge/NestedScalar.lean` defines
  `eliminateInnerDerivatives`, which rewrites nested scalar derivatives inner-first.

## Implementation notes

We reflect the body in the parameter-embedding convention of
`CAS/Calculus/ParameterEmbedding.lean`: the differentiated variable is coordinate zero and every
binder-independent real subterm is a frozen parameter. The derivative theorem is
`Verified.Expr.hasDerivAt_eval_lineEmbed`, which rests on `Verified.Expr.hasFDerivAt_eval`
(`CAS/Calculus/Euclidean.lean`, an induction over the expression with Mathlib's `HasFDerivAt`
rules). Because the embedded coordinates reduce definitionally, the reflected function is
definitionally the user's function whenever reflection used only definitional lowerings;
otherwise `transportToFunction` leaves a function equality, which `closeMatchingGoals` proves.
`closeValidity` tries the `using` evidence verbatim when there is one, then
`symbolic_assumptions`, then each atom of the unfolded validity conjunction with finishers such
as `positivity` and `nlinarith`; universally quantified obligations are introduced first and,
over `Fin`, case split.

`closeMatchingGoals` first unfolds the checked evaluator and runs a fixed Mathlib normalization
script. When goals remain, we certify the identity with the side-conditioned normalizer of
`CAS/ClosedForm/Pipeline/Configured.lean`, whose square-root, inverse-elementary
(`exp (log a)`), rational, and real-power passes see algebra such as `(√u)² = u` and
`a ^ (b - 1) = a ^ b / a` that `ring` cannot. The kernel evaluates the run and `decideByKernel`
certifies it, so no metaprogram-level reduction of the normalizer is trusted. We try the empty
side list first; otherwise the run is read back and certified against its essential conditions.
The equality is `CAS.Verified.Expr.eval_eq_of_sideConditionPipeline_run_essential`, and
`closeValidity` proves its conditions. A residual goes to the multivariate canonical form of
`CAS/ClosedForm/Canonical.lean` (`certifyCanonicalZeroDifference`), and a folded Laplacian sum
is certified summand by summand (`CAS/ClosedForm/SideConditionCompaction.lean`). The calculus
is Mathlib's; the reflection, the transport, and the order of these routes are ours.
-/

public meta section

namespace CAS.Tactic.DerivativeBridge

open Lean Elab Tactic Meta
open AnalyticIdentities KernelReadBack

/-- The name of the derivative route of `cas` in diagnostics. -/
def operation : String := "cas"

/-! ## Unfolding checked evaluation -/

/-- Simp lemmas and simprocs that unfold the checked evaluator and the embedding
coordinates back to ordinary real syntax. -/
private def unfoldingLemmas : MetaM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := do
  return #[
    ← `(Lean.Parser.Tactic.simpLemma| Verified.Expr.eval),
    ← `(Lean.Parser.Tactic.simpLemma| Verified.Expr.diff),
    ← `(Lean.Parser.Tactic.simpLemma| Verified.Expr.ofLp_lineEmbed),
    ← `(Lean.Parser.Tactic.simpLemma| Verified.Expr.ofLp_paramEmbed),
    ← `(Lean.Parser.Tactic.simpLemma| Fin.append_left),
    ← `(Lean.Parser.Tactic.simpLemma| Fin.append_right),
    ← `(Lean.Parser.Tactic.simpLemma| Fin.castAdd_inj),
    ← `(Lean.Parser.Tactic.simpLemma| Fin.isValue),
    ← `(Lean.Parser.Tactic.simpLemma| Fin.zero_eta),
    ← `(Lean.Parser.Tactic.simpLemma| Fin.mk_one),
    ← `(Lean.Parser.Tactic.simpLemma| Matrix.cons_val),
    ← `(Lean.Parser.Tactic.simpLemma| Matrix.cons_val_zero),
    ← `(Lean.Parser.Tactic.simpLemma| Matrix.cons_val_one),
    ← `(Lean.Parser.Tactic.simpLemma| Matrix.head_cons),
    ← `(Lean.Parser.Tactic.simpLemma| reduceIte),
    ← `(Lean.Parser.Tactic.simpLemma| ite_true),
    ← `(Lean.Parser.Tactic.simpLemma| ite_false),
    ← `(Lean.Parser.Tactic.simpLemma| Nat.cast_ofNat),
    ← `(Lean.Parser.Tactic.simpLemma| Nat.cast_zero),
    ← `(Lean.Parser.Tactic.simpLemma| Nat.cast_one),
    ← `(Lean.Parser.Tactic.simpLemma| Int.ofNat_eq_natCast),
    ← `(Lean.Parser.Tactic.simpLemma| Int.cast_natCast),
    ← `(Lean.Parser.Tactic.simpLemma| Int.cast_negSucc),
    ← `(Lean.Parser.Tactic.simpLemma| Int.cast_ofNat),
    ← `(Lean.Parser.Tactic.simpLemma| Int.cast_zero),
    ← `(Lean.Parser.Tactic.simpLemma| Int.cast_one),
    ← `(Lean.Parser.Tactic.simpLemma| Fin.sum_univ_succ),
    ← `(Lean.Parser.Tactic.simpLemma| Fin.sum_univ_zero),
    ← `(Lean.Parser.Tactic.simpLemma| Fin.succ_zero_eq_one),
    ← `(Lean.Parser.Tactic.simpLemma| Fin.succ_one_eq_two),
    ← `(Lean.Parser.Tactic.simpLemma| mul_one),
    ← `(Lean.Parser.Tactic.simpLemma| one_mul),
    ← `(Lean.Parser.Tactic.simpLemma| mul_zero),
    ← `(Lean.Parser.Tactic.simpLemma| zero_mul),
    ← `(Lean.Parser.Tactic.simpLemma| add_zero),
    ← `(Lean.Parser.Tactic.simpLemma| zero_add),
    ← `(Lean.Parser.Tactic.simpLemma| sub_zero),
    ← `(Lean.Parser.Tactic.simpLemma| neg_zero),
    ← `(Lean.Parser.Tactic.simpLemma| pow_one),
    ← `(Lean.Parser.Tactic.simpLemma| Nat.reduceSub)]

private def unfoldEvaluationSyntax : MetaM (TSyntax `tactic) := do
  let lemmas ← unfoldingLemmas
  `(tactic| simp +decide only [$lemmas,*])

/-- The `simp only` script that unfolds the checked evaluator and the embedding coordinates
back to ordinary real syntax, for frontends that rewrite derivative subterms in place. -/
def unfoldEvaluationTactic : MetaM (TSyntax `tactic) :=
  unfoldEvaluationSyntax

/-- Unfold a validity predicate, or a computed side-condition list, into its ordinary
analytic conjuncts. -/
private def unfoldValiditySyntax : MetaM (TSyntax `tactic) := do
  let lemmas ← unfoldingLemmas
  `(tactic|
    simp +decide only
      [Verified.Expr.ValidAt, Verified.Expr.Alg.SideHolds, List.forall_mem_cons,
        List.not_mem_nil, false_implies, implies_true, true_and, and_true,
        Real.sqrt_ne_zero', $lemmas,*])

/-- The `simp only` script that unfolds a validity predicate, or a computed side-condition list,
into its ordinary analytic conjuncts, for frontends that prove the conjuncts themselves. -/
def unfoldValidityTactic : MetaM (TSyntax `tactic) :=
  unfoldValiditySyntax

/-! ## Validity obligations -/

/-- Render the atoms of a validity obligation that the automation could not discharge, or
`none` when no atom remains after the elementary finishers. -/
private def describeUnprovedConditions (goal : MVarId) : MetaM (Option MessageData) := do
  let type ← instantiateMVars (← goal.getType)
  let copy ← mkFreshExprMVar type
  let unfold ← unfoldValiditySyntax
  let remaining ←
    try
      withSuppressedMessagesMeta <| runTacticOnGoal copy.mvarId!
        (← `(tactic|
          ($unfold:tactic
           try (repeat' constructor)
           all_goals try (first | assumption | positivity))))
    catch _ =>
      pure [copy.mvarId!]
  if remaining.isEmpty then
    return none
  let targets ← remaining.mapM fun remainingGoal ↦
    remainingGoal.withContext do instantiateMVars (← remainingGoal.getType)
  return some m!"\nUnproved conditions:{indentD (MessageData.joinSep
    (targets.map fun target ↦ m!"{target}") m!"\n")}"

private def throwValidityFailure {α : Type}
    (operation : String) (goal : MVarId) (detail : MessageData) : MetaM α := do
  -- The unproved conditions are the informative part of the report; the failure detail of
  -- the last finishing alternative is shown only when no condition can be exhibited.
  let (remaining, detail) ←
    match ← describeUnprovedConditions goal with
    | some remaining => pure (remaining, m!"")
    | none => pure (m!"", detail)
  throwError
    "{operation} could not prove the real analytic domain conditions.\n\
     A denominator or logarithm argument may need to be nonzero, a square-root \
     argument may need to be positive, or an inverse-trigonometric argument may need to \
     avoid a branch endpoint. Supply the relevant ordinary hypothesis with \
     `{operation} using h`.{remaining}{detail}"

/--
Prove the validity obligation `goal` generated by a bridge theorem.

Without evidence the obligation is discharged by `symbolic_assumptions`, or atom by atom
after unfolding the validity conjunction; universally
quantified obligations (validity of every first symbolic derivative, or validity at every
point of a line) are first introduced and, for `Fin` indices, case split. Explicit
evidence is tried verbatim first and then added to the local context.
-/
def closeValidity
    (operation : String) (goal : MVarId) (evidence? : Option (TSyntax `term)) :
    MetaM Unit := do
  let unfold ← unfoldValiditySyntax
  -- Split the unfolded validity conjunction and discharge every atom separately, since the
  -- shared assumption solver treats a whole conjunction as one atom.
  let atoms : TSyntax `tactic ←
    `(tactic|
      ($unfold:tactic
       try (repeat' constructor)
       all_goals
         first
           | assumption
           | positivity
           | symbolic_assumptions
           | (apply ne_of_gt; positivity)
           | (apply ne_of_lt; positivity)
           | nlinarith
           | (ring_nf at *
              first | assumption | positivity | linarith | nlinarith)))
  let core : TSyntax `tactic ←
    `(tactic|
      first
        | symbolic_assumptions
        | $atoms:tactic
        | (intro i
           first
             | (fin_cases i <;> first | symbolic_assumptions | $atoms:tactic)
             | symbolic_assumptions
             | $atoms:tactic))
  let tactic ←
    match evidence? with
    | none => pure core
    | some evidence =>
        `(tactic|
          first
            | exact $evidence
            | (have hcasValidity := $evidence
               $core:tactic))
  let remaining ←
    try
      withSuppressedMessagesMeta <| runTacticOnGoal goal tactic
    catch error =>
      throwValidityFailure operation goal m!"\nDetail:{indentD error.toMessageData}"
  unless remaining.isEmpty do
    throwValidityFailure operation goal m!""
  let proof ← instantiateMVars (mkMVar goal)
  if proof.hasMVar ∨ proof.hasSorry then
    throwError "{operation} produced incomplete domain evidence"
  unless ← isTypeCorrect proof do
    throwError "{operation} produced ill-typed domain evidence"

/-- Apply `proof` to fresh metavariables for its next `count` hypotheses. The error `arityError`
is reported when the theorem has fewer hypotheses than requested. -/
def applyToFreshHypotheses (proof : Expr) (count : Nat)
    (arityError : MessageData :=
      "internal error: the bridge theorem has too few hypotheses") :
    MetaM (Expr × Array MVarId) := do
  let mut proof := proof
  let mut goals := #[]
  for _ in [:count] do
    let type ← whnf (← instantiateMVars (← inferType proof))
    unless type.isForall do
      throwError arityError
    let hypothesis ← mkFreshExprMVar type.bindingDomain!
    goals := goals.push hypothesis.mvarId!
    proof := mkApp proof hypothesis
  return (proof, goals)

/-- Instantiate a bridge theorem with the given arguments, leaving trailing validity
hypotheses as goals, prove them, and return the completed proof. `evidenceKind` names the
checked evidence in error messages, and `arityError` is passed to `applyToFreshHypotheses`. -/
def applyBridge
    (operation : String) (theoremName : Name) (arguments : Array (Option Expr))
    (validityCount : Nat) (evidence? : Option (TSyntax `term))
    (evidenceKind : String := "derivative")
    (arityError : MessageData :=
      "internal error: the bridge theorem has too few hypotheses") : MetaM Expr := do
  let applied ← mkAppOptM theoremName arguments
  let (proof, validityGoals) ← applyToFreshHypotheses applied validityCount arityError
  for validityGoal in validityGoals do
    closeValidity operation validityGoal evidence?
  let proof ← instantiateMVars proof
  if proof.hasMVar ∨ proof.hasSorry then
    throwError "{operation} produced incomplete checked {evidenceKind} evidence"
  unless ← isTypeCorrect proof do
    throwError "{operation} produced ill-typed checked {evidenceKind} evidence"
  return proof

/-! ## Euclidean domains -/

/-- The expression `EuclideanSpace ℝ (Fin dimension)`. -/
def euclideanSpace (dimension : Nat) : Expr :=
  mkApp2 (mkConst ``EuclideanSpace [Level.zero, Level.zero]) (mkConst ``Real)
    (mkApp (mkConst ``Fin) (toExpr dimension))

/-- The value of a natural-number expression when it is a literal, possibly after `whnf`. -/
def literalDimension? (dimension : Expr) : MetaM (Option Nat) := do
  let dimension ← instantiateMVars dimension
  match ← getNatValue? dimension with
  | some value => return some value
  | none => getNatValue? (← whnf dimension)

/-- The dimension bound of a `Fin` type, when it is a literal. -/
def finDimension? (index : Expr) : MetaM (Option Nat) := do
  let index := index.consumeMData
  if index.isAppOfArity ``Fin 1 then
    literalDimension? index.appArg!
  else
    return none

/-- Whether a type is a real Euclidean space `ℝ^n`, together with its literal dimension when
`n` is a numeral. The outer `none` means the type is not Euclidean; `some none` means it is
Euclidean of symbolic dimension. -/
def euclideanDimension? (domain : Expr) : MetaM (Option (Option Nat)) := do
  let domain := (← instantiateMVars domain).consumeMData
  if domain.isAppOfArity ``EuclideanSpace 2 then
    return some (← finDimension? domain.appArg!)
  let domain ← whnfR domain
  if domain.isAppOfArity ``EuclideanSpace 2 then
    return some (← finDimension? domain.appArg!)
  if domain.isAppOfArity ``PiLp 3 then
    return some (← finDimension? domain.getAppArgs[0]!)
  if domain.isAppOfArity ``WithLp 2 then
    let vectors := domain.appArg!.consumeMData
    if vectors.isForall then
      return some (← finDimension? vectors.bindingDomain!)
  return none

/-! ## Current-module definitions -/

/--
Current-module definitions that conceal the dependence of `function`'s body on its
argument of type `domain`. Imported analytic functions and binder-independent
coefficients are not collected.
-/
def dependentLocalDefinitions (domain function : Expr) : MetaM (Array Name) :=
  withLocalDeclD `t domain fun binder ↦ do
    let applied := mkApp function binder
    let definitions ← RealExpression.collectDependentLocalDefinitions binder applied
    let body ← withTransparency .reducible <| whnf applied
    RealExpression.collectDependentLocalDefinitions binder body definitions

/--
Current-module real-valued definitions occurring in `expression`, typically the stated
derivative. Unfolding them lets the conversion see the same presentation as the reflected
body; imported definitions are never unfolded.
-/
def statedLocalDefinitions (expression : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let mut names := #[]
  for name in expression.getUsedConstants do
    unless env.isImportedConst name do
      if let some (.defnInfo info) := env.find? name then
        let realValued ← forallTelescopeReducing info.type fun _ result ↦
          return result.isConstOf ``Real
        if realValued then
          names := names.push name
  return names

/-- Unfold the listed definitions in the main goal, skipping names that no longer occur
(for example after an earlier unfolding in the same pass). -/
def unfoldDefinitions (names : Array Name) : TacticM Unit := do
  if names.isEmpty then
    return
  let mut goal ← getMainGoal
  for name in names.toList.eraseDups do
    goal ← try Meta.unfoldTarget goal name catch _ => pure goal
  replaceMainGoal [goal]

/--
Repeatedly unfold the definitions returned by `collect`, which runs in the context of the
main goal, until it returns none or the fuel is spent. Repeating the pass handles chains of
ordinary user definitions.
-/
def unfoldLocalDefinitionsWhile (collect : TacticM (Array Name)) :
    (fuel : Nat := 16) → TacticM Unit
  | 0 =>
      pure ()
  | fuel + 1 => do
      let unfolded ← withMainContext do
        let definitions ← collect
        if definitions.isEmpty then
          return false
        unfoldDefinitions definitions
        return true
      if unfolded then
        unfoldLocalDefinitionsWhile collect fuel

/-! ## Checked expression constants under the evaluator -/

/-- Collect the closed checked expressions `e` under evaluations `Verified.Expr.eval ρ e` in
`expression` that are not explicit constructor trees: imported or current-module constants of
type `Verified.Expr _` and computed expressions such as a lowered residual. Binders are
entered, since the environment `ρ` of an evaluated function body may depend on the bound
variable while the expression itself is closed. -/
private def collectEvaluatedConstants : Expr → Array Expr → Array Expr
  | expression, found =>
      let found :=
        let subterm := expression.consumeMData
        if subterm.isAppOfArity ``Verified.Expr.eval 3 then
          let checked := subterm.getAppArgs[2]!
          if !checked.hasLooseBVars && !checked.hasFVar && !checked.hasMVar &&
              !isExplicitExpression checked && !found.contains checked then
            found.push checked
          else
            found
        else
          found
      match expression with
      | .app function argument =>
          collectEvaluatedConstants argument (collectEvaluatedConstants function found)
      | .lam _ type body _ | .forallE _ type body _ =>
          collectEvaluatedConstants body (collectEvaluatedConstants type found)
      | .letE _ type value body _ =>
          collectEvaluatedConstants body
            (collectEvaluatedConstants value (collectEvaluatedConstants type found))
      | .mdata _ body | .proj _ _ body => collectEvaluatedConstants body found
      | _ => found

/--
Expose, in the main goal, every closed checked expression that is evaluated but is not an
explicit constructor tree: an imported or current-module constant of type `Verified.Expr _`,
or a computed expression such as a lowered equation residual. Each such expression is read back
from one kernel evaluation, the equality with its explicit constructor tree is certified by
`decide +kernel`, the goal is rewritten, and the evaluator is unfolded to ordinary real syntax
by the same `simp only` script the derivative frontends use. Larger expressions are rewritten
first, so that rewriting `2 * x` cannot remove an occurrence of `-(2 * x)`, and an expression
that no longer occurs is skipped. Only expression data is exposed; imported definitions of real
functions stay folded. The goal is unchanged when nothing applies.
-/
def exposeCheckedExpressions (operation : String) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let constants := (collectEvaluatedConstants target #[]).insertionSort fun a b ↦
    a.sizeWithoutSharing > b.sizeWithoutSharing
  if constants.isEmpty then
    return
  let mut goal ← getMainGoal
  for checked in constants do
    unless checked.occurs (← instantiateMVars (← goal.getType)) do continue
    let index ←
      try KernelReadBack.finIndexOfType (← inferType checked)
      catch _ => continue
    let explicit ← quoteNatExpression index (← readBackExpression index checked)
    let equality ← decideByKernel operation (← mkEq checked explicit)
    let target ← instantiateMVars (← goal.getType)
    let result ← goal.rewrite target equality
    unless result.mvarIds.isEmpty do
      throwError "{operation} internal error: exposing a checked expression left auxiliary goals"
    goal ← goal.replaceTargetEq result.eNew result.eqProof
  let unfolded ←
    try
      withSuppressedMessagesMeta <| runTacticOnGoal goal (← unfoldEvaluationSyntax)
    catch _ =>
      pure [goal]
  match unfolded with
  | [] => replaceMainGoal []
  | [unfoldedGoal] => replaceMainGoal [unfoldedGoal]
  | _ => throwError "{operation} internal error: unfolding a checked expression split the goal"

/-! ## Checked derivative proofs -/

/--
A checked derivative theorem about the reflected form of an ordinary function.

`proof` is stated for `function`, the reflected form of the user's function; the
frontend identifies the two by definitional unfolding or by an explicit function
equality goal.
-/
structure Derivative where
  /-- The bridge theorem instance. -/
  proof : Expr
  /-- The reflected function `fun q ↦ expr.eval (paramEmbed c q)` (or its line form). -/
  function : Expr
  /-- The computed derivative value appearing in `proof`. -/
  value : Expr
  /-- The coordinates `p 0, …, p (n - 1)` of the evaluation point (the point itself for a
  scalar derivative). -/
  pointCoordinates : Array Expr
  /-- The frozen binder-independent parameters `c₀, …, c_{k-1}`. -/
  parameters : Array Expr

private def coordinateLiteral (dimension position : Nat) : MetaM Expr :=
  mkAppOptM ``OfNat.ofNat
    #[some (mkApp (mkConst ``Fin) (toExpr dimension)), some (mkRawNatLit position), none]

/-- The coordinate terms `q 0, …, q (n - 1)` of a Euclidean point `q : ℝ^n`. -/
def coordinateTerms (point : Expr) (dimension : Nat) : MetaM (Array Expr) := do
  let projection ← mkAppM ``WithLp.ofLp #[point]
  (Array.range dimension).mapM fun position ↦ do
    return mkApp projection (← coordinateLiteral dimension position)

/--
Prove `HasDerivAt (fun s ↦ expr.eval (lineEmbed c s)) D point` for the body of an
ordinary function `ℝ → ℝ` given by `body` in terms of `binder`.
-/
def scalarHasDerivAt
    (operation : String) (binder body point : Expr)
    (evidence? : Option (TSyntax `term)) : MetaM Derivative := do
  let reflection ← RealExpression.reflectEmbedded operation #[binder] #[binder] body
  let k := reflection.parameterCount
  let index ← RealExpression.embeddedCoordinate 1 k 0
  let indexValue ← mkEqRefl (mkNatLit 0)
  let proof ←
    applyBridge operation ``Verified.Expr.hasDerivAt_eval_lineEmbed
      #[some (toExpr k), some reflection.expression, some reflection.parameters,
        some point, some index, some indexValue] 1 evidence?
  let proofType ← instantiateMVars (← inferType proof)
  let arguments := proofType.getAppArgs
  unless proofType.isAppOfArity ``HasDerivAt 10 do
    throwError "{operation} internal error: unexpected shape of the derivative theorem"
  return {
    proof
    function := arguments[7]!
    value := arguments[8]!
    pointCoordinates := #[point]
    parameters := reflection.coordinates.extract 1 reflection.coordinates.size
  }

/-! ## Identifying the user's function with its reflected form -/

/--
Transport a derivative theorem about the reflected function to the user's `function`.

When the two are definitionally equal the proof is reused as is. Otherwise (for
example after the lowering of `abs`, `tan`, or hyperbolic functions) an equality goal
`function = reflected` is returned for the conversion cleanup to close.
-/
def transportToFunction
    (derivative : Derivative) (function : Expr) (predicate : Expr → MetaM Expr) :
    MetaM (Expr × Option MVarId) := do
  if ← isDefEq function derivative.function then
    return (derivative.proof, none)
  let functionType ← inferType function
  let equality ← mkFreshExprSyntheticOpaqueMVar (← mkEq function derivative.function)
  let motive ←
    withLocalDeclD `g functionType fun g ↦ do
      mkLambdaFVars #[g] (← predicate g)
  let congruence ← mkCongrArg motive equality
  let proof ← mkEqMPR congruence derivative.proof
  return (proof, some equality.mvarId!)

/-! ## Conversion of computed derivatives to the stated form -/

/-- Unfold the checked evaluator and the embedding coordinates back to ordinary real
syntax in every goal, leaving goals unchanged when nothing applies. -/
def unfoldEvaluation (goals : List MVarId) : MetaM (List MVarId) := do
  let tactic ← unfoldEvaluationSyntax
  let mut remaining := []
  for goal in goals do
    let goals ←
      try
        withSuppressedMessagesMeta <| runTacticOnGoal goal tactic
      catch _ =>
        pure [goal]
    remaining := remaining ++ goals
  return remaining

private def tryOnEachGoal (goals : List MVarId) (tactic : TSyntax `tactic) :
    MetaM (List MVarId) := do
  let mut remaining := []
  for goal in goals do
    let goals ←
      try
        withSuppressedMessagesMeta <| runTacticOnGoal goal tactic
      catch _ =>
        pure [goal]
    remaining := remaining ++ goals
  return remaining

/--
The fixed Mathlib normalization script identifying a computed derivative with a
stated one: simplification with the lowered analytic identities and `ring_nf`,
followed by targeted tangent, absolute-value, exponential, `field_simp`, and
nonpositive square-root cleanups.
-/
def mathlibCleanup (goals : List MVarId) : MetaM (List MVarId) := do
  -- Cancel square roots before polynomial normalization expands their radicands.
  -- This retains the visible positivity of expressions such as `1 + s ^ 2`.
  let mut prepared := []
  for goal in goals do
    if (← goal.getType).getUsedConstants.contains ``Real.sqrt then
      let saved ← saveState
      try
        let remaining ← withSuppressedMessagesMeta <| runTacticOnGoal goal (← `(tactic|
          (field_simp (disch := positivity)
           simp (disch := positivity) only [Real.sq_sqrt]
           ring1)))
        if remaining.isEmpty then
          continue
      catch _ =>
        pure ()
      saved.restore
    prepared := prepared ++ [goal]
  let goals := prepared
  let goals ← tryOnEachGoal goals (← `(tactic|
    first
      | (funext t
         simp_all [Verified.Expr.eval, Verified.Expr.diff,
           PiLp.single_apply, Real.tan_eq_sin_div_cos,
           Real.sinh_eq, Real.cosh_eq, Real.tanh_eq,
           Real.sqrt_sq_eq_abs,
           tangent_derivative_mul_normalize,
           tangent_derivative_div_normalize] <;>
         ring_nf)
      | (simp_all [Verified.Expr.eval, Verified.Expr.diff,
           PiLp.single_apply, Real.tan_eq_sin_div_cos,
           Real.sinh_eq, Real.cosh_eq, Real.tanh_eq,
           Real.sqrt_sq_eq_abs,
           tangent_derivative_mul_normalize,
           tangent_derivative_div_normalize] <;>
         ring_nf)))
  let goals ← tryOnEachGoal goals (← `(tactic|
    first
      | rw [tangent_derivative_mul_normalize]
      | rw [tangent_derivative_div_normalize]
      | rw [← tangent_scaled_sum_normalize]
      | (congr 1
         funext t
         rw [Real.tanh_eq]
         ring)
      | nlinarith [Real.sin_sq_add_cos_sq _]
      -- Commit these rewrites only when they close the goal, so expanding `2 * x`
      -- cannot prevent a later absolute-value cleanup.
      | (simp [two_mul, mul_two, Real.exp_add, Real.exp_neg] <;> ring1)
      | (rw [abs_of_pos (by linarith)]
         field_simp (disch := linarith)
         ring)
      | (rw [abs_of_neg (by linarith)]
         field_simp (disch := linarith)
         ring)
      | (field_simp (disch := positivity) <;> ring)
      | (field_simp <;> ring)
      | simp))
  let goals ← tryOnEachGoal goals
    (← `(tactic| field_simp (disch := positivity) <;> ring))
  let goals ← tryOnEachGoal goals
    (← `(tactic|
      simp [two_mul, mul_two, Real.exp_add, Real.exp_neg] <;>
        field_simp (disch := positivity) <;>
        ring))
  -- Outside [-1, 1], the total inverse-trigonometric derivatives reduce to
  -- reciprocals of square roots of negative numbers, which are zero in ℝ.
  tryOnEachGoal goals (← `(tactic| norm_num [Real.sqrt_eq_zero_of_nonpos]))

/-- The tactic identifying the evaluation of a reflected expression over an explicit atom
environment with the ordinary real term it reflects: definitional unfolding, or the unfolding
of the evaluator and coordinate vectors together with the checked lowerings of `tan`, the
hyperbolic functions, `abs`, of natural powers as real powers of the cast exponent with the
cast pushed through the exponent's arithmetic (`Real.rpow_natCast`, `Nat.cast_add`,
`Nat.cast_mul`, `Nat.cast_pow`, `Nat.cast_sub` under an `omega`-discharged bound), and of
integer powers with symbolic exponents (`Real.rpow_intCast`). -/
def loweringBridgeSyntax : MetaM (TSyntax `tactic) :=
  -- `Fin.reduceFinMk` and `reduceFinAppend` evaluate the atom vector and the embedding at the
  -- literal indices produced by `fin_cases`; they are needed when a frozen parameter is a
  -- numeral `0` or `1`, whose atom quotation evaluates to a cast that is not definitionally
  -- the literal, so that `rfl` fails. A natural power is written as the real power of its
  -- cast exponent on both sides (`Real.rpow_natCast` backwards) and the cast is pushed through
  -- the exponent's arithmetic, with `omega` discharging the non-truncation hypothesis of
  -- `Nat.cast_sub`, so that the structurally reflected exponents of the reifier match.
  `(tactic|
    first
      | rfl
      | (simp +decide (disch := omega) only
          [Verified.Expr.eval, Verified.Expr.ofLp_lineEmbed, Verified.Expr.ofLp_paramEmbed,
            Fin.reduceFinMk, reduceFinAppend, Fin.append_left, Fin.append_right, Fin.isValue,
            Matrix.cons_val,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Nat.cast_ofNat,
            Nat.cast_zero, Nat.cast_one, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
            Nat.cast_sub, one_div, Real.tan_eq_sin_div_cos, Real.sinh_eq,
            Real.cosh_eq, Real.tanh_eq, Real.sqrt_sq_eq_abs, ← Real.rpow_natCast,
            Real.rpow_intCast]))

/--
Certify with the kernel that the multivariate canonical form of `lhs - rhs` is zero.

This is the fallback of the checked identity routes when the side-conditioned pipeline does not
reduce the difference to zero. The canonical form `Verified.Expr.Alg.canonicalForm` cancels the
polynomial gcd of numerator and denominator over the atoms and canonicalizes the arguments of the
elementary functions bottom-up. It is evaluated by the kernel and read back through `readBackRun`,
the run is certified by `decide +kernel`, and the equality is
`Verified.Expr.Alg.eval_eq_of_canonicalForm_sub_eq` applied to a fresh goal for the recorded
conditions (divisor numerators and cancelled factors), which the caller discharges. Fails, naming
the residual, when the canonical form is not zero.
-/
def certifyCanonicalZeroDifference
    (operation : String) (atomIndex atomEnvironment lhs rhs : Expr) : MetaM (Expr × MVarId) := do
  let difference ← mkAppM ``Verified.Expr.sub #[lhs, rhs]
  let run ← mkAppM ``Verified.Expr.Alg.canonicalForm #[difference]
  let (normalForm, sideList) ← readBackRun atomIndex run
  unless normalForm == .nat 0 do
    let residual ← quoteNatExpression atomIndex normalForm
    throwError
      "canonical form route: the canonical rational form of the difference is not zero.\n\
       Canonical difference:{indentExpr residual}"
  let quotedSide ← quoteNatList atomIndex sideList
  let zero ← mkAppOptM ``Verified.Expr.nat #[some atomIndex, some (toExpr (0 : Nat))]
  let result ← mkAppM ``Verified.Expr.Alg.NormResult.mk #[zero, quotedSide]
  let runProof ← decideByKernel operation (← mkEq run result)
  let partialClaim ←
    mkAppOptM ``Verified.Expr.Alg.eval_eq_of_canonicalForm_sub_eq
      #[none, none, none, some lhs, some rhs, some atomEnvironment, some quotedSide,
        some runProof]
  let (claim, hypotheses) ← applyToFreshHypotheses partialClaim 1
  return (claim, hypotheses[0]!)

/--
Certify with the kernel that the side-conditioned pipeline reduces `lhs - rhs` to zero.

`lhs` and `rhs` are quoted `Verified.Expr` terms over the index type `atomIndex = Fin m`, and
`atomEnvironment : Fin m → ℝ` assigns the atoms. The statement certified by `decide +kernel` is
that the run of the pipeline on the difference has the normal form `0` and the essential side
list `side` (`CAS.Verified.Expr.essentialSide`: the recorded conditions the structural sign
checker does not prove). The empty list is tried first, which one kernel evaluation certifies
for unconditional identities and for residuals whose denominators are structurally nonzero;
only when that fails are the normal form and side list read back from one serialized kernel
evaluation (`readBackRun`) and the run certified against the essential list read back. The
result is the equality `lhs.eval atomEnvironment = rhs.eval atomEnvironment` of
`CAS.Verified.Expr.eval_eq_of_sideConditionPipeline_run_essential`, applied to a fresh goal for
the obligation `Alg.SideHolds atomEnvironment side`, which the caller discharges. When the
normal form is not zero, the multivariate canonical form is tried on the difference
(`certifyCanonicalZeroDifference`); the failure names both residuals.
-/
def certifyZeroDifference
    (operation : String) (atomIndex atomEnvironment lhs rhs : Expr) : MetaM (Expr × MVarId) := do
  let pipeline ← mkAppOptM ``Verified.Expr.sideConditionPipeline #[some atomIndex, none]
  let difference ← mkAppM ``Verified.Expr.sub #[lhs, rhs]
  let run ← mkAppM ``Verified.Expr.SidePipeline.run #[pipeline, difference]
  let zero ← mkAppOptM ``Verified.Expr.nat #[some atomIndex, some (toExpr (0 : Nat))]
  let nil ← mkAppOptM ``List.nil #[some (mkApp (mkConst ``Verified.Expr [Level.zero]) atomIndex)]
  let runExpr ← mkAppM ``Verified.Expr.Alg.NormResult.expr #[run]
  let essential ← mkAppM ``Verified.Expr.essentialSide
    #[← mkAppM ``Verified.Expr.Alg.NormResult.nonzero #[run]]
  let certify (quotedSide : Expr) : MetaM (Option Expr) := do
    let statement := mkAnd (← mkEq runExpr zero) (← mkEq essential quotedSide)
    try
      some <$> decideByKernel operation statement
    catch _ =>
      pure none
  let certified ←
    match ← certify nil with
    | some proof => pure (some (nil, proof))
    | none =>
        let (normalForm, sideList) ← readBackRun atomIndex run
        if normalForm == .nat 0 then
          let quotedSide ← quoteNatList atomIndex (essentialConditions sideList)
          match ← certify quotedSide with
          | some proof => pure (some (quotedSide, proof))
          | none => throwError "{operation} could not certify the checked normalizer run"
        else
          -- The pipeline left a residual: the multivariate canonical form is the fallback.
          let residual ← quoteNatExpression atomIndex normalForm
          try
            return ← certifyCanonicalZeroDifference operation atomIndex atomEnvironment lhs rhs
          catch canonicalError =>
            throwError
              "{operation} could not identify the two sides: the checked normalizer does not \
               reduce their difference to zero.\nNormalized difference:{indentExpr residual}\n\
               {canonicalError.toMessageData}"
  let some (quotedSide, runProof) := certified
    | throwError "{operation} internal error: the checked normalizer run was not certified"
  let partialClaim ←
    mkAppOptM ``Verified.Expr.eval_eq_of_sideConditionPipeline_run_essential
      #[none, none, some lhs, some rhs, some atomEnvironment, some quotedSide, some runProof]
  let (claim, hypotheses) ← applyToFreshHypotheses partialClaim 1
  return (claim, hypotheses[0]!)

/-! ## A shared radicand of a folded Laplacian sum -/

/-- The reflected body `expr` of a folded Laplacian value
`addList (List.ofFn fun i ↦ (expr.diff i).diff i)`. -/
def foldedBody? (symbolic : Expr) : Option Expr := do
  let symbolic := symbolic.consumeMData
  guard (symbolic.isAppOfArity ``Verified.Expr.addList 2)
  let list := symbolic.appArg!.consumeMData
  guard (list.isAppOfArity ``List.ofFn 3)
  let .lam _ _ body _ := list.appArg!.consumeMData | none
  let outer := body.consumeMData
  guard (outer.isAppOfArity ``Verified.Expr.diff 4)
  let inner := outer.appArg!.consumeMData
  guard (inner.isAppOfArity ``Verified.Expr.diff 4)
  let expr := inner.appArg!
  guard (!expr.hasLooseBVars)
  return expr

/-- The number of nodes of a checked expression. -/
def nodeCount : Verified.Expr Nat → Nat
  | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ => 1
  | .add a b | .mul a b | .sub a b | .div a b | .rpow a b => nodeCount a + nodeCount b + 1
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a
  | .sqrt a => nodeCount a + 1

/-- The arguments of square roots and logarithms and the bases of real powers in an expression,
when they are compound (neither variables nor literals), with repetitions. -/
def radicandCandidates : Verified.Expr Nat → List (Verified.Expr Nat)
  | .sqrt a | .log a => compound a ++ radicandCandidates a
  | .rpow a b => compound a ++ radicandCandidates a ++ radicandCandidates b
  | .add a b | .mul a b | .sub a b | .div a b => radicandCandidates a ++ radicandCandidates b
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a =>
      radicandCandidates a
  | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ => []
where
  /-- The argument itself when it is compound. -/
  compound : Verified.Expr Nat → List (Verified.Expr Nat)
    | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ => []
    | argument => [argument]

/-- The radicand shared by the summands of a Laplacian: the most frequent compound argument of a
square root, logarithm, or real power in the reflected body, the largest one among equally
frequent candidates. `none` when the body has no such argument. -/
def sharedRadicand? (body : Verified.Expr Nat) : Option (Verified.Expr Nat) :=
  let candidates := radicandCandidates body
  let scored := candidates.eraseDups.map fun candidate ↦
    (candidate, candidates.count candidate, nodeCount candidate)
  let better (a b : Verified.Expr Nat × Nat × Nat) : Bool :=
    a.2.1 > b.2.1 || (a.2.1 == b.2.1 && a.2.2 > b.2.2)
  (scored.foldl (fun best candidate ↦
    match best with
    | none => some candidate
    | some best => if better candidate best then some candidate else some best) none).map (·.1)

/-- Lower a checked expression over the embedded index to the ordinary real term it denotes, with
`var i` the `i`-th coordinate term for `i` below the dimension and the frozen parameter
`i - dimension` otherwise. Mirrors `Verified.Expr.eval`, so the lowering bridge identifies the
term with the evaluation of the expression. -/
def lowerEmbedded (operation : String) (coordinates parameters : Array Expr) :
    Verified.Expr Nat → MetaM Expr
  | .nat n => mkAppOptM ``Nat.cast #[some (mkConst ``Real), none, some (mkNatLit n)]
  | .int z => mkAppOptM ``Int.cast #[some (mkConst ``Real), none, some (toExpr z)]
  | .rat a b => do
      mkAppM ``HDiv.hDiv
        #[← mkAppOptM ``Int.cast #[some (mkConst ``Real), none, some (toExpr a)],
          ← mkAppOptM ``Nat.cast #[some (mkConst ``Real), none, some (mkNatLit b)]]
  | .pi => return mkConst ``Real.pi
  | .e => do
      mkAppM ``Real.exp #[← mkAppOptM ``OfNat.ofNat #[some (mkConst ``Real), some (mkRawNatLit 1),
        none]]
  | .var i => do
      if h : i < coordinates.size then
        return coordinates[i]
      else if h' : i - coordinates.size < parameters.size then
        return parameters[i - coordinates.size]
      else
        throwError "{operation} internal error: a radicand mentions an unknown coordinate"
  | .add a b => do mkAppM ``HAdd.hAdd #[← lowerEmbedded operation coordinates parameters a,
      ← lowerEmbedded operation coordinates parameters b]
  | .mul a b => do mkAppM ``HMul.hMul #[← lowerEmbedded operation coordinates parameters a,
      ← lowerEmbedded operation coordinates parameters b]
  | .sub a b => do mkAppM ``HSub.hSub #[← lowerEmbedded operation coordinates parameters a,
      ← lowerEmbedded operation coordinates parameters b]
  | .div a b => do mkAppM ``HDiv.hDiv #[← lowerEmbedded operation coordinates parameters a,
      ← lowerEmbedded operation coordinates parameters b]
  | .neg a => do mkAppM ``Neg.neg #[← lowerEmbedded operation coordinates parameters a]
  | .pow a n => do
      mkAppM ``HPow.hPow #[← lowerEmbedded operation coordinates parameters a, mkNatLit n]
  | .sin a => do mkAppM ``Real.sin #[← lowerEmbedded operation coordinates parameters a]
  | .cos a => do mkAppM ``Real.cos #[← lowerEmbedded operation coordinates parameters a]
  | .atan a => do mkAppM ``Real.arctan #[← lowerEmbedded operation coordinates parameters a]
  | .asin a => do mkAppM ``Real.arcsin #[← lowerEmbedded operation coordinates parameters a]
  | .acos a => do mkAppM ``Real.arccos #[← lowerEmbedded operation coordinates parameters a]
  | .exp a => do mkAppM ``Real.exp #[← lowerEmbedded operation coordinates parameters a]
  | .log a => do mkAppM ``Real.log #[← lowerEmbedded operation coordinates parameters a]
  | .sqrt a => do mkAppM ``Real.sqrt #[← lowerEmbedded operation coordinates parameters a]
  | .rpow a b => do mkAppM ``HPow.hPow #[← lowerEmbedded operation coordinates parameters a,
      ← lowerEmbedded operation coordinates parameters b]

/--
Certify with the kernel that a sum of quoted summands evaluates to a quoted stated value with the
shared radicand `pattern` abstracted as the atom `abstraction` before the summands are normalized
(`CAS.Verified.Expr.abstractedSummandRun`). The atom environment sends `abstraction` to the value
of `pattern`, which the lowering bridge proves; the rest is as in `certifySumDifference`, whose
kernel work this saves: with the radicand atomic, the normal forms of the summands and their
recorded conditions are small, and the conditions name the radicand itself rather than expanded
powers of it. The result is the equality of
`CAS.Verified.Expr.eval_eq_of_abstractedSummandRun_compact` with a fresh goal for its side
obligation.
-/
def certifyAbstractedSumDifference
    (operation : String) (atomIndex atomEnvironment summands stated pattern abstraction : Expr) :
    MetaM (Expr × MVarId) := do
  let run ← mkAppM ``Verified.Expr.abstractedSummandRun
    #[summands, stated, pattern, abstraction]
  let zero ← mkAppOptM ``Verified.Expr.nat #[some atomIndex, some (toExpr (0 : Nat))]
  let runExpr ← mkAppM ``Verified.Expr.Alg.NormResult.expr #[run]
  let compacted ← mkAppM ``Verified.Expr.compactNonzero
    #[← mkAppM ``Verified.Expr.Alg.NormResult.nonzero #[run]]
  let (normalForm, sideList) ← readBackPair atomIndex runExpr compacted
  unless normalForm == .nat 0 do
    let residual ← quoteNatExpression atomIndex normalForm
    throwError
      "{operation} could not identify the two sides: the checked normalizer does not \
       reduce their difference to zero with the shared radicand abstracted.\n\
       Normalized difference:{indentExpr residual}"
  let quotedSide ← quoteNatList atomIndex (essentialConditions sideList)
  let essential ← mkAppM ``Verified.Expr.essentialSide #[compacted]
  let runProof ← decideByKernel operation
    (mkAnd (← mkEq runExpr zero) (← mkEq essential quotedSide))
  let partialClaim ←
    mkAppOptM ``Verified.Expr.eval_eq_of_abstractedSummandRun_compact
      #[none, none, some summands, some stated, some pattern, some abstraction,
        some atomEnvironment, some quotedSide, some runProof]
  let (claim, hypotheses) ← applyToFreshHypotheses partialClaim 2
  -- The abstraction atom evaluates to the radicand: a lowering-bridge identity.
  let remaining ←
    try
      withSuppressedMessagesMeta <| runTacticOnGoal hypotheses[0]! (← loweringBridgeSyntax)
    catch _ =>
      throwError "{operation} could not identify the shared radicand with its atom"
  unless remaining.isEmpty do
    throwError "{operation} could not identify the shared radicand with its atom"
  return (claim, hypotheses[1]!)

/--
Certify with the kernel that a sum of quoted summands evaluates to a quoted stated value, each
summand normalized on its own before the sum (`CAS.Verified.Expr.summandRun`). This is the
certification of the Laplacian fold, whose summands share denominators that the fraction normal
form of the whole sum would cross-multiply. The recorded conditions of the summands usually do
not hold structurally (positivity of a radicand), so the run is read back first and certified
against the essential list of the compacted conditions read back
(`CAS.Verified.Expr.compactNonzero`). The result is the equality
`(addList summands).eval atomEnvironment = stated.eval atomEnvironment` of
`CAS.Verified.Expr.eval_eq_of_summandRun_compact` with a fresh goal for its side obligation.
-/
def certifySumDifference
    (operation : String) (atomIndex atomEnvironment summands stated : Expr) :
    MetaM (Expr × MVarId) := do
  let run ← mkAppM ``Verified.Expr.summandRun #[summands, stated]
  let zero ← mkAppOptM ``Verified.Expr.nat #[some atomIndex, some (toExpr (0 : Nat))]
  let runExpr ← mkAppM ``Verified.Expr.Alg.NormResult.expr #[run]
  -- The recorded conditions are compacted by the kernel (common factors extracted, products
  -- split) before the essential ones are kept, so that a denominator such as `√u * x² + √u * y²`
  -- reaches the discharger as `√u ≠ 0` and `x² + y² ≠ 0`.
  let compacted ← mkAppM ``Verified.Expr.compactNonzero
    #[← mkAppM ``Verified.Expr.Alg.NormResult.nonzero #[run]]
  let (normalForm, sideList) ← readBackPair atomIndex runExpr compacted
  unless normalForm == .nat 0 do
    let residual ← quoteNatExpression atomIndex normalForm
    throwError
      "{operation} could not identify the two sides: the checked normalizer does not \
       reduce their difference to zero.\nNormalized difference:{indentExpr residual}"
  let quotedSide ← quoteNatList atomIndex (essentialConditions sideList)
  let essential ← mkAppM ``Verified.Expr.essentialSide #[compacted]
  let runProof ← decideByKernel operation
    (mkAnd (← mkEq runExpr zero) (← mkEq essential quotedSide))
  let partialClaim ←
    mkAppOptM ``Verified.Expr.eval_eq_of_summandRun_compact
      #[none, none, some summands, some stated, some atomEnvironment, some quotedSide,
        some runProof]
  let (claim, hypotheses) ← applyToFreshHypotheses partialClaim 1
  return (claim, hypotheses[0]!)

/-- Prove `(reflected.eval atomEnvironment) = term` by the lowering bridge. -/
def bridgeReflection
    (operation : String) (atomEnvironment reflected term : Expr) : MetaM Expr := do
  let evaluation ← mkAppM ``Verified.Expr.eval #[atomEnvironment, reflected]
  let bridge ← mkFreshExprSyntheticOpaqueMVar (← mkEq evaluation term)
  let remaining ←
    try
      withSuppressedMessagesMeta <| runTacticOnGoal bridge.mvarId! (← loweringBridgeSyntax)
    catch _ =>
      throwError "{operation} could not identify a side of the identity with its reflected form"
  unless remaining.isEmpty do
    throwError "{operation} could not identify a side of the identity with its reflected form"
  instantiateMVars bridge

/--
Close `goal`, an equality `lhs = rhs` between real terms, with the checked side-conditioned
normalizer: both sides are reflected over one shared table of atoms (every maximal subterm that
is not an operation of the checked language), the pipeline is run on their difference in the
kernel and certified by `certifyZeroDifference`, the recorded conditions are discharged by
`closeValidity` from the local context or from `evidence?`, and each reflection is identified
with its ordinary term by the lowering bridge. The goal is left unassigned on failure.
-/
def closeRealEqualityGoal
    (operation : String) (goal : MVarId) (evidence? : Option (TSyntax `term)) :
    MetaM Unit := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let some (type, lhs, rhs) := target.consumeMData.eq?
    | throwError "{operation} checked identity route expected an equality"
  unless ← isDefEq type (mkConst ``Real) do
    throwError
      "{operation} proves checked identities between real numbers; this equality is in\
       {indentExpr type}"
  let (quotations, atoms) ← RealExpression.reifyOverAtoms operation #[] #[lhs, rhs]
  let atomIndex := mkApp (mkConst ``Fin) (toExpr atoms.size)
  let atomEnvironment ← RealExpression.parameterVector atoms
  let reflectedLhs := quotations[0]!
  let reflectedRhs := quotations[1]!
  let (claim, sideGoal) ←
    certifyZeroDifference operation atomIndex atomEnvironment reflectedLhs reflectedRhs
  closeValidity operation sideGoal evidence?
  let claim ← instantiateMVars claim
  let bridgeLhs ← bridgeReflection operation atomEnvironment reflectedLhs lhs
  let bridgeRhs ← bridgeReflection operation atomEnvironment reflectedRhs rhs
  let proof ← mkEqTrans (← mkEqSymm bridgeLhs) (← mkEqTrans claim bridgeRhs)
  let proof ← instantiateMVars proof
  if proof.hasMVar ∨ proof.hasSorry then
    throwError "{operation} produced incomplete identity evidence"
  unless ← isTypeCorrect proof do
    throwError "{operation} produced ill-typed identity evidence"
  goal.assign proof

/-- Whether a quoted checked expression contains a natural power whose exponent is not a
numeral, so that the kernel cannot evaluate it. -/
def hasSymbolicNaturalExponent (expression : Expr) : Bool :=
  Option.isSome <| expression.find? fun subterm ↦
    subterm.isAppOfArity ``Verified.Expr.pow 3 &&
      let exponent := subterm.appArg!.consumeMData
      exponent.nat?.isNone && exponent.rawNatLit?.isNone

/--
Close the value goal `computed = stated` with the checked side-conditioned normalizer.

`computed` is `expr.eval ρ` for the derivative's embedded environment `ρ`, whose
parameter coordinates are the frozen binder-independent subterms of the body. Those
parameters and the stated derivative are reflected again over one shared table of atoms
(maximal subterms that are not reifier operations), so that the normalizer sees their
full algebraic structure; `Verified.Expr.eval_mapVars` transports the computed value to
the atom environment. The pipeline is run on the difference in the kernel and certified
by `certifyZeroDifference`, and the emitted side conditions are discharged by
`closeValidity` (with the user's evidence when supplied). A folded Laplacian sum
(`Verified.Expr.addList`) is certified summand by summand, with the radicand its summands share
abstracted as an atom (`certifyAbstractedSumDifference`) when the body has one and directly
(`certifySumDifference`) otherwise. When the
computed expression contains a natural power with a symbolic exponent, which the kernel
cannot evaluate as data, the evaluator is unfolded first and the goal is closed as an
ordinary real identity by `closeRealEqualityGoal`, whose reflection reads the power as a real
power of the cast exponent and reflects the exponent's arithmetic.
-/
def closeValueGoalChecked
    (operation : String) (goal : MVarId) (derivative : Derivative)
    (evidence? : Option (TSyntax `term)) : MetaM Unit := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let some (_, computed, stated) := target.eq?
    | throwError "{operation} internal error: the derivative conversion goal is not an equality"
  let computed := computed.consumeMData
  unless computed.isAppOfArity ``Verified.Expr.eval 3 do
    throwError "{operation} internal error: the computed derivative is not a checked evaluation"
  let arguments := computed.getAppArgs
  let environment := arguments[1]!
  let symbolic := arguments[2]!
  if hasSymbolicNaturalExponent symbolic then
    -- A natural power with a symbolic exponent cannot be evaluated by the kernel as data. The
    -- evaluator is unfolded to ordinary syntax instead and both sides are reflected over shared
    -- atoms, which reads such a power as the real power of its cast exponent and reflects the
    -- exponent's arithmetic.
    let remaining ←
      try
        withSuppressedMessagesMeta <| runTacticOnGoal goal (← unfoldEvaluationSyntax)
      catch _ =>
        pure [goal]
    match remaining with
    | [] => return
    | [unfolded] => return ← closeRealEqualityGoal operation unfolded evidence?
    | _ => throwError "{operation} internal error: unfolding the computed derivative split the goal"
  let index := (← whnf (← inferType symbolic)).appArg!
  let dimension := derivative.pointCoordinates.size
  -- A folded Laplacian sum with a shared radicand: the radicand becomes an atom of its own,
  -- placed right after the point coordinates, so that the summands can be normalized with it
  -- abstracted (`certifyAbstractedSumDifference`).
  let radicand? ←
    match foldedBody? symbolic with
    | some body => pure (sharedRadicand? (← readBackExpression index body))
    | none => pure none
  let radicandTerm? ← radicand?.mapM
    (lowerEmbedded operation derivative.pointCoordinates derivative.parameters)
  let initialAtoms :=
    match radicandTerm? with
    | some term => derivative.pointCoordinates.push term
    | none => derivative.pointCoordinates
  -- Decompose the frozen parameters and the stated derivative into shared atoms.
  let (quotations, atoms) ←
    RealExpression.reifyOverAtoms operation initialAtoms (derivative.parameters.push stated)
  let atomIndex := mkApp (mkConst ``Fin) (toExpr atoms.size)
  let atomEnvironment ← RealExpression.parameterVector atoms
  let coordinateEntries ← (Array.range dimension).mapM fun position ↦ do
    mkAppM ``Verified.Expr.var #[← RealExpression.finLiteral position atoms.size]
  let substitution ←
    RealExpression.vectorLiteral (mkApp (mkConst ``Verified.Expr [Level.zero]) atomIndex)
      (coordinateEntries ++ quotations.pop)
  let reflectedStated := quotations.back!
  let renamed ← mkAppM ``Verified.Expr.mapVars #[substitution, symbolic]
  -- The embedded environment agrees with the atom environment through the substitution.
  let substitutedEnvironment ←
    withLocalDeclD `j index fun j ↦ do
      mkLambdaFVars #[j]
        (← mkAppM ``Verified.Expr.eval #[atomEnvironment, mkApp substitution j])
  let environmentGoal ←
    mkFreshExprSyntheticOpaqueMVar (← mkEq environment substitutedEnvironment)
  let lowering ← loweringBridgeSyntax
  let remaining ←
    try
      withSuppressedMessagesMeta <| runTacticOnGoal environmentGoal.mvarId!
        (← `(tactic| (funext j; fin_cases j <;> $lowering:tactic)))
    catch error =>
      throwError
        "{operation} could not identify the frozen parameters with their atoms:\
         {indentD error.toMessageData}"
  unless remaining.isEmpty do
    throwError "{operation} could not identify the frozen parameters with their atoms"
  let evaluation ←
    withLocalDeclD `r (← inferType environment) fun r ↦ do
      mkLambdaFVars #[r] (← mkAppM ``Verified.Expr.eval #[r, symbolic])
  let environmentStep ← mkCongrArg evaluation (← instantiateMVars environmentGoal)
  let renamingStep ← mkEqSymm
    (← mkAppM ``Verified.Expr.eval_mapVars #[atomEnvironment, substitution, symbolic])
  -- Run the pipeline on the difference in the kernel, certify the run, and discharge the
  -- emitted side conditions. A folded Laplacian sum is certified summand by summand.
  let (renamingStep, claim, sideGoal) ←
    if symbolic.consumeMData.isAppOfArity ``Verified.Expr.addList 2 then
      let summands := symbolic.consumeMData.appArg!
      let renameSummand ← withLocalDeclD `e (← inferType symbolic) fun e ↦ do
        mkLambdaFVars #[e] (← mkAppM ``Verified.Expr.mapVars #[substitution, e])
      let renamedSummands ← mkAppM ``List.map #[renameSummand, summands]
      let sumStep ← mkAppM ``Verified.Expr.eval_mapVars_addList
        #[atomEnvironment, substitution, summands]
      let (claim, sideGoal) ←
        match radicand? with
        | some pattern =>
            -- The radicand over the atoms: coordinates keep their positions, parameters are
            -- replaced by their reflections over the atoms.
            let parameterData ← quotations.pop.mapM (readBackExpression atomIndex)
            let renamedPattern ← quoteNatExpression atomIndex
              (Verified.Expr.mapVars
                (fun i ↦ if i < dimension then .var i else parameterData[i - dimension]!)
                pattern)
            let abstraction ← RealExpression.finLiteral dimension atoms.size
            certifyAbstractedSumDifference operation atomIndex atomEnvironment renamedSummands
              reflectedStated renamedPattern abstraction
        | none =>
            certifySumDifference operation atomIndex atomEnvironment renamedSummands
              reflectedStated
      pure (← mkEqTrans renamingStep sumStep, claim, sideGoal)
    else
      let (claim, sideGoal) ←
        certifyZeroDifference operation atomIndex atomEnvironment renamed reflectedStated
      pure (renamingStep, claim, sideGoal)
  closeValidity operation sideGoal evidence?
  let claim ← instantiateMVars claim
  -- Identify the stated derivative with the evaluation of its reflection.
  let statedReflection ← mkAppM ``Verified.Expr.eval #[atomEnvironment, reflectedStated]
  let bridge ← mkFreshExprSyntheticOpaqueMVar (← mkEq statedReflection stated)
  let remaining ←
    try
      withSuppressedMessagesMeta <| runTacticOnGoal bridge.mvarId! lowering
    catch _ =>
      throwError
        "{operation} could not identify the stated derivative with its reflected form"
  unless remaining.isEmpty do
    throwError "{operation} could not identify the stated derivative with its reflected form"
  let proof ← mkEqTrans environmentStep
    (← mkEqTrans renamingStep (← mkEqTrans claim (← instantiateMVars bridge)))
  let proof ← instantiateMVars proof
  if proof.hasMVar ∨ proof.hasSorry then
    throwError "{operation} produced incomplete derivative identification evidence"
  unless ← isTypeCorrect proof do
    throwError "{operation} produced ill-typed derivative identification evidence"
  goal.assign proof

/--
Close the conversion goals left after a checked derivative has been transported to the
user's statement: an optional function equality and an optional value equality
`computed = stated`.

The value goal is first attacked by unfolding and the Mathlib script. If goals remain,
the original value goal is retried with the checked normalizer. Unresolved goals are
reported with their targets, together with the reason the checked route failed.
-/
def closeMatchingGoals
    (operation : String) (functionGoal? : Option MVarId) (valueGoal? : Option MVarId)
    (derivative : Derivative) (evidence? : Option (TSyntax `term)) : MetaM Unit := do
  let goals := (functionGoal?.toList ++ valueGoal?.toList)
  if goals.isEmpty then
    return
  let saved ← saveState
  let remaining ← unfoldEvaluation goals
  let remaining ← mathlibCleanup remaining
  if remaining.isEmpty then
    return
  -- Retry the value identification with the checked normalizer on the original goal.
  let mut checkedFailure : MessageData := m!""
  if let some valueGoal := valueGoal? then
    -- Retain the failed cleanup goals for diagnostics if the checked retry also fails.
    let cleanupState ← saveState
    let checked ←
      try
        saved.restore
        let functionRemaining ←
          match functionGoal? with
          | none => pure []
          | some functionGoal => mathlibCleanup (← unfoldEvaluation [functionGoal])
        if functionRemaining.isEmpty then
          closeValueGoalChecked operation valueGoal derivative evidence?
          pure true
        else
          throwError "the reflected function could not be identified with the stated one"
      catch error =>
        checkedFailure := m!"\nChecked normalizer route:{indentD error.toMessageData}"
        pure false
    if checked then
      return
    cleanupState.restore
    reportUnresolved operation remaining checkedFailure
  else
    reportUnresolved operation remaining m!""
where
  reportUnresolved (operation : String) (remaining : List MVarId) (detail : MessageData) :
      MetaM Unit := do
    let targets ← remaining.mapM fun goal ↦
      goal.withContext do instantiateMVars (← goal.getType)
    throwError
      "{operation} computed a checked derivative, but it does not match the \
       stated result. Check the claimed derivative, or run the corresponding \
       `#cas [derive]` command to inspect the normalized result.\n\
       Remaining conversion goals:{indentD (MessageData.joinSep
         (targets.map fun target ↦ m!"{target}") m!"\n\n")}{detail}"

end CAS.Tactic.DerivativeBridge

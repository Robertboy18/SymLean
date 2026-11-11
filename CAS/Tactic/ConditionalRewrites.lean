/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Tactic.Assumptions
public import CAS.Elaboration.RealExpression

/-!
# Conditional analytic rewrites for ordinary goals

Rewrites of analytic subterms whose validity depends on a sign or a nonvanishing condition:
`Real.exp (Real.log u)`, logarithms of products and quotients, and absolute values, together
with the context facts the arithmetic finishers need. Each rewrite fires only where
`symbolic_assumptions` proves its branch condition from the local context. The arithmetic phase
of `cas` (`CAS/Tactic/Arithmetic.lean`) runs them around its simplification step, and the
elementary rewrites of `CAS/Tactic/ElementaryRewrites.lean` reuse the occurrence machinery.

## Main definitions

* `rewriteExpLog`: `Real.exp (Real.log u)` becomes `u` under `0 < u`, and `|u|` under `u ≠ 0`.
* `rewriteLogArithmetic`: `Real.log (a / b)` and `Real.log (a * b)` split by `Real.log_div` and
  `Real.log_mul` once `a ≠ 0` and `b ≠ 0` are proved.
* `rewriteAbsoluteValues`: absolute values are distributed over products and quotients, and
  `|u|` becomes `u` or `-u` once the sign of `u` is proved.
* `splitProductHypotheses`: a hypothesis `a * b ≠ 0` yields the factor conditions `a ≠ 0` and
  `b ≠ 0` (`mul_ne_zero_iff`).
* `addSquareRootFacts`: for every `√u` in the goal with `0 ≤ u` provable, the identities
  `√u ^ 2 = u` and `√u * √u = u` (`Real.sq_sqrt`, `Real.mul_self_sqrt`) join the context.
* `distributePowers`: `(a * b) ^ n` with a symbolic exponent is distributed so that
  `field_simp` can clear each factor separately.
* `prepareArithmetic` and `prepareFinishers`: the product preparation, run by the arithmetic
  route before its simplification, and the absolute-value, power, and square-root
  preparations, run after it.

## Implementation notes

Every rewrite is a theorem application. We collect the occurrences syntactically
(`collectSubterms`), let `proveProposition?` construct each branch proof with the shared symbolic
assumption solver, and rewrite with `Lean.MVarId.rewrite` and `Lean.MVarId.replaceTargetEq`; an
occurrence is skipped when no such proof is available. Occurrences are recomputed after each
rewrite, for at most `rewritingRounds` rounds, so that the output of one rewrite is processed
as well. The theorems are Mathlib's; ours is the choice of where and when they apply.

Some analytic identities must be applied before recursive simplification.
For example, simplifying inside `Real.exp (Real.log u)` can obscure the
positive-branch identity even when the local context proves `0 < u`, and
`Real.log (a / b)` only splits into `Real.log a - Real.log b` when both
arguments are known to be nonzero. The preparations of `prepareFinishers` run after the
simplification instead, so that the simplifier cannot consume the facts they add.
-/

public meta section

namespace CAS.Tactic.ConditionalRewrites

open Lean Elab Tactic Meta
open CAS.Elaboration.RealExpression (realNumeral)

/-- Collect, without duplicates, every subterm of `expression` recognized by `select`. -/
def collectSubterms {α : Type} (select : Expr → Option α) [BEq α]
    (expression : Expr) (found : Array α := #[]) : Array α :=
  let found :=
    match expression with
    | .app function argument =>
        collectSubterms select argument (collectSubterms select function found)
    | .lam _ type body _
    | .forallE _ type body _ =>
        collectSubterms select body (collectSubterms select type found)
    | .letE _ type value body _ =>
        collectSubterms select body
          (collectSubterms select value (collectSubterms select type found))
    | .proj _ _ body => collectSubterms select body found
    | .mdata _ body => collectSubterms select body found
    | _ => found
  match select expression.consumeMData with
  | some value => if found.contains value then found else found.push value
  | none => found

/-- The last explicit argument of an application of the constant `name`, if any. -/
def lastArgumentOf? (name : Name) (expression : Expr) : Option Expr :=
  let expression := expression.consumeMData
  if expression.getAppFn.consumeMData.isConstOf name then
    expression.getAppArgs.back?
  else
    none

/-- The argument `u` of an occurrence `Real.exp (Real.log u)`. -/
private def expLogArgument? (expression : Expr) : Option Expr := do
  let logApplication ← lastArgumentOf? ``Real.exp expression
  lastArgumentOf? ``Real.log logApplication

/-- The operands of an occurrence `Real.log (a / b)` or `Real.log (a * b)`, tagged by the
operation. -/
private def logArithmeticOperands? (expression : Expr) : Option (Name × Expr × Expr) := do
  let argument ← lastArgumentOf? ``Real.log expression
  let argument := argument.consumeMData
  let head := argument.getAppFn.consumeMData
  let arguments := argument.getAppArgs
  guard (arguments.size ≥ 2)
  let operation ←
    if head.isConstOf ``HDiv.hDiv then some ``Real.log_div
    else if head.isConstOf ``HMul.hMul then some ``Real.log_mul
    else none
  return (operation, arguments[arguments.size - 2]!, arguments[arguments.size - 1]!)

/-- Prove `proposition` by `symbolic_assumptions` from the local context, restoring the state
and returning `none` when it cannot. -/
def proveProposition? (proposition : Expr) : TacticM (Option Expr) := do
  let savedState ← saveState
  let goalsBefore ← getGoals
  try
    let proof ← mkFreshExprSyntheticOpaqueMVar proposition
    setGoals [proof.mvarId!]
    evalTactic (← `(tactic| symbolic_assumptions))
    let proof ← instantiateMVars proof
    unless (← getGoals).isEmpty && !proof.hasMVar do
      throwError "symbolic assumption solver left an unresolved branch condition"
    setGoals goalsBefore
    return some proof
  catch _ =>
    savedState.restore
    return none

private def expLogEqualityProof? (argument : Expr) : TacticM (Option Expr) := do
  let zero ←
    mkAppOptM ``OfNat.ofNat
      #[some (mkConst ``Real), some (mkNatLit 0), none]
  let positive ← mkLT zero argument
  if let some proof ← proveProposition? positive then
    return some (← mkAppM ``Real.exp_log #[proof])
  let nonzero ← mkAppM ``Ne #[argument, zero]
  if let some proof ← proveProposition? nonzero then
    return some (← mkAppM ``Real.exp_log_eq_abs #[proof])
  return none

private def logArithmeticEqualityProof? (occurrence : Name × Expr × Expr) :
    TacticM (Option Expr) := do
  let (operation, left, right) := occurrence
  let zero ←
    mkAppOptM ``OfNat.ofNat
      #[some (mkConst ``Real), some (mkNatLit 0), none]
  let some leftProof ← proveProposition? (← mkAppM ``Ne #[left, zero]) | return none
  let some rightProof ← proveProposition? (← mkAppM ``Ne #[right, zero]) | return none
  return some (← mkAppM operation #[leftProof, rightProof])

/-- Bound on the number of rewriting rounds of `rewriteOccurrences`; each round rewrites one
occurrence, and a round that rewrites nothing ends the loop. -/
def rewritingRounds : Nat := 64

/--
Rewrite every occurrence selected by `select` whose equality proof `prove` can construct.

Occurrences are recomputed after each rewrite, so occurrences created by a rewrite (such as
`Real.log (a * b)` produced by splitting `Real.log (1 / (a * b))`) are processed as well; the
loop stops when no occurrence can be rewritten or after `rewritingRounds` rounds.
-/
def rewriteOccurrences {α : Type} [BEq α] (select : Expr → Option α)
    (prove : α → TacticM (Option Expr)) : TacticM Unit := withMainContext do
  let maximumSteps := rewritingRounds
  let mut goal ← getMainGoal
  for _ in [:maximumSteps] do
    let target ← instantiateMVars (← goal.getType)
    let mut rewritten := false
    for occurrence in collectSubterms select target do
      if !rewritten then
        if let some equalityProof ← prove occurrence then
          try
            let result ← goal.rewrite target equalityProof
            unless result.mvarIds.isEmpty do
              throwError "conditional analytic rewrite produced auxiliary goals"
            goal ← goal.replaceTargetEq result.eNew result.eqProof
            replaceMainGoal [goal]
            rewritten := true
          catch _ =>
            pure ()
    unless rewritten do
      return

/--
Rewrite every occurrence of `Real.exp (Real.log u)` whose real logarithm
branch can be proved from the local context.

The positive branch uses `Real.exp_log`. A merely nonzero argument uses
`Real.exp_log_eq_abs`, preserving the absolute value required on the negative
branch. An occurrence is unchanged when neither condition can be proved.
-/
def rewriteExpLog : TacticM Unit :=
  rewriteOccurrences expLogArgument? expLogEqualityProof?

/--
Split every occurrence of `Real.log (a / b)` and `Real.log (a * b)` whose
operands are provably nonzero into `Real.log a - Real.log b` and
`Real.log a + Real.log b`.

Both nonzero facts are constructed by `symbolic_assumptions`, so positivity
hypotheses such as `0 < a` serve as well as `a ≠ 0`. An occurrence is unchanged
when either fact cannot be proved.
-/
def rewriteLogArithmetic : TacticM Unit :=
  rewriteOccurrences logArithmeticOperands? logArithmeticEqualityProof?

/-! ## Absolute values -/

/-- The equation `|u| = u` or `|u| = -u` for a real `u` whose sign the local context proves. -/
private def absEqualityProof? (argument : Expr) : TacticM (Option Expr) := do
  unless ← isDefEqGuarded (← inferType argument) (mkConst ``Real) do
    return none
  let zero ← realNumeral 0
  if let some proof ← proveProposition? (← mkLT zero argument) then
    return some (← mkAppM ``abs_of_pos #[proof])
  if let some proof ← proveProposition? (← mkLE zero argument) then
    return some (← mkAppM ``abs_of_nonneg #[proof])
  if let some proof ← proveProposition? (← mkLT argument zero) then
    return some (← mkAppM ``abs_of_neg #[proof])
  if let some proof ← proveProposition? (← mkLE argument zero) then
    return some (← mkAppM ``abs_of_nonpos #[proof])
  return none

/--
Distribute absolute values over products and quotients (`abs_mul`, `abs_div`), then replace
every real `|u|` by `u` or `-u` when `0 < u`, `0 ≤ u`, `u < 0`, or `u ≤ 0` is proved by
`symbolic_assumptions`. Occurrences whose sign is unknown are unchanged.
-/
def rewriteAbsoluteValues : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.getUsedConstants.contains ``abs do
    return
  evalTactic (← `(tactic| try simp only [abs_mul, abs_div, abs_neg, abs_abs]))
  -- The distribution step may already have closed a goal such as `|x| = |x|`.
  if (← getGoals).isEmpty then
    return
  rewriteOccurrences (lastArgumentOf? ``abs) absEqualityProof?

/-! ## Context preparation -/

/-- The factors of a nonvanishing product hypothesis `a * b ≠ 0`. -/
private def productNonvanishing? (type : Expr) : Option (Expr × Expr) := do
  let (_, lhs, rhs) ← type.consumeMData.ne?'
  guard rhs.zero?
  let lhs := lhs.consumeMData
  guard (lhs.isAppOfArity ``HMul.hMul 6)
  let arguments := lhs.getAppArgs
  return (arguments[4]!, arguments[5]!)

/-- Add the factor conditions of the pending nonvanishing product hypotheses, recursively. -/
private def splitProducts (goal : MVarId) : List Expr → Nat → MetaM MVarId
  | [], _ => pure goal
  | _, 0 => pure goal
  | hypothesis :: pending, fuel + 1 => goal.withContext do
      let type ← instantiateMVars (← inferType hypothesis)
      let some (left, right) := productNonvanishing? type
        | splitProducts goal pending fuel
      let split ←
        mkAppM ``Iff.mp
          #[← mkAppOptM ``mul_ne_zero_iff #[none, none, none, some left, some right], hypothesis]
      let leftProof ← mkAppM ``And.left #[split]
      let rightProof ← mkAppM ``And.right #[split]
      let (leftFVar, goal) ← goal.note (← mkFreshUserName `hcasFactor) leftProof
      let (rightFVar, goal) ← goal.note (← mkFreshUserName `hcasFactor) rightProof
      splitProducts goal (mkFVar leftFVar :: mkFVar rightFVar :: pending) fuel

/--
Split every hypothesis `h : a * b ≠ 0` (or `¬ a * b = 0`) into the factor conditions `a ≠ 0`
and `b ≠ 0` by `mul_ne_zero_iff`, recursively for nested products. The original hypothesis is
kept; the new ones let `field_simp` and `positivity` see each factor.
-/
def splitProductHypotheses : TacticM Unit := withMainContext do
  let mut pending : List Expr := []
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then
      continue
    if (productNonvanishing? (← instantiateMVars declaration.type)).isSome then
      pending := declaration.toExpr :: pending
  if pending.isEmpty then
    return
  let goal ← splitProducts (← getMainGoal) pending.reverse rewritingRounds
  replaceMainGoal [goal]

/--
For every square root `√u` occurring in the goal whose radicand is provably nonnegative, add
`√u ^ 2 = u` and `√u * √u = u` to the local context (`Real.sq_sqrt`, `Real.mul_self_sqrt`).
The nonnegativity is proved by `symbolic_assumptions`, so `0 < u` and `0 ≤ u` hypotheses serve
equally, and structurally nonnegative radicands need none. The identities are then available
to the arithmetic finishers that run after the target simplification of `Arithmetic.close`.
-/
def addSquareRootFacts : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.getUsedConstants.contains ``Real.sqrt do
    return
  let radicands := collectSubterms (lastArgumentOf? ``Real.sqrt) target
  let zero ← realNumeral 0
  let mut goal ← getMainGoal
  for radicand in radicands do
    if radicand.hasLooseBVars then
      continue
    let some nonneg ← proveProposition? (← mkLE zero radicand)
      | continue
    let (_, squared) ←
      goal.note (← mkFreshUserName `hcasSqrtSq) (← mkAppM ``Real.sq_sqrt #[nonneg])
    let (_, multiplied) ←
      squared.note (← mkFreshUserName `hcasSqrtMul) (← mkAppM ``Real.mul_self_sqrt #[nonneg])
    goal := multiplied
  replaceMainGoal [goal]

/-- A power `(a * b) ^ n` of a product with a symbolic natural exponent, as `(a, b, n)`. -/
private def symbolicProductPower? (expression : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let expression := expression.consumeMData
  unless expression.isAppOfArity ``HPow.hPow 6 do
    return none
  let arguments := expression.getAppArgs
  let exponent := arguments[5]!
  unless ← isDefEqGuarded (← inferType exponent) (mkConst ``Nat) do
    return none
  if (← getNatValue? exponent).isSome then
    return none
  let base := arguments[4]!.consumeMData
  unless base.isAppOfArity ``HMul.hMul 6 do
    return none
  let factors := base.getAppArgs
  return some (factors[4]!, factors[5]!, exponent)

/--
Distribute a symbolic natural power over a product, `(a * b) ^ n = a ^ n * b ^ n` (`mul_pow`).
`field_simp` clears such a denominator only once it is written factor by factor, so that each
factor's nonvanishing can be discharged separately. Numeral exponents are left alone; the
simplifier and `ring_nf` handle them.
-/
def distributePowers : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.getUsedConstants.contains ``HPow.hPow do
    return
  let mut goal ← getMainGoal
  for _ in [:rewritingRounds] do
    let target ← instantiateMVars (← goal.getType)
    let occurrences ← (collectSubterms (fun e ↦ some e) target).filterMapM fun e ↦ do
      if e.hasLooseBVars then return none
      return (← symbolicProductPower? e).map fun factors ↦ (e, factors)
    let some (_, left, right, exponent) := occurrences[0]?
      | break
    let equality ← mkAppM ``mul_pow #[left, right, exponent]
    let result ← goal.rewrite target equality
    unless result.mvarIds.isEmpty do
      break
    goal ← goal.replaceTargetEq result.eNew result.eqProof
  replaceMainGoal [goal]

/--
Prepare an ordinary goal for the arithmetic route before its simplification step: split
nonvanishing product hypotheses into their factors. Every step is a theorem application;
nothing is assumed.
-/
def prepareArithmetic : TacticM Unit := do
  splitProductHypotheses

/--
Prepare the simplified goal for the arithmetic finishers: evaluate absolute values of
sign-known arguments, distribute symbolic powers over products, and record the square-root
identities the context provides. These run after the target simplification of
`Arithmetic.close`, so that the simplifier sees the goal exactly as stated and cannot consume
the added identities first.
-/
def prepareFinishers : TacticM Unit := do
  rewriteAbsoluteValues
  if (← getGoals).isEmpty then
    return
  distributePowers
  if (← getGoals).isEmpty then
    return
  addSquareRootFacts

end CAS.Tactic.ConditionalRewrites

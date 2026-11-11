/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Differential.Tactic
public import CAS.ClosedForm.Scalar.Conditions

/-!
# The symbolic side-condition tactic

Every checked frontend of the computer algebra system (exact routes, differentiation, integration,
conditional rewrites, and the PDE bridge files) generates the same small family of analytic
obligations: nonvanishing denominators and logarithm arguments, positive square-root arguments, and
finite collections of such facts stated as `Verified.Expr.ValidAt`, `ValidityRequirements.Holds`, or
`Alg.SideHolds`. `symbolic_assumptions` is the single tactic that discharges them. On failure it
reports the atomic facts it could not prove and leaves the goal unchanged.

## Main definitions

* `Tactic.Assumptions.closeMainGoal`: the two phases below on the main goal, with an optional
  fallback for the atoms that resist the finishers.
* `symbolic_assumptions`: the tactic, `closeMainGoal` without a fallback.

## Implementation notes

We work in two phases.

1. *Reduction.* The checked requirement container is evaluated in the kernel-friendly way: the
   list or requirement collection is reduced with full transparency while the evaluation point
   stays opaque (`reduceSideHolds`, `reduceValidityRequirements`), `ValidAt` and
   `DiffExpr.AnalyticSideCondition` goals are first replaced by the requirement collections that
   imply them, and the explicit lists are then unfolded to a conjunction of atomic real facts with
   `simp only`. Binders are introduced, `Fin` indices are split, conjunctions are separated, and
   membership hypotheses introduced on the way are unfolded to their defining inequalities. No
   algebraic simplification is applied to the atoms, so a generated condition keeps the syntactic
   shape a user hint refers to.
2. *Finishing.* In each atom we first rewrite the coordinate projections of the standard
   evaluation points to real arithmetic, turn the literals of the checked evaluator into real
   numerals and write its squares as `a ^ 2` (`unfoldCoordinates`), and we specialize the
   pointwise domain families of the context at the membership facts already there. The atom is
   then closed by one of `assumption`, `positivity`, `norm_num`, or `nlinarith` (`positivity`
   and `nlinarith` are also tried in their `≠ 0` forms `apply ne_of_gt; positivity` and
   `intro hzero; nlinarith`, and a disequality hypothesis `a ≠ b` closes `a - b ≠ 0` in any
   linear arrangement through `intro hzero; apply_assumption <;> linarith` or
   `intro hzero; apply_assumption <;> nlinarith`). Mathlib's `bound` tactic
   is deliberately not among the finishers: importing `Mathlib.Tactic.Bound` reserves the token
   `bound`, which would break ordinary identifiers named `bound` in every file that imports the
   computer algebra tactics. Then `norm_num` normalises the atom once before most of the
   finishers are retried, commutative normalization matches reordered atomic facts, and a final
   `ring_nf` retry exposes polynomial squares and products to `positivity`. Atoms that resist
   are retried once more with the atoms already proved as additional hypotheses, since one
   requirement list often states a quantity both in the user's syntax and in the normalizer's
   expanded form.

Hypotheses may be stated as `0 < e` or as `e ≠ 0` interchangeably where the implication is valid:
`positivity` proves `e ≠ 0` from `0 < e`, and `0 < (x - a) ^ 2 + ε ^ 2` from `ε ≠ 0`. Evidence
supplied through a `using` clause is added to the local context by the calling frontend.

`Tactic.Assumptions.closeMainGoal` gives each atom that resists the finishers, also with the
proved atoms as hypotheses, to a fallback chosen by the caller. The integration frontend uses it
to prove that a denominator does not vanish on a bounded interval, by the box route of `cas`.

Every step is a tactic or a theorem application (the container reductions apply
`Verified.Expr.ValidityRequirements.holds_of_eq` and `Verified.Expr.Alg.sideHolds_of_eq` to a
definitional equation), so the kernel checks the whole proof and no assumption is ever inserted.
The finishers are Mathlib's; ours is the reduction of the requirement containers and the fixed
order in which the finishers run.
-/

-- `symbolic_assumptions` unfolds `HoldsAt` with `simp only`, which needs the equation lemma
-- `HoldsAt.eq_def`. Lean proves it on first use; naming it here proves it once, in this module,
-- instead of in every file that runs the tactic (about 90 ms there).
attribute [local simp] CAS.Scalar.DomainCondition.HoldsAt.eq_def

public meta section

namespace CAS

open Lean Elab Tactic Meta

namespace Tactic.Assumptions

/-- Run a tactic script on one goal and return the goals it leaves. -/
private def runOn (goal : MVarId) (tactic : TSyntax `tactic) : TacticM (List MVarId) :=
  evalTacticAt tactic goal

/-- Run a tactic script on one goal, returning the original goal if the script fails. -/
private def tryOn (goal : MVarId) (tactic : TSyntax `tactic) : TacticM (List MVarId) := do
  try
    runOn goal tactic
  catch _ =>
    return [goal]

/-- Close the goal from a hypothesis, up to definitional unfolding. -/
private def closeByAssumption (goal : MVarId) : TacticM Bool := do
  try
    goal.assumption
    return true
  catch _ =>
    return false

/-- Whether a type is `Fin n` for a numeral `n`, so that its inhabitants can be enumerated. -/
private def isFinLiteral (type : Expr) : MetaM Bool := do
  let type ← whnfR type
  let some bound := type.app1? ``Fin | return false
  return (← instantiateMVars bound).nat?.isSome || bound.isRawNatLit

/-- Unfold membership in the standard set constructors so that hypotheses introduced from a patch
expose their defining inequalities, then split up to `fuel` nested conjunctions. -/
private def normalizeHypothesis (fuel : Nat) (goal : MVarId) (name : Name) :
    TacticM (List MVarId) := do
  let ident := mkIdent name
  let goals ← tryOn goal (← `(tactic|
    simp only [Set.mem_ofPred_eq, Set.mem_Ioi, Set.mem_Iio, Set.mem_Ici, Set.mem_Iic,
      Set.mem_Ioo, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_inter_iff, Set.mem_univ,
      Set.mem_sdiff, Set.mem_compl_iff, Set.mem_singleton_iff,
      Scalar.DomainCondition.HoldsAt, Scalar.DomainCondition.ne, Scalar.DomainCondition.lt,
      Scalar.DomainCondition.le, Scalar.DomainCondition.gt, Scalar.DomainCondition.ge,
      Verified.Expr.eval, Verified.Expr.SymVar.expr] at $ident:ident))
  let [goal] := goals | return goals
  let isConjunction ← goal.withContext do
    let some declaration := (← getLCtx).findFromUserName? name | return false
    let type ← whnfR (← instantiateMVars declaration.type)
    return type.isAppOfArity ``And 2
  match fuel with
  | 0 => return [goal]
  | fuel + 1 =>
    unless isConjunction do
      return [goal]
    let left := name.appendAfter "Left"
    let right := name.appendAfter "Right"
    let goals ← tryOn goal
      (← `(tactic| obtain ⟨$(mkIdent left):ident, $(mkIdent right):ident⟩ := $ident:ident))
    let [goal] := goals | return goals
    let goals ← normalizeHypothesis fuel goal left
    return (← goals.mapM fun goal ↦ normalizeHypothesis fuel goal right).flatten

/-- The `simp only` set that turns an explicit requirement list into atomic real facts. -/
private def unfoldContainers : TacticM (TSyntax `tactic) :=
  `(tactic|
    simp only [Verified.Expr.ValidityRequirements.Holds, Verified.Expr.Alg.SideHolds,
      Scalar.DomainCondition.HoldsAt, Scalar.DomainCondition.ne, Scalar.DomainCondition.lt,
      Scalar.DomainCondition.le, Scalar.DomainCondition.gt, Scalar.DomainCondition.ge,
      List.forall_mem_cons, List.forall_mem_nil, List.not_mem_nil, false_implies,
      implies_true, and_true, true_and, Verified.Expr.eval, Verified.Expr.SymVar.expr,
      Real.sqrt_ne_zero', Real.sqrt_pos])

/-- Rewrite coordinate projections of the standard evaluation points, `x + t • single i 1` and
`ofLp (origin + t • direction)`, to ordinary real arithmetic, evaluate the integer and natural
literals of the checked evaluator to real numerals, and write squares produced by the normalizers
as `a ^ 2` so that `positivity` recognizes them. -/
private def unfoldCoordinates : TacticM (TSyntax `tactic) :=
  `(tactic|
    simp +decide only [EuclideanSpace.single, PiLp.single_apply, PiLp.add_apply, PiLp.sub_apply,
      PiLp.smul_apply, PiLp.neg_apply, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul,
      WithLp.ofLp_neg, WithLp.ofLp_toLp, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
      Pi.single_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      ↓reduceIte, Int.reduceNegSucc, Int.cast_neg, Int.cast_one, Int.cast_zero, Int.cast_ofNat,
      Int.cast_natCast, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat, mul_one, one_mul, mul_zero,
      zero_mul, add_zero, zero_add, ← sq])

/-- Whether a hypothesis type is a set membership, a domain condition, or a conjunction, so that
its defining inequalities should be exposed before the finishers run. -/
private def isStructuredHypothesis (type : Expr) : MetaM Bool := do
  let type ← whnfR type
  return type.isAppOfArity ``Membership.mem 5 || type.isAppOfArity ``And 2 ||
    type.isAppOfArity ``Scalar.DomainCondition.HoldsAt 3

/-- Revert the structured hypotheses of the context so that the binder pass reintroduces and
normalizes them. -/
private def revertStructuredHypotheses (goal : MVarId) : MetaM MVarId := goal.withContext do
  let mut structured : Array FVarId := #[]
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then
      continue
    unless ← isProp declaration.type do
      continue
    if ← isStructuredHypothesis declaration.type then
      structured := structured.push declaration.fvarId
  if structured.isEmpty then
    return goal
  let (_, goal) ← goal.revert structured (preserveOrder := true)
  return goal

/-- Number of container-unfolding steps allowed for one goal and, separately, the number of
nested conjunctions split in one hypothesis. -/
private def reductionFuel : Nat := 64

/-- Reduce one goal to atomic real facts, returning those facts as goals. Each recursive step
consumes one unit of `fuel`; a goal that is still structured when the fuel runs out is returned as
an atom. -/
private def expose (fuel : Nat) (goal : MVarId) : TacticM (List MVarId) := do
  match fuel with
  | 0 => return [goal]
  | fuel + 1 =>
    let expose := expose fuel
    if ← goal.isAssigned then
      return []
    if ← closeByAssumption goal then
      return []
    let target ← goal.withContext do
      pure (← instantiateMVars (← goal.getType)).consumeMData
    if target.isConstOf ``True then
      goal.assign (mkConst ``True.intro)
      return []
    if target.isAppOfArity ``And 2 then
      let goals ← runOn goal (← `(tactic| constructor))
      return (← goals.mapM expose).flatten
    if target.isForall then
      let binder := target.bindingName!
      let name ←
        if binder.isAnonymous || binder.hasMacroScopes then mkFreshUserName `hcas else pure binder
      let ident := mkIdent name
      let [goal] ← runOn goal (← `(tactic| intro $ident:ident))
        | throwError "symbolic_assumptions internal error: intro produced several goals"
      let (type, isProp) ← goal.withContext do
        let some declaration := (← getLCtx).findFromUserName? name
          | throwError "symbolic_assumptions internal error: introduced hypothesis vanished"
        pure (declaration.type, ← isProp declaration.type)
      if ← isFinLiteral type then
        let goals ← runOn goal (← `(tactic| fin_cases $ident:ident))
        let literals ← `(tactic| simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk])
        let goals ← goals.mapM fun goal ↦ tryOn goal literals
        return (← goals.flatten.mapM expose).flatten
      if isProp then
        let goals ← normalizeHypothesis reductionFuel goal name
        return (← goals.mapM expose).flatten
      return ← expose goal
    if target.isAppOfArity ``Verified.Expr.ValidAt 3 then
      return ← expose (← validAtToRequirements goal)
    if target.isAppOfArity ``DiffExpr.AnalyticSideCondition 5 then
      return ← expose (← analyticSideConditionToRequirements goal)
    let isHolds := target.isAppOfArity ``Verified.Expr.ValidityRequirements.Holds 3
    let isSideHolds := target.isAppOfArity ``Verified.Expr.Alg.SideHolds 3
    let isDomain := target.isAppOfArity ``Scalar.DomainCondition.HoldsAt 3
    if isHolds || isSideHolds || isDomain then
      let goal ←
        if isHolds then reduceValidityRequirements goal
        else if isSideHolds then reduceSideHolds goal
        else pure goal
      let goals ← tryOn goal (← unfoldContainers)
      match goals with
      | [remaining] =>
          if remaining == goal then
            -- The container did not compute to an explicit list; treat it as an atom.
            return [goal]
          return ← expose remaining
      | _ => return (← goals.mapM expose).flatten
    return [goal]

/-- The fixed finishing script for one atomic real fact. -/
private def finisher : TacticM (TSyntax `tactic) :=
  `(tactic|
    solve
      | assumption
      | positivity
      | (apply ne_of_gt; positivity)
      | norm_num
      | nlinarith
      | (intro hzero; nlinarith)
      | (intro hzero; apply_assumption <;> linarith)
      | (intro hzero; apply_assumption <;> nlinarith)
      | (norm_num <;> solve
          | assumption
          | positivity
          | nlinarith
          | (intro hzero; nlinarith)
          | (intro hzero; apply_assumption <;> linarith))
      | (simp only [mul_comm, add_comm] at *; assumption)
      | (ring_nf <;> solve
          | assumption
          | positivity
          | (apply ne_of_gt; positivity)
          | nlinarith
          | (intro hzero; nlinarith)))

/-- Specialize real pointwise domain families only at proved membership facts.
The bounds keep unrelated universal hypotheses out of unrestricted proof search. -/
private def specializeDomainFamilies (goal : MVarId) : TacticM MVarId := goal.withContext do
  let mut families : Array Expr := #[]
  let mut members : Array (Expr × Expr) := #[]
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      let type := declaration.type.consumeMData
      if type.isForall && type.bindingDomain!.isConstOf ``Real && families.size < 16 then
        let body := type.bindingBody!.consumeMData
        if body.isForall && body.bindingDomain!.isAppOfArity ``Membership.mem 5 then
          families := families.push (mkFVar declaration.fvarId)
      if type.isAppOfArity ``Membership.mem 5 && members.size < 32 then
        members := members.push (type.getAppArgs[4]!, mkFVar declaration.fvarId)
  let mut goal := goal
  for (point, member) in members do
    for family in families do
      let saved ← saveState
      try
        let application := mkApp family point
        let type ← whnfR (← inferType application)
        unless type.isForall do
          saved.restore
          continue
        unless ← isDefEq type.bindingDomain! (← inferType member) do
          saved.restore
          continue
        let proof := mkApp application member
        unless ← isProp (← inferType proof) do
          saved.restore
          continue
        let (_, next) ← goal.note (← mkFreshUserName `hcasDomain) proof
        goal := next
      catch error =>
        saved.restore
        if error.isRuntime then throw error
  return goal

/-- Normalize one atomic fact and try to close it. On success the normalized statement and its
proof are returned; on failure the normalized goal is. -/
private def finish (goal : MVarId) : TacticM (Except MVarId (Expr × Expr)) := do
  let goals ← tryOn goal (← unfoldCoordinates)
  let [goal] := goals | return .ok (← instantiateMVars (← goal.getType), .const ``True.intro [])
  let goal ← specializeDomainFamilies goal
  try
    let remaining ← runOn goal (← finisher)
    unless remaining.isEmpty do
      return .error goal
    return .ok (← instantiateMVars (← goal.getType), ← instantiateMVars (mkMVar goal))
  catch _ =>
    return .error goal

/-- Whether every free variable of `e` is available in the context of `goal`. -/
private def availableIn (goal : MVarId) (e : Expr) : MetaM Bool := goal.withContext do
  let context ← getLCtx
  return !(← instantiateMVars e).hasAnyFVar fun fvarId ↦ !context.contains fvarId

/--
Retry the unproved atoms with the atoms proved so far as additional hypotheses.

The requirement list of one checked route often states the same quantity twice, once in the
user's syntax and once in the normalizer's expanded form (for example the radicand of a square root
and the denominator it produces). The expanded form is beyond `positivity`, but `nlinarith` closes
it from the already proved unexpanded fact.
-/
private def finishWithProved (proved : Array (Expr × Expr)) (goal : MVarId) :
    TacticM (Option MVarId) := do
  let mut goal := goal
  for (type, proof) in proved do
    if ← availableIn goal type <&&> availableIn goal proof then
      let asserted ← goal.assert (← mkFreshUserName `hcasProved) type proof
      let (_, introduced) ← asserted.intro1P
      goal := introduced
  match ← finish goal with
  | .ok _ => return none
  | .error remaining => return some remaining

/--
Reduce the main goal to atomic real facts and close each of them as `symbolic_assumptions` does.
An atom that resists the finishers, also with the atoms already proved as hypotheses, is given to
`fallback?` when there is one, which must close it or throw; the state of a failed attempt is
restored. On failure the unproved atoms are reported.
-/
def closeMainGoal (fallback? : Option (MVarId → TacticM Unit)) : TacticM Unit := focus do
  let goal ← getMainGoal
  let atoms ← expose reductionFuel (← revertStructuredHypotheses goal)
  let mut unsolved : Array MVarId := #[]
  let mut proved : Array (Expr × Expr) := #[]
  for atom in atoms do
    match ← finish atom with
    | .ok fact => proved := proved.push fact
    | .error remaining => unsolved := unsolved.push remaining
  let mut stillUnsolved : Array MVarId := #[]
  for atom in ← unsolved.toList.filterMapM (finishWithProved proved) do
    match fallback? with
    | none => stillUnsolved := stillUnsolved.push atom
    | some fallback =>
        let saved ← saveState
        try
          fallback atom
          unless ← atom.isAssigned do
            throwError "symbolic_assumptions: the fallback left the fact open"
        catch error =>
          if error.isRuntime then throw error
          saved.restore
          stillUnsolved := stillUnsolved.push atom
  if stillUnsolved.isEmpty then
    replaceMainGoal []
  else
    let goals := MessageData.joinSep (stillUnsolved.toList.map MessageData.ofGoal) Format.line
    throwError
      "symbolic_assumptions could not prove the generated analytic condition from the \
       local context. Unproved facts:{indentD goals}"

end Tactic.Assumptions

/--
Close a checked analytic side condition from the local context.

Supported goals are `Verified.Expr.ValidAt`, `Verified.Expr.ValidityRequirements.Holds`,
`Verified.Expr.Alg.SideHolds`, `DiffExpr.AnalyticSideCondition`, `Scalar.DomainCondition.HoldsAt`,
their conjunctions and finite `Fin`-indexed or patch-indexed families, and the atomic real facts
they unfold to. The requirement containers are reduced in the kernel-friendly way and each atomic
fact is then closed by `assumption`, `positivity`, `norm_num`, or `nlinarith`; see the
module documentation for the exact contract. The tactic never inserts an assumption; on failure
it reports the unproved facts.
-/
syntax (name := symbolicAssumptions) "symbolic_assumptions" : tactic

elab_rules : tactic
  | `(tactic| symbolic_assumptions) => Tactic.Assumptions.closeMainGoal none

end CAS

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.Scalar.QuadraticDiscriminant
public import CAS.Tactic.ConditionalRewrites
public import CAS.Tactic.GlobalBounds
public import CAS.Tactic.NonvanishingDischarger
public import CAS.Tactic.RealExpression
public meta import CAS.Tactic.ProofCarrier
public import CAS.Polynomial.Sparse.MultivariateGcd -- shake: keep: the equation-hint route quotes `exactQuotientExpr?` for the kernel

/-!
# Arithmetic closure for symbolic tactics

The arithmetic phase of the `cas` tactic. `close` proves an equality, a disequality or an order
relation from the local context with Mathlib's arithmetic tactics, and `closeWithEquation`
proves an equality from an equation hint `cas using h`. Besides the arithmetic stage of `cas`,
`close` serves certificate inference, which uses it whenever a checked certificate leaves a
budget comparison to prove, the endpoint formulas of the integration tactic and the elementary
rewrites stage.

## Main definitions

* `closeAlgebraicEquality`: an equality by `assumption`, `rfl`, `ring1` or `ac_rfl`.
* `close`: the arithmetic phase on the main goal, optionally unfolding local definitions.
* `closeWithEquation`: an equality as a polynomial multiple of an equation hypothesis.

## Implementation notes

We first try cheap closers on the goal as stated. On an equality these are
`closeAlgebraicEquality`, which treats analytic subterms as atoms, and then the product,
quotient and exponent-addition identities `Real.sqrt_mul`, `Real.sqrt_div`, `Real.div_rpow` and
`Real.rpow_add`, whose sign conditions must follow by `assumption` or `positivity`. On an order
relation they are `linarith` and `CAS.Analysis.Scalar.mixed_energy_le_of_discriminant`, which
bounds `b * E * H` by `A * E ^ 2 + B * H ^ 2` when `0 ≤ A`, `0 ≤ B` and `b ^ 2 ≤ 4 * A * B`.
They come before any simplification, because simplification can rewrite only some powers of an
atom, or change the reciprocal form of a target such as `1 / x ^ 2 ≤ 1` that a hypothesis states
in the same shape. Then we apply the branch-checked rewrites of
`CAS/Tactic/ConditionalRewrites.lean` and simplify the target alone: the hypotheses that are
closed or share a variable with it serve as simp lemmas, `sinh`, `cosh` and `tanh` stay folded
on an order goal, and a closed hypothesis that `norm_num` refutes closes the goal. If
simplification fails or exhausts the recursion depth, we discard its partial changes. After
`ConditionalRewrites.prepareFinishers` and, on an order goal, the range facts of
`CAS/Tactic/GlobalBounds.lean`, the finisher (`norm_num`, `field_simp` with `cas_nonvanishing`,
`ring1`, `positivity`, `linarith` or `nlinarith`) is chosen from `Classify.arithmeticFeatures`.
Every step is a Mathlib tactic or a theorem application, so the kernel checks the whole proof
term; ours is the order of the steps and the choice of finisher.

For an equation hint `h : a = b`, `closeWithEquation` clears denominators in the goal and then
in `h` with `field_simp`. The multiplier `m` with `goal difference = m * (a - b)` is an exact
quotient in the sparse multivariate polynomial ring over the shared atoms: we reflect both
differences with `RealExpression.reifyOverAtoms`, the kernel evaluates
`Polynomial.Sparse.Multivariate.exactQuotientExpr?` (division by leading terms in graded
lexicographic order, `CAS/Polynomial/Sparse/MultivariateGcd.lean`) and
`KernelReadBack.readBackList` reads the quotient back. We trust nothing about it:
`linear_combination m * h` checks the multiplier with `ring1`, and `linarith` and `nlinarith`
remain the fallback when the division is not exact.
-/

public meta section

namespace CAS.Tactic.Arithmetic

open Lean Elab Tactic Meta
open CAS.Elaboration.RealExpression (realNumeral)

/-- Run a tactic, restoring the state and continuing when it fails, also when it exhausts the
recursion depth. Simplification can loop on an equation whose right-hand side contains its
left-hand side, both in the arithmetic preparation and in `field_simp`'s nonvanishing
discharger. A plain `try` does not catch that runtime exception. Heartbeat exhaustion is
propagated. -/
private def attemptTactic (tactic : TSyntax `tactic) : TacticM Unit := do
  let saved ← saveState
  tryCatchRuntimeEx (evalTactic tactic) fun error ↦ do
    saved.restore
    if error.isRuntime ∧ !error.isMaxRecDepth then
      throw error

/-- Expose the inequalities in a relevant conjunction, including interval membership.
This is propositional elimination; analytic expressions and quantified facts are untouched. -/
private partial def conjunctionFacts (proof : Expr) : MetaM (Array Expr) := do
  let type ← whnfD (← inferType proof)
  if type.isAppOfArity ``And 2 then
    return (← conjunctionFacts (← mkAppM ``And.left #[proof])) ++
      (← conjunctionFacts (← mkAppM ``And.right #[proof]))
  return #[proof]

/-- A closed numerical hypothesis may itself be contradictory, independently of the target.
`norm_num` supplies the proof; no hypotheses are rewritten or discarded. -/
private def closedContradiction? (proof type : Expr) : MetaM (Option Expr) := do
  let saved ← saveState
  try
    let result ← Mathlib.Meta.NormNum.eval type
    unless result.expr.isFalse do
      saved.restore
      return none
    return some (← mkEqMP (← result.getProof) proof)
  catch error =>
    saved.restore
    if error.isRuntime then throw error
    return none

private def simplify
    (preserveBoundedFunctions : Bool)
    (defs? : Option (Array (TSyntax ``Lean.Parser.Tactic.simpLemma))) :
    TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let targetVariables := (collectFVars {} target).fvarSet
  let mut facts : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  let mut goal ← getMainGoal
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let type ← instantiateMVars decl.type
      if !type.hasFVar && (← isProp type) then
        if let some contradiction ← closedContradiction? (mkFVar decl.fvarId) type then
          goal.assign (← mkFalseElim (← goal.getType) contradiction)
          replaceMainGoal []
          return
      if (← isProp type) &&
          (!type.hasFVar || (collectFVars {} type).fvarIds.any targetVariables.contains) then
        let fact ← Term.exprToSyntax (mkFVar decl.fvarId)
        facts := facts.push (← `(Lean.Parser.Tactic.simpLemma| $fact:term))
        for component in ← conjunctionFacts (mkFVar decl.fvarId) do
          unless component == mkFVar decl.fvarId do
            let (_, next) ← goal.note (← mkFreshUserName `hcasComponent) component
            goal := next
  replaceMainGoal [goal]
  let defs := defs?.getD #[] ++ facts
  -- Only the target is simplified. In particular, unrelated analytic hypotheses are
  -- never normalized just because an elementary calculation occurs in their context.
  if preserveBoundedFunctions then
    attemptTactic (← `(tactic|
      simp [Real.exp_log, Real.tan_eq_sin_div_cos, Real.sqrt_sq_eq_abs, $defs,*]))
  else
    attemptTactic (← `(tactic|
      simp [Real.exp_log, Real.tan_eq_sin_div_cos,
        Real.sinh_eq, Real.cosh_eq, Real.tanh_eq, Real.sqrt_sq_eq_abs,
        Real.exp_neg, $defs,*]))

private def closeEquality
    (features : Classify.ArithmeticFeatures) : TacticM Unit := do
  if !features.hasVariables then
    -- A closed goal may still contain transcendental constants such as `Real.pi`, whose
    -- cancellation `norm_num` does not know; the field route with `positivity` does.
    evalTactic (← `(tactic|
      first
        | (norm_num; done)
        | (field_simp (disch := (first | positivity | assumption | linarith)) <;>
           ring_nf <;>
           simp [Real.exp_neg]; done)))
  else if features.hasDivision then
    -- A hypothesis may use a different simp normal form (`a ≠ b` instead of `dist a b ≠ 0`).
    -- The discharger splits the denominator and recovers each atom's nonvanishing proof.
    evalTactic (← `(tactic|
      field_simp (disch := cas_nonvanishing) <;>
      ring_nf <;>
      simp [Real.exp_neg]))
  else if features.hasNonlinearSyntax then
    -- `ring` falls back to `ring_nf` and succeeds without closing the goal, which would hide
    -- the arithmetic finisher; `ring1` fails cleanly instead.
    evalTactic (← `(tactic| first | ring1 | nlinarith))
  else
    evalTactic (← `(tactic| first | ring1 | linarith))

private def closeOrder
    (features : Classify.ArithmeticFeatures) : TacticM Unit := do
  GlobalBounds.addTargetFacts
  if !features.hasVariables then
    evalTactic (← `(tactic| solve | norm_num | positivity | nlinarith | linarith))
  else if features.hasPositivitySyntax then
    evalTactic (← `(tactic| first | assumption | positivity | nlinarith))
  else if features.hasNonlinearSyntax then
    evalTactic (← `(tactic| nlinarith))
  else
    evalTactic (← `(tactic| linarith))

private def closeDisequality
    (features : Classify.ArithmeticFeatures) : TacticM Unit := do
  if !features.hasVariables then
    evalTactic (← `(tactic| norm_num [Rat.cast_def]))
  else
    try
      evalTactic (← `(tactic| positivity))
    catch _ => try
      evalTactic (← `(tactic| linarith))
    catch _ =>
        throwError
          "cas could not prove the remaining disequality from local hypotheses.\n\
           Add the required nonzero hypothesis and pass it to `cas`, for example \
           `cas using hx` when `hx : x ≠ 0`"

/--
Close an equality using hypotheses, definitional equality, ring operations, or commutativity.

Ring normalization precedes AC simplification so arithmetic proofs can keep expensive
functions as atoms. In particular, an integral can commute with another summand without
being evaluated.
Associativity and commutativity also apply in additive groups that are not rings.
The caller restores the proof state if none of these closing tactics applies.
-/
def closeAlgebraicEquality : TacticM Unit := focus do
  evalTactic (← `(tactic| first | assumption | rfl | ring1 | ac_rfl))

/-- Product, quotient, and exponent-addition identities with their actual sign conditions. -/
private def closeElementaryEquality : TacticM Unit := do
  let target ← withMainContext <| instantiateMVars (← getMainTarget)
  unless (target.find? fun e ↦
      e.isAppOf ``Real.sqrt || e.isAppOf ``Real.rpow ||
        (e.isAppOf ``HPow.hPow && e.getAppArgs[1]? == some (mkConst ``Real))).isSome do
    throwError "no elementary power identity"
  evalTactic (← `(tactic|
    simp (disch := (first | assumption | positivity)) only
      [Real.sqrt_mul, Real.sqrt_div, Real.div_rpow, ← Real.rpow_add, mul_div_cancel₀]))
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic|
      first
        | (ring_nf; norm_num; done)
        | (field_simp (disch := cas_nonvanishing); ring1)))

/-- Recognize a scalar mixed quadratic term and use the generic discriminant theorem. -/
private def closeQuadraticOrder : TacticM Unit := do
  evalTactic (← `(tactic|
    apply CAS.Analysis.Scalar.mixed_energy_le_of_discriminant <;>
      first
        | assumption
        | positivity
        | (field_simp (disch := cas_nonvanishing) <;> norm_num <;> nlinarith)))

/--
Close the current arithmetic goal, optionally after unfolding the supplied
local definitions.

This operation is shared by the arithmetic stage of `cas` and certificate-budget weakening.
-/
def close
    (defs? : Option (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := none) :
    TacticM Unit := focus do
  let initialKind ← withMainContext do
    Classify.goalKind <$> instantiateMVars (← getMainTarget)
  if initialKind == .equality then
    -- Regroup atoms before simplification can rewrite only some of their powers.
    match ← ProofCarrier.attemptClosingMainGoal "CAS algebraic equality"
        closeAlgebraicEquality with
    | .ok _ => return
    | .error _ => pure ()
    match ← ProofCarrier.attemptClosingMainGoal "CAS elementary identity"
        closeElementaryEquality with
    | .ok _ => return
    | .error _ => pure ()
  if initialKind == .order then
    -- Preserve the atoms shared with hypotheses, such as `1 / x ^ 2 ≤ 1`, before
    -- simplification changes the target's reciprocal or power normal form.
    match ← ProofCarrier.attemptClosingMainGoal "CAS linear arithmetic"
        (evalTactic (← `(tactic| linarith))) with
    | .ok _ => return
    | .error _ => pure ()
    match ← ProofCarrier.attemptClosingMainGoal "CAS quadratic discriminant"
        closeQuadraticOrder with
    | .ok _ => return
    | .error _ => pure ()
  ConditionalRewrites.rewriteExpLog
  ConditionalRewrites.rewriteLogArithmetic
  ConditionalRewrites.prepareArithmetic
  simplify (initialKind == .order) defs?
  if (← getGoals).isEmpty then
    return
  -- Prepare auxiliary identities after target simplification, so they are available
  -- in their original form to the arithmetic finishers.
  ConditionalRewrites.prepareFinishers
  if (← getGoals).isEmpty then
    return
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let features := Classify.arithmeticFeatures target
    match Classify.goalKind target with
    | .equality => closeEquality features
    | .disequality => closeDisequality features
    | .order => closeOrder features
    | _ =>
        if target.consumeMData.isConstOf ``False then
          throwError
            "checked simplification reduces the requested relation to `False`"
        else
          throwError
            "cas expected an equality or order relation after simplification"

/-! ## Equation hints with polynomial multipliers -/

/-- The real term of an integer literal. -/
private def realInteger (z : Int) : MetaM Expr :=
  if z < 0 then do mkAppM ``Neg.neg #[← realNumeral z.natAbs] else realNumeral z.toNat

/-- Render a polynomial read back from the kernel as an ordinary real term over the atom table:
literals become numerals, variables the atoms they stand for, and the ring operations their
Mathlib counterparts. Fails on any other node. -/
private def realPolynomialTerm (atoms : Array Expr) : Verified.Expr Nat → MetaM Expr
  | .nat n => realNumeral n
  | .int z => realInteger z
  | .rat num den => do mkAppM ``HDiv.hDiv #[← realInteger num, ← realNumeral den]
  | .var i => do
      let some atom := atoms[i]?
        | throwError "cas equation hint: the multiplier names an unknown atom"
      pure atom
  | .add a b => do
      mkAppM ``HAdd.hAdd #[← realPolynomialTerm atoms a, ← realPolynomialTerm atoms b]
  | .sub a b => do
      mkAppM ``HSub.hSub #[← realPolynomialTerm atoms a, ← realPolynomialTerm atoms b]
  | .mul a b => do
      mkAppM ``HMul.hMul #[← realPolynomialTerm atoms a, ← realPolynomialTerm atoms b]
  | .neg a => do mkAppM ``Neg.neg #[← realPolynomialTerm atoms a]
  | .pow a k => do mkAppM ``HPow.hPow #[← realPolynomialTerm atoms a, mkNatLit k]
  | _ => throwError "cas equation hint: the multiplier is not a polynomial"

/--
The multiplier `m` with `goalLhs - goalRhs = m * (hypLhs - hypRhs)` as an ordinary real term,
found by exact division in the sparse multivariate polynomial ring over the shared atoms of the
four terms (every maximal subterm that is not a ring operation is an atom); `none` when a
difference is not a polynomial in the atoms or the division is not exact. The division
(`Polynomial.Sparse.Multivariate.exactQuotientExpr?`) runs in the kernel and its result is read
back; nothing about it is trusted, since `linear_combination` certifies the multiplier with
`ring1`.
-/
private def polynomialMultiplier? (goalLhs goalRhs hypLhs hypRhs : Expr) :
    MetaM (Option Expr) := do
  try
    let goalDifference ← mkAppM ``HSub.hSub #[goalLhs, goalRhs]
    let hypothesisDifference ← mkAppM ``HSub.hSub #[hypLhs, hypRhs]
    let (quotations, atoms) ←
      RealExpression.reifyOverAtoms "cas" #[] #[goalDifference, hypothesisDifference]
    let atomIndex := mkApp (mkConst ``Fin) (toExpr atoms.size)
    let quotient ← mkAppM ``Polynomial.Sparse.Multivariate.exactQuotientExpr?
      #[quotations[0]!, quotations[1]!]
    let candidates ←
      KernelReadBack.readBackList atomIndex (← mkAppM ``Option.toList #[quotient])
    match candidates with
    | [multiplier] => some <$> realPolynomialTerm atoms multiplier
    | _ => return none
  catch _ =>
    return none

/--
Close an ordinary real equality from an equation hypothesis `equation : a = b`.

The goal is cleared of denominators with `field_simp` (nonvanishing facts are discharged by
`cas_nonvanishing` from the context), the hypothesis is added to the context and cleared of
denominators the same way, and the goal is then closed as a polynomial multiple of the
hypothesis: the multiplier is the exact quotient of the goal difference by the hypothesis
difference in the sparse multivariate polynomial ring over the atoms of both
(`polynomialMultiplier?`; a constant when a linear combination with coefficient `±1` would do),
and `linear_combination multiplier * equation` certifies it. When the division is not exact,
the goal is still tried as a linear consequence of the hypothesis and the context (`linarith`,
`nlinarith`); the route fails cleanly otherwise. The goal is simplified before the hypothesis is
introduced, so that the discharger's `simp_all` never meets the simplified hypothesis as a
rewrite rule whose right-hand side contains its left-hand side.
-/
def closeWithEquation (equation : TSyntax `term) : TacticM Unit := focus do
  attemptTactic (← `(tactic| field_simp (disch := cas_nonvanishing)))
  if (← getGoals).isEmpty then
    return
  let hypothesis := mkIdent (← mkFreshUserName `hcasEquation)
  evalTactic (← `(tactic| have $hypothesis:ident := $equation))
  attemptTactic (← `(tactic| field_simp (disch := cas_nonvanishing) at $hypothesis:ident))
  let goal ← getMainGoal
  let multiplier? ← goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let some (_, goalLhs, goalRhs) := target.consumeMData.eq? | return none
    let hypothesisType ← instantiateMVars (← (← getFVarId hypothesis).getDecl).type
    let some (_, hypLhs, hypRhs) := hypothesisType.consumeMData.eq? | return none
    polynomialMultiplier? goalLhs goalRhs hypLhs hypRhs
  if let some multiplier := multiplier? then
    let multiplierSyntax ← goal.withContext (Term.exprToSyntax multiplier)
    let combination ← `($multiplierSyntax * $hypothesis:ident)
    attemptTactic (← `(tactic| linear_combination $combination:term))
    if (← getGoals).isEmpty then
      return
  try
    evalTactic (← `(tactic|
      all_goals first | linarith [$hypothesis:ident] | nlinarith [$hypothesis:ident]))
  catch _ =>
    throwError
      "the goal does not follow from the equation hint: the difference of its sides is not an \
       exact polynomial multiple of the difference of the hypothesis, and the linear and \
       nonlinear arithmetic finishers failed"

end CAS.Tactic.Arithmetic

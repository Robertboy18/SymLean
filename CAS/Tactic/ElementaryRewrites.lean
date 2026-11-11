/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Tactic.AnalyticIdentities
public import CAS.Tactic.Arithmetic
public meta import CAS.Tactic.Arithmetic
public import CAS.Tactic.PolynomialEquations
public meta import CAS.Tactic.PolynomialEquations

/-!
# Elementary rewrites for bare `cas` on an identity

When the earlier routes of bare `cas` do not prove an ordinary real equality, `close` rewrites
three kinds of elementary subterms with Mathlib theorems and tries again:

* multiple angles and sums inside `sin` and `cos` (`expandAngles`): `sin (k * a)` and
  `cos (k * a)` for a numeral `k` use the double- and triple-angle formulas when `k` is `2` or
  `3`, and for `4 ≤ k ≤ maxMultiple` are peeled to `(k - 1) * a + a` and expanded by the
  addition formulas, as are `sin (a ± b)` and `cos (a ± b)`; larger multiples stay unexpanded;
* exponentials of multiples of logarithms (`rewriteExpLogMultiples`): `exp (k * log u)` becomes
  `u ^ k` for a natural numeral `k` under `0 < u` and `|u| ^ k` under `u ≠ 0`, and the real
  power `u ^ k` for any other `k` under `0 < u`;
* products of real powers with one base (`combineRealPowers`): `u ^ a * u ^ b` becomes
  `u ^ (a + b)` under `0 < u`, or under `0 ≤ u` and `a + b ≠ 0`, and the exponent is evaluated
  (`u ^ (1/2 + 1/2) = u`).

## Main definitions

* `applicable`: whether the goal has a sine, a cosine, an exponential together with a
  logarithm, or a real power.
* `close`: the three rewrites, then the arithmetic phase, then `grobner` modulo the circle
  equations.

## Implementation notes

Each rewrite applies a theorem whose hypothesis is proved from the local context by
`symbolic_assumptions`, or by `norm_num` for numeral facts; an occurrence whose hypothesis cannot
be proved is left alone. We peel a multiple angle with `AnalyticIdentities.sin_mul_of_eq_add_one`
or `AnalyticIdentities.cos_mul_of_eq_add_one`, after `norm_num` proves `k = (k - 1) + 1`, and we
stop at `maxMultiple` because each step beyond the triple-angle formulas doubles the expression.
The exponential rewrite runs only when the goal contains both `exp` and `log`: we first split
every `exp (a + b)` and `exp (a - b)` with `Real.exp_add` and `Real.exp_sub` and resolve
`exp (log u)` with `ConditionalRewrites.rewriteExpLog`. The stage runs only after the earlier
routes have failed, so that a goal they prove keeps their proof.

The rewritten goal goes to `Arithmetic.close`. When that fails and sines or cosines remain, we
prove the polynomial identity in them modulo `sin a ^ 2 + cos a ^ 2 = 1` for each remaining angle
`a`, by core `grobner` with the instances of `Real.sin_sq_add_cos_sq` as hypotheses
(`PolynomialEquations.attempt`). This is the right ideal: for one angle, or several independent
ones, a polynomial in the sines and cosines that vanishes at all real angles lies in the ideal of
the circle equations. Angles are related only through numeral multiples written `k * a`, so `x`
and `x / 2` count as independent angles.
-/

public meta section

namespace CAS.Tactic.ElementaryRewrites

open Lean Elab Tactic Meta
open CAS.Elaboration.RealExpression (realNumeral)

/-- Prove a closed numeral proposition with `norm_num`, or return `none`. -/
private def proveNumeral? (proposition : Expr) : TacticM (Option Expr) := do
  let saved ← saveState
  let goalsBefore ← getGoals
  try
    let proof ← mkFreshExprSyntheticOpaqueMVar proposition
    setGoals [proof.mvarId!]
    evalTactic (← `(tactic| norm_num))
    let proof ← instantiateMVars proof
    unless (← getGoals).isEmpty && !proof.hasMVar do
      throwError "norm_num left the numeral fact open"
    setGoals goalsBefore
    return some proof
  catch _ =>
    saved.restore
    return none

/-- The largest multiple `k` for which `sin (k * a)` and `cos (k * a)` are expanded. Beyond the
triple-angle formulas each step doubles the expression, so the bound keeps it small. -/
def maxMultiple : Nat := 8

/-- `sin (k * a)` or `cos (k * a)` with a numeral `2 ≤ k ≤ maxMultiple`, as
`(isSine, k, numeral, a)`. -/
private def multipleAngle? (expression : Expr) : Option (Bool × Nat × Expr × Expr) := do
  let expression := expression.consumeMData
  let isSine ←
    if expression.isAppOfArity ``Real.sin 1 then some true
    else if expression.isAppOfArity ``Real.cos 1 then some false
    else none
  let argument := expression.appArg!.consumeMData
  guard (argument.isAppOfArity ``HMul.hMul 6)
  let numeral := argument.getAppArgs[4]!
  let angle := argument.getAppArgs[5]!
  let k ← numeral.consumeMData.nat?
  guard (2 ≤ k && k ≤ maxMultiple)
  guard !angle.hasLooseBVars
  return (isSine, k, numeral, angle)

/-- For an occurrence found by `multipleAngle?`, the double- or triple-angle formula, or for
larger `k` the equation `sin (k * a) = sin ((k - 1) * a) * cos a + cos ((k - 1) * a) * sin a`
or its cosine form. -/
private def multipleAngleEquation? (occurrence : Bool × Nat × Expr × Expr) :
    TacticM (Option Expr) := do
  let (isSine, k, numeral, angle) := occurrence
  if k == 2 || k == 3 then
    let theoremName := match isSine, k with
      | true, 2 => ``Real.sin_two_mul
      | false, 2 => ``Real.cos_two_mul
      | true, _ => ``Real.sin_three_mul
      | false, _ => ``Real.cos_three_mul
    -- A formula whose numeral differs from the occurrence's does not rewrite, and the occurrence
    -- is then skipped by `rewriteOccurrences`.
    return some (← mkAppM theoremName #[angle])
  let previous ← mkNumeral (mkConst ``Real) (k - 1)
  let one ← mkNumeral (mkConst ``Real) 1
  let some step ← proveNumeral? (← mkEq numeral (← mkAppM ``HAdd.hAdd #[previous, one]))
    | return none
  let theoremName := if isSine then ``AnalyticIdentities.sin_mul_of_eq_add_one
    else ``AnalyticIdentities.cos_mul_of_eq_add_one
  return some (← mkAppM theoremName #[step, angle])

/-- Expand multiple angles and sums inside `sin` and `cos`. Returns whether the goal changed. -/
def expandAngles : TacticM Bool := withMainContext do
  let before ← instantiateMVars (← getMainTarget)
  unless before.getUsedConstants.any (· == ``Real.sin) ||
      before.getUsedConstants.any (· == ``Real.cos) do
    return false
  for _ in [:ConditionalRewrites.rewritingRounds] do
    let target ← instantiateMVars (← getMainTarget)
    ConditionalRewrites.rewriteOccurrences multipleAngle? multipleAngleEquation?
    evalTactic (← `(tactic| try simp only [Real.sin_add, Real.cos_add, Real.sin_sub,
      Real.cos_sub, Real.sin_neg, Real.cos_neg, one_mul]))
    if (← getGoals).isEmpty then
      return true
    if (← instantiateMVars (← getMainTarget)) == target then
      break
  return (← getGoals).isEmpty || (← instantiateMVars (← getMainTarget)) != before

/-- `exp (k * log u)` or `exp (log u * k)`, as `(logFirst, k, u)`. -/
private def expLogMultiple? (expression : Expr) : Option (Bool × Expr × Expr) := do
  let expression := expression.consumeMData
  guard (expression.isAppOfArity ``Real.exp 1)
  let argument := expression.appArg!.consumeMData
  guard (argument.isAppOfArity ``HMul.hMul 6)
  let left := argument.getAppArgs[4]!.consumeMData
  let right := argument.getAppArgs[5]!.consumeMData
  guard !argument.hasLooseBVars
  if right.isAppOfArity ``Real.log 1 then
    return (false, left, right.appArg!)
  if left.isAppOfArity ``Real.log 1 then
    return (true, right, left.appArg!)
  none

/-- The equation for an occurrence of `exp (k * log u)`, with the branch hypothesis proved from
the local context. -/
private def expLogEquation? (occurrence : Bool × Expr × Expr) : TacticM (Option Expr) := do
  let (logFirst, k, u) := occurrence
  let zero ← realNumeral 0
  let positive? ← ConditionalRewrites.proveProposition? (← mkLT zero u)
  if let some n := k.consumeMData.nat? then
    let cast ← mkAppOptM ``Nat.cast #[some (mkConst ``Real), none, some (mkNatLit n)]
    let some hk ← proveNumeral? (← mkEq k cast) | return none
    if let some hu := positive? then
      let theoremName := if logFirst then ``AnalyticIdentities.exp_log_mul_of_pos
        else ``AnalyticIdentities.exp_mul_log_of_pos
      return some (← mkAppM theoremName #[hk, hu])
    let some hu ← ConditionalRewrites.proveProposition? (← mkAppM ``Ne #[u, zero])
      | return none
    let theoremName := if logFirst then ``AnalyticIdentities.exp_log_mul_of_ne_zero
      else ``AnalyticIdentities.exp_mul_log_of_ne_zero
    return some (← mkAppM theoremName #[hk, hu])
  let some hu := positive? | return none
  if logFirst then
    return some (← mkEqSymm (← mkAppM ``Real.rpow_def_of_pos #[hu, k]))
  return some (← mkAppM ``AnalyticIdentities.exp_mul_log_eq_rpow #[k, hu])

/-- Rewrite exponentials of multiples of logarithms. Returns whether the goal changed. -/
def rewriteExpLogMultiples : TacticM Bool := withMainContext do
  let before ← instantiateMVars (← getMainTarget)
  unless before.getUsedConstants.any (· == ``Real.log) &&
      before.getUsedConstants.any (· == ``Real.exp) do
    return false
  evalTactic (← `(tactic| try simp only [Real.exp_add, Real.exp_sub]))
  if (← getGoals).isEmpty then
    return true
  ConditionalRewrites.rewriteExpLog
  ConditionalRewrites.rewriteOccurrences expLogMultiple? expLogEquation?
  return (← instantiateMVars (← getMainTarget)) != before

/-- Combine products of real powers with one base and evaluate numeral exponents. Returns whether
the goal changed. -/
def combineRealPowers : TacticM Bool := withMainContext do
  let before ← instantiateMVars (← getMainTarget)
  unless (before.find? fun e ↦ e.isAppOf ``HPow.hPow &&
      e.getAppArgs[1]? == some (mkConst ``Real)).isSome do
    return false
  evalTactic (← `(tactic|
    try simp (disch := (first | assumption | positivity | (norm_num; done) | symbolic_assumptions))
      only [← Real.rpow_add, ← Real.rpow_add']))
  if (← getGoals).isEmpty then
    return true
  evalTactic (← `(tactic|
    try norm_num only [Real.rpow_one, Real.rpow_zero, Real.rpow_natCast, Real.rpow_two]))
  if (← getGoals).isEmpty then
    return true
  return (← instantiateMVars (← getMainTarget)) != before

/-- The angles `a` of the sines and cosines in `expression`. -/
private def angles (expression : Expr) : Array Expr :=
  ConditionalRewrites.collectSubterms (fun e ↦
    if (e.isAppOfArity ``Real.sin 1 || e.isAppOfArity ``Real.cos 1) && !e.hasLooseBVars then
      some e.appArg!
    else none) expression

/-- Whether the goal has a subterm that one of the elementary rewrites addresses: a sine or
cosine, an exponential together with a logarithm, or a real power. -/
def applicable : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let constants := target.getUsedConstants
  return constants.contains ``Real.sin || constants.contains ``Real.cos ||
    (constants.contains ``Real.exp && constants.contains ``Real.log) ||
    (target.find? fun e ↦ e.isAppOf ``HPow.hPow &&
      e.getAppArgs[1]? == some (mkConst ``Real)).isSome

/-- Close the main goal, an ordinary real equality, after the elementary rewrites: the Mathlib
arithmetic script first, then, when sines or cosines remain, core `grobner` with
`sin a ^ 2 + cos a ^ 2 = 1` for each remaining angle. Fails, with the state unchanged, when no
rewrite applies or the rewritten goal is still not proved. -/
def close (defs? : Option (Array (TSyntax ``Lean.Parser.Tactic.simpLemma))) :
    TacticM Unit := focus do
  let angleChanged ← expandAngles
  if (← getGoals).isEmpty then return
  let expChanged ← rewriteExpLogMultiples
  if (← getGoals).isEmpty then return
  let powerChanged ← combineRealPowers
  if (← getGoals).isEmpty then return
  unless angleChanged || expChanged || powerChanged do
    throwError "no elementary rewrite applies"
  match ← ProofCarrier.attemptClosingMainGoal "CAS rewritten arithmetic"
      (Arithmetic.close defs?) with
  | .ok _ => return
  | .error arithmeticError =>
      let target ← withMainContext do instantiateMVars (← getMainTarget)
      let angles := angles target
      if angles.isEmpty then
        throw arithmeticError
      let circles ← withMainContext <| angles.mapM fun angle ↦ do
        Term.exprToSyntax (← mkAppM ``Real.sin_sq_add_cos_sq #[angle])
      match ← PolynomialEquations.attempt circles with
      | .ok _ => return
      | .error error =>
          throwError "after the elementary rewrites, neither the arithmetic script nor \
            polynomial reasoning modulo sin² + cos² = 1 proved the goal:\
            {indentD arithmeticError.toMessageData}\n{indentD error.toMessageData}"

end CAS.Tactic.ElementaryRewrites

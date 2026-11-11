/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Tactic.NormNum.Core

/-!
# General-purpose fallbacks of bare `cas`

When the routes of bare `cas` do not close a goal, it hands the goal to the general automation of
Lean and Mathlib before reporting failure: `norm_num` for a closed proposition of the kind
`.other` of `Classify.goalKind` (not an equality, a disequality, an order relation or a
certificate proposition), and core `grind`, which combines congruence closure, E-matching, linear
arithmetic and a commutative-ring solver. Both produce ordinary proof terms that the kernel checks.

## Main definitions

* `closeClosedByNormNum`, `closeByGrind`: the two fallbacks.
* `withHeartbeatBudget`, `attemptWithinBudget`: run a fallback under its own heartbeat budget,
  set by the option `cas.grindHeartbeats`.
* `hasSmallNumerals`: the bound on numerals under which the `norm_num` fallback runs.

## Implementation notes

The procedures are Lean's and Mathlib's; ours are the heartbeat budget and, for `norm_num`, the
bound on numerals. Each fallback runs under its own heartbeat budget (`withHeartbeatBudget`), so
that a hopeless goal costs a bounded amount of elaboration. The budget is real: the tactic form
`set_option maxHeartbeats n in tac` changes only the option, while Lean's heartbeat check reads the
limit fixed when the declaration began (`Lean.Core.Context.maxHeartbeats`), so it does not bound
`tac`. The budget bounds elaboration only, in heartbeats rather than wall time; the kernel checks
the finished declaration under `maxHeartbeats`, as for every proof.

`norm_num` runs only when every closed natural-number and integer subterm of the goal has a bound
of at most `10 ^ 12` computed from its literals, ring operations, numeral powers and casts
(`hasSmallNumerals`); any other such term blocks it. Some of its decision procedures, such as
trial division for `Nat.Prime`, run for a time that grows with the values without consuming
heartbeats, so the heartbeat budget alone would not bound them.
-/

public meta section

namespace CAS.Tactic.Fallback

open Lean Elab Tactic Meta

/-- Heartbeat budget of the `grind` and `norm_num` fallbacks of bare `cas`, in thousands as for
`maxHeartbeats`; `0` disables them. -/
register_option cas.grindHeartbeats : Nat := {
  defValue := 20000
  descr := "heartbeat budget (in thousands) of the grind and norm_num fallbacks of bare cas; \
    0 disables them"
}

/-- Run `action` with at most `budget` thousand heartbeats, counted from now, and never more
than the enclosing declaration has left. Exhausting this budget, checked when `action` returns or
fails, is reported as an ordinary error naming `description`, so that the caller can continue
with other routes. When the enclosing budget is exhausted, before or after `action`, its heartbeat
error propagates unchanged; there is no extra allowance. Any other failure of `action` propagates
unchanged. The error names `option`, the option that sets the budget. -/
def withHeartbeatBudget {α : Type} (description : String) (budget : Nat) (action : TacticM α)
    (option : Name := `cas.grindHeartbeats) : TacticM α := do
  -- Nothing is left to lend when the enclosing budget is already spent.
  checkSystem "cas fallback"
  let context ← readThe Core.Context
  let now ← IO.getNumHeartbeats
  let requested := max (budget * 1000) 1
  let used := now - context.initHeartbeats
  -- A limit of `0` would mean no limit at all, so an enclosing budget spent to the last
  -- heartbeat is reported as spent.
  if context.maxHeartbeats != 0 && used ≥ context.maxHeartbeats then
    Core.throwMaxHeartbeat `cas `maxHeartbeats context.maxHeartbeats
  let limit :=
    if context.maxHeartbeats == 0 then requested
    else min requested (context.maxHeartbeats - used)
  let result ← tryCatchRuntimeEx
    (withTheReader Core.Context
      (fun context ↦ { context with initHeartbeats := now, maxHeartbeats := limit }) do
        -- The local budget, still in force, is checked after `action` whether it returns or
        -- fails: work between two checks of `action` (an uninterruptible kernel reduction, for
        -- example) still counts against it.
        let result ← tryCatchRuntimeEx action fun error ↦ do
          checkSystem "cas fallback"
          throw error
        checkSystem "cas fallback"
        return result)
    fun error ↦ do
      -- The enclosing budget may be the one that ran out: its own check then raises its error,
      -- also before an ordinary failure goes back to the caller.
      checkSystem "cas fallback"
      if error.isMaxHeartbeat then
        throwError "{description} did not finish within its budget of {budget} thousand \
          heartbeats (option `{option}`)"
      throw error
  checkSystem "cas fallback"
  return result

private def budget : TacticM Nat := do
  let budget := cas.grindHeartbeats.get (← getOptions)
  if budget == 0 then
    throwError "the grind and norm_num fallbacks are disabled (`cas.grindHeartbeats` is 0)"
  return budget

/-- Run `attempt`, a validated route attempt, under the fallback budget. An exhausted budget
becomes an ordinary failure of the attempt; the state is restored by the attempt itself. -/
def attemptWithinBudget {α : Type} (description : String)
    (attempt : TacticM (Except Exception α)) : TacticM (Except Exception α) := do
  let saved ← saveState
  try
    withHeartbeatBudget description (← budget) attempt
  catch error =>
    if error.isRuntime then
      throw error
    saved.restore
    return .error error

/-- Close the main goal with core `grind`. -/
def closeByGrind : TacticM Unit := focus do
  evalTactic (← `(tactic| grind))

/-- The largest natural number or integer, in absolute value, for which the `norm_num` fallback
runs. `norm_num`'s decision procedures compute with the values directly, and some of them, such as
trial division for `Nat.Prime`, run for a time that grows with the value without consuming
heartbeats; up to `10 ^ 12` trial division up to the square root is cheap. -/
def maxNormNumNumeral : Nat := 1000000000000

/-- An upper bound, at most `maxNormNumNumeral`, on the absolute value of a natural-number or
integer term built from literals by `+`, `-`, `*`, `/`, `%`, numeral powers, negation, successor
and casts; `none` when the term has another form or the bound is larger. -/
partial def numeralBound? (term : Expr) : Option Nat := do
  let term := term.consumeMData
  let small (n : Nat) : Option Nat := if n ≤ maxNormNumNumeral then some n else none
  if let some n := term.rawNatLit? then return ← small n
  if term.isAppOfArity ``OfNat.ofNat 3 then
    return ← numeralBound? term.appFn!.appArg!
  let arguments := term.getAppArgs
  let binary := arguments.size == 6
  if binary && (term.isAppOf ``HAdd.hAdd || term.isAppOf ``HSub.hSub) then
    return ← small ((← numeralBound? arguments[4]!) + (← numeralBound? arguments[5]!))
  if binary && term.isAppOf ``HMul.hMul then
    return ← small ((← numeralBound? arguments[4]!) * (← numeralBound? arguments[5]!))
  -- `|a / b| ≤ |a|`, and a remainder is at most the larger of `|a|` and `|b|`; the divisor is
  -- bounded too, since `norm_num` evaluates it.
  if binary && term.isAppOf ``HDiv.hDiv then
    discard <| numeralBound? arguments[5]!
    return ← numeralBound? arguments[4]!
  if binary && term.isAppOf ``HMod.hMod then
    return ← small (max (← numeralBound? arguments[4]!) (← numeralBound? arguments[5]!))
  if binary && term.isAppOf ``HPow.hPow then
    let base ← numeralBound? arguments[4]!
    let exponent ← numeralBound? arguments[5]!
    -- `|b| ≤ 1` gives `|b ^ k| ≤ 1`, also for `0 ^ 0 = 1`.
    if base ≤ 1 then return 1
    if exponent > 64 then none
    return ← small (Nat.pow base exponent)
  if term.isAppOfArity ``Neg.neg 3 || term.isAppOfArity ``Nat.cast 3 ||
      term.isAppOfArity ``Int.cast 3 || term.isAppOfArity ``Int.ofNat 1 then
    return ← numeralBound? term.appArg!
  if term.isAppOfArity ``Nat.succ 1 then
    return ← small ((← numeralBound? term.appArg!) + 1)
  none

/-- Whether every closed natural-number or integer subterm of `expression` has a bound from
`numeralBound?`: the condition under which the `norm_num` fallback runs. -/
partial def hasSmallNumerals (expression : Expr) : MetaM Bool := do
  let expression := expression.consumeMData
  if !expression.hasLooseBVars && !expression.hasFVar && !expression.hasMVar then
    if let some type ← try some <$> (whnfR (← inferType expression)) catch _ => pure none then
      if type.isConstOf ``Nat || type.isConstOf ``Int then
        return (numeralBound? expression).isSome
  match expression with
  | .app function argument => return (← hasSmallNumerals function) && (← hasSmallNumerals argument)
  | .lam _ type body _ | .forallE _ type body _ =>
      return (← hasSmallNumerals type) && (← hasSmallNumerals body)
  | .letE _ type value body _ =>
      return (← hasSmallNumerals type) && (← hasSmallNumerals value) &&
        (← hasSmallNumerals body)
  | .proj _ _ body => hasSmallNumerals body
  | _ => return true

/-- Close the main goal, a proposition without local variables whose natural-number and integer
subterms are bounded by `maxNormNumNumeral` (`hasSmallNumerals`), with `norm_num`. -/
def closeClosedByNormNum : TacticM Unit := focus do
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  if target.hasFVar || target.hasMVar then
    throwError "norm_num fallback: the goal mentions local variables"
  unless ← withMainContext (hasSmallNumerals target) do
    throwError "norm_num fallback: the goal has a natural number or integer that is not \
      bounded by 10 ^ 12, for which norm_num's decision procedures can run without a bound"
  evalTactic (← `(tactic| norm_num))
  unless (← getGoals).isEmpty do
    throwError "norm_num did not close the goal"

end CAS.Tactic.Fallback

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Global analytic bounds for symbolic arithmetic

Unconditional Mathlib range theorems, such as `-1 ≤ sin x` and `sin x ≤ 1`,
made available to the arithmetic phase of `cas`. For every `sin`, `cos` and `tanh` subterm of
the goal, `addTargetFacts` adds the lower and upper bounds, the bound on the absolute value and
the bound on the square; the arithmetic route (`CAS/Tactic/Arithmetic.lean`) calls it before it
closes an order goal. The registry records only theorem names and function heads. Each fact
inserted into a proof state is an ordinary application of a Mathlib theorem; the registry itself
carries no evidence.
-/

public meta section

namespace CAS.Tactic.GlobalBounds

open Lean Elab Tactic Meta

private structure UnaryEntry where
  functionName : Name
  lowerTheorem : Name
  upperTheorem : Name
  absTheorem? : Option Name := none
  squareTheorem? : Option Name := none

private def unaryEntries : Array UnaryEntry := #[
  ⟨``Real.sin, ``Real.neg_one_le_sin, ``Real.sin_le_one,
    ``Real.abs_sin_le_one, ``Real.sin_sq_le_one⟩,
  ⟨``Real.cos, ``Real.neg_one_le_cos, ``Real.cos_le_one,
    ``Real.abs_cos_le_one, ``Real.cos_sq_le_one⟩,
  ⟨``Real.tanh, ``Real.neg_one_lt_tanh, ``Real.tanh_lt_one,
    ``Real.abs_tanh_lt_one, ``Real.tanh_sq_lt_one⟩
]

private def collectArguments
    (expression : Expr) (entry : UnaryEntry) (arguments : Array Expr := #[]) : Array Expr :=
  let stripped := expression.consumeMData
  let arguments :=
    if stripped.getAppFn.consumeMData.isConstOf entry.functionName then
      let applicationArguments := stripped.getAppArgs
      if applicationArguments.isEmpty then arguments
      else
        let argument := applicationArguments[applicationArguments.size - 1]!
        if arguments.contains argument then arguments else arguments.push argument
    else
      arguments
  match expression with
  | .app function argument =>
      collectArguments argument entry (collectArguments function entry arguments)
  | .lam _ type body _
  | .forallE _ type body _ =>
      collectArguments body entry (collectArguments type entry arguments)
  | .letE _ type value body _ =>
      collectArguments body entry
        (collectArguments value entry (collectArguments type entry arguments))
  | .proj _ _ body => collectArguments body entry arguments
  | .mdata _ body => collectArguments body entry arguments
  | _ => arguments

/-- Add unconditional global bounds for supported analytic subterms whose arguments are
well scoped in the current goal context. -/
def addTargetFacts : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let mut proofs : Array Expr := #[]
  for entry in unaryEntries do
    for argument in collectArguments target entry do
      -- A subterm of a lambda body may depend on a binder that is absent here.
      if argument.hasLooseBVars then
        continue
      proofs := proofs.push (← mkAppM entry.lowerTheorem #[argument])
      proofs := proofs.push (← mkAppM entry.upperTheorem #[argument])
      if let some theoremName := entry.absTheorem? then
        proofs := proofs.push (← mkAppM theoremName #[argument])
      if let some theoremName := entry.squareTheorem? then
        proofs := proofs.push (← mkAppM theoremName #[argument])
  let mut goal ← getMainGoal
  for proof in proofs do
    let name ← Lean.Core.mkFreshUserName `_casGlobalBound
    let (_, nextGoal) ← goal.note name proof
    goal := nextGoal
  replaceMainGoal [goal]

end CAS.Tactic.GlobalBounds

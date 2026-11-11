/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Tactic.KernelReadBack

/-!
# Kernel-friendly reduction of checked side-condition lists

The exact computer algebra system states its obligations as `Verified.Expr.Alg.SideHolds ρ side`,
where `side` is a list of checked expressions computed by a normalizer. Before those obligations
can be handed to ordinary real arithmetic, the list has to be evaluated to an explicit
`[d₁, …, dₖ]`. That evaluation is a step of `symbolic_assumptions`, the public side-condition
tactic, which calls `reduceSideHolds`, and `reduceValidityRequirements` for a requirement
collection; no tactic syntax is declared here.

## Implementation notes

The evaluation keeps the environment `ρ` opaque and evaluates only the list argument. A list of
checked expressions over a `Fin` index, or a requirement collection over one, is evaluated by the
kernel in one reduction (`CAS.Tactic.KernelReadBack`), and the equality of the original
argument with the explicit list is certified by `decide +kernel` before it is transported through
the caller's theorem (`Verified.Expr.Alg.sideHolds_of_eq`, or
`Verified.Expr.ValidityRequirements.holds_of_eq`); the elaborator never unfolds the normalizer
run that produced the list. Arguments of any other type are reduced with full transparency by
the elaborator: when the reduced list is definitionally equal to the original at the default
transparency the goal is `change`d, and otherwise the equality is transported with a
`rfl` proof that the kernel checks by evaluation.
-/

public meta section

namespace CAS.Tactic

open Lean Elab Tactic Meta

/-- Whether a quoted list of checked expressions is already explicit, so that no evaluation is
needed to read it. -/
private def isExplicitList : Expr → Bool
  | .app (.const ``List.nil _) _ => true
  | .app (.app (.app (.const ``List.cons _) _) head) tail =>
      KernelReadBack.isExplicitExpression head && isExplicitList tail
  | .mdata _ list => isExplicitList list
  | _ => false

/--
Evaluate a list of checked expressions, or a requirement collection, over a `Fin` index with the
kernel, returning the explicit value together with a kernel-certified proof that it equals the
argument. Returns `none` for other argument types, and for explicit lists, which need no
evaluation.
-/
private def kernelReducedArgument? (argument : Expr) : MetaM (Option (Expr × Expr)) := do
  let type ← whnfD (← inferType argument)
  if type.isAppOfArity ``List 1 then
    if isExplicitList argument then
      return none
    let some index ← try some <$> KernelReadBack.finIndexOfType type catch _ => pure none
      | return none
    let list ← KernelReadBack.readBackList index argument
    let reduced ← KernelReadBack.quoteNatList index list
    let equality ←
      KernelReadBack.decideByKernel "symbolic_assumptions" (← mkEq argument reduced)
    return some (reduced, equality)
  if type.isAppOfArity ``Verified.Expr.ValidityRequirements 1 then
    let index := type.appArg!
    unless (← KernelReadBack.finBound? index).isSome do
      return none
    let (nonzero, positive) ← KernelReadBack.readBackRequirements index argument
    let reduced ← mkAppM ``Verified.Expr.ValidityRequirements.mk
      #[← KernelReadBack.quoteNatList index nonzero, ← KernelReadBack.quoteNatList index positive]
    let equality ←
      KernelReadBack.decideByKernel "symbolic_assumptions" (← mkEq argument reduced)
    return some (reduced, equality)
  return none

/--
Replace argument `index` of the application `fn args` in the goal by its full-transparency
reduction.

The result is a goal for the reduced statement. If `change` cannot identify the two statements at
the default transparency, the equality of the original and reduced arguments is proved by
`Eq.refl` under full transparency and transported with `transport`, a theorem of the shape
`∀ {..}, original = reduced → P reduced → P original` whose explicit arguments are exactly the
equality proof and the reduced-statement proof.
-/
def reduceApplicationArgument (goal : MVarId) (fn : Name) (arity index : Nat)
    (transport : Name) (expected : String) : MetaM MVarId := goal.withContext do
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity fn arity do
    throwError "{expected}"
  let head := target.getAppFn.consumeMData
  let args := target.getAppArgs
  let argument := args[index]!
  if let some (reduced, equality) ← kernelReducedArgument? argument then
    let reducedTarget := mkAppN head (args.set! index reduced)
    let reducedProof ← mkFreshExprMVar reducedTarget
    goal.assign (← mkAppM transport #[equality, reducedProof])
    return reducedProof.mvarId!
  let reduced ← withTransparency .all <|
    reduce argument (skipTypes := false) (skipProofs := false)
  let reducedTarget := mkAppN head (args.set! index reduced)
  try
    goal.change reducedTarget
  catch _ =>
    let equality ← mkFreshExprMVar (← mkEq argument reduced)
    let reducedProof ← mkFreshExprMVar reducedTarget
    withTransparency .all do
      unless ← isDefEq argument reduced do
        throwError
          "the checked side-condition list did not reduce definitionally; \
           provide its proof explicitly"
      equality.mvarId!.assign (← mkEqRefl argument)
    goal.assign (← mkAppM transport #[equality, reducedProof])
    return reducedProof.mvarId!

/--
Evaluate the list in a goal `Verified.Expr.Alg.SideHolds ρ side` while keeping the environment
`ρ` opaque. The returned goal states the same obligation for the explicit list.
-/
def reduceSideHolds (goal : MVarId) : MetaM MVarId :=
  reduceApplicationArgument goal ``Verified.Expr.Alg.SideHolds 3 2
    ``Verified.Expr.Alg.sideHolds_of_eq "expected a SideHolds goal"

end CAS.Tactic

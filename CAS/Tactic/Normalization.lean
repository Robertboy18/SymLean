/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.Configured
public import CAS.Tactic.ProofCarrier
public meta import CAS.Tactic.KernelReadBack
import CAS.Tactic.KernelReadBack

/-!
# Symbolic normalization

The rewriting core behind `cas_nf`. It finds evaluated `Verified.Expr` terms
inside arbitrary propositions, computes their checked normal forms, and
rewrites them using the corresponding denotational equality theorem.
The normalizer changes only the symbolic syntax tree under `Verified.Expr.eval`.
It does not unfold the evaluator into an ordinary real expression.

## Main definitions

* `withNormalizer`: run a transformation with the reflected normalizer, then discharge the side
  conditions it generated.
* `normalizeAtLocation`: normalize every evaluated symbolic expression at a location.

## Implementation notes

Without evidence we run `Verified.Expr.simplifyPipeline` of
`CAS/ClosedForm/Pipeline/Configured.lean` through `Verified.Expr.Pipeline.runFixed`: the kernel
evaluates the run and `KernelReadBack.readBackQuotedPair` reads the normal form back. The
equation between the run and the read-back form is certified by `KernelReadBack.decideByKernel`
when it is closed, and by a kernel definitional-equality check and `rfl` when an abstract index
type keeps it open; `Verified.Expr.eval_eq_of_simplifyPipeline_runFixed_eq` carries it to the
evaluations. With evidence (`cas_nf using h`) the side-aware
`Verified.Expr.sideConditionPipeline` runs instead, and
`Verified.Expr.eval_eq_of_sideConditionPipeline_run_result` records each generated nonzero
obligation `Alg.SideHolds ρ nonzero` as a Lean goal, which `withNormalizer` closes by `exact h`
and checks for completeness and type correctness. Nothing read back is trusted: every rewrite is
a theorem of the pipeline applied to a computation the kernel has checked.
-/

public meta section

namespace CAS.Tactic.Normalization

open Lean Elab Tactic Meta
open Mathlib.Tactic

private def evalArguments? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e := e.consumeMData
  let args := e.getAppArgs
  let fn := e.getAppFn
  unless args.size >= 2 do
    return none
  let ρ := args[args.size - 2]!
  let expr := args[args.size - 1]!
  unless fn.isConstOf ``Verified.Expr.eval do
    return none
  return some (ρ, expr)

private def hasChanged (source normalized : Expr) : MetaM Bool := do
  if source.cleanupAnnotations == normalized.cleanupAnnotations then
    return false
  return !Lean.Kernel.isDefEqGuarded (← getEnv) (← getLCtx) source normalized

private def certifyResult (operation : String) (run result : Expr) : MetaM Expr := do
  let statement ← mkEq run result
  if statement.hasFVar then
    -- `decide +kernel` requires a closed proposition. An abstract index type stays
    -- in this equality even when all expression data reduce without comparing indices.
    unless Lean.Kernel.isDefEqGuarded (← getEnv) (← getLCtx) run result do
      throwError "{operation} could not certify the open computation by kernel reduction"
    return ← mkEqRefl result
  KernelReadBack.decideByKernel operation statement

private def normalizeWithoutSide (ρ expr : Expr) : MetaM (Option Simp.Result) := do
  let index := (← whnfD (← inferType expr)).appArg!
  let pipeline ← mkAppOptM ``Verified.Expr.simplifyPipeline #[some index, none]
  let run ← mkAppM ``Verified.Expr.Pipeline.runFixed #[pipeline, expr]
  let nil ← mkAppOptM ``List.nil #[some (← inferType expr)]
  let (normalizedExpr, _) ← KernelReadBack.readBackQuotedPair index run nil
  unless ← hasChanged expr normalizedExpr do
    return none
  let checked ← certifyResult "cas_nf" run normalizedExpr
  let result ← mkAppM ``Verified.Expr.eval #[ρ, normalizedExpr]
  let transport ← mkAppM ``Verified.Expr.eval_eq_of_simplifyPipeline_runFixed_eq
    #[ρ, expr, normalizedExpr]
  -- The kernel checks the computation equality; elaborating this final application
  -- must not unfold the normalizer again to compare the proof's type.
  return some { expr := result, proof? := some (mkApp transport checked) }

private def normalizeWithSide
    (sideGoals : IO.Ref (Array MVarId)) (ρ expr : Expr) : MetaM (Option Simp.Result) := do
  let index := (← whnfD (← inferType expr)).appArg!
  let pipeline ← mkAppOptM ``Verified.Expr.sideConditionPipeline #[some index, none]
  let run ← mkAppM ``Verified.Expr.SidePipeline.run #[pipeline, expr]
  let (normalizedExpr, nonzero) ← KernelReadBack.readBackQuotedPair index
    (← mkAppM ``Verified.Expr.Alg.NormResult.expr #[run])
    (← mkAppM ``Verified.Expr.Alg.NormResult.nonzero #[run])
  unless ← hasChanged expr normalizedExpr do
    return none
  let quoted ← mkAppM ``Verified.Expr.Alg.NormResult.mk #[normalizedExpr, nonzero]
  let checked ← certifyResult "cas_nf using" run quoted
  let sideType ← mkAppM ``Verified.Expr.Alg.SideHolds #[ρ, nonzero]
  let sideProof ← mkFreshExprSyntheticOpaqueMVar sideType
  let result ← mkAppM ``Verified.Expr.eval #[ρ, normalizedExpr]
  let transport ← mkAppM ``Verified.Expr.eval_eq_of_sideConditionPipeline_run_result
    #[ρ, expr, normalizedExpr, nonzero]
  sideGoals.modify (·.push sideProof.mvarId!)
  return some { expr := result, proof? := some (mkApp2 transport checked sideProof) }

private def normalizeEval
    (sideGoals? : Option (IO.Ref (Array MVarId))) (e : Expr) :
    MetaM (Option Simp.Result) := do
  let some (ρ, expr) ← evalArguments? e | return none
  match sideGoals? with
  | none => normalizeWithoutSide ρ expr
  | some sideGoals => normalizeWithSide sideGoals ρ expr

private def dischargeSideGoals
    (side : TSyntax `term) (sideGoals : Array MVarId) : TacticM Unit := do
  for sideGoal in sideGoals do
    unless ← sideGoal.isAssigned do
      let remaining ← evalTacticAt (← `(tactic| exact $side)) sideGoal
      unless remaining.isEmpty do
        throwError "cas_nf using did not discharge every generated side condition"
    let some assignment := (← getMCtx).getExprAssignmentCore? sideGoal
      | throwError "cas_nf using left a generated side condition unassigned"
    let assignment ← instantiateMVars assignment
    if assignment.hasMVar ∨ assignment.hasSorry then
      throwError "cas_nf using constructed incomplete side-condition evidence"
    ProofCarrier.rejectIncompleteDependencies "cas_nf using side-condition evidence" assignment
    unless ← isTypeCorrect assignment do
      throwError "cas_nf using constructed ill-typed side-condition evidence"
    let assignmentType ← instantiateMVars (← inferType assignment)
    ProofCarrier.rejectIncompleteDependencies "cas_nf using side-condition type" assignmentType

/-- Run a transformation with a reflected-expression normalizer, then discharge every
generated side condition. The callback retains the evaluator and its original index type.
It returns `none` for an unrecognized or unchanged term; computation failures propagate. -/
def withNormalizer {α : Type} (side? : Option (TSyntax `term))
    (action : (Expr → MetaM (Option Simp.Result)) → TacticM α) : TacticM α := do
  let sideGoals ← IO.mkRef #[]
  let sideGoals? := side?.map fun _ ↦ sideGoals
  let result ← action (normalizeEval sideGoals?)
  match side? with
  | none => pure ()
  | some side => dischargeSideGoals side (← sideGoals.get)
  return result

/--
Normalize every supported evaluated symbolic expression at `loc`.

When `side?` is present, the term is checked independently against each exact
nonzero obligation emitted by the side-aware simplification pipeline.
-/
def normalizeAtLocation
    (side? : Option (TSyntax `term)) (loc : Location) : TacticM Unit :=
  withNormalizer side? fun normalize ↦ do
    let atomState ← IO.mkRef {}
    let evaluate (e : Expr) : Mathlib.Tactic.AtomM Simp.Result := do
      let some result ← normalize e | failure
      return result
    let transform :=
      Mathlib.Tactic.AtomM.recurse atomState {} (wellBehavedDischarge := false) evaluate pure
    transformAtLocation (transform ·) "cas_nf" loc

end CAS.Tactic.Normalization

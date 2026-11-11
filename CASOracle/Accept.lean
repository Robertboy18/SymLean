/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import CAS.Command.Common
import CASOracle.Oracle

/-!
# The acceptance boundary of the oracle commands

Every command and tactic of `CASOracle` proves its theorems through `proveStatement` (or its
forms `tryProve` and `firstProved`), `closeGoal` and `withAuditedEvidence`, and nothing an oracle
says reaches the user in any other way. Proposals that cannot be checked (that a factor is
irreducible, that a solution list is complete, that a Gröbner basis is reduced) are shown under
"Oracle hints (not checked)".

## Implementation notes

A proof is accepted on these terms only:

* the proposition is built by the command from its own input and the oracle's proposal, never
  read off the proof (`proveStatement`);
* a proof with metavariables or `sorry` is refused;
* the proof must depend on no axiom outside `propext`, `Classical.choice` and `Quot.sound`
  (`audit`, an absolute check: unlike `ProofCarrier.withKernelOnlyAxioms` it allows no axiom
  that the inputs happen to use, so a natively checked `cega [fast]` certificate is refused too);
* the kernel checks it at once, as an auxiliary theorem added with kernel checking forced on
  (`CAS.Tactic.Explanation.kernelCheckedProof`, through the evidence report or `closeGoal`);
* a command's report is logged only after the auxiliary theorems it added pass the same axiom
  audit (`withAuditedEvidence`); otherwise its messages and declarations are discarded.
-/

namespace CASOracle.Accept

open Lean Elab Command Meta Term Tactic
open CAS CAS.Tactic CAS.Tactic.Explanation CAS.Command.InfoView

/-- Refuse a proof with metavariables or `sorry`, a constant the kernel has not accepted, or an
axiom outside the standard three. -/
def audit (description : String) (proposition proof : Lean.Expr) : MetaM Unit := do
  let proposition ← instantiateMVars proposition
  let proof ← instantiateMVars proof
  if proposition.hasMVar || proof.hasMVar then
    throwError "{description}: the proof is incomplete"
  if proposition.hasSorry || proof.hasSorry then
    throwError "{description}: the proof uses sorry"
  let (found, unknown) ← ProofCarrier.axiomAudit #[proposition, proof]
  unless unknown.isEmpty do
    throwError "{description}: the proof uses {unknown.toList}, which the kernel has not \
      accepted"
  unless found.isEmpty do
    let names := found.toList.map fun (axiomName, constant) ↦ s!"{axiomName} (through {constant})"
    throwError "{description}: the proof depends on {names}, outside propext, Classical.choice \
      and Quot.sound"

/-- Elaborate `statement` and its proof `proof`, both built by the command, and audit them. The
returned proposition is the elaborated `statement`, not the type of the proof. -/
def proveStatement (description : String) (statement proof : Term) :
    TermElabM (Lean.Expr × Lean.Expr) := do
  let saved ← saveState
  try
    let proposition ← elabType statement
    synthesizeSyntheticMVarsNoPostponing
    let proposition ← instantiateMVars proposition
    let value ← withoutErrToSorry <| elabTermEnsuringType proof proposition
    synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    audit description proposition value
    return (proposition, value)
  catch error =>
    saved.restore
    throw error

/-- `proveStatement`, with `none` for any failure. -/
def tryProve (description : String) (statement proof : Term) :
    TermElabM (Option (Lean.Expr × Lean.Expr)) := do
  try return some (← proveStatement description statement proof) catch _ => return none

/-- The first statement-proof pair that `tryProve` accepts. -/
def firstProved (description : String) (statement : Term) (proofs : List Term) :
    TermElabM (Option (Lean.Expr × Lean.Expr)) := do
  for proof in proofs do
    if let some result ← tryProve description statement proof then
      return some result
  return none

/-- The checked part of a report: each step is audited and checked by the kernel against the
proposition the command built. -/
def evidence (steps : Array (String × Lean.Expr × Lean.Expr)) : MetaM MessageData := do
  let mut unchecked := #[]
  for (label, proposition, proof) in steps do
    audit label proposition proof
    unchecked := unchecked.push { label, proposition, proof : UncheckedExplanationStep }
  CAS.Command.evidenceReportMessage unchecked

/-- The node of a report that holds what the oracle claimed and nothing checked. -/
def hintsNode (oracle : Oracle) (hints : Array MessageData) : MessageData :=
  computationNode s!"Oracle hints from {oracle.name} (not checked)" hints

/-- The new constants of the current module since `before`. -/
private def newConstants (before : NameSet) : CommandElabM (Array Name) := do
  return (← getEnv).constants.map₂.foldl (init := #[]) fun acc name _ ↦
    if before.contains name then acc else acc.push name

/-- Run a command `action` and keep its messages and declarations only if every theorem it
added depends on no axiom outside the standard three. -/
def withAuditedEvidence (description : String) (action : CommandElabM Unit) :
    CommandElabM Unit := do
  let env ← getEnv
  let messages := (← get).messages
  let before := env.constants.map₂.foldl (init := ({} : NameSet)) fun acc name _ ↦
    acc.insert name
  action
  let added ← newConstants before
  let (found, unknown) ← liftTermElabM <|
    ProofCarrier.axiomAudit (added.map fun name ↦ mkConst name)
  unless found.isEmpty && unknown.isEmpty do
    setEnv env
    modify fun state ↦ { state with messages }
    throwError "{description}: refused, the evidence depends on \
      {(found.map (·.1)).toList ++ unknown.toList}, outside propext, Classical.choice and \
      Quot.sound"

/-- Close the main goal with a proof built by `build` on a copy of it: the proof is audited,
checked by the kernel as an auxiliary theorem closed over the local context (local definitions
substituted), that theorem is audited in turn, and the goal is assigned to it applied to the
locals. On failure the goal is unchanged. -/
def closeGoal (description : String) (build : MVarId → TacticM Unit) : TacticM Unit :=
  ProofCarrier.tacticEntry description do
    discard <| ProofCarrier.runClosingMainGoal description do
      ProofCarrier.withKernelOnlyAxioms description do
        let goal ← Tactic.getMainGoal
        goal.withContext do
          let target ← instantiateMVars (← goal.getType)
          let copy ← mkFreshExprSyntheticOpaqueMVar target
          build copy.mvarId!
          let proof ← instantiateMVars copy
          audit description target proof
          let checked ← kernelCheckedProof description target proof
          -- The kernel checked the closure, in which the local definitions the proof reaches
          -- are substituted; audit that theorem too, so an axiom hidden in a local `let` is
          -- refused as well.
          audit description target checked
          goal.assign checked
          Tactic.replaceMainGoal []
        return ((), #[])

/-- Parse the oracle named in the syntax. -/
def oracleOf (stx : TSyntax `ident) : CoreM Oracle := do
  let some oracle := Oracle.ofName? stx.getId
    | throwErrorAt stx "unknown oracle {stx.getId}; use sympy, sage, pari, flint, maxima or \
        gappa"
  return oracle

end CASOracle.Accept

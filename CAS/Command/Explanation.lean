/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Tactic.Explanation
public meta import CAS.Tactic.Explanation

/-!
# InfoView rendering for checked tactic explanations

`render` prints an `ExplanationReport` as a compact InfoView tree, `Proof evidence`, with two
children: `Checked proof steps`, each step with its proposition, its validation and its theorem,
and `Planner metadata (not proof)`. Every section is collapsed by default so command reports can
show their primary result without flooding the panel. `renderSummary` is the one-line footer that
question-mark tactics print below their suggestion. Expressions remain
structured `MessageData.ofExpr` values, preserving hover information after
`addMessageContext` captures the current environment, metavariable context,
and local context.

## Main definitions

* `CAS.Command.Explanation.render`: the evidence tree of a report.
* `CAS.Command.Explanation.renderSummary`: the footer below the suggestion of a question-mark
  tactic, with the selected route.

## Implementation notes

The renderer cannot promote planner metadata to evidence: its checked branch
accepts only `CheckedExplanationStep` values produced by validation
(`CAS.Tactic.Explanation.UncheckedExplanationStep.validate`). Generated
proof terms remain in those validated values but are not printed: the
proposition and theorem attribution provide a stable, readable explanation.

Each evidence step records which check has already happened. Explicit proposed
evidence is checked by adding an auxiliary theorem to the kernel. A completed
tactic goal reuses the elaborator's proof-carrier check and awaits the enclosing
declaration's kernel check. Both reject incomplete evidence; the renderer keeps
their validation levels distinct.
-/

public meta section

namespace CAS.Command.Explanation

open Lean Meta
open CAS.Tactic.Explanation

private def checkedStepMessage (step : CheckedExplanationStep) : MessageData :=
  let validation : String :=
    match step.validation with
    | .kernel => "proof term checked by the kernel against this proposition"
    | .elaborator =>
        "completed proof checked by the elaborator; kernel check occurs when the declaration is accepted"
  let children := #[
    m!"Proposition: {MessageData.ofExpr (showPowerTypes step.proposition)}",
    m!"Validation: {validation}"
  ]
  let children :=
    match step.theoremName? with
    | some theoremName =>
        children.push <| m!"Theorem: {MessageData.ofConstName theoremName}"
    | none => children
  MessageData.trace
    {
      cls := `CAS.explanation.checkedStep
      collapsed := true
    }
    m!"{step.label}"
    children

private def plannerStepMessage (step : PlannerExplanationStep) : MessageData :=
  let children :=
    if step.detail.isEmpty then
      #[]
    else
      #[m!"{step.detail}"]
  MessageData.trace
    {
      cls := `CAS.explanation.plannerStep
      collapsed := true
    }
    m!"{step.label}: {step.status.label}"
    children

private def checkedEvidenceMessage
    (steps : Array CheckedExplanationStep) : MessageData :=
  MessageData.trace
    {
      cls := `CAS.explanation.checkedEvidence
      collapsed := true
    }
    m!"Checked proof steps"
    (steps.map checkedStepMessage)

private def plannerMetadataMessage
    (steps : Array PlannerExplanationStep) : MessageData :=
  MessageData.trace
    {
      cls := `CAS.explanation.plannerMetadata
      collapsed := true
    }
    m!"Planner metadata (not proof)"
    (steps.map plannerStepMessage)

/--
Render a validated explanation report with the current message context.

The result is suitable for an InfoView diagnostic, a `TryThis` footer, or
command output. Its two child traces always separate checked
evidence from planner metadata, and the entire report remains collapsed until
requested.
-/
def render (report : ExplanationReport) : MetaM MessageData := do
  let message :=
    MessageData.trace
      {
        cls := `CAS.explanation
        collapsed := true
      }
      m!"Proof evidence"
      #[
        checkedEvidenceMessage report.checkedEvidence,
        plannerMetadataMessage report.plannerMetadata
      ]
  addMessageContext message

/--
Render the compact footer used by question-mark tactics below their suggestion.

The tactic has already closed the original goal through the checked proof
carrier, and it suggests either the call that ran or a replacement that it ran
on the original goal and that closed it with a complete proof of it. This
summary names the selected route without printing the reflected propositions
stored in the full report.
-/
def renderSummary (report : ExplanationReport) : MetaM MessageData := do
  let selected := report.plannerMetadata.filter fun step ↦
    step.status = .selected
  let route :=
    if selected.isEmpty then
      ""
    else
      s!" Selected route: {", ".intercalate <| selected.toList.map (·.label)}."
  addMessageContext m!"Lean checked the suggested replacement against the original goal.{route}"

end CAS.Command.Explanation

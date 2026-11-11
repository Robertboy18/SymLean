/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public meta import Lean.Elab.Command
public import Lean.Message
public meta import CAS.Command.Syntax

/-!
# Shared InfoView reports for symbolic commands

The `#cas` modes print their reports with `logReport`, directly or through the handler they
call, so every report has the same compact form. The command as typed, up to the bracket that
closes its mode (`commandHeader?`), the real domain, input and output types, and primary result
remain visible, while computation traces and proof evidence live under one collapsed
`More details` node (`reportMessage`). A command may also expose further results read off the
primary one and the side conditions under which its analytic theorem applies.

## Main definitions

* `CAS.Command.InfoView.ReportSummary`: the visible part of a report, as strings.
* `CAS.Command.InfoView.commandHeader?`: the heading, the command as typed up to its mode bracket.
* `CAS.Command.InfoView.reportMessage`: the message of a report, with its details collapsed.
* `CAS.Command.InfoView.logReport`: log a report at a syntax node.
* `CAS.Command.InfoView.computationNode`: a collapsed node of the details.

## Implementation notes

Inside the language server, reports are silent information diagnostics. Lean
still serves them to the InfoView, but supporting editor clients do not draw
diagnostic squiggles or add them to the Problems panel. Command-line
elaboration keeps ordinary information diagnostics so report regressions and
terminal inspection remain available. A report checks nothing itself: the strings of
`ReportSummary` come from the caller's checked result, and proof evidence is validated before it
is rendered for the details (`CAS.Command.evidenceReportMessage`,
`CAS.Command.Explanation.render`).
-/

public meta section

namespace CAS.Command.InfoView

open Lean Elab Command

/--
The compact, user-facing part of a symbolic command report.

Rendered types and domains have separate string fields. The caller must derive
them from its checked result; this presentation record does not itself validate
that the strings describe the certificate's scalar field or domain.
-/
structure ReportSummary where
  /-- The scalar domain in which the command result is certified. -/
  domain : String
  /-- The rendered input expression. -/
  input : String
  /-- The displayed type of the input expression. -/
  inputType : String
  /-- The rendered primary result. -/
  output : String
  /-- The displayed type of the primary result. -/
  outputType : String
  /-- Further results read off the primary one, each shown as `label: value` below it. -/
  furtherResults : Array (String × String) := #[]
  /-- Optional side conditions under which the reported theorem applies. -/
  conditions? : Option String := none

/-- A collapsible node in the detailed symbolic computation tree. -/
def computationNode (label : String) (children : Array MessageData) : MessageData :=
  .trace
    {
      cls := `CAS.Command.computation
      collapsed := true
    }
    m!"{label}"
    children

private def moreDetailsNode (children : Array MessageData) : MessageData :=
  .trace
    {
      cls := `CAS.Command.details
      collapsed := true
    }
    m!"More details"
    children

/--
The command `stx` as typed, from `#cas` to the bracket that closes its mode, on one line, such as
`#cas (prec := 40) [enclose x in [0, 1]]`; `none` when `stx` is not a `#cas` command.
-/
def commandHeader? (stx : Syntax) : Option String := Id.run do
  let args := stx.getArgs
  unless args[0]?.any (·.isToken "#cas") do return none
  let mut depth := 0
  for h : i in [0:args.size] do
    if args[i].isToken "[" then
      depth := depth + 1
    else if args[i].isToken "]" then
      depth := depth - 1
      if depth = 0 then
        let text := CAS.Command.surfaceText (mkNullNode (args.extract 0 (i + 1)))
        return some <| " ".intercalate <|
          ((text.splitOn "\n").map (·.trimAscii.toString)).filter (!·.isEmpty)
  return none

/--
Render the stable summary shared by exact and numerical `#cas` modes under the heading `header`.

Only the domain, typed input and output, the further results and any necessary side conditions
are expanded by default. Derivations, certificates, and planner diagnostics belong
in `details`.
-/
def reportMessage (header : String) (summary : ReportSummary) (details : Array MessageData) :
    MessageData :=
  let primary :=
    m!"{header}\nDomain: {summary.domain}\n\
      Input ({summary.inputType}): {summary.input}\n\
      Output ({summary.outputType}): {summary.output}"
  let primary := summary.furtherResults.foldl
    (fun primary (label, value) ↦ m!"{primary}\n{label}: {value}") primary
  let primary :=
    match summary.conditions? with
    | some conditions => m!"{primary}\nConditions: {conditions}"
    | none => primary
  let details := moreDetailsNode details
  m!"{primary}\n\n{details}"

/--
Log a `#cas` report at `ref` without decorating its source expression as a diagnostic. Its heading
is the running command as typed (`commandHeader?`).

Language-server reports remain queryable by the Lean InfoView while avoiding
the blue underline used for ordinary information diagnostics. Command-line
reports are ordinary information diagnostics, because terminals have no source
decorations and their output supports end-to-end regression checks.
-/
def logReport (ref : Syntax) (summary : ReportSummary)
    (details : Array MessageData) : CommandElabM Unit := do
  let isSilent := Elab.inServer.get (← getOptions)
  let command ← getRef
  let header := (commandHeader? command).getD (CAS.Command.surfaceText command)
  logAt ref (reportMessage header summary details)
    (severity := .information) (isSilent := isSilent)

end CAS.Command.InfoView

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.CEGA
public import CAS.Command.Explanation
public import CAS.IntegrationTactic
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
meta import CAS.CEGA

/-!
# Optional `cas?` and `cega?` tactic reports

`cas?` takes the arguments of `cas` (the syntax category `casArgs`) and `cega?` those of `cega`
(the category `cegaArgs`), so every form of either tactic has a reporting twin, including the
forms that other modules add. Despite the question mark, these are theorem tactics rather than
calculator commands: on success they close the current goal, suggest the non-reporting call to
keep in the proof, and attach an InfoView explanation. The option `cas.verbose` shows the
complete evidence tree. Importing `CAS.ExactTactic` alone does not load these reports.

## Implementation notes

`cas?` runs the plain call of `cas` and reports the route that closed the goal, as the route
records it (`ExactTactic.runRecordingRoute`). `cega?` runs the plain call of `cega`, except that
bare `cega?` does not try the last route of bare `cega`, the closed decidable kernel certificate.
When `cas?` or bare `cega?` closes an ordinary inequality through the CEGA box route, the
suggestion is the explicit `cega [enclose ...]` call that runs the same query, since that call
records the box the proof depends on; an integral whose primitive the planner found suggests the
`cas [integrate primitive := F]` call that checks it, and every route registered with
`@[cas_route]` returns the call it suggests.

We offer such a call only after running it. `checkedSuggestion` runs the candidate on the
original goal with error recovery disabled and keeps it only if it closes that goal, and no
other, with a complete proof; otherwise the suggestion is the plain call, the one that ran. When
a route refuses, its message names the query it ran or the shape it wanted. Additional evidence
claims are checked independently. The proof of the goal is the one the non-reporting tactic
built, which has already been checked to be complete, type-correct, and equal to the goal. Route
selection and planner details are labeled as metadata, not proof.
-/

public meta section

namespace CAS

open Lean Elab Tactic Meta
open Lean.Parser.Term
open CEGA.Elaboration

/-! ## Report construction -/

private def runReportedQueryWithValue {α : Type}
    (action : TacticM α)
    (plannerMetadata : α → Array Tactic.Explanation.PlannerExplanationStep)
    (additionalEvidence :
      α → MetaM (Array Tactic.Explanation.UncheckedExplanationStep) :=
        fun _ ↦ pure #[])
    (finalAttribution : α → Option Name := fun _ ↦ none) :
    TacticM (Tactic.Explanation.ExplanationReport × α) :=
  Tactic.ProofCarrier.preservingStateOnFailure do
    -- A determinant certificate is deeper than the default recursion limit; its validation here
    -- needs the limit the determinant evaluation raises for itself.
    let target ← withMainContext do instantiateMVars (← getMainTarget)
    let depth := if Tactic.Determinant.hasLiteralDeterminant target then
      Tactic.Determinant.recursionDepth else 0
    let closed ← withAtLeastMaxRecDepth depth <|
      Tactic.ProofCarrier.runClosingMainGoal "query tactic" action
    -- Additional evidence is checked independently because each displayed
    -- proposition is a separate public claim.
    let checkedEvidence ← closed.goal.withContext do
      Tactic.Explanation.validateAll (← additionalEvidence closed.value)
    let finalStep ← closed.goal.withContext do
      Tactic.Explanation.CheckedExplanationStep.ofClosedMainGoal
        "final proof assigned to the original goal" closed
        (finalAttribution closed.value)
    return ({
      checkedEvidence := checkedEvidence.push finalStep
      plannerMetadata := plannerMetadata closed.value
    }, closed.value)

private def runReportedQuery {α : Type}
    (action : TacticM α)
    (plannerMetadata : α → Array Tactic.Explanation.PlannerExplanationStep)
    (additionalEvidence :
      α → MetaM (Array Tactic.Explanation.UncheckedExplanationStep) :=
        fun _ ↦ pure #[])
    (finalAttribution : α → Option Name := fun _ ↦ none) :
    TacticM Tactic.Explanation.ExplanationReport :=
  Prod.fst <$>
    runReportedQueryWithValue action plannerMetadata additionalEvidence finalAttribution

/-- The replay and explanation a route of `cas` returned with its proof, if it returned one. A
pointwise route's result belongs to the pointwise goal, not to the original one. -/
private def routeResult? : ExactTactic.SelectedRoute → Option Tactic.RouteRegistry.Result
  | .integral result | .command result | .registered _ result => some result
  | _ => none

/-- The call of `cas` to keep in the proof: the explicit `cega [enclose ...]` query of the box
route, the replay a route returned, or else `plain`, the call that ran. -/
private def casSuggestion (route? : Option ExactTactic.SelectedRoute)
    (plain : TSyntax `tactic) : TSyntax `tactic :=
  match route? with
  | some (.boxInequality query) => query
  | some route => (routeResult? route).elim plain (·.replay)
  | none => plain

/-- The tactic to keep in the proof after a bare `cega` route. -/
private def cegaSuggestion (route : CEGA.BareRoute) : TacticM (TSyntax `tactic) := do
  match route with
  | .boxInequality query => pure query
  | .integral replay => pure replay
  | .certificateGoal replay => pure replay
  | .inclusion query => pure query
  | .carrier _ => `(tactic| cega)

private def casPlannerMetadata
    (route? : Option ExactTactic.SelectedRoute) :
    Array Tactic.Explanation.PlannerExplanationStep :=
  match route? with
  | none => #[]
  | some route =>
      #[{ label := s!"CAS route: {route.label}", status := .selected }] ++
        ((routeResult? route).map (·.plannerMetadata)).getD #[]

private def casEvidence (route? : Option ExactTactic.SelectedRoute) :
    MetaM (Array Tactic.Explanation.UncheckedExplanationStep) :=
  pure <| ((route?.bind routeResult?).map (·.evidence)).getD #[]

private def casFinalAttribution (route? : Option ExactTactic.SelectedRoute) : Option Name :=
  (route?.bind routeResult?).bind (·.finalAttribution?)

private def cegaPlannerMetadata
    (route : Tactic.CEGA.SelectedRoute) :
    Array Tactic.Explanation.PlannerExplanationStep :=
  #[{
    label := s!"CEGA route: {route.label}"
    status := .selected
  }]

private def bareCegaPlannerMetadata
    (route : CEGA.BareRoute) :
    Array Tactic.Explanation.PlannerExplanationStep :=
  #[{
    label := s!"CEGA route: {route.label}"
    status := .selected
  }]

/-- The projection of the certificate that a query in `mode` proves. -/
private def projectionLabel : BoxQueryMode → String
  | .enclose => "enclosure"
  | .bound => "upper bound"
  | .absBound => "absolute bound"
  | .approx => "midpoint approximation"

private def queryPlannerMetadata (query : BoxQueryMode × EnclosureMethod) :
    Array Tactic.Explanation.PlannerExplanationStep :=
  let refinement := match query.2 with
    | .plain => ""
    | .subdivided => " after checked box refinement"
  #[{
    label := s!"CEGA box query: {projectionLabel query.1}{refinement}"
    status := .selected
  }]

/-- The suggestion of a reporting tactic whose plain call `plain` closed the goal: `candidate`
when it is `plain`, or when, run on the goal of `original` (the state before the plain call ran),
it closes that goal and no other with a complete proof whose type is the goal
(`ProofCarrier.runClosingMainGoal`) and logs no error; otherwise `plain`, which has just been
checked. The run has error recovery disabled, and its effects, messages, traces and info trees are
discarded. Under `trace.cas.validation` the outcome is traced; heartbeat exhaustion propagates,
since it is the budget of the whole declaration. -/
private def checkedSuggestion (original : Tactic.SavedState) (plain candidate : TSyntax `tactic) :
    TacticM (TSyntax `tactic) := do
  if candidate.raw == plain.raw then
    return plain
  let after ← saveState
  let traces ← getTraceState
  original.restore
  Core.resetMessageLog
  let firstError? : TacticM (Option MessageData) := do
    return ((← Core.getMessageLog).toList.find? (·.severity == .error)).map (·.data)
  let failure? ← tryCatchRuntimeEx
    (do
      discard <| withoutRecover <|
        Tactic.ProofCarrier.runClosingMainGoal "the suggested replacement" (evalTactic candidate)
      firstError?)
    fun error ↦ do
      if error.isMaxHeartbeat then
        throw error
      return some ((← firstError?).getD error.toMessageData)
  after.restore (restoreInfo := true)
  setTraceState traces
  let some failure := failure? | do
    trace[cas.validation] "The suggested replacement{indentD candidate}\nclosed the original goal"
    return candidate
  trace[cas.validation] "The suggested replacement{indentD candidate}\nfailed on the original \
    goal, so the suggestion is the call that ran{indentD plain}\n{failure}"
  return plain

/-- Offer `suggestion`, checked against the original goal by `checkedSuggestion`, with the
report of the call `plain` that closed the goal below it. -/
private def addSuggestion
    (ref : Syntax) (original : Tactic.SavedState) (plain suggestion : TSyntax `tactic)
    (report : Tactic.Explanation.ExplanationReport) :
    TacticM Unit := do
  let suggestion ← checkedSuggestion original plain suggestion
  let reportMessage ←
    if cas.verbose.get (← getOptions) then
      Command.Explanation.render report
    else
      Command.Explanation.renderSummary report
  Lean.Meta.Tactic.TryThis.addSuggestion ref
    { suggestion }
    (origSpan? := ← getRef)
    (footer := m!"\n\n{reportMessage}")

/-! ## Public query tactic syntax -/

/-- Run a whole `cas?` or `cega?` elaborator, the query and its report, as
`Tactic.ProofCarrier.tacticEntry` does: the state is restored on failure and an exhausted
recursion depth is an ordinary failure. The elaborated syntax starts with the atom `cas?` or
`cega?`, which names the tactic. -/
private def reported (body : TacticM Unit) : TacticM Unit := do
  let head := (← getRef)[0].getAtomVal
  Tactic.ProofCarrier.tacticEntry (if head.isEmpty then "cas?" else head) body

/-- The call of the plain tactic `head`, of syntax kind `kind`, with the arguments of `stx`, a
call of its reporting twin. -/
private def plainCall (kind : SyntaxNodeKind) (head : String) (stx : Syntax) : TSyntax `tactic :=
  ⟨Syntax.node .none kind #[Syntax.atom (SourceInfo.fromRef stx[0]) head, stx[1]]⟩

/-- `cas?` proves the goal as `cas` with the same arguments does and suggests the call to keep in
the proof.

## Theorem
The goal shapes of `cas`, with the arguments of its forms, as in `cas? using h`,
`cas? using [h₁, h₂]` and `cas? [l₁, l₂]`.

## Conditions and limits
The suggestion is the explicit call that the closing route records, when that call, run on the
original goal, closes it with no error: `cega [enclose x in [a, b]] e` after the box route, with
the box and the expression that the route used, and `cas [integrate primitive := F]` after the
integration route, when it checked a primitive `F` written as an ordinary function. Otherwise the
suggestion is the call as written. A summary under the suggestion names the selected route, and
the InfoView shows the route and its checked evidence.

## Options
`set_option cas.verbose true` replaces the summary under the suggestion by the full report, with
the planner steps and the checked evidence; the default is `false`. The other options are those of
`cas`.

## Examples
```lean
example (x : ℝ) : (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by
  cas?
```
```output
Try this: [apply] cas
Lean checked the suggested replacement against the original goal. Selected route: CAS route:
ordinary Lean simplification/arithmetic.
```
```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 3 := by
  cas?
```
```output
Try this: [apply] cega [enclose x in [0, 1]] (Real.exp x)
Lean checked the suggested replacement against the original goal. Selected route: CAS route:
checked CEGA box enclosure of an ordinary inequality.
```
```lean
example (x y : ℝ) (h₁ : x + y = 3) (h₂ : x - y = 1) : x = 2 := by
  cas? using [h₁, h₂]
```
```output
Try this: [apply] cas using [h₁, h₂]
Lean checked the suggested replacement against the original goal. Selected route: CAS route:
polynomial consequences of equation hypotheses.
```

## In a proof
```lean
theorem exp_le_three (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 3 := by
  cega [enclose x in [0, 1]] (Real.exp x)
```
The suggested call replaces `cas?` in the proof.

## See also
The tactics `cas`, `cega?` and `cega`.

## Possible issues
```lean
example (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 2 := by
  cas?
```
```output
cas could not prove this arithmetic relation. The statement may be false, or it may lie outside
the supported normalization and arithmetic fragment
```
`cas?` fails where `cas` fails, with the message of `cas`, and suggests nothing.
```lean
example (x : ℝ) : x + 1 = 1 + x := by
  set_option maxRecDepth 12 in cas?
```
```output
cas exceeded Lean's maximum recursion depth (the option maxRecDepth is 12; some routes run with a
higher limit of their own). This is a resource limit, not a refutation of the goal.
```
The message names a larger setting to try, written as `set_option maxRecDepth n in` before the
tactic.
-/
syntax (name := tacticCas?) "cas?" (ppSpace casArgs)? : tactic

/-- `cega?` proves the goal as `cega` with the same arguments does and suggests the explicit call to
keep in the proof.

## Theorem
The goal shapes of `cega`. Bare `cega?` runs the routes of bare `cega` except the kernel
certificate of a closed decidable proposition.

## Conditions and limits
When the box route closed the goal, the suggestion is the explicit query
`cega [enclose x in [a, b]] e` with the box and the expression that the route used, provided that
query, run on the original goal, closes it; otherwise the suggestion is the call as written. The
InfoView shows the route and its checked evidence.

## Options
`set_option cas.verbose true` replaces the summary under the suggestion by the full report, as for
`cas?`; the default is `false`. The other options are those of `cega`.

## Examples
```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cega?
```
```output
Try this: [apply] cega [enclose x in [0, 1]] (Real.sin x)
```
```lean
example : Real.sqrt 2 ≤ 1.415 := by
  cega?
```
```output
Try this: [apply] cega [enclose] (√2)
```

## In a proof
```lean
theorem cega_sin_bound (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cega [enclose x in [0, 1]] (Real.sin x)
```
The suggested call replaces `cega?` in the proof.

## See also
The tactics `cega`, `cas?` and `cas`, and the mode `enclose`.

## Possible issues
```lean
example (x : ℝ) : Real.sin x ≤ 1.5 := by
  cega?
```
```output
cega box route: no rational bounds on `x` in the hypotheses
```
`cega?` refuses the goals that `cega` refuses, with the same message.
-/
syntax (name := tacticCega?) "cega?" (cegaArgs)? : tactic

/-- The elaborator of `cas?`: it runs `cas` with the same arguments, recording the closing route,
and offers the call to keep (`casSuggestion`, checked on the original goal) with the report of the
run below it. -/
@[tactic tacticCas?] def evalCas? : Tactic := fun stx ↦ reported do
  let original ← saveState
  let plain := plainCall ``ExactTactic.tacticCas "cas" stx
  let (report, route?) ← runReportedQueryWithValue (ExactTactic.runRecordingRoute plain)
    casPlannerMetadata casEvidence casFinalAttribution
  addSuggestion stx[0] original plain (casSuggestion route? plain) report

/-- The elaborator of `cega?`: it runs `cega` with the same arguments and offers the call to keep,
checked on the original goal, with the report of the run below it. For bare `cega` the suggestion is
the explicit call of the route that closed the goal (`cegaSuggestion`); for the other forms it is
the call as written. -/
@[tactic tacticCega?] def evalCega? : Tactic := fun stx ↦ reported do
  let original ← saveState
  let plain := plainCall ``CEGA.tacticCega "cega" stx
  match plain with
  | `(tactic| cega) =>
      -- Plain `cega` runs the routes of bare `cega?` first, so it closes the goal as they did.
      let (report, route) ← runReportedQueryWithValue CEGA.closeBare bareCegaPlannerMetadata
      addSuggestion stx[0] original plain (← cegaSuggestion route) report
  | `(tactic| cega using $carrier:term) =>
      let report ← runReportedQuery
        (Tactic.ProofCarrier.withKernelOnlyAxioms "cega? using" do
          let (route, carrierExpr) ← Tactic.CEGA.closeUsingCarrier carrier
          return (route, #[carrierExpr]))
        cegaPlannerMetadata
      addSuggestion stx[0] original plain plain report
  | `(tactic| cega $cfg:optConfig [enclose $bindings:cegaIntervalBinding,*] $expr:term) =>
      let report ← runReportedQuery (CEGA.closeEncloseQuery cfg bindings.getElems expr)
        queryPlannerMetadata (finalAttribution := fun query ↦ some query.1.soundTheorem)
      addSuggestion stx[0] original plain plain report
  | _ =>
      let report ← runReportedQuery (evalTactic plain) fun _ ↦ #[]
      addSuggestion stx[0] original plain plain report

end CAS

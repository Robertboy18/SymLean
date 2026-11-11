/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Common
public import CAS.Tactic.DerivativeBridge
public meta import CAS.Tactic.DerivativeBridge
public meta import Lean.Meta.Tactic.TryThis

/-!
# Headline theorems of `#cas` reports

The reports built with `withHeadlines`, those of `CAS.Command.Simplification`,
`CAS.Command.Differential`, `CAS.Command.Integration` and `CAS.Command.CEGA`, open their checked
evidence with a theorem about the user's own Mathlib terms, quantified over the real variables,
with the checked conditions as hypotheses (`conditionTerms`): the input as
`ReifiedExpr.inputTerm` prints it, with each function of `DesugaredFunction` (`Real.tan`, `|a|`)
named exactly where the user applied it, and the result as `exprTerm` prints it, with such a
function named where the result has its form and the input applies the function somewhere
(`ReifiedExpr.resultFunction?`). The `Conditions` line of the report prints the same conditions
in its display form, so the hypothesis `0 < 2 * x + 2` shows as `x + 1 > 0`.

## Main definitions

* `CAS.Command.headlineStep`: a headline as an evidence step, named by the lemma of its proof.
* `CAS.Command.withHeadlines`: validate the headlines of a report, each on a budget of its own.
* `CAS.Command.offerExample`: under `cas.suggest`, the first headline offered as an `example`.
* `CAS.Command.headlineBridge`: a reflected expression identified with its printed term.
* `CAS.Command.headlineConditions`: the reflected conditions from the hypotheses of a headline.

## Implementation notes

The certificate a mode checks is a statement about reflected `Verified.Expr` terms, and the
headline is transported from it by a lemma of the mode. The hypotheses of that lemma identify
each reflected expression with its printed term (`headlineBridge`), fix the checked route by one
kernel decision, and reduce the reflected conditions to the hypotheses of the headline
(`DerivativeBridge.closeValidity`). A headline is then validated as every evidence step is
(`CAS.Tactic.Explanation.UncheckedExplanationStep.validate`), so its proof is checked by the
kernel as an auxiliary theorem before the report prints it.

`headlineStep` elaborates the statement, opens its binders, runs the proof of the mode and returns
the step with the lemma as its theorem name. `withHeadlines` validates the headlines of a report,
each with a heartbeat budget of its own, so that a headline that fails or runs out of heartbeats
leaves the report with its reflected evidence alone. Under `set_option cas.suggest true`,
`offerExample` offers the first headline as an `example` to paste in place of the command, once
the binders and the type of that `example`, elaborated as the `example` command elaborates them
where the `#cas` command is, with the variables of its section, form a proposition definitionally
equal to the headline, and the whole command has then elaborated there without errors to a
declaration with no `sorry` whose type is definitionally equal to the headline in the same way, so
that the `example` takes no variable of the section as an argument. `checkExample` makes these
checks on a copy of the command state and gives the text of the `example`, which `offerExample`
offers and `#cas [sos ...]` prints, or the check that failed (`ExampleFailure`).
-/

public meta section

namespace CAS

/-- Offer the headline theorem of a `#cas` report, its first checked step, as an `example` to paste
in place of the command, proved by `cas`, or for an enclosure with a configuration by `cega` with
that configuration. It is offered when the binders and the type of the `example`, elaborated as
the `example` command elaborates them, form a proposition definitionally equal to the headline at
instance transparency, and the whole `example` command then elaborates without errors to a
declaration with no `sorry` whose type is definitionally equal to the headline in the same way,
so that the `example` takes no variable of the section as an argument. These are checked where
the `#cas` command is, with that file's open namespaces, notation, options and section variables,
so a copy pasted elsewhere can elaborate differently or not at all. -/
register_option cas.suggest : Bool := {
  defValue := false
  descr := "offer the headline theorem of a #cas report as an example to paste in place of the \
    command, when the binders and the type of the example, elaborated where the command is with \
    the section variables, are the headline and the example elaborates there without errors to \
    a declaration of the headline with no sorry"
}

end CAS

namespace CAS.Command

open Lean Elab Command Meta
open CAS.Tactic.Explanation
open CAS.Elaboration.RealExpression (DesugaredFunction)

/-- The tactic identifying `eval ρ e`, at a vector literal `ρ` of variables, with the term that
`exprTerm` prints for `e`: the evaluator and the vector are unfolded, the numeral casts are pushed
to the literals and the functions of `DesugaredFunction` are rewritten by their
`DesugaredFunction.rewriteLemmas`, with `norm_num` for rationals that the printer writes in lowest
terms and `ring1` for the forms of the functions that differ from theirs by ring arithmetic. -/
def headlineBridgeSyntax : MetaM (TSyntax `tactic) := do
  let table ← (DesugaredFunction.all.flatMap (·.rewriteLemmas)).toArray.mapM fun name ↦
    `(Lean.Parser.Tactic.simpLemma| $(mkCIdent name):ident)
  `(tactic| first
    | (simp only [Verified.Expr.eval, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
        Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one, neg_div, div_one,
        $table,*]; done)
    | (norm_num [Verified.Expr.eval]; done)
    | (simp only [Verified.Expr.eval, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
        Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one, neg_div, div_one,
        $table,*] <;> ring1)
    | (norm_num [Verified.Expr.eval, $table,*] <;> ring1))

/-- A proof of `eval ρ reflected = term`, where `term` is the elaborated `exprTerm` of the
reflected expression at the variables of `ρ`. -/
def headlineBridge (ρ reflected term : Expr) : MetaM Expr := do
  let goal ← mkFreshExprSyntheticOpaqueMVar
    (← mkEq (← mkAppM ``Verified.Expr.eval #[ρ, reflected]) term)
  let remaining ← Tactic.KernelReadBack.withSuppressedMessagesMeta <|
    Tactic.KernelReadBack.runTacticOnGoal goal.mvarId! (← headlineBridgeSyntax)
  unless remaining.isEmpty do
    throwError "the printed term differs from the evaluation of its reflected expression"
  instantiateMVars goal

/-- A proof of `∀ i, eval ρ (G i) = g i`, where `G` is a vector literal of `n` reflected
expressions and `g` the vector literal of their elaborated `exprTerm`s at the variables of `ρ`,
entry by entry as `headlineBridge` proves one. -/
def headlineBridgeEntries (n : Nat) (ρ G g : Expr) : MetaM Expr := do
  let goal ← mkFreshExprSyntheticOpaqueMVar (← withLocalDeclD `i (quotedVariableType n) fun i ↦ do
    mkForallFVars #[i] (← mkEq (← mkAppM ``Verified.Expr.eval #[ρ, mkApp G i]) (mkApp g i)))
  let remaining ← Tactic.KernelReadBack.withSuppressedMessagesMeta <|
    Tactic.KernelReadBack.runTacticOnGoal goal.mvarId!
      (← `(tactic| (intro i; fin_cases i <;> $(← headlineBridgeSyntax))))
  unless remaining.isEmpty do
    throwError "a printed entry differs from the evaluation of its reflected expression"
  instantiateMVars goal

/-- The tactic that proves reflected conditions whose real facts, once unfolded, are each a
hypothesis, a fact of `positivity`, or the nonzero fact of a positive hypothesis: the hypotheses
of a headline are the checked conditions of `conditionTerms`, and the requirements they leave out
hold automatically or follow from a positive requirement. -/
private def headlineFactsSyntax : MetaM (TSyntax `tactic) := do
  `(tactic|
    ($(← Tactic.DerivativeBridge.unfoldValidityTactic):tactic
     try (repeat' constructor)
     all_goals
       first
         | assumption
         | positivity
         | (apply ne_of_gt; assumption)
         | (apply ne_of_gt; positivity)))

/-- Prove the reflected conditions `goal` (a `SideHolds` or `ValidAt` statement at a vector of
variables) from the hypotheses in the local context: fact by fact as `headlineFactsSyntax` does,
and otherwise by `DerivativeBridge.closeValidity`. -/
def headlineConditions (operation : String) (goal : Expr) : MetaM Expr := do
  let saved ← saveState
  let proof ← mkFreshExprMVar goal
  let direct ←
    try
      let remaining ← Tactic.KernelReadBack.withSuppressedMessagesMeta <|
        Tactic.KernelReadBack.runTacticOnGoal proof.mvarId! (← headlineFactsSyntax)
      pure remaining.isEmpty
    catch _ =>
      pure false
  let proof ← instantiateMVars proof
  if direct && !proof.hasMVar && !proof.hasSorry then
    return proof
  saved.restore
  let proof ← mkFreshExprMVar goal
  Tactic.DerivativeBridge.closeValidity operation proof.mvarId! none
  instantiateMVars proof

/-- Proofs of the conjuncts of `proof`, a proof of a conjunction. -/
partial def headlineConjuncts (proof : Expr) : MetaM (Array Expr) := do
  let type := (← instantiateMVars (← inferType proof)).consumeMData
  if type.isAppOfArity ``And 2 then
    return (← headlineConjuncts (← mkAppM ``And.left #[proof])) ++
      (← headlineConjuncts (← mkAppM ``And.right #[proof]))
  return #[proof]

private def withHeadlineFacts {α : Type} (facts : List Expr) (locals : Array Expr)
    (k : Array Expr → MetaM α) : MetaM α :=
  match facts with
  | [] => k locals
  | fact :: rest => do
    withLocalDeclD `hcondition (← instantiateMVars (← inferType fact)) fun hypothesis ↦
      withHeadlineFacts rest (locals.push hypothesis) k

/-- Prove the reflected conditions `goal` as `headlineConditions` does, with the proofs `facts`
of further hypotheses added to the local context. -/
def headlineConditionsWith (operation : String) (goal : Expr) (facts : Array Expr) :
    MetaM Expr :=
  withHeadlineFacts facts.toList #[] fun locals ↦ do
    return mkAppN (← mkLambdaFVars locals (← headlineConditions operation goal)) facts

/-- A proof of `∀ s, line s = Function.update (line base) coordinate s`, for a function `line`
from the reals to vector literals whose entry `coordinate` is the argument and whose other
entries do not depend on it. -/
def headlineLine (line coordinate base : Expr) : MetaM Expr := do
  let goal ← mkFreshExprSyntheticOpaqueMVar (← withLocalDeclD `s (mkConst ``Real) fun s ↦ do
    mkForallFVars #[s] (← mkEq (line.beta #[s])
      (← mkAppM ``Function.update #[line.beta #[base], coordinate, s])))
  let remaining ← Tactic.KernelReadBack.withSuppressedMessagesMeta <|
    Tactic.KernelReadBack.runTacticOnGoal goal.mvarId! (← `(tactic|
      (intro s; funext i; fin_cases i <;> first | rfl | simp [Function.update_apply])))
  unless remaining.isEmpty do
    throwError "the line through the point was not identified"
  instantiateMVars goal

/-- Elaborate the headline `statement`, whose first `binders` binders are its variables and
hypotheses, and prove it with `prove`, which receives those binders as local variables together
with the conclusion. The step names `theoremName` as the lemma its proof applies. -/
def headlineStep (label : String) (theoremName : Name) (statement : TSyntax `term)
    (binders : Nat) (prove : Array Expr → Expr → TermElabM Expr) :
    TermElabM UncheckedExplanationStep := do
  let type ← Term.withoutErrToSorry <| Term.elabType statement
  Term.synthesizeSyntheticMVarsNoPostponing
  let type ← instantiateMVars type
  if type.hasMVar || type.hasSorry then
    throwError "{label}: the statement did not elaborate"
  let proof ← forallBoundedTelescope type (some binders) fun locals conclusion ↦ do
    unless locals.size = binders do
      throwError "{label}: the statement has fewer binders than expected"
    let proof ← instantiateMVars (← prove locals conclusion)
    if proof.hasMVar || proof.hasSorry then
      throwError "{label}: incomplete proof"
    mkLambdaFVars locals proof
  return { label, proposition := type, proof := ← mkExpectedTypeHint proof type,
           theoremName? := some theoremName }

/-- Open the first `names.length` binders of `type` with the names `names`, and continue with `k`
on the new local variables and the rest of `type`. -/
private def withNamedBinders {α : Type} (type : Expr) (names : List Name) (locals : Array Expr)
    (k : Array Expr → Expr → MetaM α) : MetaM α :=
  match names, type with
  | name :: rest, .forallE _ domain body info =>
    withLocalDecl name info domain fun fvar ↦
      withNamedBinders (body.instantiate1 fvar) rest (locals.push fvar) k
  | _, _ => k locals type

/-- The binders and the conclusion of `type` as an `example` states them. The variables keep their
names, consecutive variables of one type form one binder, and the hypotheses are named `h`, or
`h₁`, `h₂`, … when there are several, with primes added to `h` while one of these names is also
the name of a variable. Each binder is its names with the text of their type. -/
private def exampleBinders (type : Expr) : MetaM (Array (Array Name × String) × Format) := do
  let (kinds, variableNames) ← forallTelescope type fun locals _ ↦ do
    let mut kinds : Array Bool := #[]
    let mut variableNames : Array Name := #[]
    for fvar in locals do
      let decl ← fvar.fvarId!.getDecl
      let hypothesis ← isProp decl.type
      kinds := kinds.push hypothesis
      unless hypothesis do variableNames := variableNames.push decl.userName
    return (kinds, variableNames)
  let count := (kinds.filter id).size
  let hypothesisNames (stem : String) : Array Name :=
    if count = 1 then #[Name.mkSimple stem]
    else (Array.range count).map fun i ↦ Name.mkSimple (stem ++ (i + 1).toSubscriptString)
  let mut stem := "h"
  while (hypothesisNames stem).any variableNames.contains do
    stem := stem ++ "'"
  let mut pending := (hypothesisNames stem).toList
  let mut names : Array Name := #[]
  let mut variableIndex := 0
  for hypothesis in kinds do
    if hypothesis then
      names := names.push (pending.headD `h)
      pending := pending.tail
    else
      names := names.push (variableNames[variableIndex]?.getD `x)
      variableIndex := variableIndex + 1
  withNamedBinders type names.toList #[] fun locals conclusion ↦ do
    let mut binders : Array (Array Name × String) := #[]
    let mut groupType? : Option Expr := none
    for fvar in locals do
      let decl ← fvar.fvarId!.getDecl
      let text := (← ppExpr decl.type).pretty 1000000
      if (← isProp decl.type) then
        binders := binders.push (#[decl.userName], text)
        groupType? := none
      else if groupType? == some decl.type then
        binders := binders.modify (binders.size - 1) fun (group, text) ↦
          (group.push decl.userName, text)
      else
        binders := binders.push (#[decl.userName], text)
        groupType? := some decl.type
    return (binders, ← ppExpr conclusion)

/-- The text of `example binders : conclusion := by tactic`: on one line when it fits in 100
columns, and otherwise with the conclusion from the next line on at an indentation of four and
the tactic on a line of its own. -/
private def exampleText (binders : Array (Array Name × String)) (conclusion : Format)
    (tactic : String) : String := Id.run do
  let mut head := "example"
  for (names, type) in binders do
    let group := " ".intercalate (names.map toString).toList
    head := s!"{head} ({group} : {type})"
  let flat := s!"{head} : {conclusion.pretty 1000000} := by {tactic}"
  if flat.length ≤ 100 && !flat.contains '\n' then
    return flat
  let statement := (conclusion ++ Format.text " := by").pretty 100 4 4
  return s!"{head} :\n    {statement}\n  {tactic}"

/-- Run `x` on the command state with no messages and no snapshot tasks, with asynchronous
elaboration off so that every message reaches the state, and restore the whole state afterwards,
its environment, messages, info trees and traces included, also when `x` throws or is
interrupted. -/
private def withTrialState {α : Type} (x : CommandElabM α) : CommandElabM α := do
  let saved ← get
  try
    modify fun state ↦ { state with messages := .empty, snapshotTasks := #[] }
    withScope (fun scope ↦ { scope with opts := Elab.async.set scope.opts false }) <|
      withReader ({ · with snap? := none }) x
  finally
    set saved

/-- Whether the `example` command `stx` states `type`: whether its binders and its type, elaborated
where the `#cas` command is, with the variables of the section, as the `example` command
elaborates them, form without errors a proposition with no metavariable or `sorry` that is
definitionally equal to `type` at instance transparency. -/
private def exampleStates (stx : Syntax) (type : Expr) : CommandElabM Bool := do
  unless stx.isOfKind ``Parser.Command.declaration && stx[1].isOfKind ``Parser.Command.example do
    return false
  let (binders, some typeSyntax) := expandOptDeclSig stx[1][1] | return false
  modify fun state ↦ { state with messages := .empty }
  let states ← try
      runTermElabM fun _ ↦ Term.withoutErrToSorry do
        let stated ← Term.withAutoBoundImplicit <| Term.elabBinders binders.getArgs fun xs ↦ do
          let body ← Term.elabType typeSyntax
          Term.synthesizeSyntheticMVarsNoPostponing
          mkForallFVars (← Term.addAutoBoundImplicits xs none) body
        let stated ← instantiateMVars stated
        if stated.hasMVar || stated.hasSorry then return false
        withTransparency .instances <| isDefEq stated type
    catch _ => pure false
  return states && !(← get).messages.hasErrors

/-- Why `checkExample` gives no `example`. -/
inductive ExampleFailure where
  /-- No `example` of a printing of the proposition states it (`exampleStates`). -/
  | notStated
  /-- An `example` states the proposition, but where the `#cas` command is its command has an
  error, or the declaration it forms has a `sorry` in its type or its value or is not found in
  its info trees. -/
  | notElaborated
  /-- An `example` states the proposition and elaborates without errors, but the declaration it
  forms has another type, as when its proof uses a variable of the section that its header does
  not, which the `example` command then takes as an argument. -/
  | otherDeclaration

/-- The declaration `name`, with the environment that holds it, from the first context of `tree`,
the outermost first, whose environment has it among its declarations, private ones included. The
`example` command saves such a context after its declaration is added and before the environment
is restored (`Term.elabMutualDef`), when info trees are enabled. -/
private partial def savedDeclaration? (name : Name) :
    InfoTree → Option (Environment × ConstantInfo)
  | .context (.commandCtx info) tree =>
    let env := info.env.setExporting false
    (env.find? name).map (env, ·) <|> savedDeclaration? name tree
  | .context _ tree => savedDeclaration? name tree
  | .node _ children => children.findSome? (savedDeclaration? name)
  | .hole _ => none

/-- Whether the `example` command `stx`, elaborated by the command elaborator where the `#cas`
command is, with that file's open namespaces, notation, options and variables, forms a
declaration of `type`: neither its messages nor the diagnostics of its snapshot tasks have an
error, and the declaration that it adds, `_example` in the current namespace or the private name
of that, as the environment saved in its info trees holds it, has no `sorry` in its type or its
value and has a type definitionally equal to `type` at instance transparency. The `example`
command takes as arguments the variables of the section that its header or its proof uses, so
that type is another proposition when the proof uses a variable that the header does not. It runs
inside `withTrialState`, which restores the state. -/
private def exampleProves (stx : Syntax) (type : Expr) :
    CommandElabM (Except ExampleFailure Unit) := do
  modify fun state ↦
    { state with messages := .empty, snapshotTasks := #[], infoState := { enabled := true } }
  try elabCommand stx catch _ => return .error .notElaborated
  let state ← get
  let mut messages : MessageLog := state.messages
  for task in state.snapshotTasks do
    for snapshot in task.get.getAll do
      messages := messages ++ snapshot.diagnostics.msgLog
  if messages.hasErrors then return .error .notElaborated
  let name := (← getCurrNamespace) ++ `_example
  let privateName := mkPrivateName (← getEnv) name
  let some (env, declaration) := state.infoState.trees.findSome? fun tree ↦
      savedDeclaration? name tree <|> savedDeclaration? privateName tree
    | return .error .notElaborated
  if declaration.type.hasSorry || (declaration.value? (allowOpaque := true)).any (·.hasSorry) then
    return .error .notElaborated
  let same ← try
      liftTermElabM <| withEnv env <| withTransparency .instances <|
        isDefEq declaration.type type
    catch _ => pure false
  return if same then .ok () else .error .otherDeclaration

/-- The text of an `example` of the proposition `type` proved by one of `tactics`, checked where
the `#cas` command is, with the variables of its section, or why there is none. The statement is
printed with the marks of `showPowerTypes`, and also with the types of all its numerals
(`pp.numericTypes`) when no `example` of the first printing states `type` (`exampleStates`). For
the first printing with which the `example` of a tactic states `type`, the text is that of the
first such `example` whose command forms a declaration of `type` with no `sorry`
(`exampleProves`), and otherwise the failure is that of the last of them. The binders of the
`example` are those of `type`, or none with `binders := false`, for tactics that introduce them.
It runs on a copy of the command state, which it restores (`withTrialState`). -/
def checkExample (type : Expr) (tactics : Array String) (binders : Bool := true) :
    CommandElabM (Except ExampleFailure String) := withTrialState do
  let shown : MetaM (Array (Array Name × String) × Format) :=
    if binders then exampleBinders (showPowerTypes type)
    else do return (#[], ← ppExpr (showPowerTypes type))
  for numericTypes in [false, true] do
    let (shownBinders, conclusion) ← runTermElabM fun _ ↦
      withOptions (pp.numericTypes.set · numericTypes) shown
    let mut failure? : Option ExampleFailure := none
    for text in tactics.map (exampleText shownBinders conclusion) do
      let .ok stx := Parser.runParserCategory (← getEnv) `command text | continue
      unless (← exampleStates stx type) do continue
      match ← exampleProves stx type with
      | .ok () => return .ok text
      | .error failure => failure? := some failure
    if let some failure := failure? then return .error failure
  return .error .notStated

/-- Under `set_option cas.suggest true`, offer `statement?`, the statement of the first checked
step of a report, as an `example` to paste in place of the command, proved by the first of
`tactics` with which it is checked. The statement is written with its signs as `tidySigns` writes
them, on a copy of the command state (`withTrialState`), and the `example` is the text that
`checkExample` gives: its binders and its type, elaborated as the `example` command elaborates
them, form a proposition definitionally equal to the statement at instance transparency
(`exampleStates`), and the whole command then elaborates without errors to a declaration with no
`sorry` whose type is definitionally equal to the statement in the same way (`exampleProves`),
both where the `#cas` command is, with the variables of its section. With the option off it
returns before any trial elaboration. -/
def offerExample (statement? : Option Expr) (tactics : Array String := #["cas"]) :
    CommandElabM Unit := do
  unless cas.suggest.get (← getOptions) do return
  let some statement := statement? | return
  let type ← withTrialState <| liftTermElabM do
    return (← tidySigns (← instantiateMVars statement)).1
  let .ok text ← checkExample type tactics | return
  let ref ← getRef
  liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion ref { suggestion := .string text }
    (origSpan? := ref)

/-- Build a headline with `action` and validate it, with a budget of `maxHeartbeats` heartbeats of
its own, or return `none`, with the state and the messages restored, when one of its steps fails
or exceeds that budget. -/
private def headlineOrNone (action : TermElabM UncheckedExplanationStep) :
    TermElabM (Option CheckedExplanationStep) := do
  let saved ← saveState
  tryCatchRuntimeEx (withCurrHeartbeats do return some (← (← action).validate)) fun _ ↦ do
    saved.restore (restoreInfo := true)
    return none

/-- Run the headline constructions `headlines` as `headlineOrNone` does and continue with `k` on
the validated headlines. The heartbeats that the headlines used are given back to `k`, so that the
rest of the report is checked with the budget it has without them. The statement of the first
validated headline is returned with the result, for `offerExample`. -/
def withHeadlines {α : Type} (headlines : Array (TermElabM UncheckedExplanationStep))
    (k : Array CheckedExplanationStep → TermElabM α) : TermElabM (α × Option Expr) := do
  let start ← IO.getNumHeartbeats
  let checked ← headlines.filterMapM headlineOrNone
  let used := (← IO.getNumHeartbeats) - start
  let result ← withTheReader Core.Context
    (fun context ↦ { context with initHeartbeats := context.initHeartbeats + used }) (k checked)
  return (result, ← checked[0]?.mapM (instantiateMVars ·.proposition))

/-- A list of reflected expressions over `Fin n` as a closed list literal. -/
def quoteVerifiedList (n : Nat) (expressions : List (Verified.Expr (Fin n))) : MetaM Expr := do
  mkListLit (mkApp (mkConst ``Verified.Expr [Level.zero]) (quotedVariableType n))
    (← expressions.mapM quoteVerifiedExpr)

end CAS.Command

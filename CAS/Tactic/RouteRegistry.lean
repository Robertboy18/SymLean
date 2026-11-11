/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public meta import CAS.Tactic.Explanation
public import CAS.Tactic.Explanation
import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Command

/-!
# Environment-scoped computer algebra routes

Modules add routes to `cas`, backends to the `#cas` commands and a factorizer over `ℚ` by
registering declarations with `@[cas_route name]` instead of overriding the elaborators of `CAS`
or setting process state. A registration names a route, the compiled declaration that runs it, a
priority (default `1000`) and, for a route of `cas`, an optional goal predicate that selects the
goals it is offered:

* a declaration of type `Closer` is a route of `cas`. Bare `cas` calls the routes named
  `integral`, `box` and `command` from its own stages; `CAS.IntegrationTactic` and
  `CAS.Command.GaussianIntegral`, `CAS.CEGA` and `CAS.Command.Goals` register them. A route under
  any other name, such as the `hex` route of `CASHex.Algebra`, is a stage of its own, placed
  among the built-in stages of bare `cas` by its priority (`ExactTactic.routeOrder` lists the
  order), and `cas?` reports it when it closes the goal;
* a declaration of type `CommandBackend` is a backend of the `#cas` command mode it is named after.
  The command tries its backends, highest priority first, before its own computation;
* a declaration of type `FactorProvider`, registered under the name `factor`, factors polynomials
  over `ℚ` for the commands and the integration planner (`factorProvider?`). `CASHex.Factor`
  registers Hex's factorizer. Without one, they use only the factors they find themselves.

## Implementation notes

Registrations are environment data: dispatch follows the current import closure, not the order in
which modules were initialized, and `registrations` lists it, highest priority first and, at equal
priority, in the order of the modules. The attribute checks the type of the declaration when it
is applied, and the compiled declaration is evaluated against that type (`evalConstCheck`) when
it is called. The registry supplies dispatch only and proves nothing: the caller validates the
proof assigned to the goal through `ProofCarrier.attemptClosingMainGoal`, a command backend
reports only results it has checked, and the callers of a factorizer check every factorization
they use.
-/

public meta section

namespace CAS.Tactic.RouteRegistry

open Lean Elab Tactic

/--
The replay and explanation returned by a route.

The selected route supplies these together with its proof, so a report need not rerun a
planner to discover what happened. The reporting layer checks any additional evidence
before displaying it; the caller checks the proof assigned to the original goal.
-/
structure Result where
  /-- Tactic syntax that preserves the selected calculation when replayed. `cas?` suggests it
  only after running it on the original goal, where it must close that goal with a complete proof
  of it; otherwise it suggests the call that ran. -/
  replay : TSyntax `tactic
  /-- Available planner decisions, distinct from checked mathematical evidence. -/
  plannerMetadata : Array Explanation.PlannerExplanationStep := #[]
  /-- Additional propositions and proofs to validate before displaying an explanation. -/
  evidence : Array Explanation.UncheckedExplanationStep := #[]
  /-- A theorem used to transfer the checked calculation to the original goal, if applicable. -/
  finalAttribution? : Option Name := none

/-- A route of `cas`: it closes the main goal, given the optional side evidence of `cas using`,
and returns its replay and explanation. -/
abbrev Closer := Option (TSyntax `term) → TacticM Result

/-- The goal predicate of a registered route: whether its closer is offered a goal with this
target. It runs in the goal's local context. -/
abbrev GoalPredicate := Expr → MetaM Bool

/-- A backend of a `#cas` command mode: it elaborates the command, logging its report, or returns
`false` to leave the command to the next backend and finally to the command's own computation.

The registry does not inspect the report: a backend that returns `true` must have logged a report
whose every claim it proved and checked, as the commands' own reports are built (through
`CAS.Command.evidenceReportMessage` or `CAS.Command.Algebra.checkedEvidence`, which
validate the proofs before rendering them), and an input it cannot certify must make it return
`false` or throw, not report an unchecked answer. -/
abbrev CommandBackend := Syntax → Command.CommandElabM Bool

/-- A factorizer of polynomials over `ℚ`, each given by its coefficients from the constant term
up: the monic irreducible factors with their exponents, `[]` for a constant. It is an untrusted
search; its callers check every factorization they use. -/
abbrev FactorProvider := Array Rat → List (Array Rat × Nat)

/-- What a registered declaration provides. -/
inductive Kind where
  /-- A route of `cas`, of type `Closer`. -/
  | closer
  /-- A backend of a `#cas` command mode, of type `CommandBackend`. -/
  | commandBackend
  /-- A factorizer over `ℚ`, of type `FactorProvider`. -/
  | factorProvider
  deriving Repr, BEq, Inhabited

/-- A registration of `@[cas_route]`. -/
structure Registration where
  /-- The route or command mode. -/
  route : Name
  /-- The compiled declaration. -/
  declaration : Name
  /-- The priority: higher runs earlier. -/
  priority : Nat
  /-- The goal predicate of a route of `cas`, if any. -/
  goal? : Option Name := none
  /-- What the declaration provides. -/
  kind : Kind
  /-- The module in which the declaration was registered. -/
  owner : Name
  deriving Repr, Inhabited

private initialize registry :
    SimplePersistentEnvExtension Registration (Array Registration) ←
  registerSimplePersistentEnvExtension {
    name := `CAS.Tactic.RouteRegistry.registry
    addImportedFn := fun states ↦ states.foldl (· ++ ·) #[]
    addEntryFn := Array.push
  }

/-- The registrations visible in `env`, highest priority first; registrations of equal priority
keep the order of their modules in the import closure. -/
def registrations (env : Environment) : Array Registration :=
  (registry.getState env).insertionSort fun a b ↦ a.priority > b.priority

/-- The registrations of `route` of the given kind, highest priority first. -/
def registrationsOf (env : Environment) (route : Name) (kind : Kind) : Array Registration :=
  (registrations env).filter fun entry ↦ entry.route == route && entry.kind == kind

/-- The routes that bare `cas` calls from its own stages rather than as stages of their own. -/
def stageProviders : Array Name := #[`integral, `box, `command]

/-- The registered routes of `cas` that run as stages of their own, highest priority first. -/
def extensionRoutes (env : Environment) : Array Registration :=
  (registrations env).filter fun entry ↦
    entry.kind == .closer && !stageProviders.contains entry.route

private unsafe def evalCloserUnsafe (declaration : Name) : CoreM Closer :=
  evalConstCheck Closer ``Closer declaration

@[implemented_by evalCloserUnsafe]
private opaque evalCloser (declaration : Name) : CoreM Closer

private unsafe def evalGoalPredicateUnsafe (declaration : Name) : CoreM GoalPredicate :=
  evalConstCheck GoalPredicate ``GoalPredicate declaration

@[implemented_by evalGoalPredicateUnsafe]
private opaque evalGoalPredicate (declaration : Name) : CoreM GoalPredicate

private unsafe def evalCommandBackendUnsafe (declaration : Name) : CoreM CommandBackend :=
  evalConstCheck CommandBackend ``CommandBackend declaration

@[implemented_by evalCommandBackendUnsafe]
private opaque evalCommandBackend (declaration : Name) : CoreM CommandBackend

private unsafe def evalFactorProviderUnsafe (env : Environment) (opts : Options)
    (declaration : Name) : Except String FactorProvider :=
  Id.run (Environment.evalConstCheck FactorProvider env opts ``FactorProvider declaration).run

@[implemented_by evalFactorProviderUnsafe]
private opaque evalFactorProvider (env : Environment) (opts : Options) (declaration : Name) :
    Except String FactorProvider

/-- Whether the registration is offered the main goal: always without a goal predicate. -/
def accepts (entry : Registration) : TacticM Bool := do
  let some predicate := entry.goal? | return true
  let accepts ← evalGoalPredicate predicate
  withMainContext do accepts (← instantiateMVars (← getMainTarget))

/-- The compiled closer of a registered route of `cas`. -/
def closer (entry : Registration) : CoreM Closer :=
  evalCloser entry.declaration

/-- The route `route` of `cas` as one closer: its registered closers that accept the main goal,
tried in order of priority until one succeeds, with the state restored after each failure, which
the last failure reports. `none` when no registered closer accepts the goal. -/
def closer? (route : Name) : TacticM (Option Closer) := do
  let mut found := #[]
  for entry in registrationsOf (← getEnv) route .closer do
    if ← accepts entry then
      found := found.push (← closer entry)
  let some last := found.back? | return none
  return some fun side? ↦ do
    let saved ← saveState
    for run in found.pop do
      try
        return ← run side?
      catch _ =>
        saved.restore
    last side?

/-- Run the backends registered for the `#cas` mode `route` on the command `stx`, highest priority
first, until one elaborates it; a backend that declines leaves the state as it was. Returns whether
one elaborated the command. A backend's `true` is accepted as it is: the contract of
`CommandBackend`, that it reports only checked results, is the backend's to keep. -/
def runCommandBackends (route : Name) (stx : Syntax) : Command.CommandElabM Bool := do
  for entry in registrationsOf (← getEnv) route .commandBackend do
    let backend ← Command.liftCoreM <| evalCommandBackend entry.declaration
    let saved ← get
    if ← backend stx then
      return true
    set saved
  return false

/-- The factorizer over `ℚ` registered under `factor` with the highest priority, if any. -/
def factorProvider? {m : Type → Type} [Monad m] [MonadEnv m] [MonadOptions m] [MonadError m] :
    m (Option FactorProvider) := do
  let env ← getEnv
  let some entry := (registrationsOf env `factor .factorProvider)[0]? | return none
  match evalFactorProvider env (← getOptions) entry.declaration with
  | .ok provider => return some provider
  | .error message => throwError message

/-- Register a route of `cas` (a declaration of type `RouteRegistry.Closer`), a backend of a
`#cas` command mode (type `RouteRegistry.CommandBackend`) or, under the name `factor`, a
factorizer over `ℚ` (type `RouteRegistry.FactorProvider`), with an optional priority (default
`1000`; higher runs earlier) and, for a route of `cas`, an optional goal predicate (a declaration
of type `RouteRegistry.GoalPredicate`). -/
syntax (name := casRouteAttr) "cas_route " ident (ppSpace Parser.Command.namedPrio)?
  (" (" &"goal" " := " ident ")")? : attr

initialize registerBuiltinAttribute {
  name := `casRouteAttr
  descr := "register a route of `cas`, a backend of a `#cas` command mode or a factorizer"
  applicationTime := .afterCompilation
  add := fun declaration stx kind ↦ do
    unless kind == .global do throwAttrMustBeGlobal `cas_route kind
    let route := stx[1].getId
    -- Lean expands the priority macros (`high`, `low`) before it applies the attribute.
    let priority ← if stx[2].isNone then pure (eval_prio default) else
      match stx[2][0][3].isNatLit? with
      | some priority => pure priority
      | none => throwErrorAt stx[2] "expected a priority"
    let info ← getConstInfo declaration
    let kind ← match info.type with
      | .const ``Closer _ => pure Kind.closer
      | .const ``CommandBackend _ => pure Kind.commandBackend
      | .const ``FactorProvider _ => pure Kind.factorProvider
      | type => throwError "a `cas_route` declaration has type `RouteRegistry.Closer` (a route \
          of `cas`), `RouteRegistry.CommandBackend` (a backend of a `#cas` command mode) or \
          `RouteRegistry.FactorProvider` (a factorizer over `ℚ`); `{declaration}` has \
          type{indentExpr type}"
    if kind == .factorProvider && route != `factor then
      throwErrorAt stx[1] "a factorizer is registered under the name `factor`"
    let goal? ← if stx[3].isNone then pure none else do
      let goalSyntax := stx[3][3]
      unless kind == .closer do
        throwErrorAt goalSyntax "only a route of `cas` takes a goal predicate"
      let goal ← resolveGlobalConstNoOverload goalSyntax
      unless (← getConstInfo goal).type.isConstOf ``GoalPredicate do
        throwErrorAt goalSyntax "the goal predicate `{goal}` must have type \
          `RouteRegistry.GoalPredicate`"
      pure (some goal)
    if (registry.getState (← getEnv)).any (·.declaration == declaration) then
      throwError "`{declaration}` is already registered with `cas_route`"
    modifyEnv fun env ↦ registry.addEntry env
      { route, declaration, priority, goal?, kind, owner := env.mainModule }
}

end CAS.Tactic.RouteRegistry

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public meta import Lean.Util.Heartbeats
public meta import Lean.Util.CollectFVars

public meta import Lean.Elab.SyntheticMVars
public import Lean.Meta.Basic
meta import all Lean.Util.CollectAxioms

/-!
# Shared proof-carrier elaboration utilities

Metaprogramming shared by the routes of the `cas` and `cega` frontends: the entry of a
user-facing tactic, the checks a proof passes before it closes a goal, the audit of its axioms,
kernel checks of auxiliary theorems under the declaration's heartbeat budget, and the search for
proof carriers. A caller supplies its recognized type heads and projection policy; the functions
here only classify types, traverse expressions, and check proofs before assigning them to the
current goal.

## Main definitions

* `tacticEntry`: the entry of the closing elaborators of `cas` and `cega`.
* `runClosingMainGoal` and its fail-closed form `attemptClosingMainGoal`: run a route that must
  close exactly the original main goal, and validate the proof assigned to it.
* `checkCompletedProof`, `validateAssignedProof`, `assignExactProof`: the checks of a proof.
* `axiomAudit`, `withKernelOnlyAxioms`: the axioms a proof depends on, and the policy of a route
  that promises a kernel-checked proof.
* `mkKernelAuxLemma`, `addUncachedTheorem`, `cacheClosedProof`: auxiliary theorems checked by the
  kernel; `runKernelCheck` charges such a check to the declaration's budget.
* `findByTypeHead?`, `collectTypedSubexpressions`: the search for proof carriers.

## Implementation notes

The closing elaborators of `cas` and `cega` enter through `tacticEntry`, which restores the
tactic state on failure and turns an exhausted recursion depth into an ordinary error that
`first` and `try` can catch; heartbeat exhaustion still ends the declaration. A route runs inside
`runClosingMainGoal` and must close exactly the original main goal. We do not take the route's
word for it: we read the proof assigned to that goal and require that it has no metavariables or
`sorry`, also among its dependencies, that it passes `Meta.check` at reducible or else at full
transparency, and that its type equals the goal, syntactically after normalization or else by
definitional equality. The kernel checks the final theorem when the declaration is added. A
failure report that suggests a call, such as a larger `maxRecDepth` or a deeper `cega`
subdivision, gives one that parses as written and keeps the user's configuration; none is
promised to succeed.

The walk over a dependency closure is Lean's own `CollectAxioms` computation, which
`axiomClosures` runs with one cache for a list of constants, and `cachedKernelLemma?` repeats the
lookup of `Lean.Meta.mkAuxLemma`. Ours are the closing discipline and the axiom policy on top of
them. `cacheClosedProof` checks a closed proof synchronously in the kernel as an auxiliary theorem
(through `mkKernelAuxLemma`) and returns its constant; the Hex route of `CASHex.Algebra` closes
its goals this way. The search for carriers visits a term before its subterms; a subterm whose
type cannot be inferred outside its original binder context is not collected, and the search
goes on into its subterms instead of failing.
-/

public meta section

namespace CAS.Tactic.ProofCarrier

open Lean Elab Tactic Meta

/-- Trace the validation of a proof before it closes a goal (its metavariables, its dependencies
and its type) and the replay of a `cas?` or `cega?` suggestion on the original goal. -/
initialize registerTraceClass `cas.validation

/-- Profiling phases of the CAS frontends. Under `trace.profiler` (or `trace.cas.profile`), kernel
evaluations, proof validations and axiom audits appear as trace nodes of their own, so that a
profile separates them from the route code that runs them. -/
initialize registerTraceClass `cas.profile
/-- The profile node of each kernel evaluation, under `trace.cas.profile`. -/
initialize registerTraceClass `cas.profile.kernel (inherited := true)
/-- The profile node of each proof validation, under `trace.cas.profile`. -/
initialize registerTraceClass `cas.profile.validation (inherited := true)
/-- The profile node of each axiom dependency check, under `trace.cas.profile`. -/
initialize registerTraceClass `cas.profile.axioms (inherited := true)

/--
The validated result of an action that closed exactly the original main goal.

The original goal and target are retained because reporting validates its
explanation objects separately from the proof-completion check.
-/
structure ClosedMainGoal (α : Type) where
  private mk ::
  /-- The caller-specific result produced while closing the goal. -/
  value : α
  /-- The metavariable that was the main goal before the action ran. -/
  goal : MVarId
  /-- The instantiated type of the original main goal. -/
  target : Expr
  /-- The complete proof assigned to `goal`, type-checked by the elaborator.
  The kernel checks it when the enclosing declaration is accepted. -/
  proof : Expr

/--
Find the entry whose first component names the head constructor of `type`.

The second component is caller-supplied projection or dispatch data.
-/
def findByTypeHead? {α : Type} (entries : Array (Name × α)) (type : Expr) :
    Option (Name × α) :=
  let head := type.consumeMData.getAppFn
  entries.findSome? fun entry ↦
    if head.isConstOf entry.1 then some entry else none

private def collectTypedSubexpressionsAux :
    Nat →
    (Expr → Bool) → Expr → Array (Expr × Expr) →
    MetaM (Array (Expr × Expr))
  | 0, _, _, terms =>
      pure terms
  | fuel + 1, accepts, expression, terms => do
      let expression := expression.consumeMData
      let terms ←
        try
          let type ← inferType expression
          if accepts type ∧ !terms.any (fun candidate ↦ candidate.1 == expression) then
            pure <| terms.push (expression, type)
          else
            pure terms
        catch _ =>
          pure terms
      match expression with
      | .app function argument =>
          let terms ← collectTypedSubexpressionsAux fuel accepts function terms
          collectTypedSubexpressionsAux fuel accepts argument terms
      | .lam _ type body _
      | .forallE _ type body _ =>
          let terms ← collectTypedSubexpressionsAux fuel accepts type terms
          collectTypedSubexpressionsAux fuel accepts body terms
      | .letE _ type value body _ =>
          let terms ← collectTypedSubexpressionsAux fuel accepts type terms
          let terms ← collectTypedSubexpressionsAux fuel accepts value terms
          collectTypedSubexpressionsAux fuel accepts body terms
      | .proj _ _ body =>
          collectTypedSubexpressionsAux fuel accepts body terms
      | _ =>
        pure terms

/--
Collect distinct subexpressions whose inferred types satisfy `accepts`.

The root is considered before its children. Each returned pair contains
the subexpression followed by its inferred type.
-/
def collectTypedSubexpressions
    (accepts : Expr → Bool) (expression : Expr) :
    MetaM (Array (Expr × Expr)) :=
  collectTypedSubexpressionsAux
    (expression.sizeWithoutSharing + 1) accepts expression #[]

/-- Run a tactic action, restoring its initial state before propagating any failure. -/
def preservingStateOnFailure {α : Type} (action : TacticM α) : TacticM α := do
  let saved ← saveState
  tryCatchRuntimeEx action fun error ↦ do
    saved.restore
    throw error

/-- The failure of `tactic` when it exhausts Lean's recursion depth: an ordinary error that
names the option and a setting that parses, so that `first` and `try` can go on. Some routes raise
the limit for themselves (`withAtLeastMaxRecDepth`), so the option's value need not be the limit
that ran out. -/
def recursionDepthError (tactic : String) : TacticM Exception := do
  let depth := maxRecDepth.get (← getOptions)
  return .error (← getRef) m!"{tactic} exceeded Lean's maximum recursion depth (the option \
    maxRecDepth is {depth}; some routes run with a higher limit of their own). This is a \
    resource limit, not a refutation of the goal. A larger setting may help: write \
    `set_option maxRecDepth {4 * depth} in` before the tactic; or make the goal smaller."

/-- The first line of Lean's text for an exhausted recursion depth (`maxRecDepthErrorMessage`),
which some tactics, such as `simp`, embed in an ordinary error. -/
private def rawRecursionDepthText : String :=
  (maxRecDepthErrorMessage.splitOn "\n").headD maxRecDepthErrorMessage

/-- Run the elaborator of the user-facing tactic `tactic`: restore the initial state before
propagating any failure, and report an exhausted recursion depth with `recursionDepthError`
instead of Lean's runtime exception, which `first` and `try` do not catch. An ordinary error that
quotes Lean's recursion text (`simp` nests it) keeps its whole report, after a sentence that says
so; that quote shows only that some inner step ran out of depth. Heartbeat exhaustion still
propagates: it is the budget of the whole declaration. Only the failure of the outermost call
changes, so a goal the tactic proves keeps its proof. -/
def tacticEntry {α : Type} (tactic : String) (action : TacticM α) : TacticM α :=
  preservingStateOnFailure do
    tryCatchRuntimeEx action fun error ↦ do
      if error.isMaxRecDepth then
        throw (← recursionDepthError tactic)
      if error.isRuntime then
        throw error
      let .error ref report := error | throw error
      unless ((← report.toString).splitOn rawRecursionDepthText).length > 1 do
        throw error
      let depth := maxRecDepth.get (← getOptions)
      throw <| .error ref m!"{tactic} failed, and a step inside it reports that it exceeded \
        Lean's maximum recursion depth (the option maxRecDepth is {depth}). A larger setting may \
        help: write `set_option maxRecDepth {4 * depth} in` before the tactic.\n{report}"

/--
Run a Boolean tactic-state probe and restore the original state when it
returns `false` or throws.
-/
def restoringStateOnFalse (action : TacticM Bool) : TacticM Bool := do
  let saved ← saveState
  tryCatchRuntimeEx
    (do
      if ← action then
        return true
      saved.restore
      return false)
    fun error ↦ do
      saved.restore
      throw error

/--
Run an optional tactic-state probe and restore the original state when it
returns `none` or throws.
-/
def restoringStateOnNone {α : Type} (action : TacticM (Option α)) :
    TacticM (Option α) := do
  let saved ← saveState
  tryCatchRuntimeEx
    (do
      match ← action with
      | some value => return some value
      | none =>
          saved.restore
          return none)
    fun error ↦ do
      saved.restore
      throw error

/-- Test definitional equality without retaining generated metavariable assignments.

A probe that exhausts the recursion depth while unfolding a checked computation (a normalizer
run compared with its expected value) answers `false`, so that the caller can fall back to the
kernel; a heartbeat timeout is propagated, since it is the user's budget for the whole tactic. -/
def isDefEqReadOnly (lhs rhs : Expr) : TacticM Bool := do
  let saved ← saveState
  tryCatchRuntimeEx
    (do
      let result ← isDefEq lhs rhs
      saved.restore
      return result)
    fun error ↦ do
      saved.restore
      if error.isRuntime ∧ !error.isMaxRecDepth then
        throw error
      return false

/-! ## Axiom closures

`collectAxioms` computes the axioms of the dependency closure of one constant and starts from an
empty cache on every call. Imported constants cost a lookup (their axioms are recorded with their
module), but the auxiliary theorems that the routes add to the current module, such as
`_proof_N` and `_evidence_N`, are walked again for every constant that reaches them: auditing the
`k` constants of a proof one at a time walks a large certificate up to `k` times.
`axiomClosures` runs Lean's own algorithm once for a whole list of
constants, with one cache, as Lean does when it records the axioms of a module. -/

/-- The axioms of the dependency closures of `constants`, one array per constant, sorted by
`Name.lt`: Lean's `collectAxioms` computation with one cache shared by the whole list.

A constant reached through a cycle (inductive types and their constructors, mutually recursive
unsafe definitions) inside the walk of an earlier constant of the list may receive the smaller
entry cached during that walk; the axioms it misses are then in the entry of an earlier
constant. The union of the entries of every prefix of the list is therefore the one that
`collectAxioms` gives, and an audit that asks, constant by constant in order, for the first one
whose closure contains a given axiom (`axiomAudit`, `firstIncomplete?`) reaches the same
verdict as with `collectAxioms`. -/
def axiomClosures (constants : Array Name) : MetaM (Array (Array Name)) := do
  let env ← getEnv
  let exported := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  return CollectAxioms.runM (env.setExporting false) do
    constants.mapM (CollectAxioms.collectAndGet exported.find?)

/-- The first constant of `constants` whose dependency closure contains `sorryAx`, with the
shared cache of `axiomClosures`; the constants after it are not walked. -/
def firstIncomplete? (constants : Array Name) : MetaM (Option Name) := do
  let env ← getEnv
  let exported := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  return CollectAxioms.runM (env.setExporting false) do
    for name in constants do
      let axioms ← CollectAxioms.collectAndGet exported.find? name
      if axioms.any (fun ax ↦ (mkConst ax).hasSorry) then
        return some name
    return none

/-- Reject expressions that depend transitively on declarations containing proof holes. -/
def rejectIncompleteDependencies (description : String) (expression : Expr) : MetaM Unit :=
  withTraceNode `cas.profile.axioms (fun _ ↦ return m!"dependency audit: {description}") do
    -- Elaborating a proof can hide a recovered hole in an auxiliary theorem.
    -- Inspect transitive dependencies as well as the returned expression itself.
    if let some name ← firstIncomplete? expression.getUsedConstants then
      throwError "{description} depends on incomplete declaration {name}"

/-! ## Axiom policy

A kernel-only route promises a proof that the kernel checks in full. Lean's auxiliary-lemma cache
(`Lean.Meta.mkAuxLemma`) is keyed by the statement alone, so it can hand such a route a lemma
proved earlier by native evaluation. Theorems that depend on an axiom other than `propext`,
`Classical.choice` and `Quot.sound` therefore never enter that cache (`addUncachedTheorem`,
`mkKernelAuxLemma`), a cached lemma that depends on one is replaced instead of reused
(`mkKernelAuxLemma`), and a route can reject a completed proof that depends on one
(`withKernelOnlyAxioms`). -/

/-- The axioms of Lean's logic that a kernel-checked proof may use. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- The axioms outside `standardAxioms` on which the expressions depend, each with one constant
through which it is reached, and the constants that the kernel has not accepted
(`collectAxioms` reports no axiom for those). -/
def axiomAudit (expressions : Array Expr) : MetaM (Array (Name × Name) × Array Name) :=
  withTraceNode `cas.profile.axioms (fun _ ↦ return m!"axiom audit") do
    let checked := ((← getEnv).setExporting false).checked.get
    let mut accepted : Array Name := #[]
    let mut unknown : Array Name := #[]
    let mut visited : NameSet := {}
    for expression in expressions do
      for constant in expression.getUsedConstants do
        if visited.contains constant then continue
        visited := visited.insert constant
        if (checked.find? constant).isNone then
          unknown := unknown.push constant
        else
          accepted := accepted.push constant
    let mut found : Array (Name × Name) := #[]
    for constant in accepted, axioms in ← axiomClosures accepted do
      for axiomName in axioms do
        unless standardAxioms.contains axiomName || found.any (·.1 == axiomName) do
          found := found.push (axiomName, constant)
    return (found, unknown)

/-- The axioms outside `standardAxioms` on which `expression` depends, each with one constant of
`expression` through which it is reached. -/
def nonstandardAxioms (expression : Expr) : MetaM (Array (Name × Name)) :=
  return (← axiomAudit #[expression]).1

/-- Whether the expressions use only constants the kernel has accepted and depend on no axiom
outside `standardAxioms`. -/
def kernelClean (expressions : Array Expr) : MetaM Bool := do
  let (found, unknown) ← axiomAudit expressions
  return found.isEmpty && unknown.isEmpty

/-- Add a theorem under a fresh auxiliary name, outside the auxiliary-lemma cache, and check it
in the kernel now. Natively checked certificates use this, so that no later request for the same
statement can receive them from the cache. -/
def addUncachedTheorem (levelParams : List Name) (type value : Expr) (kind : Name) :
    MetaM Name := do
  let name ← mkAuxDeclName (kind := kind)
  withOptions (fun options ↦ debug.skipKernelTC.set (Elab.async.set options false) false) do
    addDecl <| .thmDecl { name, levelParams, type, value }
  return name

/-- The theorem the auxiliary-lemma cache holds for `type`, if it depends only on the standard
axioms. This is the lookup of `Lean.Meta.mkAuxLemma` (the entry for the current privacy, then,
in a private context, the public one, each only with the same universe parameters), without
adding anything. -/
def cachedKernelLemma? (levelParams : List Name) (type : Expr) : MetaM (Option Name) := do
  let env ← getEnv
  let lemmas := (auxLemmasExt.getState env).lemmas
  let key : AuxLemmaKey := { type, isPrivate := !env.isExporting, defeq := false }
  let lookup (key : AuxLemmaKey) : Option Name :=
    match lemmas.find? key with
    | some (name, cachedLevels) => if cachedLevels == levelParams then some name else none
    | none => none
  let found := (lookup key).orElse fun _ ↦
    if key.isPrivate then lookup { key with isPrivate := false } else none
  let some name := found | return none
  unless ← kernelClean #[mkConst name (levelParams.map mkLevelParam)] do
    return none
  return some name

/-- `mkAuxLemma` for a proof that the kernel checks in full. A proof whose statement or value
depends on an axiom outside `standardAxioms` (an input of the caller) is checked under a fresh
name and kept out of the cache, whose users expect kernel-only lemmas. A cache hit that depends
on such an axiom is not reused: the proof is checked under a fresh name, which also replaces the
cache entry for the current privacy. -/
def mkKernelAuxLemma (levelParams : List Name) (type value : Expr) (kind : Name) :
    MetaM Name := do
  unless ← kernelClean #[type, value] do
    return ← addUncachedTheorem levelParams type value kind
  let before ← getEnv
  let name ← mkAuxLemma levelParams type value (kind? := some kind)
  if before.contains name &&
      !(← kernelClean #[mkConst name (levelParams.map mkLevelParam)]) then
    trace[cas.validation] "Auxiliary-lemma cache returned {name}, which uses a \
      nonstandard axiom; checking the proof under a fresh name"
    return ← mkAuxLemma levelParams type value (kind? := some kind) (cache := false)
  return name

/-- The worklist of `reachableLocals`: each local declaration is visited once. -/
private partial def reachableLocalsFrom (lctx : LocalContext) :
    List FVarId → FVarIdSet → Array Expr → MetaM (Array Expr)
  | [], _, sources => return sources
  | fvarId :: pending, seen, sources => do
      if seen.contains fvarId then
        return ← reachableLocalsFrom lctx pending seen sources
      let seen := seen.insert fvarId
      let some declaration := lctx.find? fvarId
        | reachableLocalsFrom lctx pending seen sources
      let parts ← (#[declaration.type] ++ declaration.value?.toArray).mapM instantiateMVars
      let next := parts.foldl (fun acc part ↦ (Lean.collectFVars {} part).fvarIds.toList ++ acc)
        pending
      reachableLocalsFrom lctx next seen (sources ++ parts)

/-- The types and values of the local declarations reachable from `roots` through their free
variables, following the types and values of the declarations reached, instantiated. -/
private def reachableLocals (lctx : LocalContext) (roots : Array Expr) : MetaM (Array Expr) := do
  let mut pending : List FVarId := []
  for root in roots do
    pending := (Lean.collectFVars {} (← instantiateMVars root)).fvarIds.toList ++ pending
  reachableLocalsFrom lctx pending {} #[]

/-- Run `action`, which closes the main goal by a route that promises a kernel-checked proof, and
audit the completed proof together with the local declarations it reaches (their types and, for
`let`-bound ones, values, transitively). A constant the kernel has not accepted, or `sorryAx`, is
rejected. Another axiom outside `standardAxioms` is accepted only when the route's inputs already
depend on it: the goal's type, the terms the action returns (such as an explicit carrier), and
the local declarations these and the proof reach. The caller restores the state on failure. -/
def withKernelOnlyAxioms {α : Type} (description : String) (action : TacticM (α × Array Expr)) :
    TacticM α := do
  let goal ← getMainGoal
  let declaration ← goal.getDecl
  let (value, inputs) ← action
  let proof ← instantiateMVars (mkMVar goal)
  let used ← reachableLocals declaration.lctx #[proof]
  let (found, unknown) ← axiomAudit (#[proof] ++ used)
  unless unknown.isEmpty do
    throwError "{description} built a proof that uses {unknown.toList.map MessageData.ofName}, \
      which the kernel has not accepted"
  if found.any (·.1 == ``sorryAx) then
    throwError "{description} built a proof that depends on `sorryAx`"
  if found.isEmpty then
    return value
  let roots := #[declaration.type, proof] ++ inputs
  let sources := #[declaration.type] ++ inputs ++ (← reachableLocals declaration.lctx roots)
  let allowed := (← axiomAudit (← sources.mapM instantiateMVars)).1.map (·.1)
  let rejected := found.filter fun (axiomName, _) ↦ !allowed.contains axiomName
  unless rejected.isEmpty do
    let causes := rejected.map fun (axiomName, constant) ↦
      m!"`{.ofConstName axiomName}` (through `{.ofConstName constant}`)"
    throwError "{description} promises a kernel-checked proof, but the proof it built depends \
      on {MessageData.joinSep causes.toList ", "}, which neither the goal nor the hypotheses \
      and carrier it uses depend on. Natively checked certificates are used only by \
      `cega [fast]` with `cega.nativeCertificates` set to true."
  return value

/-! ## Kernel budgets

`Lean.Kernel.whnf` takes no heartbeat budget and cannot be interrupted, but its allocations
advance the heartbeat counter of the elaborating thread, so its work can be charged when it
returns (`chargeKernelEvaluation`). A kernel check through `addDecl` honours the `maxHeartbeats`
option, relative to its own start; `withRemainingKernelBudget` lowers that option to what the
declaration has left, so that a sequence of checks shares one budget. -/

/-- Charge the kernel work done since the declaration started against `maxHeartbeats`: throw
Lean's heartbeat exception, naming `task`, when the declaration has used more. -/
def chargeKernelEvaluation (task : String) : CoreM Unit := do
  let context ← read
  unless context.maxHeartbeats == 0 do
    let used := (← IO.getNumHeartbeats) - context.initHeartbeats
    if context.maxHeartbeats < used then
      throw <| .error (← getRef) <| .tagged `runtime.maxHeartbeats m!"(deterministic) timeout: \
        {task} brought this declaration to {used / 1000} heartbeats, over the maximum \
        ({context.maxHeartbeats / 1000}). Kernel evaluation cannot be interrupted, so its work \
        is charged when it returns.\n\
        Use `set_option maxHeartbeats <num>` to raise the limit, or make the computation smaller."

/-- Run `action`, whose kernel checks (`addDecl`) then get the heartbeats the declaration has
left, rounded up to the next thousand, instead of a fresh `maxHeartbeats` each; `action`
receives that allowance, in thousands. A declaration that is already over its budget stops here
with Lean's heartbeat exception. With `maxHeartbeats 0` nothing changes. -/
def withRemainingKernelBudget {α : Type} (task : String) (action : Nat → MetaM α) :
    MetaM α := do
  let context ← readThe Core.Context
  if context.maxHeartbeats == 0 then
    return ← action (maxHeartbeats.get (← getOptions))
  chargeKernelEvaluation task
  let used := (← IO.getNumHeartbeats) - context.initHeartbeats
  let remaining := max 1 ((context.maxHeartbeats - used + 999) / 1000)
  let current := maxHeartbeats.get (← getOptions)
  let allowance := if current == 0 then remaining else min current remaining
  withOptions (maxHeartbeats.set · allowance) (action allowance)

/-- Whether an error raised by `addDecl` reports a kernel deterministic timeout. `addDecl` turns
the kernel's structured exception into an ordinary error, so its rendered text is the only
evidence left; this reads its first words, as printed by Lean v4.35 (`Lean/Message.lean`). -/
def isKernelTimeout (error : Exception) : MetaM Bool :=
  return (← error.toMessageData.toString).startsWith "(kernel) deterministic timeout"

/-- Whether an error raised by `addDecl` reports the kernel's recursion limit; see
`isKernelTimeout`. -/
def isKernelDeepRecursion (error : Exception) : MetaM Bool :=
  return (← error.toMessageData.toString).startsWith "(kernel) deep recursion"

/-- Lean's heartbeat exception for a kernel check of `operation` that ran out of the heartbeats
it was given (the `maxHeartbeats` option inside `withRemainingKernelBudget`). It ends the tactic:
the check had what was left of the declaration's budget, or all of the option's. -/
def kernelTimeoutError (operation : String) (allowance : Nat) : MetaM Exception := do
  let context ← readThe Core.Context
  return .error (← getRef) <| .tagged `runtime.maxHeartbeats m!"(deterministic) timeout: \
    {operation}: the kernel ran out of the {allowance} thousand heartbeats it was given for this \
    check; the declaration's maximum is {context.maxHeartbeats / 1000} thousand.\n\
    Use `set_option maxHeartbeats <num>` to raise the limit, or make the computation smaller."

/-- Run a kernel check under `withRemainingKernelBudget`, turn a kernel timeout into
`kernelTimeoutError` and any other failure into `onRejection`, and charge the work afterwards.
When the check fails, with an error or a resource exception, the environment is restored first,
which drops the axiom that `addDecl` registers for a rejected declaration. This is not a full
transaction: the charge after a successful check, and interrupts, leave the declarations it
added, and callers keep their own state restoration. The check itself is forced into the kernel
and made synchronous. -/
def runKernelCheck {α : Type} (operation : String) (action : MetaM α)
    (onRejection : Exception → MetaM α) : MetaM α := do
  let environment ← getEnv
  let result ← withRemainingKernelBudget operation fun allowance ↦
    tryCatchRuntimeEx
      (withOptions (fun options ↦ debug.skipKernelTC.set (Elab.async.set options false) false)
        action)
      fun error ↦ do
        setEnv environment
        if error.isRuntime then
          throw error
        if ← isKernelTimeout error then
          throw (← kernelTimeoutError operation allowance)
        -- The rejected check's work counts as well, before any report or further route.
        chargeKernelEvaluation operation
        onRejection error
  chargeKernelEvaluation operation
  return result

/-- Cache a closed proof as a kernel-checked auxiliary theorem. Subsequent proof construction
uses its constant instead of repeatedly elaborating a large certificate term. Local parameters
must be abstracted by the caller. The theorem is checked synchronously and adds no axiom. -/
def cacheClosedProof (description : String) (proof : Expr) : MetaM Expr := do
  let proof ← instantiateMVars proof
  let proposition ← instantiateMVars (← inferType proof)
  if proof.hasFVar || proof.hasMVar || proof.hasSorry ||
      proposition.hasFVar || proposition.hasMVar || proposition.hasSorry then
    throwError "{description} requires complete closed evidence"
  rejectIncompleteDependencies description proof
  rejectIncompleteDependencies description proposition
  let name ← runKernelCheck description
      (mkKernelAuxLemma [] proposition proof ((← getMainModule) ++ `_certificate))
      fun error ↦ throw error
  return mkConst name

/-- Synthesize, instantiate, and type-check a proof (with the elaborator's checker) before it
is returned to the caller. The kernel checks the final theorem when the declaration is added. -/
def checkCompletedProof (description : String) (proof : Expr) : TacticM Expr :=
  withTraceNode `cas.profile.validation (fun _ ↦ return m!"validation: {description}") do
    trace[cas.validation] "Synthesizing completed proof metavariables"
    Term.synthesizeSyntheticMVarsNoPostponing
    trace[cas.validation] "Proof metavariables synthesized"
    let proof ← instantiateMVars proof
    if proof.hasMVar ∨ proof.hasSorry then
      throwError "{description} constructed incomplete evidence: the proof term still contains \
        metavariables or placeholders"
    trace[cas.validation] "Checking proof dependencies"
    rejectIncompleteDependencies description proof
    trace[cas.validation] "Proof dependencies checked"
    -- A local hypothesis can hide an incomplete declaration in its type without
    -- mentioning that declaration in the proof term itself.
    let proofType ← instantiateMVars (← inferType proof)
    if proofType.hasMVar ∨ proofType.hasSorry then
      throwError "{description} constructed evidence with an incomplete type"
    trace[cas.validation] "Checking proof type dependencies"
    rejectIncompleteDependencies description proofType
    trace[cas.validation] "Proof type dependencies checked"
    -- Numerical definitions can remain opaque while checking a proof whose types already agree.
    -- Unfold them only when the complete check needs stronger definitional equality.
    tryCatchRuntimeEx
      (do
        trace[cas.validation] "Checking completed proof expression"
        Meta.check proof .reducible
        trace[cas.validation] "Completed proof expression checked")
      fun error ↦ do
        if error.isRuntime then
          throw error
        tryCatchRuntimeEx
          (Meta.check proof .all)
          fun error ↦ do
            if error.isRuntime then
              throw error
            throwError "{description} constructed ill-typed evidence"
    return proof

/-- Normalize local definitions, lambda applications, and source annotations without
unfolding numerical definitions. Finite case splits can introduce identity applications
and annotations inside indices; those do not change the proposition. -/
private def normalizeProofType (expression : Expr) : MetaM Expr := do
  let expression ← Core.betaReduce (← zetaReduce (← instantiateMVars expression))
  Core.transform expression (pre := fun expression ↦ return match expression with
    | .mdata _ body => .visit body
    | _ => .continue)

/-- Compare proof types without unfolding a numerical predicate when their normalized
syntax agrees. Kernel checking still validates the completed proof. -/
private def proofTypesAgree (lhs rhs : Expr) : MetaM Bool := do
  let lhs ← normalizeProofType lhs
  let rhs ← normalizeProofType rhs
  if lhs == rhs then
    return true
  trace[cas.validation] "Normalized proof types require definitional equality \
    (remaining elaboration heartbeats: {(← getRemainingHeartbeats) / 1000})\n\
    Certificate syntax: {lhs.dbgToString}\nGoal syntax: {rhs.dbgToString}"
  isDefEq lhs rhs

/--
Validate the completed proof assigned to a previously current goal.

The assignment is read from the original metavariable: an empty goal list alone
would not show that the action proved the same target or that its proof is
complete.
-/
def validateAssignedProof
    (description : String) (goal : MVarId) (target : Expr) : TacticM Expr :=
  goal.withContext do
    let some proof := (← getMCtx).getExprAssignmentCore? goal
      | throwError "{description} left the original goal unassigned"
    let proof ← checkCompletedProof description proof
    let proofType ← instantiateMVars (← inferType proof)
    if proofType.hasMVar ∨ proofType.hasSorry then
      throwError "{description} constructed evidence with an incomplete type"
    let target ← instantiateMVars target
    unless ← proofTypesAgree proofType target do
      throwError
        "{description} constructed a proof of{indentExpr proofType}\n\
         but the original goal is{indentExpr target}"
    return proof

/--
Assign `proof` when its type is definitionally equal to the current target.

Returning `false` leaves the tactic state unchanged. Invalid or incomplete
evidence raises an error after restoring the original state.
-/
def assignExactProof (description : String) (proof : Expr) : TacticM Bool :=
  restoringStateOnFalse do
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    let proofType ← instantiateMVars (← inferType proof)
    trace[cas.validation] "Comparing certificate and goal types"
    unless ← proofTypesAgree proofType target do
      return false
    trace[cas.validation] "Certificate and goal types agree"
    goal.assign (← checkCompletedProof description proof)
    replaceMainGoal []
    return true

/--
Run `action`, require it to close exactly the original main goal, and validate
the proof assigned to that goal.

Other goals present before the action are preserved in their original order,
and unassigned siblings must remain unassigned.
This function does not restore state on failure; use
`attemptClosingMainGoal` for a fail-closed probe or
`preservingStateOnFailure` around an elaborator entry point.
-/
def runClosingMainGoal {α : Type}
    (description : String) (action : TacticM α) :
    TacticM (ClosedMainGoal α) := do
  let goalsBefore ← getGoals
  let goal ← getMainGoal
  let unassignedSiblings ← (goalsBefore.drop 1).filterM fun sibling ↦
    return !(← sibling.isAssignedOrDelayedAssigned)
  let target ← withMainContext <| instantiateMVars (← getMainTarget)
  let value ← action
  Term.synthesizeSyntheticMVarsNoPostponing
  unless (← getGoals) == goalsBefore.drop 1 do
    throwError "{description} did not close exactly its original main goal"
  let proof ← validateAssignedProof description goal target
  -- A metavariable can remain in the goal list after its proof has been assigned.
  -- Comparing lists alone would overlook an action that also solved a sibling.
  for sibling in unassignedSiblings do
    if ← sibling.isAssignedOrDelayedAssigned then
      throwError "{description} assigned a sibling goal"
  return { value, goal, target, proof }

/--
Attempt an exact main-goal closure, restoring the complete tactic state after
ordinary failures and resource-limit exceptions. Ordinary failures are returned
as `.error`; resource-limit exceptions propagate after restoration.
-/
def attemptClosingMainGoal {α : Type}
    (description : String) (action : TacticM α) :
    TacticM (Except Exception (ClosedMainGoal α)) := do
  let saved ← saveState
  tryCatchRuntimeEx
    (return .ok (← runClosingMainGoal description action))
    fun error ↦ do
      saved.restore
      if error.isRuntime then
        throw error
      return .error error

end CAS.Tactic.ProofCarrier

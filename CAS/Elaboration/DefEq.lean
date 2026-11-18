/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public meta import Lean.Meta.GetUnfoldableConst
meta import all Lean.OriginalConstKind
public meta import Lean.Meta.Tactic.Apply
public meta import Lean.HeadIndex
public meta import Lean.Util.CollectFVars
public meta import Lean.Util.ForEachExpr
public meta import Lean.Util.ReplaceExpr
public meta import Lean.Meta.Tactic.Assumption
public meta import Lean.Elab.Tactic.Basic
public import Lean.Elab.Tactic.Basic
public import Lean.Meta.Basic

/-!
# Definitional comparison in stages

The frontends compare elaborated terms in many places: a subterm with the coordinates already
found, a type with `ℝ`, a measure with Lebesgue measure, the statement of a certificate with the
goal. `agree` is the comparison they share. It answers at the cheapest stage that can.

## Main definitions

* `agree`, `agreeGuarded`: whether two terms are definitionally equal, tried on the syntax, then
  with reducible definitions unfolded, then at the caller's transparency in the view of a
  module.
* `sealed`: whether no importing module can unfold a definition; `withModuleView` runs a check
  so that it does not unfold such a definition, `reachesSealed` tells whether a term can reach
  one at all, and `withModuleViewWhen` installs the view only then.
* `staged`, `apply`, `applyConst`: run a speculative step, such as the application of a rule, in
  the same stages.
* `abstract`: `Lean.Meta.kabstract` with `agree` as its comparison.
* `assumption`, `refl`, and the internal tactics `cas_assumption` and `cas_rfl`: close a goal by
  a hypothesis or by reflexivity, compared with `agree`.
* `cas_staged tacs`: the internal tactic that gives another closing step of a tactic script,
  such as `ac_rfl` or `fun_prop`, the same stages; `cas_sealed tacs` runs a step that is not a
  closer, such as `congr 1`, in the view of a module.

## Implementation notes

A `module` cannot unfold a definition whose body its defining module does not export. A file
outside the module system loads every body, so there Lean's unifier, at the default
transparency, unfolds the operations of `ℝ`, which Mathlib declares private, down to Cauchy
sequences, and `MeasureTheory.integral`, `Complex.exp`, `fderiv` and `nhds`, whose bodies Mathlib
does not export. A comparison of two different real terms that stops at `Real.mul` in a module
then runs for seconds, and a tactic that makes such comparisons on speculation (is this subterm
one of the coordinates, does this rule apply, does `rfl` close the goal) runs out of heartbeats.

The first stage is syntactic equality. The second is `Meta.isDefEq` at the transparency
`.reducible`. There Lean unfolds reducible definitions and still compares implicit arguments,
the instances among them, with instances unfolded, which is what makes `2 * x` written with two
elaborations of the same instance one term. The second stage is not `.instances`: on Lean
v4.36.0 a comparison at that transparency that fails on two sums of `n` terms takes time
exponential in `n`, because each addition is compared twice and the test for a natural-number
offset, a call of `Meta.isDefEq` on the instance, empties the cache of failed comparisons. The
last stage is the comparison the callers made before, at their transparency. In a module it is
unchanged. Outside a module it runs under `withModuleView`, which leaves folded the definitions
that no importing module can unfold (`sealed`):

* a private definition of an imported module;
* a public definition that its module exports without its body. Lean records these: `addDecl`
  notes the original kind of every declaration that it exports as another kind, here a
  definition exported as a constant without a value (`Lean.getOriginalConstKind?`).

Every other definition is unfolded as before: the definitions of the current file and the
exported definitions of the libraries, among them SymLean's reflected evaluators such as
`Verified.Expr.eval`. So the last stage answers outside a module as it does inside one, for a
success as for a failure, up to three approximations:

* a private definition that its module exports with its body (Mathlib does so under
  `backward.privateInPublic`) is left folded, although a module can unfold it: a file outside
  the module system has no record that tells it from a private definition that is not exported;
* Lean drops a custom unfolding predicate while it reduces the discriminants of a `match` below
  the default transparency, so a sealed reducible definition or instance can be unfolded there;
* the second stage runs without the view, so where Lean compares implicit arguments it can
  unfold a sealed instance, such as the multiplication of `ℝ`, which a module cannot.

The record is read through `import all Lean.OriginalConstKind`, since Lean offers no public
query for a file outside the module system. It is an implementation detail of Lean: the first
check of `tests/kinds/Cases.lean` fails when it no longer says what a module can unfold.

Lean keeps no `whnf` cache and no permanent `isDefEq` cache while a custom unfolding predicate is
set. A comparison whose terms cannot reach a sealed definition (`reachesSealed`), such as
`Nat.fib 20 = 6765`, is a computation and runs without the predicate, with Lean's caches
(`withModuleViewWhen`). `withModuleView` is for one comparison or one short step and should not
enclose an evaluation. Without the cache a comparison in the view that fails on two terms with
the same deep nesting of functions tries the arguments again at every level, so its time grows
exponentially with the depth (two compositions of seven elementary functions: 34 M heartbeats,
against 0.15 M in a module).
-/

public meta section

namespace CAS.Elaboration.DefEq

open Lean Meta

/-- Whether `name` is a private declaration of an imported module that uses the module system. An
importing `module` does not see it, unless its module exports it under
`backward.privateInPublic`, which a file outside the module system cannot tell. -/
def hidden (env : Environment) (name : Name) : Bool :=
  isPrivateName name &&
    match env.getModuleIdxFor? name with
    | some index => env.header.moduleData[index.toNat]?.any (·.isModule)
    | none => false

/-- Whether `name` is an imported definition that its module exports without its body, by Lean's
record of the declarations exported as another kind than they were declared. The record is read
for imported names only: for a name of the current file it is extension state, which must not be
read during instance resolution. -/
def exportedWithoutBody (env : Environment) (name : Name) : Bool :=
  env.isImportedConst name &&
    privateConstKindsExt.find? (asyncMode := .local) env name matches some .defn

/-- Whether the view of a module leaves `name` folded: a `hidden` declaration, or a definition
that is `exportedWithoutBody`. -/
def sealed (env : Environment) (name : Name) : Bool :=
  hidden env name || exportedWithoutBody env name

/-- Lean's rule for which constants `whnf` and `isDefEq` unfold, without the `sealed` ones. -/
def canUnfold (config : Meta.Config) (info : ConstantInfo) : CoreM Bool := do
  if sealed (← getEnv) info.name then
    return false
  match config.canUnfoldPredicateConfig with
  | .default => canUnfoldDefault config info
  | .atMatcher => canUnfoldAtMatcher config info

/-- Run `action`, one comparison or one short closing step, in the view of a module: a `sealed`
definition is not unfolded. In a `module` nothing changes: its environment does not hold those
bodies. Lean keeps no `whnf` cache under a custom unfolding predicate, so `action` should not
evaluate anything large. Lean itself drops the predicate while it reduces the discriminants of a
`match` below the default transparency, so a sealed reducible definition or instance can still
be unfolded there. -/
def withModuleView {n : Type → Type} {α : Type} [MonadControlT MetaM n] [Monad n] [MonadEnv n]
    (action : n α) : n α := do
  if (← getEnv).header.isModule then
    action
  else
    withCanUnfoldPred canUnfold action

/-- The imported constants already known to reach, or not to reach, a sealed definition. An entry
is read only for a constant that the current environment imports. -/
initialize reachCache : IO.Ref (Std.HashMap Name Bool) ← IO.mkRef {}

/-- Whether unfolding the definition `root`, and those in its body in turn, can reach a `sealed`
definition. The search walks the bodies of definitions (not of theorems, whose proofs are never
unfolded), each constant once, and remembers its answers for imported constants. -/
def reachesSealedFrom (root : Name) : MetaM Bool := do
  let env ← getEnv
  let known ← reachCache.get
  let recorded? (name : Name) : Option Bool :=
    if env.isImportedConst name then known[name]? else none
  if let some answer := recorded? root then
    return answer
  -- Answers found in this walk.
  let mut fresh : Std.HashMap Name Bool := {}
  -- The constants whose bodies the walk has entered, finished or not.
  let mut entered : NameSet := {}
  -- Whether the walk met a constant whose body it had not finished: a definition that names
  -- itself, as the compiled form of a `partial def` does.
  let mut looped := false
  -- The path from `root` to the constant being examined, each with its constants still to visit.
  let mut path : Array (Name × List Name) := #[(root, [root])]
  let mut found := false
  while !found do
    let some (name, pending) := path.back? | break
    match pending with
    | [] =>
        path := path.pop
        fresh := fresh.insert name false
    | next :: rest =>
        path := path.pop.push (name, rest)
        match fresh[next]? <|> recorded? next with
        | some true => found := true
        | some false => pure ()
        | none =>
            if entered.contains next then
              looped := true
            else
              entered := entered.insert next
              -- The kind is known at once, also for a declaration that is still being elaborated.
              match env.findAsync? next with
              | some info =>
                  if !(info.kind matches .defn) then
                    fresh := fresh.insert next false
                  else if sealed env next then
                    fresh := fresh.insert next true
                    found := true
                  else if let .defnInfo definition := info.toConstantInfo then
                    path := path.push (next, definition.value.getUsedConstants.toList)
                  else
                    fresh := fresh.insert next false
              | none => fresh := fresh.insert next false
  if found then
    -- Every constant on the path reaches the sealed definition.
    fresh := path.foldl (fun fresh (name, _) ↦ fresh.insert name true) fresh
  -- After a loop, a constant finished before the sealed definition was found may reach it
  -- through the constant it looped to, so only the positive answers are kept.
  let answers := fresh.toArray.filter fun (name, answer) ↦
    env.isImportedConst name && (answer || !(found && looped))
  unless answers.isEmpty do
    reachCache.modify fun cache ↦
      answers.foldl (fun cache (name, answer) ↦ cache.insert name answer) cache
  return found

/-- Whether unfolding can reach a `sealed` definition from the constants that `terms` mention.
Lean unfolds a `let`-bound local variable and reduces types on the way, so the types and values
of the local variables that the terms mention, and of those these mention in turn, count as
well. -/
def reachesSealed (terms : Array Expr) : MetaM Bool := do
  let lctx ← getLCtx
  let mut seen : FVarIdSet := {}
  let mut pending := terms.toList
  while true do
    let term :: rest := pending | break
    pending := rest
    let term ← instantiateMVars term
    if ← term.getUsedConstants.anyM reachesSealedFrom then
      return true
    for fvarId in (collectFVars {} term).fvarIds do
      unless seen.contains fvarId do
        seen := seen.insert fvarId
        if let some declaration := lctx.find? fvarId then
          pending := declaration.type :: (declaration.value?.toList ++ pending)
  return false

/-- `reachesSealed` for a step on `goal`: its target, every hypothesis of its context, and
`others`, such as the statement of a rule that the step applies. -/
def goalReachesSealed (goal : MVarId) (others : Array Expr := #[]) : MetaM Bool :=
  goal.withContext do
    let mut terms := others.push (← goal.getType)
    for declaration in ← getLCtx do
      unless declaration.isImplementationDetail do
        terms := terms.push declaration.type
    reachesSealed terms

/-- `withModuleView action` when `reaches` holds, and `action` as written otherwise, so that it
keeps Lean's caches. `reaches` tells whether what `action` compares can reach a sealed definition
(`reachesSealed`, `goalReachesSealed`). In a `module` this is `action`, and `reaches` is not
run. -/
def withModuleViewWhen {n : Type → Type} {α : Type} [MonadControlT MetaM n] [Monad n]
    [MonadEnv n] [MonadLiftT MetaM n] (reaches : MetaM Bool) (action : n α) : n α := do
  if (← getEnv).header.isModule then
    action
  else if ← reaches then
    withModuleView action
  else
    action

/-- `Meta.isDefEq` at the caller's transparency as a file inside the module system would run it:
unchanged in a module and for terms that cannot reach a sealed definition, in the view of a
module otherwise. -/
def isDefEqInModuleView (lhs rhs : Expr) : MetaM Bool :=
  withModuleViewWhen (reachesSealed #[lhs, rhs]) (isDefEq lhs rhs)

/-- Whether `lhs` and `rhs` are definitionally equal: by their syntax, else with reducible
definitions unfolded, else at the caller's transparency in the view of a module
(`isDefEqInModuleView`). Below the default transparency the caller's own setting is the only
stage after the syntax. Metavariables are assigned as `Meta.isDefEq` assigns them. -/
def agree (lhs rhs : Expr) : MetaM Bool := do
  if lhs == rhs then
    return true
  unless (← getTransparency) matches .default | .all do
    return ← isDefEq lhs rhs
  if ← withTransparency .reducible <| isDefEq lhs rhs then
    return true
  isDefEqInModuleView lhs rhs

/-- `agree`, with `false` for a comparison that throws an ordinary error. -/
def agreeGuarded (lhs rhs : Expr) : MetaM Bool := do
  try agree lhs rhs catch _ => return false

/-- Replace every subterm of `e` that agrees with `pattern` (`agree`) by the loose bound
variable `0`, as `Lean.Meta.kabstract` does with `Meta.isDefEq` for all occurrences. Only
subterms without loose bound variables that have the head and the number of arguments of
`pattern` are compared, and a subterm that agrees is not searched further. Each distinct subterm
is compared once, where `kabstract` compares every occurrence again; the two differ only when a
comparison assigns a metavariable that changes the answer for a subterm compared before. -/
def abstract (e pattern : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let pattern ← instantiateMVars pattern
  if pattern.isFVar then
    return e.abstract #[pattern]
  let head := pattern.toHeadIndex
  let arity := pattern.headNumArgs
  -- Whether to go on into the subterms of `term`; the answer of each comparison is recorded.
  let visit (term : Expr) : StateRefT (Std.HashMap Expr Bool) MetaM Bool := do
    if term.hasLooseBVars || term.toHeadIndex != head || term.headNumArgs != arity then
      return true
    if let some answer := (← get)[term]? then
      return !answer
    let answer ← agree term pattern
    modify (·.insert term answer)
    return !answer
  let (_, answers) ← (e.forEach' visit).run {}
  let marker := mkFVar (← mkFreshFVarId)
  return (e.replace fun term ↦ if answers.getD term false then some marker else none).abstract
    #[marker]

/-- Run `action`, a closing or matching step on `goal` that is tried on speculation, in the stages
of `agree`: with reducible definitions unfolded only and, when that throws, once more at the
caller's transparency, in the view of a module when the goal or one of `others`, the other terms
that the step compares, can reach a sealed definition (`goalReachesSealed`). The state is
restored between the two attempts. -/
def staged {α : Type} (goal : MVarId) (action : MetaM α) (others : Array Expr := #[]) :
    MetaM α := do
  unless (← getTransparency) matches .default | .all do
    return ← action
  let saved ← saveState
  try
    withTransparency .reducible action
  catch _ =>
    saved.restore
    withModuleViewWhen (goalReachesSealed goal others) action

/-- Apply `rule` to `goal` in the stages of `staged`: a rule that is tried on speculation and
does not fit is refused where a module would refuse it. -/
def apply (goal : MVarId) (rule : Expr) : MetaM (List MVarId) := do
  staged goal (goal.apply rule) #[← goal.withContext <| inferType rule]

/-- `apply` for the constant `name`. -/
def applyConst (goal : MVarId) (name : Name) : MetaM (List MVarId) := do
  staged goal (goal.applyConst name) #[(← getConstInfo name).type]

/-- Close `goal` by a hypothesis whose type agrees with it (`agree`), the latest one first, as
`Lean.MVarId.assumptionCore` does with `Meta.isDefEq`. Returns whether it closed the goal. -/
def assumption (goal : MVarId) : MetaM Bool :=
  goal.withContext do
    goal.checkNotAssigned `assumption
    let type ← goal.getType
    let found? ← (← getLCtx).findDeclRevM? fun declaration ↦ do
      if declaration.isImplementationDetail then
        return none
      else if ← agree type declaration.type then
        return some declaration.fvarId
      else
        return none
    match found? with
    | none => return false
    | some fvarId => goal.assign (mkFVar fvarId); return true

/-- Close `goal`, an equality `a = b`, by `Eq.refl a` when its sides agree (`agree`). Returns
whether it closed the goal; `false` also for a goal that is not an equality. -/
def refl (goal : MVarId) : MetaM Bool :=
  goal.withContext do
    goal.checkNotAssigned `rfl
    let some (_, lhs, rhs) := (← whnfR (← instantiateMVars (← goal.getType))).eq? | return false
    -- As `rfl`: the approximations of `Lean.MVarId.applyRfl`, and synthetic opaque metavariables
    -- may be assigned, as `eq_refl` allows after `refine`.
    unless ← withAssignableSyntheticOpaque <| approxDefEq <| agreeGuarded lhs rhs do
      return false
    goal.assign (← mkEqRefl lhs)
    return true

open Elab Tactic in
/--
`cas_assumption` closes the main goal by a hypothesis, as `assumption` does, with each
comparison made in the stages of `CAS.Elaboration.DefEq.agree`: the syntax, then reducible
definitions, then the default transparency in the view of a module. A goal that `assumption`
closes in a `module` is closed by `cas_assumption` there as well, and a goal that no hypothesis
proves is left without unfolding the real numbers. The frontends of SymLean use it in their
tactic scripts; it is not a documented form of `cas`.
-/
syntax (name := casAssumption) "cas_assumption" : tactic

open Elab Tactic in
elab_rules : tactic
  | `(tactic| cas_assumption) => do
    let goal ← getMainGoal
    -- Synthetic opaque metavariables may be assigned, as in `assumption` after `refine`.
    unless ← withAssignableSyntheticOpaque <| assumption goal do
      throwTacticEx `cas_assumption goal
    replaceMainGoal []

open Elab Tactic in
/--
`cas_staged tacs` runs the closing step `tacs` of a tactic script in the stages of
`CAS.Elaboration.DefEq.agree`: first with reducible definitions unfolded only and without error
recovery and, when that fails, once more at the surrounding transparency, in the view of a
module when the main goal or one of its hypotheses can reach a sealed definition (the terms
inside `tacs` are not looked at). A step that `tacs` proves at the default transparency in a
`module` is proved by `cas_staged tacs` there as well. Like `try`, it takes a tactic sequence:
`cas_staged t; u` runs `t; u` in stages, and `(cas_staged t); u` only `t`.

It is meant for steps that a script tries on speculation and that compare terms by definitional
unfolding: `ac_rfl`, the application of a rule that may not fit (`apply`), and `fun_prop`, whose
rules are applied the same way. Outside the module system such a comparison, when it fails,
would unfold the operations of `ℝ` down to Cauchy sequences, or `nhds` down to its infimum. The
frontends of SymLean use it; it is not a documented form of `cas`.
-/
syntax (name := casStaged) "cas_staged " tacticSeq : tactic

open Elab Tactic in
elab_rules : tactic
  | `(tactic| cas_staged $tactics:tacticSeq) => do
    unless (← getTransparency) matches .default | .all do
      return ← evalTactic tactics
    let saved ← saveState
    try
      -- Without error recovery, as in `first`: an elaboration error must end this attempt, not
      -- be logged and recovered from.
      withoutRecover <| withTransparency .reducible <| evalTactic tactics
    catch _ =>
      saved.restore (restoreInfo := true)
      withModuleViewWhen (goalReachesSealed (← getMainGoal)) (evalTactic tactics)

open Elab Tactic in
/--
`cas_sealed tacs` runs `tacs` in the view of a module (`CAS.Elaboration.DefEq.withModuleView`)
when the main goal or one of its hypotheses can reach a definition that no importing module can
unfold, and as written otherwise. In a `module` it is `tacs`. Like `try`, it takes a tactic
sequence.

It is meant for a short step of a tactic script that is not a closer but compares terms by
definitional unfolding on the way, such as `congr 1`, which tries reflexivity on the goals it
produces. The frontends of SymLean use it; it is not a documented form of `cas`.
-/
syntax (name := casSealed) "cas_sealed " tacticSeq : tactic

open Elab Tactic in
elab_rules : tactic
  | `(tactic| cas_sealed $tactics:tacticSeq) => do
    withModuleViewWhen (goalReachesSealed (← getMainGoal)) (evalTactic tactics)

open Elab Tactic in
/--
`cas_rfl` closes the main goal by reflexivity, as `rfl` does. The two sides of an equality are
compared in the stages of `CAS.Elaboration.DefEq.agree`: the syntax, then reducible definitions,
then the default transparency in the view of a module. Another reflexive relation goes to
`cas_staged rfl`. A goal that `rfl` closes in a `module` is closed by `cas_rfl` there as well,
and a goal that does not hold by reflexivity is left without unfolding the real numbers. The
frontends of SymLean use it in their tactic scripts; it is not a documented form of `cas`.
-/
syntax (name := casRfl) "cas_rfl" : tactic

open Elab Tactic in
elab_rules : tactic
  | `(tactic| cas_rfl) => do
    let goal ← getMainGoal
    let target ← goal.withContext do whnfR (← instantiateMVars (← goal.getType))
    if target.eq?.isSome then
      unless ← refl goal do
        throwTacticEx `cas_rfl goal "the two sides are not definitionally equal"
      replaceMainGoal []
    else
      evalTactic (← `(tactic| cas_staged rfl))

end CAS.Elaboration.DefEq

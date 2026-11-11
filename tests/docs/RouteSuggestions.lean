/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS

/-!
# The suggestions of `cas?` for registered routes

A route registered with `@[cas_route]` returns, with its proof, the call that `cas?` suggests.
`cas?` runs that call on the original goal and suggests it only when it closes that goal with a
complete proof; otherwise it suggests the call that ran. The three routes of this file are
registered here and nowhere else, each for goals of its own.
-/

open Lean Elab Tactic CAS.Tactic.RouteRegistry

/-- The goal of `replayedRoute`. -/
def ReplayedGoal (n : ℕ) : Prop := n + 0 = n

theorem replayedGoal (n : ℕ) : ReplayedGoal n := Nat.add_zero n

/-- Whether the goal is `ReplayedGoal n`. -/
def isReplayedGoal : GoalPredicate := fun target ↦
  return target.consumeMData.isAppOfArity ``ReplayedGoal 1

/-- A route whose suggested call is the one it ran. -/
@[cas_route replayedRoute (priority := 3000) (goal := isReplayedGoal)]
def replayedRoute : Closer := fun _ ↦ do
  let replay ← `(tactic| exact $(mkIdent ``replayedGoal) _)
  evalTactic replay
  return { replay := replay }

/--
info: Try this:
  [apply] exact replayedGoal _

Lean checked the suggested replacement against the original goal. Selected route: CAS route: replayedRoute.
-/
#guard_msgs in
example (n : ℕ) : ReplayedGoal n := by
  cas?

example (n : ℕ) : ReplayedGoal n := by
  exact replayedGoal _

/-- The goal of `misreplayedRoute`. -/
def MisreplayedGoal (n : ℕ) : Prop := n + 0 = n

theorem misreplayedGoal (n : ℕ) : MisreplayedGoal n := Nat.add_zero n

/-- Whether the goal is `MisreplayedGoal n`. -/
def isMisreplayedGoal : GoalPredicate := fun target ↦
  return target.consumeMData.isAppOfArity ``MisreplayedGoal 1

/-- A route that proves `MisreplayedGoal n` but suggests a call that proves only
`MisreplayedGoal 0`. -/
@[cas_route misreplayedRoute (priority := 3000) (goal := isMisreplayedGoal)]
def misreplayedRoute : Closer := fun _ ↦ do
  evalTactic (← `(tactic| exact $(mkIdent ``misreplayedGoal) _))
  return { replay := ← `(tactic| exact $(mkIdent ``misreplayedGoal) 0) }

-- The call the route suggests fails on the goal, so `cas?` suggests the call that ran.
/--
info: Try this:
  [apply] cas

Lean checked the suggested replacement against the original goal. Selected route: CAS route: misreplayedRoute.
-/
#guard_msgs in
example (n : ℕ) : MisreplayedGoal n := by
  cas?

example (n : ℕ) : MisreplayedGoal n := by
  cas

/-- The goal of `openReplayRoute`. -/
def OpenReplayGoal (n : ℕ) : Prop := n + 0 = n

theorem openReplayGoal (n : ℕ) : OpenReplayGoal n := Nat.add_zero n

/-- Whether the goal is `OpenReplayGoal n`. -/
def isOpenReplayGoal : GoalPredicate := fun target ↦
  return target.consumeMData.isAppOfArity ``OpenReplayGoal 1

/-- A route that proves `OpenReplayGoal n` but suggests a call that leaves the goal open. -/
@[cas_route openReplayRoute (priority := 3000) (goal := isOpenReplayGoal)]
def openReplayRoute : Closer := fun _ ↦ do
  evalTactic (← `(tactic| exact $(mkIdent ``openReplayGoal) _))
  return { replay := ← `(tactic| skip) }

-- The call the route suggests runs without an error but does not close the goal.
/--
info: Try this:
  [apply] cas using [Nat.add_zero n]

Lean checked the suggested replacement against the original goal. Selected route: CAS route: openReplayRoute.
-/
#guard_msgs in
example (n : ℕ) : OpenReplayGoal n := by
  cas? using [Nat.add_zero n]

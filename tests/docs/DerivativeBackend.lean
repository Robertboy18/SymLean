/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS

/-!
# A registered derivative backend

SymLean defines no derivative backend: a package with Euclidean derivative operators registers
one with `@[cas_derivative_backend]` (`CAS/Tactic/DerivativeRegistry.lean`). So nothing in the
library runs the attribute, which declares a tactic adapter for the backend, or the dispatch
through the internal tactic `cas_derivative_dispatch`. This file registers a backend for one
proposition, `Marked`, and checks that `cas` does not prove `Marked` before the registration,
that the adapter exists with its docstring, that the registry passes a request to the backend
and returns its answer, and that `cas` then proves `Marked`. A backend must stay out of the
library, where a second one is an error, so the test is here.
-/

open Lean Elab Tactic CAS.Tactic.DerivativeRegistry

/-- A proposition that only the backend below recognizes. -/
@[irreducible] def Marked : Prop := True

/-- `Marked` holds. -/
theorem marked : Marked := by
  unfold Marked
  trivial

/-- Without a backend `cas` does not prove `Marked`. -/
example : Marked := by
  fail_if_success cas
  exact marked

/-- A backend whose only goal is `Marked`, which it closes with `marked`. -/
@[cas_derivative_backend]
def markedBackend : Backend := fun
  | .isGoal target => return .matches (target.isConstOf ``Marked)
  | .isTerm _ => return .matches false
  | .close _ => do
    evalTactic (← `(tactic| exact marked))
    return .closed
  | _ => throwError "this backend has no equations"

/-- info: Internal tactic adapter for the derivative backend `markedBackend`. -/
#guard_msgs in
run_meta do
  let some doc ← findDocString? (← getEnv) ``markedBackend.casDerivativeTactic
    | throwError "the attribute declared no adapter with a docstring"
  logInfo doc

/-- info: Marked: true, True: false -/
#guard_msgs in
run_elab do
  let goal ← Meta.mkFreshExprMVar (mkConst ``True)
  discard <| Tactic.run goal.mvarId! do
    logInfo m!"Marked: {← isGoal (mkConst ``Marked)}, True: {← isGoal (mkConst ``True)}"

example : Marked := by cas

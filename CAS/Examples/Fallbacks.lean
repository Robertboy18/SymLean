/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
import Mathlib.Tactic.NormNum.Prime

/-!
# Determinants, general fallbacks, and resource limits of bare `cas`

Bare `cas` evaluates determinants of matrix literals with Mathlib's `norm_det` before its other
routes, and, before it reports failure, tries `norm_num` on a proposition without variables and
core `grind`, each under the heartbeat budget `cas.grindHeartbeats`. The examples check these
routes, their refusals of false statements, and the messages for exhausted budgets. The
primality examples need `Mathlib.Tactic.NormNum.Prime`, the `norm_num` extension for `Nat.Prime`:
the fallback uses the extensions in the importing file's environment.
-/

namespace CAS.Examples.Fallbacks

/-! ## Determinants of matrix literals -/

example : Matrix.det !![(-1 : ℤ), -1, -2, 3, 0; -2, 4, 0, -5, 1; -4, 1, -2, -1, 0;
    -1, 4, -1, 4, 0; -5, 4, 1, -5, -3] = 228 := by
  cas

/-- A symbolic determinant becomes a polynomial identity. -/
example (a b c : ℝ) :
    Matrix.det !![1, a, a ^ 2; 1, b, b ^ 2; 1, c, c ^ 2] = (b - a) * (c - a) * (c - b) := by
  cas

/-- A wrong value is refused. -/
example : True := by
  fail_if_success have : Matrix.det !![(1 : ℤ), 2; 3, 4] = 2 := by cas
  trivial

/-! ## `grind` and `norm_num` -/

-- The denominator `x ^ 2 - 1` is nonzero because both of its factors are.
set_option maxHeartbeats 0 in -- the fallback keeps its own budget under an unlimited one
example (x : ℝ) (h₁ : x - 1 ≠ 0) (h₂ : x + 1 ≠ 0) :
    1 / (x - 1) - 1 / (x + 1) = 2 / (x ^ 2 - 1) := by
  cas

example (x : ℝ) (h₁ : x - 1 ≠ 0) (h₂ : x + 1 ≠ 0) :
    (x ^ 3 - 1) / (x ^ 2 - 1) = (x ^ 2 + x + 1) / (x + 1) := by
  cas

example : Nat.Prime 1000003 := by
  cas

/-- A computed large prime is not handed to `norm_num`, whose trial division would run for
minutes without consuming heartbeats; `cas` refuses it at once. -/
example : True := by
  fail_if_success have : Nat.Prime (2 ^ 61 - 1) := by cas
  fail_if_success have : Nat.Prime ((0 ^ 0 + 1) ^ 61 - 1) := by cas
  trivial

/-- Lean's `x / x` is `0` at `x = 0`, so the identity is refused without a hypothesis. -/
example (x : ℝ) : x = x := by
  fail_if_success have : x / x = 1 := by cas
  rfl

/-! ## Budgets and limits -/

/-- With the fallbacks disabled the gcd cancellation is out of reach of the earlier routes. -/
example (x : ℝ) : x = x := by
  fail_if_success
    have : x - 1 ≠ 0 → x + 1 ≠ 0 → (x ^ 3 - 1) / (x ^ 2 - 1) = (x ^ 2 + x + 1) / (x + 1) := by
      intro _ _
      set_option cas.grindHeartbeats 0 in cas
  rfl

-- The exhausted budget of `grind` is named in the report.
/--
grind did not finish within its budget of 1 thousand heartbeats
-/
#guard_msgs (error, substring := true) in
set_option cas.grindHeartbeats 1 in
example (x : ℝ) (h₁ : x - 1 ≠ 0) (h₂ : x + 1 ≠ 0) :
    (x ^ 3 - 1) / (x ^ 2 - 1) = (x ^ 2 + x + 1) / (x + 1) := by
  cas

-- `cas` acts on the main goal only; the other goals are left as they were, also when the
-- determinant evaluation alone closes the main goal.
set_option linter.style.multiGoal false in -- `cas` runs with a sibling goal open
example : Matrix.det !![(2 : ℤ), 1; 1, 2] = 3 ∧ True := by
  refine ⟨?_, ?_⟩
  cas
  trivial

/-- Exhausting the recursion depth is an ordinary failure of `cas`, not Lean's raw runtime error,
which `fail_if_success` would not catch. -/
example (x : ℝ) (h₁ : x - 1 ≠ 0) (h₂ : x + 1 ≠ 0) :
    1 / (x - 1) - 1 / (x + 1) = 2 / (x ^ 2 - 1) := by
  fail_if_success set_option maxRecDepth 12 in cas
  grind

/--
error: cas exceeded Lean's maximum recursion depth (the option maxRecDepth is 12
-/
#guard_msgs (error, substring := true) in
example (x : ℝ) (h₁ : x - 1 ≠ 0) (h₂ : x + 1 ≠ 0) :
    1 / (x - 1) - 1 / (x + 1) = 2 / (x ^ 2 - 1) := by
  set_option maxRecDepth 12 in cas

end CAS.Examples.Fallbacks

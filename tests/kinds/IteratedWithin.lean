/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS

/-! # Side conditions for iterated derivatives within a set -/

#guard_msgs in
theorem iteratedLogIco (x : ℝ) (_hx : x ∈ Set.Ico 1 2) (_hp : 0 < x) :
    iteratedDerivWithin 2 Real.log (Set.Ico 1 2) x = -(x ^ 2)⁻¹ := by
  cas

#guard_msgs in
theorem iteratedLogIoc (x : ℝ) (_hx : x ∈ Set.Ioc 1 2) (_hp : 0 < x) :
    iteratedDerivWithin 2 Real.log (Set.Ioc 1 2) x = -(x ^ 2)⁻¹ := by
  cas

/-- depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info, substring := true) in
#print axioms iteratedLogIco

/-- depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info, substring := true) in
#print axioms iteratedLogIoc

/--
error: cas could not prove unique differentiability on the set
  UniqueDiffOn ℝ s
-/
#guard_msgs in
example (x : ℝ) (s : Set ℝ) (_hx : x ∈ s) (_hp : 0 < x) :
    iteratedDerivWithin 2 Real.log s x = -(x ^ 2)⁻¹ := by
  cas

/--
error: cas could not prove unique differentiability on the set
  UniqueDiffOn ℝ (Set.Icc 1 1)
-/
#guard_msgs in
example : iteratedDerivWithin 2 (fun x : ℝ ↦ x ^ 2) (Set.Icc (1 : ℝ) 1) 1 = 2 := by
  cas

/--
error: cas could not prove that the point lies in the set
  x ∈ Set.Ico 1 2
-/
#guard_msgs in
example (x : ℝ) (_hp : 0 < x) :
    iteratedDerivWithin 2 Real.log (Set.Ico 1 2) x = -(x ^ 2)⁻¹ := by
  cas

/--
error: cas could not prove smoothness at the point
  ContDiffAt ℝ (↑2) f x
-/
#guard_msgs in
example (f : ℝ → ℝ) (x : ℝ) : iteratedDerivWithin 2 f Set.univ x = 1 := by
  cas

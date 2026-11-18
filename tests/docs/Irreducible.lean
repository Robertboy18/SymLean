/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS
import CAS.Irreducible

/-!
# The compatibility import keeps real arithmetic irreducible outside the module system

This file is not a `module`, so Lean loads the body of every imported definition, among them
the operations of `ℝ` and the other definitions that Mathlib hides from modules with
`@[no_expose]`. `CAS.Irreducible`, which `import CAS` does not load, keeps them irreducible here
as well. Without it the first test prints `Real.ofCauchy` and runs out of recursion depth. The
tactics of SymLean do not depend on it (`tests/kinds`); the integral below is proved with it to
check that they also work in a file that imports it.
-/

open Lean Meta

/--
info: Real.mul; false
-/
#guard_msgs in
run_meta do
  withLocalDeclD `x (mkConst ``Real) fun x ↦ do
    -- `whnf` of a product stops at the multiplication of `ℝ`.
    let head := (← whnfD (← mkAppM ``HMul.hMul #[x, x])).getAppFn
    -- A product of 201 factors is compared with a variable within the default recursion depth.
    let mut product := x
    for _ in [1:201] do
      product ← mkAppM ``HMul.hMul #[product, x]
    logInfo m!"{privateToUserName head.constName!}; {← isDefEq product x}"

/--
info: true
-/
#guard_msgs in
run_meta do
  let names := [``MeasureTheory.integral, ``Complex.exp, ``fderiv, ``nhds, ``tprod,
    ``Polynomial.eval₂]
  logInfo m!"{← names.allM fun name ↦ isIrreducible name}"

/-- The integral of the README, proved in a file outside the module system. -/
theorem integral_x_exp : ∫ x in (0 : ℝ)..1, x * Real.exp x = 1 := by
  cas

/--
info: 'integral_x_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms integral_x_exp

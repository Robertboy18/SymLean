/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS
import CAS.Elaboration.DefEq

/-!
# The frontends inside and outside the module system

`run.sh` elaborates this file twice: as it is written, a file outside the module system, and as
a `module` (with `module` in front and the imports turned into `public import CAS` and
`meta import CAS.Elaboration.DefEq`). Every `#guard_msgs` must hold in both.

A file outside the module system loads the body of every imported definition, among them the
operations of `ℝ`, which Mathlib declares private, and the definitions that Mathlib exports
without their body (`MeasureTheory.integral`, `Complex.exp`, `fderiv`, `nhds`). The goals and
commands below are the ones that ran out of heartbeats or of recursion depth in such a file on
Mathlib v4.36.0 before the frontends compared terms in stages (`CAS.Elaboration.DefEq`), together
with goals that must still be refused, with the same message. `CAS.Irreducible` is not imported.
-/

open Lean Meta CAS.Elaboration

/-! ## What a module can unfold -/

/--
info: sealed: [nhds, MeasureTheory.integral, Complex.exp, fderiv, Real.instMul]
unfolded: [Real.exp, Set.Icc, intervalIntegral, CAS.Verified.Expr.eval]
-/
#guard_msgs in
run_meta do
  let env ← getEnv
  let names := [``nhds, ``MeasureTheory.integral, ``Complex.exp, ``fderiv, ``Real.instMul,
    ``Real.exp, ``Set.Icc, ``intervalIntegral, ``CAS.Verified.Expr.eval]
  logInfo m!"sealed: {names.filter (DefEq.sealed env)}\n\
    unfolded: {names.filter (!DefEq.sealed env ·)}"

/--
info: x * x in the view of a module: Real.instMul.1 x x
-/
#guard_msgs in
run_meta do
  withLocalDeclD `x (mkConst ``Real) fun x ↦ do
    let product ← mkAppM ``HMul.hMul #[x, x]
    logInfo m!"x * x in the view of a module: {← DefEq.withModuleView <| whnfD product}"

/-! ## Comparisons that fail must fail early -/

/--
info: a product of 201 factors against a variable: false
x * y against y * x: false
exp x against exp (x + 1): false
two integrals with different integrands: false
two local definitions with those integrals as values: false
two sums of 24 terms that differ in the first: false
-/
#guard_msgs in
set_option maxHeartbeats 20000 in
run_meta do
  withLocalDeclD `x (mkConst ``Real) fun x ↦ withLocalDeclD `y (mkConst ``Real) fun y ↦ do
    let mut product := x
    for _ in [1:201] do
      product ← mkAppM ``HMul.hMul #[product, x]
    let xy ← mkAppM ``HMul.hMul #[x, y]
    let yx ← mkAppM ``HMul.hMul #[y, x]
    let exp ← mkAppM ``Real.exp #[x]
    let shifted ← mkAppM ``Real.exp #[← mkAppM ``HAdd.hAdd #[x, ← mkNumeral (mkConst ``Real) 1]]
    let zero ← mkNumeral (mkConst ``Real) 0
    let volume ← mkAppOptM ``MeasureTheory.MeasureSpace.volume #[some (mkConst ``Real), none]
    let integral (body : Expr) : MetaM Expr := do
      mkAppOptM ``intervalIntegral #[none, none, none,
        some (← mkLambdaFVars #[x] body), some zero, some y, some volume]
    let integralXY ← integral xy
    let integralYX ← integral yx
    -- The comparison looks through local definitions, so their values count as well.
    let locals ← withLetDecl `u (mkConst ``Real) integralXY fun u ↦
      withLetDecl `v (mkConst ``Real) integralYX fun v ↦ DefEq.agree u v
    -- With instances unfolded Lean compares each addition twice: 2 ^ 23 comparisons here.
    let mut sumX := x
    let mut sumY := y
    for _ in [1:24] do
      sumX ← mkAppM ``HAdd.hAdd #[sumX, x]
      sumY ← mkAppM ``HAdd.hAdd #[sumY, x]
    logInfo m!"a product of 201 factors against a variable: {← DefEq.agree product x}\n\
      x * y against y * x: {← DefEq.agree xy yx}\n\
      exp x against exp (x + 1): {← DefEq.agree exp shifted}\n\
      two integrals with different integrands: {← DefEq.agree integralXY integralYX}\n\
      two local definitions with those integrals as values: {locals}\n\
      two sums of 24 terms that differ in the first: {← DefEq.agree sumX sumY}"

/-! ## Comparisons that hold by unfolding must still hold -/

/-- A definition of this file, which the comparisons unfold. -/
noncomputable def shiftOne (x : ℝ) : ℝ := x + 1

/--
info: a definition of this file against its body: true
Real.cosh against its body: true
Nat.fib 20 against 6765: true
-/
#guard_msgs in
run_meta do
  withLocalDeclD `x (mkConst ``Real) fun x ↦ do
    let one ← mkNumeral (mkConst ``Real) 1
    let body ← mkAppM ``HAdd.hAdd #[x, one]
    let cosh ← mkAppM ``Real.cosh #[x]
    let complex ← mkAppM ``Complex.re #[← mkAppM ``Complex.cosh #[← mkAppM ``Complex.ofReal #[x]]]
    let fib ← mkAppM ``Nat.fib #[mkNatLit 20]
    logInfo m!"a definition of this file against its body: \
      {← DefEq.agree (← mkAppM ``shiftOne #[x]) body}\n\
      Real.cosh against its body: {← DefEq.agree cosh complex}\n\
      Nat.fib 20 against 6765: {← DefEq.agree fib (mkNatLit 6765)}"

/-! ## The search for sealed definitions ends on a definition that names itself -/

/-- A definition whose compiled form names itself. -/
partial def spin (n : ℕ) : ℕ := spin (n + 1)

/--
info: the compiled form of spin reaches a sealed definition: false
-/
#guard_msgs in
run_meta do
  logInfo m!"the compiled form of spin reaches a sealed definition: \
    {← DefEq.reachesSealedFrom ((``spin).str "_unsafe_rec")}"

/-! ## The goals that ran out of heartbeats -/

/-- The integral of the README. -/
theorem integral_x_exp : ∫ x in (0 : ℝ)..1, x * Real.exp x = 1 := by
  cas

-- In a module the theorem is private and printed with its private name, hence the substring.
/--
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (info, substring := true) in
#print axioms integral_x_exp

example (a b : ℝ) :
    ∫ (x : ℝ) in a..b, x * Real.exp x = Real.exp b * (b - 1) - Real.exp a * (a - 1) := by
  cas

example (a b : ℝ) (h : ∀ t ∈ Set.uIcc a b, t ≠ 0) :
    (∫ t in a..b, Real.log t / t) = Real.log b ^ 2 / 2 - Real.log a ^ 2 / 2 := by
  cas using h

example (a b : ℝ) (hpositive : ∀ t ∈ Set.uIcc a b, 0 < t) :
    (∫ t in a..b, 1 / t) = Real.log b - Real.log a := by
  cas using hpositive

example (a b : ℝ) (h : a ^ 2 + b ^ 2 ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.exp (a * x) * Real.sin (b * x) =
      (Real.exp a * (a * Real.sin b - b * Real.cos b) + b) / (a ^ 2 + b ^ 2) := by
  cas using h

example : ∫ x in (0 : ℝ)..1, x * Real.cos (Real.pi * x) = -(2 / Real.pi ^ 2) := by
  cas

example : 1 / Real.pi * ∫ x in -Real.pi..Real.pi, x * Real.sin x = 2 := by
  cas

example : ∫ x in (0 : ℝ)..Real.pi, x * (Real.pi - x) * Real.sin x = 4 := by
  cas

example (s : ℝ) (hs : 0 < s) : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s * t)) * 1 = 1 / s := by
  cas

example (h : MeasureTheory.IntegrableOn (fun x : ℝ ↦ (1 - x) * Real.exp (-x)) (Set.Ioi 0)) :
    ∫ x in Set.Ioi (0 : ℝ), (1 - x) * Real.exp (-x) = 0 := by
  cas using h

example : (∫ t in (0 : ℝ)..1, 1 / (1 + t ^ 2)) = Real.pi / 4 := by
  cas

example (x y : ℝ) : Real.sin (x + y) = Real.sin x * Real.cos y + Real.cos x * Real.sin y := by
  cas

example (x : ℝ) : deriv (fun t : ℝ ↦ Real.sinh (2 * t)) x = 2 * Real.cosh (2 * x) := by
  cas

example (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  cas

example (x : ℝ) (h : Real.cos x ≠ 0) : HasDerivAt (fun x ↦ Real.tan x) (1 / Real.cos x ^ 2) x := by
  cas

example (x : ℝ) : HasDerivAt (fun t : ℝ ↦ (1 / 101 : ℝ) * t ^ 101) (x ^ 100) x := by
  cas

example : (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 3 / 4 := by
  cega

example : Real.exp 1 ≤ 2.72 := by
  cega

example : 1 / 2 < ∫ x in (-1 : ℝ)..1, |x| := by
  cega

/-! ## Goals that hold by unfolding a definition -/

example (x : ℝ) : shiftOne x - (x + 1) = 0 := by
  cas

example (x : ℝ) : Real.cosh x = (Complex.cosh x).re := by
  cas

example (f : ℝ → ℝ) (x : ℝ) : deriv f x = fderiv ℝ f x 1 := by
  cas

example (f : ℝ → ℝ) (a b : ℝ) :
    ∫ x in a..b, f x = (∫ x in Set.Ioc a b, f x) - ∫ x in Set.Ioc b a, f x := by
  cas

example : Nat.fib 20 = 6765 := by
  cas

example (x : ℝ) : True := by
  let u : ℝ := shiftOne x
  have : u = x + 1 := by cas_rfl
  trivial

/-- Lebesgue measure under another name. -/
noncomputable def lebesgue : MeasureTheory.Measure ℝ := MeasureTheory.volume

example : ∫ x in (0 : ℝ)..1, x ∂lebesgue = 1 / 2 := by
  cas

/-- A normal form is compared with its source by the elaborator. The kernel, outside the module
system, computes `0 ^ 2 = 0` in `ℝ` and would report no change here. -/
theorem sq_sqrt_of_nonpos (P : ℝ → Prop) (x : ℝ) (hx : x ≤ 0) (h : P (√x ^ 2)) : P 0 := by
  cas_nf using hx at h
  exact h

/-! ## Long sums

A comparison of two sums that fails must not cost more with their length than it did. With
instances unfolded Lean v4.36.0 compares each addition twice, in a module as well, so a
reflexivity check on two sums of 24 terms that differ in the first took all the heartbeats. -/

example (x : ℝ) :
    x ^ 1 + x ^ 2 + x ^ 3 + x ^ 4 + x ^ 5 + x ^ 6 + x ^ 7 + x ^ 8 + x ^ 9 + x ^ 10 + x ^ 11 +
    x ^ 12 + x ^ 13 + x ^ 14 + x ^ 15 + x ^ 16 + x ^ 17 + x ^ 18 + x ^ 19 + x ^ 20 + x ^ 21 +
    x ^ 22 + x ^ 23 + x ^ 24 =
      x ^ 24 + x ^ 23 + x ^ 22 + x ^ 21 + x ^ 20 + x ^ 19 + x ^ 18 + x ^ 17 + x ^ 16 + x ^ 15 +
      x ^ 14 + x ^ 13 + x ^ 12 + x ^ 11 + x ^ 10 + x ^ 9 + x ^ 8 + x ^ 7 + x ^ 6 + x ^ 5 + x ^ 4 +
      x ^ 3 + x ^ 2 + x ^ 1 := by
  cas

/--
error: cas could not prove this arithmetic relation.
-/
#guard_msgs (error, substring := true) in
example (x : ℝ) :
    x ^ 1 + x ^ 2 + x ^ 3 + x ^ 4 + x ^ 5 + x ^ 6 + x ^ 7 + x ^ 8 + x ^ 9 + x ^ 10 + x ^ 11 +
    x ^ 12 + x ^ 13 + x ^ 14 + x ^ 15 + x ^ 16 + x ^ 17 + x ^ 18 + x ^ 19 + x ^ 20 + x ^ 21 +
    x ^ 22 + x ^ 23 + x ^ 24 =
      x ^ 24 + x ^ 23 + x ^ 22 + x ^ 21 + x ^ 20 + x ^ 19 + x ^ 18 + x ^ 17 + x ^ 16 + x ^ 15 +
      x ^ 14 + x ^ 13 + x ^ 12 + x ^ 11 + x ^ 10 + x ^ 9 + x ^ 8 + x ^ 7 + x ^ 6 + x ^ 5 + x ^ 4 +
      x ^ 3 + x ^ 2 + x ^ 1 + 1 := by
  cas

example (x : ℝ) (P : ℝ → Prop)
    (h : P (x ^ 1 + x ^ 2 + x ^ 3 + x ^ 4 + x ^ 5 + x ^ 6 + x ^ 7 + x ^ 8 + x ^ 9 + x ^ 10 +
    x ^ 11 + x ^ 12 + x ^ 13 + x ^ 14 + x ^ 15 + x ^ 16 + x ^ 17 + x ^ 18 + x ^ 19 + x ^ 20 +
    x ^ 21 + x ^ 22 + x ^ 23 + x ^ 24 + x ^ 25 + x ^ 26 + x ^ 27 + x ^ 28 + x ^ 29 + x ^ 30 +
    x ^ 31 + x ^ 32 + x ^ 33 + x ^ 34 + x ^ 35 + x ^ 36 + x ^ 37 + x ^ 38 + x ^ 39 + x ^ 40)) :
    P (x ^ 40 + x ^ 39 + x ^ 38 + x ^ 37 + x ^ 36 + x ^ 35 + x ^ 34 + x ^ 33 + x ^ 32 + x ^ 31 +
    x ^ 30 + x ^ 29 + x ^ 28 + x ^ 27 + x ^ 26 + x ^ 25 + x ^ 24 + x ^ 23 + x ^ 22 + x ^ 21 +
    x ^ 20 + x ^ 19 + x ^ 18 + x ^ 17 + x ^ 16 + x ^ 15 + x ^ 14 + x ^ 13 + x ^ 12 + x ^ 11 +
    x ^ 10 + x ^ 9 + x ^ 8 + x ^ 7 + x ^ 6 + x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x ^ 1) := by
  cas_nf at h ⊢
  exact h

/-! ## Goals that must be refused, with their message -/

/--
error: cas could not prove this arithmetic relation.
-/
#guard_msgs (error, substring := true) in
example (x y : ℝ) : x * y = y * x + 1 := by
  cas

/--
error: cas could not prove this arithmetic relation.
-/
#guard_msgs (error, substring := true) in
example (x : ℝ) : Real.exp x = Real.exp (x + 1) := by
  cas

/--
error: cas found a checked antiderivative, but it does not match the stated primitive or integral
-/
#guard_msgs (error, substring := true) in
example : ∫ x in (0 : ℝ)..1, x * Real.exp x = 2 := by
  cas

/--
error: cas proves interval integrals with Mathlib's default Lebesgue measure on ℝ only
-/
#guard_msgs (error, substring := true) in
example : ∫ x in (0 : ℝ)..1, x ∂(MeasureTheory.Measure.dirac 0) = 0 := by
  cas

/-! ## Commands -/

/--
Output (scalar ℝ; definite integral): 1
-/
#guard_msgs (info, substring := true) in
#cas [integrate x in [0, 1]] (x * exp x)

/--
Output (scalar ℝ; definite integral): 1/2*pi
-/
#guard_msgs (info, substring := true) in
#cas [integrate x in [0, π]] (sin x ^ 2)

/--
Output (scalar ℝ; definite integral): 1
-/
#guard_msgs (info, substring := true) in
#cas [integrate x in [0, ∞]] (exp (-x))

/--
Output (scalar ℝ; definite integral): 1/4*pi
-/
#guard_msgs (info, substring := true) in
#cas [integrate x in [0, 1]] (1 / (1 + x ^ 2))

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.BottomUp
public import CAS.ClosedForm.Pipeline.Core

/-!
# Domain-aware elementary-function simplification

Checked simplification of `exp (log a)` to `a`. The identity holds for `0 < a` but fails for
other reals under Mathlib's totalized logarithm `Real.log`, which is why the rewrite is a side
pass and not part of the unconditional smart constructors.

## Main definitions

* `expLogCleanup`: rewrite one node `exp (log a)` to `a`, recording the entry `sqrt a`.
* `elementaryDeepCleanup`: the same rewrite at every node, bottom-up.
* `elementarySidePass`: the side pass `inverse-elementary`.

## Main results

* `eval_expLogCleanup`, `eval_elementaryDeepCleanup`: the rewrites preserve evaluation when the
  recorded entries are nonzero.

## Implementation notes

We record the obligation `0 < a` as the entry `sqrt a`: `Real.sqrt_ne_zero'` turns `sqrt a ≠ 0`
into `0 < a`, the hypothesis of `Real.exp_log`. If `definitelyNonpositive` recognizes `a` as a
literal that is zero or negative, the node is left alone, since the obligation would be false.
`elementaryDeepCleanup` is `BottomUp.run` of the one-node rewrite, so its soundness is an
instance of `BottomUp.eval_run`. In `configuredSidePipeline` the pass runs both before and after
the base normalizer.
-/

@[expose] public section

namespace CAS.Verified.Expr

/-- Recognize numeric leaves that cannot lie on the positive logarithm branch. -/
def definitelyNonpositive {ι : Type*} : Verified.Expr ι → Bool
  | .nat value => value == 0
  | .int value => decide (value ≤ 0)
  | .rat numerator denominator => denominator != 0 && decide (numerator ≤ 0)
  | .neg (.nat _) => true
  | .neg (.int value) => decide (0 ≤ value)
  | .neg (.rat numerator denominator) => denominator != 0 && decide (0 ≤ numerator)
  | _ => false

/--
Simplify one top-level `exp (log a)` node on the positive branch.

The side pipeline represents branch witnesses as expressions known
to be nonzero. The condition `sqrt a ≠ 0` is equivalent to `0 < a`, so it is
an exact witness for Mathlib's `Real.exp_log` theorem.
-/
def expLogCleanup {ι : Type*} : Verified.Expr ι → Alg.NormResult ι
  | .exp (.log a) =>
      if definitelyNonpositive a then
        { expr := .exp (.log a), nonzero := [] }
      else
        { expr := a, nonzero := [.sqrt a] }
  | expr => { expr := expr, nonzero := [] }

/-- Soundness of positive-branch exponential-logarithm simplification. -/
theorem eval_expLogCleanup {ι : Type*} (ρ : ι → ℝ)
    (expr : Verified.Expr ι)
    (hside : Alg.SideHolds ρ (expLogCleanup expr).nonzero) :
    (expLogCleanup expr).expr.eval ρ = expr.eval ρ := by
  cases expr with
  | exp argument =>
      cases argument with
      | log a =>
          simp only [expLogCleanup] at hside ⊢
          split_ifs at hside ⊢
          · rfl
          · exact (Real.exp_log (Real.sqrt_ne_zero'.mp hside.of_singleton)).symm
      | _ => rfl
  | _ => rfl

/-- Add local elementary side conditions to those inherited from child nodes. -/
def elementaryTopAfter {ι : Type*} [DecidableEq ι]
    (rebuilt : Verified.Expr ι) (inherited : List (Verified.Expr ι)) :
    Alg.NormResult ι :=
  let top := expLogCleanup rebuilt
  { expr := top.expr, nonzero := Alg.cleanSide (inherited ++ top.nonzero) }

/-- Child side conditions remain available after elementary simplification. -/
theorem sideHolds_inherited_of_elementaryTopAfter
    {ι : Type*} [DecidableEq ι] {ρ : ι → ℝ}
    (rebuilt : Verified.Expr ι) (inherited : List (Verified.Expr ι))
    (hside : Alg.SideHolds ρ (elementaryTopAfter rebuilt inherited).nonzero) :
    Alg.SideHolds ρ inherited :=
  (Alg.sideHolds_of_cleanSide hside).append_left

/-- The local elementary rewrite is sound after recursively rebuilding children. -/
theorem eval_elementaryTopAfter {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (rebuilt : Verified.Expr ι) (inherited : List (Verified.Expr ι))
    (hside : Alg.SideHolds ρ (elementaryTopAfter rebuilt inherited).nonzero) :
    (elementaryTopAfter rebuilt inherited).expr.eval ρ = rebuilt.eval ρ :=
  eval_expLogCleanup ρ rebuilt (Alg.sideHolds_of_cleanSide hside).append_right

/-- Recursively simplify positive-branch inverse elementary functions. -/
def elementaryDeepCleanup {ι : Type*} [DecidableEq ι] :
    Verified.Expr ι → Alg.NormResult ι :=
  BottomUp.run elementaryTopAfter

/-- Soundness of recursive domain-aware elementary simplification. -/
theorem eval_elementaryDeepCleanup {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) :
    ∀ expr : Verified.Expr ι,
      Alg.SideHolds ρ (elementaryDeepCleanup expr).nonzero →
        (elementaryDeepCleanup expr).expr.eval ρ = expr.eval ρ := by
  simpa [elementaryDeepCleanup] using
    BottomUp.eval_run elementaryTopAfter
      sideHolds_inherited_of_elementaryTopAfter eval_elementaryTopAfter ρ

/-- Checked side pass for inverse elementary-function simplification. -/
def elementarySidePass {ι : Type*} [DecidableEq ι] : SidePass ι where
  name := "inverse-elementary"
  run := elementaryDeepCleanup
  sound := by
    intro ρ expr hside
    exact eval_elementaryDeepCleanup ρ expr hside

end CAS.Verified.Expr

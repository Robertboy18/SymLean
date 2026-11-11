/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Expression.Rational

/-!
# Symbolic transformation pipelines

The checked transformation pipelines of the closed-form computer algebra system. A `Pass` is a
named rewrite of `Verified.Expr` with an unconditional proof that it preserves evaluation, and a
`SidePass` is a named rewrite that also returns the nonzero obligations its proof needs. A
`Pipeline` is a list of passes with a fuel bound for fixed-point iteration. A `SidePipeline`
iterates its pre side passes, runs its base pipeline to a fixed point, iterates its post side
passes and runs the base pipeline to a fixed point again. `PassInfo` names a configured pass and
its phase, and `SidePipeline.passInfo` lists the configured passes of a pipeline and their phases,
for reports. The concrete passes are in `Pipeline.Passes`, and the configured pipelines in
`Pipeline.Configured`.

## Main definitions

* `Pass`, `SidePass`: named rewrites together with their soundness proofs.
* `runPipeline`, `runFixed`, `Pipeline.runFixed`: one round of a pass list and its fuel-bounded
  fixed point.
* `runSidePasses`, `runSidePassesIter`: one round and the fixed point of a list of side passes,
  collecting their obligations.
* `SidePipeline.run`: the staged run of a side pipeline.
* `PassKind`, `PassPhase`, `PassInfo`: metadata on the configured passes and their phases, for
  reports. None of them enters a proof.

## Main results

* `eval_runPipeline`, `eval_runFixed`: checked passes and their fixed point preserve evaluation.
* `eval_runSidePasses`, `eval_runSidePassesIter`: side passes preserve evaluation when their
  obligations hold.
* `SidePipeline.eval_run`: a side pipeline preserves evaluation when every recorded obligation
  holds.

## Implementation notes

Each pass carries its own soundness proof, so a pipeline is sound by construction. We prove the
composition theorems once, by induction on the pass list and on the fuel, and never reason about
a particular run. In the tactics the kernel evaluates a run, `decide +kernel` certifies the
equation between the run and its result, and the evaluation theorems carry it over to the real
expressions. This is proof by reflection, a classical technique.

The obligation list (`Alg.SideHolds`) holds nonzero facts only. A pass whose proof needs
`0 < a` records the entry `sqrt a`, since `Real.sqrt_ne_zero'` turns `sqrt a ≠ 0` into `0 < a`,
and the command output prints such an entry as `a > 0`. `Alg.cleanSide` removes duplicates
whenever two obligation lists are joined. Every loop stops after the first round that changes
nothing, or when the fuel runs out, so a run terminates without any termination argument for
the rewrites; a loop cut off by the fuel still returns a sound result, possibly not fully
simplified. The side-pass loops use the fuel of the base pipeline.
-/

@[expose] public section

namespace CAS.Verified.Expr

/-! ### Pipelines of named passes

Passes are grouped into named pipelines. The four passes of `checkedPasses` (structural,
trigonometric, algebraic, common factors) are `Pass` values. The rewrites that need nonzero or
positivity facts (exp and log, real powers, fractions, square roots) are `SidePass` values, and
so are four unconditional cleanups that run among them (`sqrt-numeral`, `pythagorean`,
`unit-ratio`, `common-add-factor`).
-/


/-- Classification used by planner diagnostics for checked and conditional passes. -/
inductive PassKind where
  | checked
  | sideConditioned
deriving DecidableEq, Repr

/-- Phase of a configured pass in its `PassInfo`: its stage in a side pipeline, or `direct`. -/
inductive PassPhase where
  /-- A pass used outside the staged side-condition-aware pipeline. -/
  | direct
  /-- A side pass run before the ordinary fixed-point normalizer. -/
  | preNormalization
  /-- A checked pass in the ordinary fixed-point normalizer. -/
  | baseNormalization
  /-- A side pass run after the first ordinary fixed-point normalization. -/
  | postNormalization
deriving Repr, DecidableEq

/-- Stable user-facing label for an execution phase. -/
def PassPhase.label : PassPhase → String
  | .direct => "direct"
  | .preNormalization => "pre-normalization"
  | .baseNormalization => "base normalization"
  | .postNormalization => "post-normalization"

/-- Report metadata for one configured pass of a pipeline: its name, kind and phase.

This is the exact pipeline's counterpart of the planner vocabulary `CAS.RouteStep`;
see that module for why the two types remain separate. Neither enters a proof. -/
structure PassInfo where
  /-- Stable diagnostic name of the pass. -/
  name : String
  /-- Proof-obligation class of the pass. -/
  kind : PassKind
  /-- Stage of the pipeline in which the pass is configured. -/
  phase : PassPhase := .direct
deriving Repr, DecidableEq

/-- Set the phase in the metadata of a pass, leaving the pass itself unchanged. -/
def PassInfo.inPhase (info : PassInfo) (phase : PassPhase) : PassInfo :=
  { info with phase }

/-- A named denotation-preserving simplification pass. -/
structure Pass (ι : Type*) where
  /-- Stable diagnostic name of the pass. -/
  name : String
  /-- The symbolic transformation performed by the pass. -/
  run : Verified.Expr ι → Verified.Expr ι
  /-- Pointwise denotational soundness of the transformation. -/
  sound : ∀ (ρ : ι → ℝ) (expr : Verified.Expr ι),
    (run expr).eval ρ = expr.eval ρ

/-- The report metadata of a checked pass: its name, kind `checked` and phase `direct`. -/
def Pass.info {ι : Type*} (pass : Pass ι) : PassInfo where
  name := pass.name
  kind := .checked

/-- A named simplification pipeline.

The `fuel` field controls fixed-point execution.  Keeping this metadata with the pass list makes
pipelines inspectable in reports and lets checked and side-aware routes share the same runner. -/
structure Pipeline (ι : Type*) where
  /-- Stable diagnostic name of the pipeline. -/
  name : String
  /-- Ordered transformations executed in each pipeline round. -/
  passes : List (Pass ι)
  /-- Maximum number of fixed-point rounds. -/
  fuel : Nat

/-- The report metadata of the configured passes of a pipeline, in order. -/
def Pipeline.passInfo {ι : Type*} (pipeline : Pipeline ι) : List PassInfo :=
  pipeline.passes.map Pass.info

/-- A named simplification pass that emits algebraic side conditions. -/
structure SidePass (ι : Type*) where
  /-- Stable diagnostic name of the side-condition-emitting pass. -/
  name : String
  /-- The transformation and nonzero obligations produced by the pass. -/
  run : Verified.Expr ι → Alg.NormResult ι
  /-- If the emitted nonzero obligations hold, the transformation preserves evaluation. -/
  sound : ∀ (ρ : ι → ℝ) (expr : Verified.Expr ι),
    Alg.SideHolds ρ (run expr).nonzero → ((run expr).expr).eval ρ = expr.eval ρ

/-- The report metadata of a side pass: its name, kind `sideConditioned` and phase `direct`. -/
def SidePass.info {ι : Type*} (pass : SidePass ι) : PassInfo where
  name := pass.name
  kind := .sideConditioned

/-- Run a list of side-condition-emitting passes, accumulating cleaned nonzero obligations. -/
def runSidePasses {ι : Type*} [DecidableEq ι] :
    List (SidePass ι) → Verified.Expr ι → Alg.NormResult ι
  | [], expr => { expr := expr, nonzero := [] }
  | pass :: passes, expr =>
      let current := pass.run expr
      let rest := runSidePasses passes current.expr
      { expr := rest.expr, nonzero := Alg.cleanSide (current.nonzero ++ rest.nonzero) }

/-- Sequential side-condition pass execution preserves denotation when all emitted obligations
hold. -/
theorem eval_runSidePasses {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) :
    ∀ (passes : List (SidePass ι)) (expr : Verified.Expr ι),
      Alg.SideHolds ρ (runSidePasses passes expr).nonzero →
        ((runSidePasses passes expr).expr).eval ρ = expr.eval ρ
  | [], expr, _ => by simp [runSidePasses]
  | pass :: passes, expr, hside =>
      have hboth := Alg.sideHolds_of_cleanSide hside
      (eval_runSidePasses ρ passes _ hboth.append_right).trans
        (pass.sound ρ expr hboth.append_left)

/-- Fuel-bounded iteration of a side-pass sequence.

Unlike checked base passes, side passes may introduce obligations, so every round's emitted
nonzero conditions are accumulated and globally cleaned.
-/
def runSidePassesIter {ι : Type*} [DecidableEq ι] (passes : List (SidePass ι)) :
    Nat → Verified.Expr ι → Alg.NormResult ι
  | 0, expr => { expr := expr, nonzero := [] }
  | fuel + 1, expr =>
      let current := runSidePasses passes expr
      if current.expr = expr then
        current
      else
        let rest := runSidePassesIter passes fuel current.expr
        { expr := rest.expr, nonzero := Alg.cleanSide (current.nonzero ++ rest.nonzero) }

/-- Iterated side-pass execution preserves denotation when all emitted obligations hold. -/
theorem eval_runSidePassesIter {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (passes : List (SidePass ι)) :
    ∀ (fuel : Nat) (expr : Verified.Expr ι),
      Alg.SideHolds ρ (runSidePassesIter passes fuel expr).nonzero →
        ((runSidePassesIter passes fuel expr).expr).eval ρ = expr.eval ρ
  | 0, expr, _ => by simp [runSidePassesIter]
  | fuel + 1, expr, hside => by
      simp only [runSidePassesIter] at hside ⊢
      split_ifs at hside ⊢ with hfixed
      · rw [hfixed]
      · have hboth := Alg.sideHolds_of_cleanSide hside
        exact (eval_runSidePassesIter ρ passes fuel _ hboth.append_right).trans
          (eval_runSidePasses ρ passes expr hboth.append_left)

/-- A base pipeline with side-condition-emitting passes run before and after it.

Such pipelines are stronger than ordinary simplification because they may introduce
obligations such as nonzero denominators. -/
structure SidePipeline (ι : Type*) where
  /-- Stable diagnostic name of the side-condition-aware pipeline. -/
  name : String
  /-- The ordinary fixed-point normalization stage. -/
  base : Pipeline ι
  /-- Side passes run before the base normalization stage. -/
  preSidePasses : List (SidePass ι) := []
  /-- Side passes run after the base normalization stage. -/
  sidePasses : List (SidePass ι)

/-- The configured passes of a side pipeline with their phases, for reports: the pre side passes,
the passes of the base pipeline (listed once, although a run uses the base pipeline twice), then
the post side passes. -/
def SidePipeline.passInfo {ι : Type*} (pipeline : SidePipeline ι) : List PassInfo :=
  pipeline.preSidePasses.map (fun pass ↦ pass.info.inPhase .preNormalization) ++
    pipeline.base.passInfo.map (fun pass ↦ pass.inPhase .baseNormalization) ++
      pipeline.sidePasses.map (fun pass ↦ pass.info.inPhase .postNormalization)

/-- Run a list of passes from left to right. -/
def runPipeline {ι : Type*} (passes : List (Pass ι)) (expr : Verified.Expr ι) :
    Verified.Expr ι :=
  passes.foldl (fun acc pass ↦ pass.run acc) expr

/-- Sequential execution of checked passes preserves denotation. -/
theorem eval_runPipeline {ι : Type*} (ρ : ι → ℝ) (passes : List (Pass ι))
    (expr : Verified.Expr ι) :
    (runPipeline passes expr).eval ρ = expr.eval ρ := by
  induction passes generalizing expr with
  | nil => rfl
  | cons pass passes ih => exact (ih (pass.run expr)).trans (pass.sound ρ expr)

/-- Fuel-bounded fixed-point execution for a pipeline.

The runner stops when one full pipeline round leaves the expression unchanged, or when the fuel is
exhausted, so execution is total. -/
def runFixed {ι : Type*} [DecidableEq ι] (passes : List (Pass ι)) :
    Nat → Verified.Expr ι → Verified.Expr ι
  | 0, expr => expr
  | fuel + 1, expr =>
      let next := runPipeline passes expr
      if next = expr then
        next
      else
        runFixed passes fuel next

/-- Fixed-point iteration of checked passes preserves denotation. -/
theorem eval_runFixed {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (passes : List (Pass ι)) :
    ∀ (fuel : Nat) (expr : Verified.Expr ι),
      (runFixed passes fuel expr).eval ρ = expr.eval ρ
  | 0, _ => rfl
  | fuel + 1, expr => by
      simp only [runFixed]
      split_ifs with hfixed
      · rw [hfixed]
      · exact (eval_runFixed ρ passes fuel _).trans (eval_runPipeline ρ passes expr)

/-- Fuel-bounded fixed-point execution for a named pipeline. -/
def Pipeline.runFixed {ι : Type*} [DecidableEq ι] (pipeline : Pipeline ι)
    (expr : Verified.Expr ι) : Verified.Expr ι :=
  Expr.runFixed pipeline.passes pipeline.fuel expr

/-- Run a side-condition-aware pipeline. -/
def SidePipeline.run {ι : Type*} [DecidableEq ι] (pipeline : SidePipeline ι)
    (expr : Verified.Expr ι) : Alg.NormResult ι :=
  let pre := runSidePassesIter pipeline.preSidePasses pipeline.base.fuel expr
  let post := runSidePassesIter pipeline.sidePasses pipeline.base.fuel
    (pipeline.base.runFixed pre.expr)
  { expr := pipeline.base.runFixed post.expr, nonzero := Alg.cleanSide (pre.nonzero ++ post.nonzero)
    }

/-- A side-condition-aware pipeline preserves evaluation under its emitted assumptions.

The checked base passes are sound by construction. This theorem composes their soundness with that
of the pre- and post-normalization side passes. -/
theorem SidePipeline.eval_run {ι : Type*} [DecidableEq ι] (pipeline : SidePipeline ι)
    (ρ : ι → ℝ) (expr : Verified.Expr ι)
    (hside : Alg.SideHolds ρ (pipeline.run expr).nonzero) :
    (pipeline.run expr).expr.eval ρ = expr.eval ρ := by
  have hboth := Alg.sideHolds_of_cleanSide hside
  calc (pipeline.run expr).expr.eval ρ = _ := eval_runFixed ρ _ _ _
    _ = _ := eval_runSidePassesIter ρ _ _ _ hboth.append_right
    _ = _ := eval_runFixed ρ _ _ _
    _ = expr.eval ρ := eval_runSidePassesIter ρ _ _ _ hboth.append_left

end CAS.Verified.Expr

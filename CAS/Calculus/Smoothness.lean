/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.ParameterEmbedding
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Smoothness of checked expression evaluation

At a point where `expr.ValidAt` holds, evaluation `fun y : ℝ^n ↦ expr.eval y` is `C^m` for every
smoothness order `m : WithTop ℕ∞`, the analytic order `ω` included (`contDiffAt_eval`). The
theorems are stated in the two conventions of the regularity goals of `cas`: functions
`ℝ^n → ℝ` presented through `Verified.Expr.paramEmbed`, and functions `ℝ → ℝ` presented through
`Verified.Expr.lineEmbed`.

## Main results

* `contDiffAt_eval`, `differentiableAt_eval`: evaluation is `C^m` for every `m`, and
  differentiable, at a valid point.
* `contDiff_paramEmbed`, `contDiff_lineEmbed`: both embeddings are affine, hence smooth.
* `contDiffAt_eval_paramEmbed`, `contDiffOn_eval_paramEmbed`, `contDiff_eval_paramEmbed`, with
  the `DifferentiableAt`, `Differentiable`, `ContinuousAt`, `ContinuousOn`, `Continuous`,
  `DifferentiableOn`, `AnalyticAt` and `AnalyticOnNhd` forms, for evaluation along
  `paramEmbed`; the forms on a set and the global forms ask for validity on the set or
  everywhere.
* `contDiffAt_eval_lineEmbed` to `analyticOnNhd_eval_lineEmbed`: the same forms along
  `lineEmbed`.

## Implementation notes

We prove `contDiffAt_eval` by induction on the expression for an arbitrary order `m`, since
Mathlib's lemmas for the field operations and for the elementary functions away from their
singularities hold at every order (`ContDiffAt.div`, `ContDiffAt.exp`, `ContDiffAt.log`,
`ContDiffAt.sqrt`, `ContDiffAt.rpow`, `Real.contDiff_arctan`, `Real.contDiffAt_arcsin`,
`Real.contDiffAt_arccos`, ...). One induction thus gives every order at once, and continuity,
differentiability on a set and analyticity are read off at the orders `0`, `1` and `ω`
(`ContDiffAt.analyticAt`). The hypothesis is the validity predicate of the derivative theorems of
`CAS.Calculus.Euclidean`, so the same side conditions serve both; it is sufficient but not the
largest smooth domain, since for square roots and real powers positivity is used only to get the
nonzero hypotheses of `ContDiffAt.sqrt` and `ContDiffAt.rpow`. `CAS.Tactic.Regularity` reflects the
user's function and applies these theorems, and the validity hypotheses of the forms on a set and
the global forms are the obligations it discharges with `symbolic_assumptions`.
-/

@[expose] public section

namespace CAS

namespace Verified.Expr

/--
Evaluation of a valid verified expression is `C^m` at the point for every order `m`,
including the analytic order.
-/
theorem contDiffAt_eval {n : ℕ} {m : WithTop ℕ∞} (expr : Verified.Expr (Fin n))
    (x : ℝ^n) (h : expr.ValidAt x) :
    ContDiffAt ℝ m (fun y : ℝ^n ↦ expr.eval y) x := by
  induction expr generalizing x with
  | nat | int | rat | pi | e => exact contDiffAt_const
  | var i => exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt
  | add a b ha hb => exact (ha _ h.1).add (hb _ h.2)
  | mul a b ha hb => exact (ha _ h.1).mul (hb _ h.2)
  | sub a b ha hb => exact (ha _ h.1).sub (hb _ h.2)
  | div a b ha hb => exact (ha _ h.1).div (hb _ h.2.1) h.2.2
  | neg a ha => exact (ha _ h).neg
  | pow a k ha => exact (ha _ h).pow k
  | sin a ha => exact (ha _ h).sin
  | cos a ha => exact (ha _ h).cos
  | atan a ha => exact Real.contDiff_arctan.contDiffAt.comp x (ha _ h)
  | asin a ha => exact (Real.contDiffAt_arcsin h.2.1 h.2.2).comp x (ha _ h.1)
  | acos a ha => exact (Real.contDiffAt_arccos h.2.1 h.2.2).comp x (ha _ h.1)
  | exp a ha => exact (ha _ h).exp
  | log a ha => exact (ha _ h.1).log h.2
  | sqrt a ha => exact (ha _ h.1).sqrt h.2.ne'
  | rpow a b ha hb => exact (ha _ h.1).rpow (hb _ h.2.1) h.2.2.ne'

/-- Evaluation of a valid verified expression is differentiable at the point. -/
theorem differentiableAt_eval {n : ℕ} (expr : Verified.Expr (Fin n))
    (x : ℝ^n) (h : expr.ValidAt x) :
    DifferentiableAt ℝ (fun y : ℝ^n ↦ expr.eval y) x :=
  (hasFDerivAt_eval expr x h).differentiableAt

variable {n k : ℕ} {m : WithTop ℕ∞}

/-! ## The parameter embedding -/

/-- The parameter embedding is affine, hence smooth of every order. -/
theorem contDiff_paramEmbed (c : Fin k → ℝ) : ContDiff ℝ m (paramEmbed (n := n) c) := by
  rw [funext (paramEmbed_eq_linear_add c)]
  exact (paramEmbedL n k).contDiff.add contDiff_const

/-- Evaluation along the parameter embedding is `C^m` at every valid point. -/
theorem contDiffAt_eval_paramEmbed (expr : Verified.Expr (Fin (n + k)))
    (c : Fin k → ℝ) (p : ℝ^n) (h : expr.ValidAt (paramEmbed c p)) :
    ContDiffAt ℝ m (fun q : ℝ^n ↦ expr.eval (paramEmbed c q)) p :=
  (contDiffAt_eval expr (paramEmbed c p) h).comp p (contDiff_paramEmbed c).contDiffAt

/-- Evaluation along the parameter embedding is `C^m` on a set of valid points. -/
theorem contDiffOn_eval_paramEmbed (expr : Verified.Expr (Fin (n + k)))
    (c : Fin k → ℝ) (s : Set (ℝ^n)) (h : ∀ p ∈ s, expr.ValidAt (paramEmbed c p)) :
    ContDiffOn ℝ m (fun q : ℝ^n ↦ expr.eval (paramEmbed c q)) s :=
  fun p hp ↦ (contDiffAt_eval_paramEmbed expr c p (h p hp)).contDiffWithinAt

/-- Evaluation along the parameter embedding is `C^m` when the expression is valid
everywhere. -/
theorem contDiff_eval_paramEmbed (expr : Verified.Expr (Fin (n + k)))
    (c : Fin k → ℝ) (h : ∀ p : ℝ^n, expr.ValidAt (paramEmbed c p)) :
    ContDiff ℝ m (fun q : ℝ^n ↦ expr.eval (paramEmbed c q)) :=
  contDiff_iff_contDiffAt.2 fun p ↦ contDiffAt_eval_paramEmbed expr c p (h p)

/-- Evaluation along the parameter embedding is differentiable at every valid point. -/
theorem differentiableAt_eval_paramEmbed (expr : Verified.Expr (Fin (n + k)))
    (c : Fin k → ℝ) (p : ℝ^n) (h : expr.ValidAt (paramEmbed c p)) :
    DifferentiableAt ℝ (fun q : ℝ^n ↦ expr.eval (paramEmbed c q)) p :=
  (hasFDerivAt_eval_paramEmbed expr c p h).differentiableAt

/-- Evaluation along the parameter embedding is differentiable when the expression is
valid everywhere. -/
theorem differentiable_eval_paramEmbed (expr : Verified.Expr (Fin (n + k)))
    (c : Fin k → ℝ) (h : ∀ p : ℝ^n, expr.ValidAt (paramEmbed c p)) :
    Differentiable ℝ (fun q : ℝ^n ↦ expr.eval (paramEmbed c q)) :=
  fun p ↦ differentiableAt_eval_paramEmbed expr c p (h p)

/-- Evaluation along the parameter embedding is continuous at every valid point. -/
theorem continuousAt_eval_paramEmbed (expr : Verified.Expr (Fin (n + k)))
    (c : Fin k → ℝ) (p : ℝ^n) (h : expr.ValidAt (paramEmbed c p)) :
    ContinuousAt (fun q : ℝ^n ↦ expr.eval (paramEmbed c q)) p :=
  (contDiffAt_eval_paramEmbed (m := 0) expr c p h).continuousAt

/-- Evaluation along the parameter embedding is continuous on a set of valid points. -/
theorem continuousOn_eval_paramEmbed (expr : Verified.Expr (Fin (n + k)))
    (c : Fin k → ℝ) (s : Set (ℝ^n)) (h : ∀ p ∈ s, expr.ValidAt (paramEmbed c p)) :
    ContinuousOn (fun q : ℝ^n ↦ expr.eval (paramEmbed c q)) s :=
  (contDiffOn_eval_paramEmbed (m := 0) expr c s h).continuousOn

/-- Evaluation along the parameter embedding is continuous when the expression is valid
everywhere. -/
theorem continuous_eval_paramEmbed (expr : Verified.Expr (Fin (n + k)))
    (c : Fin k → ℝ) (h : ∀ p : ℝ^n, expr.ValidAt (paramEmbed c p)) :
    Continuous (fun q : ℝ^n ↦ expr.eval (paramEmbed c q)) :=
  (contDiff_eval_paramEmbed (m := 0) expr c h).continuous

/-- Evaluation along the parameter embedding is differentiable on a set of valid points. -/
theorem differentiableOn_eval_paramEmbed (expr : Verified.Expr (Fin (n + k)))
    (c : Fin k → ℝ) (s : Set (ℝ^n)) (h : ∀ p ∈ s, expr.ValidAt (paramEmbed c p)) :
    DifferentiableOn ℝ (fun q : ℝ^n ↦ expr.eval (paramEmbed c q)) s :=
  (contDiffOn_eval_paramEmbed (m := 1) expr c s h).differentiableOn one_ne_zero

/-- Evaluation along the parameter embedding is analytic at every valid point. -/
theorem analyticAt_eval_paramEmbed (expr : Verified.Expr (Fin (n + k)))
    (c : Fin k → ℝ) (p : ℝ^n) (h : expr.ValidAt (paramEmbed c p)) :
    AnalyticAt ℝ (fun q : ℝ^n ↦ expr.eval (paramEmbed c q)) p :=
  (contDiffAt_eval_paramEmbed (m := ⊤) expr c p h).analyticAt

/-- Evaluation along the parameter embedding is analytic on a neighbourhood of every point of
a set of valid points. -/
theorem analyticOnNhd_eval_paramEmbed (expr : Verified.Expr (Fin (n + k)))
    (c : Fin k → ℝ) (s : Set (ℝ^n)) (h : ∀ p ∈ s, expr.ValidAt (paramEmbed c p)) :
    AnalyticOnNhd ℝ (fun q : ℝ^n ↦ expr.eval (paramEmbed c q)) s :=
  fun p hp ↦ analyticAt_eval_paramEmbed expr c p (h p hp)

/-! ## The affine coordinate line -/

/-- The one-dimensional coordinate map `s ↦ (s)` is linear, hence smooth of every order. -/
theorem contDiff_toLp_vecCons : ContDiff ℝ m (fun s : ℝ ↦ (WithLp.toLp 2 ![s] : ℝ^1)) := by
  have hfun : (fun s : ℝ ↦ (WithLp.toLp 2 ![s] : ℝ^1)) =
      fun s ↦ s • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
    ext s j
    fin_cases j
    simp
  rw [hfun]
  exact contDiff_id.smul contDiff_const

/-- The affine coordinate line is smooth of every order. -/
theorem contDiff_lineEmbed (c : Fin k → ℝ) : ContDiff ℝ m (lineEmbed c) :=
  (contDiff_paramEmbed c).comp contDiff_toLp_vecCons

/-- Evaluation along the affine coordinate line is `C^m` at every valid point. -/
theorem contDiffAt_eval_lineEmbed (expr : Verified.Expr (Fin (1 + k)))
    (c : Fin k → ℝ) (t : ℝ) (h : expr.ValidAt (lineEmbed c t)) :
    ContDiffAt ℝ m (fun s : ℝ ↦ expr.eval (lineEmbed c s)) t :=
  (contDiffAt_eval expr (lineEmbed c t) h).comp t (contDiff_lineEmbed c).contDiffAt

/-- Evaluation along the affine coordinate line is `C^m` on a set of valid points. -/
theorem contDiffOn_eval_lineEmbed (expr : Verified.Expr (Fin (1 + k)))
    (c : Fin k → ℝ) (s : Set ℝ) (h : ∀ t ∈ s, expr.ValidAt (lineEmbed c t)) :
    ContDiffOn ℝ m (fun t : ℝ ↦ expr.eval (lineEmbed c t)) s :=
  fun t ht ↦ (contDiffAt_eval_lineEmbed expr c t (h t ht)).contDiffWithinAt

/-- Evaluation along the affine coordinate line is `C^m` when the expression is valid
everywhere. -/
theorem contDiff_eval_lineEmbed (expr : Verified.Expr (Fin (1 + k)))
    (c : Fin k → ℝ) (h : ∀ t : ℝ, expr.ValidAt (lineEmbed c t)) :
    ContDiff ℝ m (fun s : ℝ ↦ expr.eval (lineEmbed c s)) :=
  contDiff_iff_contDiffAt.2 fun t ↦ contDiffAt_eval_lineEmbed expr c t (h t)

/-- Evaluation along the affine coordinate line is differentiable at every valid point. -/
theorem differentiableAt_eval_lineEmbed (expr : Verified.Expr (Fin (1 + k)))
    (c : Fin k → ℝ) (t : ℝ) (h : expr.ValidAt (lineEmbed c t)) :
    DifferentiableAt ℝ (fun s : ℝ ↦ expr.eval (lineEmbed c s)) t :=
  (hasDerivAt_eval_lineEmbed expr c t (Fin.castAdd k (0 : Fin 1)) (by simp) h).differentiableAt

/-- Evaluation along the affine coordinate line is differentiable when the expression is
valid everywhere. -/
theorem differentiable_eval_lineEmbed (expr : Verified.Expr (Fin (1 + k)))
    (c : Fin k → ℝ) (h : ∀ t : ℝ, expr.ValidAt (lineEmbed c t)) :
    Differentiable ℝ (fun s : ℝ ↦ expr.eval (lineEmbed c s)) :=
  fun t ↦ differentiableAt_eval_lineEmbed expr c t (h t)

/-- Evaluation along the affine coordinate line is continuous at every valid point. -/
theorem continuousAt_eval_lineEmbed (expr : Verified.Expr (Fin (1 + k)))
    (c : Fin k → ℝ) (t : ℝ) (h : expr.ValidAt (lineEmbed c t)) :
    ContinuousAt (fun s : ℝ ↦ expr.eval (lineEmbed c s)) t :=
  (contDiffAt_eval_lineEmbed (m := 0) expr c t h).continuousAt

/-- Evaluation along the affine coordinate line is continuous on a set of valid points. -/
theorem continuousOn_eval_lineEmbed (expr : Verified.Expr (Fin (1 + k)))
    (c : Fin k → ℝ) (s : Set ℝ) (h : ∀ t ∈ s, expr.ValidAt (lineEmbed c t)) :
    ContinuousOn (fun t : ℝ ↦ expr.eval (lineEmbed c t)) s :=
  (contDiffOn_eval_lineEmbed (m := 0) expr c s h).continuousOn

/-- Evaluation along the affine coordinate line is continuous when the expression is valid
everywhere. -/
theorem continuous_eval_lineEmbed (expr : Verified.Expr (Fin (1 + k)))
    (c : Fin k → ℝ) (h : ∀ t : ℝ, expr.ValidAt (lineEmbed c t)) :
    Continuous (fun s : ℝ ↦ expr.eval (lineEmbed c s)) :=
  (contDiff_eval_lineEmbed (m := 0) expr c h).continuous

/-- Evaluation along the affine coordinate line is differentiable on a set of valid points. -/
theorem differentiableOn_eval_lineEmbed (expr : Verified.Expr (Fin (1 + k)))
    (c : Fin k → ℝ) (s : Set ℝ) (h : ∀ t ∈ s, expr.ValidAt (lineEmbed c t)) :
    DifferentiableOn ℝ (fun t : ℝ ↦ expr.eval (lineEmbed c t)) s :=
  (contDiffOn_eval_lineEmbed (m := 1) expr c s h).differentiableOn one_ne_zero

/-- Evaluation along the affine coordinate line is analytic at every valid point. -/
theorem analyticAt_eval_lineEmbed (expr : Verified.Expr (Fin (1 + k)))
    (c : Fin k → ℝ) (t : ℝ) (h : expr.ValidAt (lineEmbed c t)) :
    AnalyticAt ℝ (fun s : ℝ ↦ expr.eval (lineEmbed c s)) t :=
  (contDiffAt_eval_lineEmbed (m := ⊤) expr c t h).analyticAt

/-- Evaluation along the affine coordinate line is analytic on a neighbourhood of every point
of a set of valid points. -/
theorem analyticOnNhd_eval_lineEmbed (expr : Verified.Expr (Fin (1 + k)))
    (c : Fin k → ℝ) (s : Set ℝ) (h : ∀ t ∈ s, expr.ValidAt (lineEmbed c t)) :
    AnalyticOnNhd ℝ (fun t : ℝ ↦ expr.eval (lineEmbed c t)) s :=
  fun t ht ↦ analyticAt_eval_lineEmbed expr c t (h t ht)

end Verified.Expr

end CAS

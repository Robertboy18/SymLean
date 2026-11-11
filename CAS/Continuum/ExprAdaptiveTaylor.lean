/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.CompiledDerivative
public import CAS.Continuum.TaylorModel
public import CAS.Continuum.IntervalEval.Attempt

/-!
# Adaptive Taylor models for verified symbolic expressions

Taylor models for symbolic expressions, built from symbolic differentiation
and an arbitrary interval backend.

The central constructor, `panelOfRange`, accepts any
`RealIntervalBackend`. It uses the backend only for a proved enclosure of the
symbolic `(order + 1)`-st derivative. The Taylor polynomial, remainder theorem,
exact-rational stopping budget, subdivision policy, and final `ApproxOn`
theorem remain independent of the interval implementation.

The noncomputable certificate constructors `panel?` and `adaptiveToTolerance?`
instantiate `panelOfRange` with the exact-rational interval evaluator, through
`CompiledDerivative.enclosureAttempt?`.
The enclosure data are computable; the constructors also build real-valued models.

## Implementation notes

`panel?` compiles the `(order + 1)`-st derivative with `RationalInterval.compileDerivative?`,
which also proves `ValidIteratesOn (order + 2)` on the panel; that validity gives the smoothness
hypothesis of `taylorLeafCandidate` through `Verified.Expr.contDiffOn_univariateEval`, so no
caller proves smoothness. The interval of the compiled derivative yields the rational bound
`absMax`, and `adaptiveToTolerance?` runs `RationalAdaptiveSystem.searchPartial` with this
builder, recompiling every child panel. The search proposes the panels; the kernel checks each
leaf and `adaptiveToTolerance?_sound` gives `ApproxOn` with the requested tolerance.
-/

@[expose] public section

open Set

namespace CAS.Continuum.ExprAdaptiveTaylor

open CAS
open CAS.Certificate
open CAS.Verified

universe u

/--
Build one symbolic Taylor leaf from a proved derivative enclosure.

`derivativeRange` may come from any implementation of `RealIntervalBackend`.
Adaptive stopping reads only the exact rational `derivativeBound`.
-/
noncomputable def panelOfRange
    {I : Type u} [RealIntervalBackend I]
    (expr : Verified.Expr (Fin 1)) (order : ℕ) (a b derivativeBound : ℚ)
    (hab : (a : ℝ) < (b : ℝ))
    (hvalid :
      expr.ValidIteratesOn (order + 2) (Icc (a : ℝ) (b : ℝ)))
    (derivativeRange : I)
    (hrange :
      ∀ x ∈ Icc (a : ℝ) (b : ℝ),
        RealIntervalBackend.MemReal derivativeRange
          ((expr.symbolicDerivative (order + 1)).eval
            !₂[x]))
    (hbound :
      max
          |RealIntervalBackend.lo derivativeRange|
          |RealIntervalBackend.hi derivativeRange| ≤
        (derivativeBound : ℝ)) :
    RationalBudgetCandidate
      (@(RationalModelTree.adaptiveSystem expr.univariateEval).error a b) := by
  apply taylorLeafCandidate (C := derivativeBound) hab
  · have hnonneg :
        (0 : ℝ) ≤ (derivativeBound : ℝ) :=
      (abs_nonneg (RealIntervalBackend.lo derivativeRange)).trans
        ((le_max_left _ _).trans hbound)
    exact_mod_cast hnonneg
  · exact
      Verified.Expr.contDiffOn_univariateEval expr (order + 1)
        (uniqueDiffOn_Icc hab) hvalid
  · intro x hx
    rw [
      Verified.Expr.iteratedDerivWithin_univariateEval_eq_symbolicDerivative
        expr (order + 1) (uniqueDiffOn_Icc hab)
        (hvalid.mono (Nat.le_succ (order + 1))) hx]
    rw [Real.norm_eq_abs]
    exact
      (abs_le_max_abs_abs
        (RealIntervalBackend.lower_mem (hrange x hx))
        (RealIntervalBackend.upper_mem (hrange x hx))).trans hbound

/--
Build one symbolic Taylor candidate using automatic exact-rational range
analysis of the required derivative.

Unsupported operations or unresolved side conditions return `none`. Adaptive
search may then subdivide the rational panel and retry. Analytic validity of
the expression and all required derivative levels is inferred from the same
checked panel intervals; callers do not supply a separate smoothness
proof.
-/
noncomputable def panel?
    (expr : Verified.Expr (Fin 1)) (order : ℕ) (a b : ℚ)
    (hab : (a : ℝ) < (b : ℝ)) :
    Option
      (RationalBudgetCandidate
        (@(RationalModelTree.adaptiveSystem expr.univariateEval).error a b)) := by
  match hcompiled :
      RationalInterval.compileDerivative? expr (order + 1) a b hab with
  | none => exact none
  | some compiled =>
      match hattempt :
          compiled.enclosureAttempt? with
      | none => exact none
      | some attempt =>
          exact some
            (panelOfRange expr order a b attempt.interval.absMax hab
              compiled.validity.cert attempt.interval
              (fun _x hx ↦ attempt.memReal hx)
              (by
                change
                  max |(attempt.interval.lo : ℝ)|
                      |(attempt.interval.hi : ℝ)| ≤
                    (attempt.interval.absMax : ℝ)
                exact_mod_cast (le_of_eq attempt.interval.absMax_eq_max.symm)))

/--
Construct a piecewise Taylor model to an exact rational tolerance.

Every child panel is recompiled independently, so symbolic side conditions and
derivative ranges may become provable or sharper after subdivision.
-/
noncomputable def adaptiveToTolerance?
    (expr : Verified.Expr (Fin 1)) (order depth : ℕ)
    (a b tolerance : ℚ)
    (hab : (a : ℝ) < (b : ℝ)) :
    Option
      (AdaptiveResult
        (@(RationalModelTree.adaptiveSystem expr.univariateEval).error a b)
        (tolerance : ℝ)) :=
  (RationalModelTree.adaptiveSystem expr.univariateEval).searchPartial
    (s := Icc (a : ℝ) (b : ℝ))
    (fun {_ _} hpanel _hsub ↦
      panel? expr order _ _ hpanel)
    depth a b hab Set.Subset.rfl tolerance

/-- Every successful exact symbolic adaptive Taylor result is uniformly sound. -/
theorem adaptiveToTolerance?_sound
    {expr : Verified.Expr (Fin 1)} {a b tolerance : ℚ}
    (result :
      AdaptiveResult
        (@(RationalModelTree.adaptiveSystem expr.univariateEval).error a b)
        (tolerance : ℝ)) :
    ApproxOn expr.univariateEval result.result.model
      (Icc (a : ℝ) (b : ℝ)) (tolerance : ℝ) :=
  RationalModelTree.sound_of_adaptive result

end CAS.Continuum.ExprAdaptiveTaylor

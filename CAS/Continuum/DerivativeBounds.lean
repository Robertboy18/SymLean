/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import CAS.Continuum.IntervalBackend

/-!
# Local bounds for iterated derivatives

Taylor, quadrature and differential-equation estimates need the same input: on every compact
interval in a domain `s`, an upper bound for the norm of an iterated derivative.
`IteratedDerivativeBounderOn n f s` provides it. For every nondegenerate interval `[a, b] ⊆ s`
it gives a number `bound` and a proof that `‖iteratedDerivWithin n f (Icc a b) x‖ ≤ bound` for
`x ∈ [a, b]`, and `certify` packages this as a `BoundCert`. The bound may come from symbolic
estimates, from an interval of any `RealIntervalBackend` (`ofBackend`), or from two-sided
enclosures of the derivative (`ofEnclosures`).

A bound on `iteratedDerivWithin` does not make `f` of class `Cⁿ`. Smoothness is a separate
hypothesis of the theorems that use these bounds.

## Implementation notes

A bounder is a function of the interval, not one number: the adaptive and composite quadrature
rules ask for a new bound on every panel they create, and each answer carries its own `sound`
proof, which the kernel checks. We bound `iteratedDerivWithin n f (Icc a b)` because the error
theorems take their hypothesis in that form: the quadrature panel rules, and Mathlib's
`taylor_mean_remainder_bound` behind the Taylor certificates. `ofEnclosures` and `ofBackend` turn
an enclosure `[lo, hi]` of the derivative into the bound `max |lo| |hi|` through
`BoundCert.absOfEnclosure`.
-/

@[expose] public section

open Set

namespace CAS.Continuum

open CAS.Certificate

universe u

/--
A producer of certified local norm bounds for the `n`-th ordinary derivative.

The interval is required to be nondegenerate.  This keeps local enclosures
useful for refinement and ensures that every reported upper bound is
nonnegative.
-/
structure IteratedDerivativeBounderOn
    (n : ℕ) (f : ℝ → ℝ) (s : Set ℝ) where
  /-- Certified upper bound on an ordered interval. -/
  bound : {a b : ℝ} → (hab : a < b) → Icc a b ⊆ s → ℝ
  /-- The reported value bounds the intended within-derivative norm. -/
  sound : ∀ {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s),
    BoundOn (fun x ↦ ‖iteratedDerivWithin n f (Icc a b) x‖)
      (Icc a b) (bound hab hsub)

namespace IteratedDerivativeBounderOn

variable {n : ℕ} {f : ℝ → ℝ} {s : Set ℝ}

/-- Transport a derivative-bound producer across equality of the underlying functions. -/
def congr {g : ℝ → ℝ} (bounder : IteratedDerivativeBounderOn n f s)
    (hfg : f = g) :
    IteratedDerivativeBounderOn n g s := by
  subst g
  exact bounder

/--
Transport a derivative-bound producer across equality on its declared domain.

This is the local analogue of `congr`. It applies to functions that agree on the region of
interest but differ, or are singular, outside it.
-/
def congrOn {g : ℝ → ℝ} (bounder : IteratedDerivativeBounderOn n f s)
    (hfg : Set.EqOn f g s) :
    IteratedDerivativeBounderOn n g s where
  bound := bounder.bound
  sound := by
    intro a b hab hsub x hx
    calc
      ‖iteratedDerivWithin n g (Icc a b) x‖ =
          ‖iteratedDerivWithin n f (Icc a b) x‖ :=
        (congrArg norm
          (iteratedDerivWithin_congr (hfg.mono hsub) hx)).symm
      _ ≤ bounder.bound hab hsub :=
        bounder.sound hab hsub x hx

/-- Package the local derivative estimate as a generic upper-bound certificate. -/
noncomputable def certify
    (bounder : IteratedDerivativeBounderOn n f s)
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s) :
    BoundCert ℝ (Icc a b) :=
  BoundCert.ofBoundOn
    (fun x ↦ ‖iteratedDerivWithin n f (Icc a b) x‖)
    (bounder.bound hab hsub) (bounder.sound hab hsub)

/-- Transporting a bounder across function equality preserves its reported bound. -/
@[simp]
theorem congr_bound {g : ℝ → ℝ}
    (bounder : IteratedDerivativeBounderOn n f s) (hfg : f = g)
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s) :
    (bounder.congr hfg).bound hab hsub = bounder.bound hab hsub := by
  subst g
  rfl

/-- Domain-local function transport also preserves every reported local bound. -/
@[simp]
theorem congrOn_bound {g : ℝ → ℝ}
    (bounder : IteratedDerivativeBounderOn n f s) (hfg : Set.EqOn f g s)
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s) :
    (bounder.congrOn hfg).bound hab hsub = bounder.bound hab hsub :=
  rfl

/-- The local certificate implies the intended derivative-norm estimate. -/
theorem norm_iteratedDerivWithin_le
    (bounder : IteratedDerivativeBounderOn n f s)
    {a b x : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s)
    (hx : x ∈ Icc a b) :
    ‖iteratedDerivWithin n f (Icc a b) x‖ ≤
      bounder.bound hab hsub :=
  bounder.sound hab hsub x hx

/-- Every local derivative bound produced on a nondegenerate interval is nonnegative. -/
theorem bound_nonneg
    (bounder : IteratedDerivativeBounderOn n f s)
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s) :
    0 ≤ bounder.bound hab hsub := by
  have hx : (a + b) / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
  exact (norm_nonneg _).trans (bounder.norm_iteratedDerivWithin_le hab hsub hx)

/--
Build local derivative bounds from two-sided CEGA enclosures of the derivative.

The enclosure is converted through `BoundCert.absOfEnclosure`, so the resulting
upper bound is `max |lo| |hi|`.
-/
noncomputable def ofEnclosures
    (enclose : {a b : ℝ} → (hab : a < b) → Icc a b ⊆ s →
      EnclosureCert ℝ (Icc a b))
    (hfn : ∀ {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s),
      Set.EqOn (enclose hab hsub).fn
        (iteratedDerivWithin n f (Icc a b)) (Icc a b)) :
    IteratedDerivativeBounderOn n f s where
  bound := fun hab hsub ↦
    (BoundCert.absOfEnclosure (enclose hab hsub)).upper
  sound := by
    intro a b hab hsub x hx
    change ‖iteratedDerivWithin n f (Icc a b) x‖ ≤
      (BoundCert.absOfEnclosure (enclose hab hsub)).upper
    rw [Real.norm_eq_abs, ← hfn hab hsub hx]
    exact (BoundCert.absOfEnclosure (enclose hab hsub)).sound x hx

/--
Build local derivative bounds directly from any sound real-interval backend.

Backend membership is first converted to an `EnclosureCert`, then to the
absolute-value `BoundCert` used by analysis.
-/
noncomputable def ofBackend {ι : Type u} [RealIntervalBackend ι]
    (interval : {a b : ℝ} → (hab : a < b) → Icc a b ⊆ s → ι)
    (sound : ∀ {a b x : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s),
      x ∈ Icc a b →
      RealIntervalBackend.MemReal (interval hab hsub)
        (iteratedDerivWithin n f (Icc a b) x)) :
    IteratedDerivativeBounderOn n f s :=
  ofEnclosures
    (fun hab hsub ↦
      RealIntervalBackend.enclosureCertOfMemReal (interval hab hsub)
        (fun _x hx ↦ sound hab hsub hx))
    (fun _hab _hsub _x _hx ↦ rfl)

end IteratedDerivativeBounderOn
end CAS.Continuum

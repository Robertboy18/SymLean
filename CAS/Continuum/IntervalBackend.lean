/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.ModelApproximation

/-!
# Interval backends for CEGA

CEGA states its numerical facts in the certificate language of `CAS.Certificate`: `EnclosedOn`,
`BoundOn`, `ResidualBound`, `EnclosureCert` and `ApproxCert`. `RealIntervalBackend ι` is what an
interval representation `ι` must provide to produce these facts: real endpoints `lo` and `hi`, a
membership predicate `MemReal`, and the projections `lower_mem` and `upper_mem` from membership
to the endpoint inequalities. `RationalInterval`, a FloatLib interval with rational endpoints and
an endpoint-order proof, is the one instance; the interval evaluator, the derivative bounds and
the quadrature rules are stated for any instance. The class is a semantic contract only: it
prescribes no executable arithmetic, rounding schedule, or cost model.

## Main definitions

* `RealIntervalBackend`, with the `center` and `radius` of the real endpoints.
* `RealIntervalBackend.enclosureCertOfMemReal`, `RealIntervalBackend.approxCertAroundOfMemRealLe`:
  certificates from the statement that `f x` lies in one interval for every `x` in a patch.
* `ApproxCert.evaluateRhsAtOfInterval`, `ModelApproxCert.evaluateAtOfInterval`: replace the
  value of an approximation at one point by the midpoint of an interval containing it, adding
  the radius to the error.

## Main results

* `RealIntervalBackend.abs_sub_center_le_radius`: `|x - center I| ≤ radius I` for `x ∈ I`.
* `RealIntervalBackend.enclosedOn_of_memReal`, `residualBound_of_memReal_le`: interval
  containment gives an enclosure, and a residual bound `ε` when the interval lies in `[-ε, ε]`.
-/

@[expose] public section

namespace CAS.Continuum

open CAS.Certificate

universe u

/--
A CEGA-facing real interval backend.

The backend chooses the interval representation.  CEGA only asks for lower
and upper real endpoints plus sound projections from backend membership to real
inequalities, so any representation with these projections fits the same API;
`RationalInterval` is the one instance.

The interface permits empty enclosures: it does not require `lo I ≤ hi I`.
Any inhabited enclosure has ordered endpoints by `lower_mem` and `upper_mem`.
-/
class RealIntervalBackend (ι : Type u) where
  /-- Lower real endpoint. -/
  lo : ι → ℝ
  /-- Upper real endpoint. -/
  hi : ι → ℝ
  /-- Backend membership predicate, interpreted over real values. -/
  MemReal : ι → ℝ → Prop
  /-- Membership implies the lower endpoint bound. -/
  lower_mem : ∀ {I : ι} {x : ℝ}, MemReal I x → lo I ≤ x
  /-- Membership implies the upper endpoint bound. -/
  upper_mem : ∀ {I : ι} {x : ℝ}, MemReal I x → x ≤ hi I

namespace RealIntervalBackend

variable {ι : Type u} [RealIntervalBackend ι]

/-- Midpoint of the real endpoints exposed by an interval backend. -/
noncomputable def center (I : ι) : ℝ :=
  (RealIntervalBackend.lo I + RealIntervalBackend.hi I) / 2

/-- Half-width of the real endpoints exposed by an interval backend. -/
noncomputable def radius (I : ι) : ℝ :=
  (RealIntervalBackend.hi I - RealIntervalBackend.lo I) / 2

/-- Membership gives the standard midpoint/radius absolute-error estimate. -/
theorem abs_sub_center_le_radius {I : ι} {x : ℝ}
    (hx : RealIntervalBackend.MemReal I x) :
    |x - center I| ≤ radius I := by
  rw [abs_le, center, radius]
  constructor <;> linarith [RealIntervalBackend.lower_mem hx, RealIntervalBackend.upper_mem hx]

/--
If `f x` lies in the backend interval `I` for every `x ∈ s`, then `f` is enclosed on `s` by the
real endpoints of `I`.
-/
theorem enclosedOn_of_memReal {α : Type*} {f : α → ℝ} {s : Set α} {I : ι}
    (h : ∀ x, x ∈ s → RealIntervalBackend.MemReal I (f x)) :
    EnclosedOn f s (RealIntervalBackend.lo I) (RealIntervalBackend.hi I) := fun x hx ↦
  ⟨RealIntervalBackend.lower_mem (h x hx), RealIntervalBackend.upper_mem (h x hx)⟩

/-- If a backend interval lies inside `[-ε, ε]`, interval containment gives a
CEGA residual bound with error `ε`. -/
theorem residualBound_of_memReal_le {α : Type*} {residual : α → ℝ} {s : Set α}
    {I : ι} {ε : ℝ}
    (hlo : -ε ≤ RealIntervalBackend.lo I)
    (hhi : RealIntervalBackend.hi I ≤ ε)
    (h : ∀ x, x ∈ s → RealIntervalBackend.MemReal I (residual x)) :
    ResidualBound residual s ε := enclosedOn_residualBound (enclosedOn_of_memReal h) hlo hhi

/-! ## Certificate constructors -/

/--
Turn backend interval containment into an `EnclosureCert`.

A concrete evaluator only has to prove that every point of the patch maps into its backend
interval; CEGA receives a two-sided certificate with real endpoints.
-/
def enclosureCertOfMemReal {α : Type*} {f : α → ℝ} {s : Set α} (I : ι)
    (h : ∀ x, x ∈ s → RealIntervalBackend.MemReal I (f x)) :
    EnclosureCert α s :=
  EnclosureCert.ofEnclosedOn f (RealIntervalBackend.lo I) (RealIntervalBackend.hi I)
    (enclosedOn_of_memReal (I := I) h)

/--
Read a backend interval as an approximation to a chosen representative value.

If all values of `f` lie in a backend interval contained in
`[center - ε, center + ε]`, CEGA records the uniform approximation
`f ≈ center` with error `ε`. `RationalInterval.midpointApproxCert` takes the midpoint and the
radius of the interval.
-/
def approxCertAroundOfMemRealLe {α : Type*} {f : α → ℝ} {s : Set α}
    (I : ι) (center ε : ℝ)
    (hlo : center - ε ≤ RealIntervalBackend.lo I)
    (hhi : RealIntervalBackend.hi I ≤ center + ε)
    (h : ∀ x, x ∈ s → RealIntervalBackend.MemReal I (f x)) :
    ApproxCert α ℝ s :=
  ApproxCert.ofRealEnclosureAround
    (enclosureCertOfMemReal (I := I) h) center ε hlo hhi

end RealIntervalBackend

end CAS.Continuum

namespace CAS.Certificate.ApproxCert

open CAS.Continuum

variable {α ι : Type*} [RealIntervalBackend ι] {patch : Set α}

/--
Evaluate the right-hand side of an approximation certificate at one point
through a verified interval.

On the singleton `{x}` the result approximates `lhs` by the midpoint of an interval `I`
containing `rhs x`, with the original error plus the radius of `I`.
-/
noncomputable def evaluateRhsAtOfInterval
    (cert : ApproxCert α ℝ patch)
    (x : α) (hx : x ∈ patch)
    (I : ι)
    (hrhs : RealIntervalBackend.MemReal I (cert.rhs x)) :
    ApproxCert α ℝ {x} where
  lhs := cert.lhs
  rhs := fun _ ↦ RealIntervalBackend.center I
  eps := cert.eps + RealIntervalBackend.radius I
  sound := by
    intro y hy
    have hyx : y = x := by
      simpa only [Set.mem_singleton_iff] using hy
    subst y
    have hroundoff :
        ‖cert.rhs x - RealIntervalBackend.center I‖ ≤
          RealIntervalBackend.radius I := by
      rw [Real.norm_eq_abs]
      exact RealIntervalBackend.abs_sub_center_le_radius hrhs
    have hsplit :
        cert.lhs x - RealIntervalBackend.center I =
          (cert.lhs x - cert.rhs x) +
            (cert.rhs x - RealIntervalBackend.center I) := by
      abel
    rw [hsplit]
    exact (norm_add_le _ _).trans
      (add_le_add (cert.sound x hx) hroundoff)

/-- Evaluating the right side through an interval leaves the left side unchanged. -/
@[simp]
theorem evaluateRhsAtOfInterval_lhs
    (cert : ApproxCert α ℝ patch)
    (x : α) (hx : x ∈ patch)
    (I : ι)
    (hrhs : RealIntervalBackend.MemReal I (cert.rhs x)) :
    (cert.evaluateRhsAtOfInterval x hx I hrhs).lhs = cert.lhs :=
  rfl

/-- The right side of the result is the constant function at the interval midpoint. -/
@[simp]
theorem evaluateRhsAtOfInterval_rhs
    (cert : ApproxCert α ℝ patch)
    (x : α) (hx : x ∈ patch)
    (I : ι)
    (hrhs : RealIntervalBackend.MemReal I (cert.rhs x)) :
    (cert.evaluateRhsAtOfInterval x hx I hrhs).rhs =
      fun _ ↦ RealIntervalBackend.center I :=
  rfl

/-- The error of the result is the original error plus the interval radius. -/
@[simp]
theorem evaluateRhsAtOfInterval_eps
    (cert : ApproxCert α ℝ patch)
    (x : α) (hx : x ∈ patch)
    (I : ι)
    (hrhs : RealIntervalBackend.MemReal I (cert.rhs x)) :
    (cert.evaluateRhsAtOfInterval x hx I hrhs).eps =
      cert.eps + RealIntervalBackend.radius I :=
  rfl

end CAS.Certificate.ApproxCert

namespace CAS.Certificate.ModelApproxCert

open CAS.Continuum

variable {α ι : Type*} [RealIntervalBackend ι] {patch : Set α}

/--
Replace a certified model value at one point by the midpoint of a backend
interval containing that value.

The returned certificate is stated on the ordinary singleton set `{x}`. Its
error is the original model error plus the interval radius.
-/
noncomputable def evaluateAtOfInterval
    (cert : ModelApproxCert α ℝ patch)
    (x : α) (hx : x ∈ patch)
    (I : ι)
    (hmodel : RealIntervalBackend.MemReal I (cert.toApproxCert.rhs x)) :
    ApproxCert α ℝ {x} :=
  cert.toApproxCert.evaluateRhsAtOfInterval x hx I hmodel

/-- Evaluating a model certificate through an interval leaves the left side unchanged. -/
@[simp]
theorem evaluateAtOfInterval_lhs
    (cert : ModelApproxCert α ℝ patch)
    (x : α) (hx : x ∈ patch)
    (I : ι)
    (hmodel : RealIntervalBackend.MemReal I (cert.toApproxCert.rhs x)) :
    (cert.evaluateAtOfInterval x hx I hmodel).lhs = cert.toApproxCert.lhs :=
  rfl

/-- The right side of the result is the constant function at the interval midpoint. -/
@[simp]
theorem evaluateAtOfInterval_rhs
    (cert : ModelApproxCert α ℝ patch)
    (x : α) (hx : x ∈ patch)
    (I : ι)
    (hmodel : RealIntervalBackend.MemReal I (cert.toApproxCert.rhs x)) :
    (cert.evaluateAtOfInterval x hx I hmodel).rhs =
      fun _ ↦ RealIntervalBackend.center I :=
  rfl

/-- The error of the result is the model error plus the interval radius. -/
@[simp]
theorem evaluateAtOfInterval_eps
    (cert : ModelApproxCert α ℝ patch)
    (x : α) (hx : x ∈ patch)
    (I : ι)
    (hmodel : RealIntervalBackend.MemReal I (cert.toApproxCert.rhs x)) :
    (cert.evaluateAtOfInterval x hx I hmodel).eps =
      cert.toApproxCert.eps + RealIntervalBackend.radius I :=
  rfl

end CAS.Certificate.ModelApproxCert

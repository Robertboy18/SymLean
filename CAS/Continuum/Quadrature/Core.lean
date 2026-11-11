/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.Quadrature
public import CAS.Continuum.IntervalBackend

/-!
# Interval-backend quadrature certificates

`QuadratureCert.replaceValueOfInterval` replaces the value of a quadrature certificate by the
midpoint of a `RealIntervalBackend` interval containing it, and adds the interval radius to the
error. A backend only proves that its interval contains the exact quadrature value.

The certificate carrier and its backend-independent composition lemmas live in
`CAS.Certificate.Quadrature`.
-/

@[expose] public section

namespace CAS.Continuum

namespace QuadratureCert

/--
Replace an exact-real quadrature value by the midpoint of an interval backend
that contains it, adding the radius of the interval to the error.
-/
noncomputable def replaceValueOfInterval
    {ι : Type*} [RealIntervalBackend ι]
    {f : ℝ → ℝ} {a b : ℝ}
    (q : QuadratureCert f a b) (I : ι)
    (hencloses : RealIntervalBackend.MemReal I q.value) :
    QuadratureCert f a b :=
  q.replaceValue
    (RealIntervalBackend.center I)
    (RealIntervalBackend.radius I)
    (by
      rw [Real.norm_eq_abs]
      exact RealIntervalBackend.abs_sub_center_le_radius hencloses)

/-- The certified value after the midpoint-radius step is the centre of the enclosing interval. -/
@[simp]
theorem replaceValueOfInterval_value
    {ι : Type*} [RealIntervalBackend ι]
    {f : ℝ → ℝ} {a b : ℝ}
    (q : QuadratureCert f a b) (I : ι)
    (hencloses : RealIntervalBackend.MemReal I q.value) :
    (q.replaceValueOfInterval I hencloses).value =
      RealIntervalBackend.center I :=
  rfl

/-- The error budget grows by exactly the radius of the enclosing interval: the analytic error
of the original certificate plus the half-width of the numerical enclosure. -/
@[simp]
theorem replaceValueOfInterval_error
    {ι : Type*} [RealIntervalBackend ι]
    {f : ℝ → ℝ} {a b : ℝ}
    (q : QuadratureCert f a b) (I : ι)
    (hencloses : RealIntervalBackend.MemReal I q.value) :
    (q.replaceValueOfInterval I hencloses).error =
      q.error + RealIntervalBackend.radius I :=
  rfl

end QuadratureCert

end CAS.Continuum

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.Quadrature
public import CAS.Continuum.IntervalBackend

/-!
# Quadrature from certified interval ranges

An interval backend can enclose an integral without selecting sample points or
assuming differentiability. If one backend interval contains every value of a
scalar integrand on `[[a, b]]`, then the constant midpoint model has uniform
error bounded by the interval radius. Integrating that estimate gives the
`QuadratureCert.ofIntervalRange` with error

```text
range radius * |b - a|.
```

The interval type is any `RealIntervalBackend`; the library's instance is `RationalInterval`.
A `QuadratureTree` can take such certificates as its leaves.
-/

@[expose] public section

open MeasureTheory

namespace CAS.Continuum
namespace QuadratureCert

/--
Turn a uniform backend interval enclosure of a scalar integrand into a
quadrature certificate.

The proposed value is the interval midpoint multiplied by the oriented
interval length. The error uses the unoriented length, so the result is valid
for either endpoint order.
-/
noncomputable def ofIntervalRange
    {ι : Type*} [RealIntervalBackend ι]
    {f : ℝ → ℝ} {a b : ℝ}
    (I : ι)
    (hf : IntervalIntegrable f volume a b)
    (hencloses : ∀ x ∈ Set.uIcc a b, RealIntervalBackend.MemReal I (f x)) :
    QuadratureCert f a b where
  value := (b - a) • RealIntervalBackend.center I
  error := RealIntervalBackend.radius I * |b - a|
  sound := by
    rw [← intervalIntegral.integral_const (RealIntervalBackend.center I)]
    rw [← intervalIntegral.integral_sub hf intervalIntegrable_const]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    simpa [Real.norm_eq_abs] using
      RealIntervalBackend.abs_sub_center_le_radius
        (hencloses x (Set.uIoc_subset_uIcc hx))

end QuadratureCert
end CAS.Continuum

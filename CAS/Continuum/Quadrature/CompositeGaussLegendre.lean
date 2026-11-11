/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.PanelRule
public import CAS.Continuum.Quadrature.GaussLegendrePeano

/-!
# Certified composite two-point Gauss-Legendre quadrature

The shared uniform-composite theorem applies the sharp two-point
Gauss-Legendre rule on `N` equal panels and accumulates the classical error

`C * (b-a)^5 / (4320 * N^4)`.

Here `C` bounds `|f⁗|` on every panel and `f` is `C⁴` on `[a,b]`.  The constant
`4320 = 32 · 135` is the one-panel two-point Gauss constant `(b-a)^5/4320`, the
image of the remainder `f⁗(ξ)/135` of the two-point rule on `[-1,1]`; summing `N` panels of
width `(b-a)/N` gives the `N^4` decay.

## Main results

* `gaussLegendreTwoRule.fourthOrder`: the rule as a `PanelRule 4` with denominator `4320`; its
  one-panel certificates, composite rules, tolerance plans and adaptive search are those of
  `PanelRule`.
* `QuadratureCert.compositeGaussLegendreTwo`: the certificate, built from a
  per-panel `IteratedDerivativeBounderOn 4` and the sharp one-panel estimate
  `norm_integral_sub_gaussLegendreTwoRule_valueOn_le`.
* `compositeGaussLegendreTwo_value`, `compositeGaussLegendreTwo_error`: its value
  and error budget are definitionally the composite sum and the bound above.

## Implementation notes

`gaussLegendreTwoRule.fourthOrder` packages the rule with the denominator `4320` and the
one-panel theorem of `GaussLegendrePeano`. The certificate is then `PanelRule.composite`,
which adds the `N` panel bounds `C ((b-a)/N)^5 / 4320`, so nothing specific to Gauss-Legendre
is proved here.

## References

* NIST Digital Library of Mathematical Functions, §3.5 Quadrature, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/3.5>. (3.5.19) and (3.5.21), with `n = 2`, for the remainder
  `f⁗(ξ)/135` on `[-1, 1]`.
-/

@[expose] public section

open Set

namespace CAS.Continuum

/-- Exact-real composite two-point Gauss-Legendre value. -/
noncomputable def compositeGaussLegendreTwoValue
    (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  uniformCompositeValue gaussLegendreTwoRule f N a b

namespace gaussLegendreTwoRule

/-- The two-point Gauss-Legendre rule as a panel rule of order `4`, with its sharp one-panel
constant `4320`. -/
noncomputable def fourthOrder : PanelRule 4 where
  rule := gaussLegendreTwoRule
  denominator := 4320
  denominator_pos := by norm_num
  norm_integral_sub_valueOn_le := norm_integral_sub_gaussLegendreTwoRule_valueOn_le

/-- The underlying normalized rule. -/
@[simp]
theorem fourthOrder_rule : fourthOrder.rule = gaussLegendreTwoRule :=
  rfl

/-- The one-panel denominator. -/
@[simp]
theorem fourthOrder_denominator : fourthOrder.denominator = 4320 :=
  rfl

end gaussLegendreTwoRule

namespace QuadratureCert

/-- Composite two-point Gauss-Legendre certificate with sharp analytic error. -/
noncomputable def compositeGaussLegendreTwo
    {f : ℝ → ℝ} {a b C : ℝ} {N : ℕ}
    (hab : a < b) (hN : 0 < N)
    (hf : ContDiffOn ℝ 4 f (Set.Icc a b))
    (bounder : IteratedDerivativeBounderOn 4 f (Set.Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Set.Icc l r ⊆ Set.Icc a b), bounder.bound hlr hsub ≤ C) :
    QuadratureCert f a b :=
  gaussLegendreTwoRule.fourthOrder.composite hab hN hf bounder hbound

/-- The certified value is the exact-real composite two-point Gauss-Legendre sum over the `N`
equal panels. -/
@[simp]
theorem compositeGaussLegendreTwo_value
    {f : ℝ → ℝ} {a b C : ℝ} {N : ℕ}
    (hab : a < b) (hN : 0 < N)
    (hf : ContDiffOn ℝ 4 f (Set.Icc a b))
    (bounder : IteratedDerivativeBounderOn 4 f (Set.Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Set.Icc l r ⊆ Set.Icc a b), bounder.bound hlr hsub ≤ C) :
    (compositeGaussLegendreTwo hab hN hf bounder hbound).value =
      compositeGaussLegendreTwoValue f N a b :=
  rfl

/-- The composite Gauss-Legendre certificate records its accumulated fourth-order error bound. -/
@[simp]
theorem compositeGaussLegendreTwo_error
    {f : ℝ → ℝ} {a b C : ℝ} {N : ℕ}
    (hab : a < b) (hN : 0 < N)
    (hf : ContDiffOn ℝ 4 f (Set.Icc a b))
    (bounder : IteratedDerivativeBounderOn 4 f (Set.Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Set.Icc l r ⊆ Set.Icc a b), bounder.bound hlr hsub ≤ C) :
    (compositeGaussLegendreTwo hab hN hf bounder hbound).error =
      C * (b - a) ^ 5 / (4320 * (N : ℝ) ^ 4) :=
  rfl

end QuadratureCert
end CAS.Continuum

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.PanelRule
public import CAS.Continuum.Quadrature.SimpsonPeano
public import CAS.Continuum.Interval.Rational.Arithmetic

/-!
# Certified composite Simpson quadrature

For `N > 0`, composite Simpson applies the normalized Simpson rule on `N`
equal panels.  Each panel contains two half-steps, so this is the usual
composite Simpson formula with `2N` subintervals.

The shared uniform-composite theorem accumulates the sharp one-panel constant
to

`C * (b-a)^5 / (2880 * N^4)`,

where `C` bounds `|f⁗|` on every panel and `f` is `C⁴` on `[a,b]`.  This is the
textbook composite Simpson estimate `(b-a) h^4 ‖f⁗‖_∞ / 180` with half-step
`h = (b-a)/(2N)`, since `180 · 16 = 2880`.

## Main definitions

* `simpsonRule.fourthOrder`: Simpson's rule as a `PanelRule 4` with denominator `2880`; its
  one-panel certificates, composite rules, tolerance plans and adaptive search are those of
  `PanelRule`.
* `simpsonRule.enclosure`: the rational interval enclosure of one Simpson panel.
* `QuadratureCert.compositeSimpson`: the composite certificate, assembled from a per-panel
  `IteratedDerivativeBounderOn 4` and the sharp one-panel estimate
  `norm_integral_sub_simpsonRule_valueOn_le`.

## Main results

* `compositeSimpson_value`, `compositeSimpson_error`: its value and error budget
  are definitionally the composite sum and the bound above.
* `simpsonRule.enclosure_sound`: for `a < b`, `f` of class `C⁴` on `[a, b]` with
  `‖iteratedDerivWithin 4 f (Icc a b) x‖ ≤ M` there, and samples enclosing `f`, the panel
  interval contains `∫ x in a..b, f x`.

## Implementation notes

`simpsonRule.enclosure` is the one-panel arithmetic of `CAS.Continuum.Quadrature.BatchSimpson`,
the certificate of `nintegrate` and of bare `cega` on an interval integral. From a rational
panel `[a, b]`, a budget `M ≥ 0` for the fourth derivative and sample intervals `L`, `C`, `R` at
`a`, `(a+b)/2` and `b`, it computes in exact rational arithmetic `(b-a)/6 * (L + 4 C + R)`,
widened on both sides by `M (b-a)^5 / 2880`. The nonnegative factors keep the endpoints ordered.
The sample widths stay in the weighted sum, beside the analytic remainder. The computation proves
nothing about a function: the smoothness, the derivative bound and the three sample enclosures
are hypotheses of `simpsonRule.enclosure_sound`, which the caller proves. Because the remainder
comes from the Peano-kernel estimate, no antiderivative of `f` is needed.

## References

* NIST Digital Library of Mathematical Functions, §3.5 Quadrature, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/3.5>. Equations (3.5.7) and (3.5.8), the composite Simpson rule on an
  even number of subintervals and its error term `-((b-a)/180) h⁴ f⁽⁴⁾(ξ)`.
-/

@[expose] public section

open Set

namespace CAS.Continuum

/-- Exact-real composite Simpson value over `N` equal panels. -/
noncomputable def compositeSimpsonValue
    (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  uniformCompositeValue simpsonRule f N a b

/-- Ordered weighted terms for composite Simpson quadrature. -/
noncomputable def compositeSimpsonTerms
    (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : List (ℝ × ℝ) :=
  uniformCompositeTerms simpsonRule f N a b

/-- Flattened composite Simpson terms have exactly the exact-real value. -/
theorem weightedSum_compositeSimpsonTerms
    (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) :
    weightedSum (compositeSimpsonTerms f N a b) =
      compositeSimpsonValue f N a b :=
  weightedSum_uniformCompositeTerms simpsonRule f N a b

namespace simpsonRule

/-- A rational enclosure of a Simpson panel, including its fourth-derivative error.
The three sample intervals may come from any proved evaluation method. -/
def enclosure (a b M : ℚ) (hab : a ≤ b) (hM : 0 ≤ M)
    (left middle right : RationalInterval) : RationalInterval :=
  let samples := (left.add (middle.scaleNonneg 4 (by norm_num))).add right
  let value := samples.scaleNonneg ((b - a) / 6) (by positivity)
  let error := M * (b - a) ^ 5 / 2880
  value.add (RationalInterval.ofBounds (-error) error (by
    have herror : 0 ≤ error := by positivity
    exact (neg_nonpos.mpr herror).trans herror))

/-- The sample enclosures and a fourth-derivative bound certify the whole panel integral.
The proof uses the Peano-kernel estimate and needs no elementary antiderivative. -/
theorem enclosure_sound {f : ℝ → ℝ} (a b M : ℚ) (hab : a < b) (hM : 0 ≤ M)
    (left middle right : RationalInterval)
    (hf : ContDiffOn ℝ 4 f (Icc (a : ℝ) (b : ℝ)))
    (hfourth : ∀ x ∈ Icc (a : ℝ) (b : ℝ),
      ‖iteratedDerivWithin 4 f (Icc (a : ℝ) (b : ℝ)) x‖ ≤ (M : ℝ))
    (hleft : left.MemReal (f (a : ℝ)))
    (hmiddle : middle.MemReal (f (((a + b) / 2 : ℚ) : ℝ)))
    (hright : right.MemReal (f (b : ℝ))) :
    (enclosure a b M hab.le hM left middle right).MemReal
      (∫ x in (a : ℝ)..(b : ℝ), f x) := by
  have herr : |(∫ x in (a : ℝ)..(b : ℝ), f x) - simpsonRule.valueOn f (a : ℝ) (b : ℝ)| ≤
      ((M * (b - a) ^ 5 / 2880 : ℚ) : ℝ) := by
    simpa only [Real.norm_eq_abs, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_sub,
      Rat.cast_ofNat] using
      norm_integral_sub_simpsonRule_valueOn_le (Rat.cast_lt.mpr hab) hf hfourth
  rw [← add_sub_cancel (simpsonRule.valueOn f (a : ℝ) (b : ℝ)) (∫ x in (a : ℝ)..(b : ℝ), f x)]
  refine RationalInterval.add_sound ?_ ?_
  · rw [simpsonRule_valueOn_eq_formula]
    convert RationalInterval.scaleNonneg_sound (q := (b - a) / 6) (by positivity)
      (RationalInterval.add_sound (RationalInterval.add_sound hleft
        (RationalInterval.scaleNonneg_sound (q := 4) (by norm_num) hmiddle)) hright) using 1
    push_cast
    ring
  · simpa only [RationalInterval.MemReal, RationalInterval.ofBounds, Rat.cast_neg] using
      abs_le.mp herr

/-- Simpson's rule as a panel rule of order `4`, with its sharp one-panel constant `2880`. -/
noncomputable def fourthOrder : PanelRule 4 where
  rule := simpsonRule
  denominator := 2880
  denominator_pos := by norm_num
  norm_integral_sub_valueOn_le := norm_integral_sub_simpsonRule_valueOn_le

/-- The underlying normalized rule. -/
@[simp]
theorem fourthOrder_rule : fourthOrder.rule = simpsonRule :=
  rfl

/-- The one-panel denominator. -/
@[simp]
theorem fourthOrder_denominator : fourthOrder.denominator = 2880 :=
  rfl

end simpsonRule

namespace QuadratureCert

/-- Composite Simpson quadrature with its sharp accumulated analytic error. -/
noncomputable def compositeSimpson
    {f : ℝ → ℝ} {a b C : ℝ} {N : ℕ}
    (hab : a < b) (hN : 0 < N)
    (hf : ContDiffOn ℝ 4 f (Icc a b))
    (bounder : IteratedDerivativeBounderOn 4 f (Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Icc l r ⊆ Icc a b), bounder.bound hlr hsub ≤ C) :
    QuadratureCert f a b :=
  simpsonRule.fourthOrder.composite hab hN hf bounder hbound

/-- The certified value is the exact-real composite Simpson sum over the `N` equal panels. -/
@[simp]
theorem compositeSimpson_value
    {f : ℝ → ℝ} {a b C : ℝ} {N : ℕ}
    (hab : a < b) (hN : 0 < N)
    (hf : ContDiffOn ℝ 4 f (Icc a b))
    (bounder : IteratedDerivativeBounderOn 4 f (Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Icc l r ⊆ Icc a b), bounder.bound hlr hsub ≤ C) :
    (compositeSimpson hab hN hf bounder hbound).value =
      compositeSimpsonValue f N a b :=
  rfl

/-- The composite Simpson certificate records its accumulated fourth-order error bound. -/
@[simp]
theorem compositeSimpson_error
    {f : ℝ → ℝ} {a b C : ℝ} {N : ℕ}
    (hab : a < b) (hN : 0 < N)
    (hf : ContDiffOn ℝ 4 f (Icc a b))
    (bounder : IteratedDerivativeBounderOn 4 f (Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Icc l r ⊆ Icc a b), bounder.bound hlr hsub ≤ C) :
    (compositeSimpson hab hN hf bounder hbound).error =
      C * (b - a) ^ 5 / (2880 * (N : ℝ) ^ 4) :=
  rfl

end QuadratureCert
end CAS.Continuum

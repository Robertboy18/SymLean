/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.Adaptive
public import CAS.Continuum.Quadrature.UniformComposite
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Quadrature rules with a one-panel error estimate of order `m`

A `PanelRule m` is a normalized quadrature rule `Q` together with a proof of the one-panel
estimate

`‖∫ₐᵇ f - Q(f)‖ ≤ M (b-a)^(m+1) / D`

for every `f ∈ Cᵐ[a,b]` with `‖f⁽ᵐ⁾‖ ≤ M` on `[a,b]`.  Composite rules on `N` equal panels,
tolerance planning and adaptive bisection only need these two pieces of data, so they are
built here once for every order.  The trapezoidal and midpoint rules are the second-order
instances (`D = 12` and `D = 24`, `trapezoidRule.secondOrder` and `midpointRule.secondOrder`);
Simpson's rule and the two-point Gauss-Legendre rule are the fourth-order ones (`D = 2880` and
`D = 4320`, `simpsonRule.fourthOrder` and `gaussLegendreTwoRule.fourthOrder`).

## Main definitions

* `PanelRule.certOfBounder`: the one-panel certificate whose error uses a local
  `IteratedDerivativeBounderOn m` bound.
* `PanelRule.panel`, `PanelRule.search`: a one-leaf tree and the depth-bounded adaptive
  bisection search of `AdaptiveQuadrature.search`, with leaves built by `certOfBounder`.
* `PanelRule.composite`: the composite certificate on `N` equal panels with error
  `C (b-a)^(m+1) / (D N^m)`.
* `PanelPlan.requiredPanels`: the panel count `max 1 ⌈(B / ε)^(1/m)⌉₊` for the error numerator
  `B = C (b-a)^(m+1) / D` and tolerance `ε`.
* `PanelPlan.ratRequiredPanels`: an executable count over `ℚ`, `Nat.nthRoot m ⌈B / ε⌉₊ + 1`.
* `PanelRule.compositeToTolerance`: the composite certificate with that panel count.

## Main results

* `PanelPlan.uniformCompositeError_le`: the planned panel count meets the tolerance.
* `PanelPlan.div_ratRequiredPanels_pow_le`: so does the executable one, for every rational `B`.
* `PanelRule.compositeToTolerance_error_le`, `PanelRule.compositeToTolerance_sound_le`: the
  planned composite rule approximates the integral within the requested tolerance.

## Implementation notes

A rule joins the library by proving one inequality, its one-panel estimate; the rest is shared.
`composite` is `QuadratureCert.uniformCompositeOfOrder`, which splits `[a,b]` into `N` equal
panels and adds the panel bounds, each `C ((b-a)/N)^(m+1) / D`. `search` passes `certOfBounder`
to `AdaptiveQuadrature.search`, so every leaf of an adaptive tree carries the one-panel bound
with the bounder's local derivative bound on that leaf. `PanelPlan.requiredPanels` inverts the
composite error model with a real `m`-th root. It is a noncomputable definition used in proofs;
`PanelPlan.ratRequiredPanels` computes a count over `ℚ` with Mathlib's integer root
`Nat.nthRoot`. No theorem relates the two counts; each is proved to meet the tolerance. The
compound rules and their orders are classical; the packaging into one structure is ours.

## References

* Philip J. Davis and Philip Rabinowitz, *Methods of Numerical Integration*, 2nd ed., Academic
  Press, Orlando, 1984, <https://doi.org/10.1016/C2013-0-10566-1>. A standard reference for
  the classical compound rules.
-/

@[expose] public section

open MeasureTheory Set

namespace CAS.Continuum

/-- A normalized quadrature rule with a one-panel error estimate of order `m`: the error on
`[a,b]` is at most `M (b-a)^(m+1) / D` whenever `‖f⁽ᵐ⁾‖ ≤ M` there. -/
structure PanelRule (m : ℕ) where
  /-- The rule on the reference interval `[0,1]`. -/
  rule : QuadratureRule
  /-- The denominator `D` in the one-panel error `M (b-a)^(m+1) / D`. -/
  denominator : ℝ
  /-- The denominator is positive. -/
  denominator_pos : 0 < denominator
  /-- The one-panel estimate on every ordered interval. -/
  norm_integral_sub_valueOn_le :
    ∀ {f : ℝ → ℝ} {a b M : ℝ}, a < b →
      ContDiffOn ℝ m f (Icc a b) →
      (∀ x ∈ Icc a b, ‖iteratedDerivWithin m f (Icc a b) x‖ ≤ M) →
      ‖(∫ x in a..b, f x) - rule.valueOn f a b‖ ≤
        M * (b - a) ^ (m + 1) / denominator

namespace PanelPlan

/-- Numerator `C (b-a)^(m+1) / D` of an order-`m` composite error model. -/
noncomputable def errorConstant (m : ℕ) (denominator a b C : ℝ) : ℝ :=
  C * (b - a) ^ (m + 1) / denominator

/-- Panel count `max 1 ⌈(B / ε)^(1/m)⌉₊` for an order-`m` error model with numerator
`B = errorConstant m D a b C` and tolerance `ε`. Sufficiency requires `m > 0` and a positive
tolerance; a negative numerator is below the tolerance for every panel count. -/
noncomputable def requiredPanels (m : ℕ) (denominator a b C tolerance : ℝ) : ℕ :=
  max 1 ⌈(errorConstant m denominator a b C / tolerance) ^ ((m : ℝ)⁻¹)⌉₊

/-- The planned panel count is always positive, because of the `max 1`. -/
theorem requiredPanels_pos (m : ℕ) (denominator a b C tolerance : ℝ) :
    0 < requiredPanels m denominator a b C tolerance :=
  lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

/-- The error numerator is nonnegative on an ordered interval when `0 ≤ C` and `0 < D`. -/
theorem errorConstant_nonneg {m : ℕ} {denominator a b C : ℝ}
    (hdenominator : 0 < denominator) (hab : a ≤ b) (hC : 0 ≤ C) :
    0 ≤ errorConstant m denominator a b C :=
  div_nonneg (mul_nonneg hC (pow_nonneg (sub_nonneg.mpr hab) _)) hdenominator.le

/-- For a positive order `m`, the planned panel count reduces the error model `B / N^m`
below the tolerance. -/
theorem errorConstant_div_requiredPanels_pow_le {m : ℕ} (hm : m ≠ 0)
    {denominator a b C tolerance : ℝ} (htolerance : 0 < tolerance) :
    errorConstant m denominator a b C /
        (requiredPanels m denominator a b C tolerance : ℝ) ^ m ≤ tolerance := by
  have hN : (0 : ℝ) < (requiredPanels m denominator a b C tolerance : ℝ) ^ m :=
    pow_pos (Nat.cast_pos.2 (requiredPanels_pos ..)) m
  rcases lt_or_ge (errorConstant m denominator a b C) 0 with hB | hB
  · exact (div_neg_of_neg_of_pos hB hN).le.trans htolerance.le
  have hratio : 0 ≤ errorConstant m denominator a b C / tolerance := div_nonneg hB htolerance.le
  rw [div_le_iff₀ hN, ← div_le_iff₀' htolerance, ← Real.rpow_inv_natCast_pow hratio hm]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hratio _)
    ((Nat.le_ceil _).trans (by exact_mod_cast Nat.le_max_right 1 _)) m

/-- The planned mesh meets the tolerance in the unfolded form produced by
`QuadratureCert.uniformCompositeOfOrder`: `C (b-a)^(m+1) / (D N^m) ≤ ε`. -/
theorem uniformCompositeError_le {m : ℕ} (hm : m ≠ 0)
    {denominator a b C tolerance : ℝ} (htolerance : 0 < tolerance) :
    C * (b - a) ^ (m + 1) /
        (denominator * (requiredPanels m denominator a b C tolerance : ℝ) ^ m) ≤
      tolerance := by
  simpa only [errorConstant, div_div] using
    errorConstant_div_requiredPanels_pow_le (denominator := denominator) (a := a) (b := b)
      (C := C) hm htolerance

/-- Executable panel count `Nat.nthRoot m ⌈B / ε⌉₊ + 1` for an order-`m` error model `B / N^m`
over `ℚ`: one more than the floor `m`-th root (Mathlib's `Nat.nthRoot`) of `⌈B / ε⌉₊`. -/
def ratRequiredPanels (m : ℕ) (errorConstant tolerance : ℚ) : ℕ :=
  Nat.nthRoot m ⌈errorConstant / tolerance⌉₊ + 1

/-- For a positive order `m` and a positive tolerance, the executable panel count reduces the
error model `B / N^m` below the tolerance, for every rational `B`. -/
theorem div_ratRequiredPanels_pow_le {m : ℕ} (hm : m ≠ 0) {errorConstant tolerance : ℚ}
    (htolerance : 0 < tolerance) :
    errorConstant / (ratRequiredPanels m errorConstant tolerance : ℚ) ^ m ≤ tolerance := by
  rw [div_le_iff₀ (pow_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) m), ← div_le_iff₀' htolerance]
  exact (Nat.le_ceil _).trans
    (by exact_mod_cast (Nat.lt_pow_nthRoot_add_one hm ⌈errorConstant / tolerance⌉₊).le)

end PanelPlan

namespace PanelRule

variable {m : ℕ} (R : PanelRule m)

/-- One-panel certificate whose error is `M (b-a)^(m+1) / D`, where `M` is the local bound
for `‖f⁽ᵐ⁾‖` on `[a,b]` reported by the bounder. -/
noncomputable def certOfBounder
    {f : ℝ → ℝ} {s : Set ℝ} (hf : ContDiffOn ℝ m f s)
    (bounder : IteratedDerivativeBounderOn m f s)
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s) :
    QuadratureCert f a b :=
  QuadratureCert.ofErrorBound
    (R.rule.valueOn f a b)
    (bounder.bound hab hsub * (b - a) ^ (m + 1) / R.denominator)
    (R.norm_integral_sub_valueOn_le hab (hf.mono hsub) fun _x hx ↦
      bounder.norm_iteratedDerivWithin_le hab hsub hx)

/-- The certified value is the rule transported to `[a,b]`. -/
@[simp]
theorem certOfBounder_value
    {f : ℝ → ℝ} {s : Set ℝ} (hf : ContDiffOn ℝ m f s)
    (bounder : IteratedDerivativeBounderOn m f s)
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s) :
    (R.certOfBounder hf bounder hab hsub).value = R.rule.valueOn f a b :=
  rfl

/-- The certified error is `M (b-a)^(m+1) / D` for the bounder's local bound `M`. -/
@[simp]
theorem certOfBounder_error
    {f : ℝ → ℝ} {s : Set ℝ} (hf : ContDiffOn ℝ m f s)
    (bounder : IteratedDerivativeBounderOn m f s)
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s) :
    (R.certOfBounder hf bounder hab hsub).error =
      bounder.bound hab hsub * (b - a) ^ (m + 1) / R.denominator :=
  rfl

/-- One panel as a one-leaf quadrature tree. -/
noncomputable def panel
    {f : ℝ → ℝ} {s : Set ℝ} (hf : ContDiffOn ℝ m f s)
    (bounder : IteratedDerivativeBounderOn m f s)
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s) :
    QuadratureTree f a b :=
  AdaptiveQuadrature.panel
    (fun {_ _} h hpanelSub ↦ R.certOfBounder hf bounder h hpanelSub)
    (fun {_ _} h hpanelSub ↦
      (hf.continuousOn.mono hpanelSub).intervalIntegrable_of_Icc h.le)
    hab hsub

/-- The one-leaf tree inherits the one-panel error `M (b-a)^(m+1) / D`. -/
@[simp]
theorem panel_error
    {f : ℝ → ℝ} {s : Set ℝ} (hf : ContDiffOn ℝ m f s)
    (bounder : IteratedDerivativeBounderOn m f s)
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s) :
    (R.panel hf bounder hab hsub).toCert.error =
      bounder.bound hab hsub * (b - a) ^ (m + 1) / R.denominator :=
  rfl

/--
Depth-bounded adaptive search with the rule's panels as leaves.

At depth zero the current panel must already meet the tolerance.  At positive depth, a
rejected panel is bisected and each child is checked against half the parent tolerance.
Exhausting the depth budget returns `none`.
-/
noncomputable def search
    {f : ℝ → ℝ} {s : Set ℝ} (hf : ContDiffOn ℝ m f s)
    (bounder : IteratedDerivativeBounderOn m f s) :
    (depth : ℕ) → (a b : ℝ) → (hab : a < b) →
      Icc a b ⊆ s → (tolerance : ℝ) →
      Option (QuadratureTree.WithErrorAtMost f a b tolerance) :=
  AdaptiveQuadrature.search
    (fun {_ _} h hpanelSub ↦ R.certOfBounder hf bounder h hpanelSub)
    (fun {_ _} h hpanelSub ↦
      (hf.continuousOn.mono hpanelSub).intervalIntegrable_of_Icc h.le)

/-- Composite certificate on `N` equal panels, with error `C (b-a)^(m+1) / (D N^m)` when `C`
dominates every per-panel bound for `‖f⁽ᵐ⁾‖`. -/
noncomputable def composite
    {f : ℝ → ℝ} {a b C : ℝ} {N : ℕ}
    (hab : a < b) (hN : 0 < N)
    (hf : ContDiffOn ℝ m f (Icc a b))
    (bounder : IteratedDerivativeBounderOn m f (Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Icc l r ⊆ Icc a b), bounder.bound hlr hsub ≤ C) :
    QuadratureCert f a b :=
  QuadratureCert.uniformCompositeOfOrder m R.rule R.denominator
    hab hN hf bounder hbound
    (fun hpanel hdiff hlocal ↦ R.norm_integral_sub_valueOn_le hpanel hdiff hlocal)

/-- The composite value is the rule summed over the `N` equal panels. -/
@[simp]
theorem composite_value
    {f : ℝ → ℝ} {a b C : ℝ} {N : ℕ}
    (hab : a < b) (hN : 0 < N)
    (hf : ContDiffOn ℝ m f (Icc a b))
    (bounder : IteratedDerivativeBounderOn m f (Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Icc l r ⊆ Icc a b), bounder.bound hlr hsub ≤ C) :
    (R.composite hab hN hf bounder hbound).value = uniformCompositeValue R.rule f N a b :=
  rfl

/-- The composite error budget is `C (b-a)^(m+1) / (D N^m)`. -/
@[simp]
theorem composite_error
    {f : ℝ → ℝ} {a b C : ℝ} {N : ℕ}
    (hab : a < b) (hN : 0 < N)
    (hf : ContDiffOn ℝ m f (Icc a b))
    (bounder : IteratedDerivativeBounderOn m f (Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Icc l r ⊆ Icc a b), bounder.bound hlr hsub ≤ C) :
    (R.composite hab hN hf bounder hbound).error =
      C * (b - a) ^ (m + 1) / (R.denominator * (N : ℝ) ^ m) :=
  rfl

/-- Composite certificate whose panel count is chosen by `PanelPlan.requiredPanels`. -/
noncomputable def compositeToTolerance
    {f : ℝ → ℝ} {a b C tolerance : ℝ}
    (hab : a < b)
    (hf : ContDiffOn ℝ m f (Icc a b))
    (bounder : IteratedDerivativeBounderOn m f (Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Icc l r ⊆ Icc a b), bounder.bound hlr hsub ≤ C) :
    QuadratureCert f a b :=
  R.composite hab (PanelPlan.requiredPanels_pos m R.denominator a b C tolerance)
    hf bounder hbound

/-- For a positive order and a positive tolerance, the planned composite certificate has error
budget at most the tolerance. -/
theorem compositeToTolerance_error_le (hm : m ≠ 0)
    {f : ℝ → ℝ} {a b C tolerance : ℝ}
    (hab : a < b)
    (hf : ContDiffOn ℝ m f (Icc a b))
    (bounder : IteratedDerivativeBounderOn m f (Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Icc l r ⊆ Icc a b), bounder.bound hlr hsub ≤ C)
    (htolerance : 0 < tolerance) :
    (R.compositeToTolerance (tolerance := tolerance) hab hf bounder hbound).error ≤
      tolerance :=
  PanelPlan.uniformCompositeError_le (denominator := R.denominator) (a := a) (b := b) (C := C) hm
    htolerance

/-- The planned composite value approximates the integral within the tolerance. -/
theorem compositeToTolerance_sound_le (hm : m ≠ 0)
    {f : ℝ → ℝ} {a b C tolerance : ℝ}
    (hab : a < b)
    (hf : ContDiffOn ℝ m f (Icc a b))
    (bounder : IteratedDerivativeBounderOn m f (Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Icc l r ⊆ Icc a b), bounder.bound hlr hsub ≤ C)
    (htolerance : 0 < tolerance) :
    ‖(∫ x in a..b, f x) -
        (R.compositeToTolerance (tolerance := tolerance) hab hf bounder hbound).value‖ ≤
      tolerance :=
  (R.compositeToTolerance (tolerance := tolerance) hab hf bounder hbound).sound.trans
    (R.compositeToTolerance_error_le hm hab hf bounder hbound htolerance)

end PanelRule
end CAS.Continuum

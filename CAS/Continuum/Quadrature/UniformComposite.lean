/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.DerivativeBounds
public import CAS.Continuum.Quadrature.Rule

/-!
# Uniform composite quadrature

Rule-independent infrastructure for composite quadrature:

* a uniform mesh on an ordered interval;
* exact-real values and ordered term lists for any normalized rule;
* accumulation of any one-panel `C h^(m+1) / D` theorem of order `m` into the global
  bound `C (b-a)^(m+1) / (D N^m)`, with the fourth-order case `C (b-a)^5 / (D N^4)`
  stated separately.

Concrete rule modules supply only their rule and their proved one-panel constant.

## Main definitions

* `uniformMeshPoint`: the mesh `x_k = a + k (b-a)/N`.
* `uniformCompositeValue`, `uniformCompositeTerms`: the exact-real composite value, and the
  ordered list of its weighted terms, panel after panel.
* `QuadratureCert.uniformCompositeOfOrder`: given a `Cᵐ` integrand on `[a,b]`, a per-panel
  bounder for `‖f⁽ᵐ⁾‖` dominated by `C`, and a one-panel estimate
  `‖∫ - rule‖ ≤ C (r-l)^(m+1) / D`, the composite certificate has error
  `C (b-a)^(m+1) / (D N^m)`.
* `QuadratureCert.uniformCompositeFourthOrder`: given a `C⁴` integrand on `[a,b]`,
  a per-panel bounder for `‖f⁗‖` dominated by `C`, and a one-panel estimate
  `‖∫ - rule‖ ≤ C (r-l)^5 / D`, the composite certificate has error
  `C (b-a)^5 / (D N^4)`, the case `m = 4`.

## Main results

* `uniformMeshPoint_zero`, `uniformMeshPoint_end`, `uniformMeshPoint_succ_sub`,
  `uniformMeshPoint_strictMono`: elementary properties of the mesh.
* `weightedSum_uniformCompositeTerms`: the term list sums to the exact composite value.
* `QuadratureCert.uniformCompositeOfOrder_value`, `QuadratureCert.uniformCompositeOfOrder_error`:
  the certificate stores the composite value and the global error bound.

## Implementation notes

`uniformCompositeOfOrder` splits the integral over adjacent panels with
`intervalIntegral.sum_integral_adjacent_intervals`, applies the one-panel estimate on each panel
of width `(b-a)/N`, and sums the `N` panel bounds. The one-panel hypothesis and the bounder's
`sound` field both use `iteratedDerivWithin m f (Icc l r)` on each panel. The bounder directly
certifies this local derivative; no equality with the derivative within the root interval is
assumed. Order `m = 0` is allowed, but its composite budget does not decrease with `N`.
-/

@[expose] public section

open MeasureTheory Set

namespace CAS.Continuum

/-- The `k`-th point of the uniform `N`-panel mesh from `a` to `b`. -/
noncomputable def uniformMeshPoint
    (a b : ℝ) (N k : ℕ) : ℝ :=
  a + (k : ℝ) / (N : ℝ) * (b - a)

/-- The mesh starts at the left endpoint `a` (for any `N`, since `0 / N = 0` even when `N = 0`). -/
@[simp]
theorem uniformMeshPoint_zero (a b : ℝ) (N : ℕ) :
    uniformMeshPoint a b N 0 = a := by
  simp [uniformMeshPoint]

/-- The `N`-th mesh point is the right endpoint `b`. Positivity of `N` is needed because
division by `N = 0` is totalized to `0` in Lean. -/
@[simp]
theorem uniformMeshPoint_end
    (a b : ℝ) {N : ℕ} (hN : 0 < N) :
    uniformMeshPoint a b N N = b := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [uniformMeshPoint, hNne]

/-- Consecutive mesh points are exactly one panel width `(b - a)/N` apart. -/
theorem uniformMeshPoint_succ_sub
    (a b : ℝ) {N : ℕ} (hN : 0 < N) (k : ℕ) :
    uniformMeshPoint a b N (k + 1) -
        uniformMeshPoint a b N k =
      (b - a) / N := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold uniformMeshPoint
  field_simp
  push_cast
  ring

/-- For an ordered interval `a ≤ b`, every mesh point with index `k ≤ N` lies in `[a, b]`. -/
theorem uniformMeshPoint_mem_Icc
    {a b : ℝ} {N k : ℕ} (hab : a ≤ b) (hN : 0 < N)
    (hk : k ≤ N) :
    uniformMeshPoint a b N k ∈ Icc a b := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hk0 : 0 ≤ (k : ℝ) / N := div_nonneg (Nat.cast_nonneg _) hNreal.le
  have hk1 : (k : ℝ) / N ≤ 1 := (div_le_one hNreal).2 (by exact_mod_cast hk)
  unfold uniformMeshPoint
  constructor <;> nlinarith

/-- On a nondegenerate interval `a < b` the mesh points increase strictly with the index, so each
panel `[x_k, x_{k+1}]` is itself nondegenerate. -/
theorem uniformMeshPoint_strictMono
    {a b : ℝ} {N k : ℕ} (hab : a < b) (hN : 0 < N) :
    uniformMeshPoint a b N k <
      uniformMeshPoint a b N (k + 1) := by
  rw [← sub_pos, uniformMeshPoint_succ_sub a b hN]
  exact div_pos (sub_pos.mpr hab) (by exact_mod_cast hN)

/-- Every panel of an ordered uniform mesh lies in the root interval. -/
theorem Icc_uniformMeshPoint_subset
    {a b : ℝ} {N k : ℕ} (hab : a ≤ b) (hk : k < N) :
    Icc (uniformMeshPoint a b N k)
        (uniformMeshPoint a b N (k + 1)) ⊆ Icc a b :=
  have hN : 0 < N := by omega
  Icc_subset_Icc (uniformMeshPoint_mem_Icc hab hN hk.le).1 (uniformMeshPoint_mem_Icc hab hN hk).2

/-- Exact-real composite value of a normalized rule over `N` equal panels. -/
noncomputable def uniformCompositeValue
    (rule : QuadratureRule) (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N,
    rule.valueOn f
      (uniformMeshPoint a b N k)
      (uniformMeshPoint a b N (k + 1))

/-- Ordered weighted terms for every panel of a uniform composite rule. -/
noncomputable def uniformCompositeTerms
    (rule : QuadratureRule) (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) :
    List (ℝ × ℝ) :=
  (List.range N).flatMap fun k ↦
    rule.termsOn f
      (uniformMeshPoint a b N k)
      (uniformMeshPoint a b N (k + 1))

private theorem weightedSum_flatMap
    (indices : List ℕ) (terms : ℕ → List (ℝ × ℝ)) :
    weightedSum (indices.flatMap terms) =
      (indices.map fun k ↦ weightedSum (terms k)).sum := by
  induction indices with
  | nil => simp [weightedSum]
  | cons k indices ih =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons,
        weightedSum_append, ih]

/-- Flattened terms denote exactly the corresponding composite-rule value. -/
theorem weightedSum_uniformCompositeTerms
    (rule : QuadratureRule) (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) :
    weightedSum (uniformCompositeTerms rule f N a b) =
      uniformCompositeValue rule f N a b := by
  rw [uniformCompositeTerms, weightedSum_flatMap]
  simp only [QuadratureRule.valueOn, uniformCompositeValue]
  rfl

namespace QuadratureCert

/--
Accumulate a one-panel error theorem of order `m` over a uniform mesh.

If a rule satisfies `‖∫ₗʳ f - Q f‖ ≤ C (r-l)^(m+1) / D` on every panel where `‖f⁽ᵐ⁾‖ ≤ C`,
then `N` equal panels give the global error `C (b-a)^(m+1) / (D N^m)`.
-/
noncomputable def uniformCompositeOfOrder
    (m : ℕ) (rule : QuadratureRule) (denominator : ℝ)
    {f : ℝ → ℝ} {a b C : ℝ} {N : ℕ}
    (hab : a < b) (hN : 0 < N)
    (hf : ContDiffOn ℝ m f (Icc a b))
    (bounder : IteratedDerivativeBounderOn m f (Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Icc l r ⊆ Icc a b), bounder.bound hlr hsub ≤ C)
    (onePanel :
      ∀ {l r : ℝ}, l < r →
        ContDiffOn ℝ m f (Icc l r) →
        (∀ x ∈ Icc l r,
          ‖iteratedDerivWithin m f (Icc l r) x‖ ≤ C) →
        ‖(∫ x in l..r, f x) - rule.valueOn f l r‖ ≤
          C * (r - l) ^ (m + 1) / denominator) :
    QuadratureCert f a b where
  value := uniformCompositeValue rule f N a b
  error := C * (b - a) ^ (m + 1) / (denominator * (N : ℝ) ^ m)
  sound := by
    let point := uniformMeshPoint a b N
    have hint :
        ∀ k < N, IntervalIntegrable f volume (point k) (point (k + 1)) :=
      fun k hk ↦ by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (uniformMeshPoint_strictMono hab hN).le]
        exact hf.continuousOn.mono
          (Icc_uniformMeshPoint_subset hab.le hk)
    have hsumIntegral :=
      intervalIntegral.sum_integral_adjacent_intervals hint
    simp only [point, uniformMeshPoint_zero,
      uniformMeshPoint_end a b hN] at hsumIntegral
    rw [← hsumIntegral]
    change
      ‖(∑ k ∈ Finset.range N,
          ∫ x in uniformMeshPoint a b N k..
            uniformMeshPoint a b N (k + 1), f x) -
        (∑ k ∈ Finset.range N,
          rule.valueOn f
            (uniformMeshPoint a b N k)
            (uniformMeshPoint a b N (k + 1)))‖ ≤ _
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤
          ∑ k ∈ Finset.range N,
            ‖(∫ x in uniformMeshPoint a b N k..
                uniformMeshPoint a b N (k + 1), f x) -
              rule.valueOn f
                (uniformMeshPoint a b N k)
                (uniformMeshPoint a b N (k + 1))‖ :=
        norm_sum_le _ _
      _ ≤
          ∑ _k ∈ Finset.range N,
            C * ((b - a) / N) ^ (m + 1) / denominator := by
        apply Finset.sum_le_sum
        intro k hk
        have hkN : k < N := Finset.mem_range.mp hk
        have hpanel :
            uniformMeshPoint a b N k <
              uniformMeshPoint a b N (k + 1) :=
          uniformMeshPoint_strictMono hab hN
        have hpanelSub :
            Icc (uniformMeshPoint a b N k)
                (uniformMeshPoint a b N (k + 1)) ⊆ Icc a b :=
          Icc_uniformMeshPoint_subset hab.le hkN
        have hlocal :
            ∀ x ∈ Icc
                (uniformMeshPoint a b N k)
                (uniformMeshPoint a b N (k + 1)),
              ‖iteratedDerivWithin m f
                (Icc
                  (uniformMeshPoint a b N k)
                  (uniformMeshPoint a b N (k + 1))) x‖ ≤ C := by
          intro x hx
          exact
            (bounder.norm_iteratedDerivWithin_le hpanel hpanelSub hx).trans
              (hbound hpanel hpanelSub)
        have herror :=
          onePanel hpanel (hf.mono hpanelSub) hlocal
        rw [uniformMeshPoint_succ_sub a b hN] at herror
        exact herror
      _ = C * (b - a) ^ (m + 1) /
          (denominator * (N : ℝ) ^ m) := by
        have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, div_pow]
        field_simp
        ring

/-- The value of the order-`m` accumulated certificate is the composite sum over the `N`
panels. -/
@[simp]
theorem uniformCompositeOfOrder_value
    (m : ℕ) (rule : QuadratureRule) (denominator : ℝ)
    {f : ℝ → ℝ} {a b C : ℝ} {N : ℕ}
    (hab : a < b) (hN : 0 < N)
    (hf : ContDiffOn ℝ m f (Icc a b))
    (bounder : IteratedDerivativeBounderOn m f (Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Icc l r ⊆ Icc a b), bounder.bound hlr hsub ≤ C)
    (onePanel :
      ∀ {l r : ℝ}, l < r →
        ContDiffOn ℝ m f (Icc l r) →
        (∀ x ∈ Icc l r,
          ‖iteratedDerivWithin m f (Icc l r) x‖ ≤ C) →
        ‖(∫ x in l..r, f x) - rule.valueOn f l r‖ ≤
          C * (r - l) ^ (m + 1) / denominator) :
    (uniformCompositeOfOrder m rule denominator hab hN hf bounder hbound
      onePanel).value =
      uniformCompositeValue rule f N a b :=
  rfl

/-- The order-`m` accumulated error budget is `C (b-a)^(m+1) / (D N^m)`. -/
@[simp]
theorem uniformCompositeOfOrder_error
    (m : ℕ) (rule : QuadratureRule) (denominator : ℝ)
    {f : ℝ → ℝ} {a b C : ℝ} {N : ℕ}
    (hab : a < b) (hN : 0 < N)
    (hf : ContDiffOn ℝ m f (Icc a b))
    (bounder : IteratedDerivativeBounderOn m f (Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Icc l r ⊆ Icc a b), bounder.bound hlr hsub ≤ C)
    (onePanel :
      ∀ {l r : ℝ}, l < r →
        ContDiffOn ℝ m f (Icc l r) →
        (∀ x ∈ Icc l r,
          ‖iteratedDerivWithin m f (Icc l r) x‖ ≤ C) →
        ‖(∫ x in l..r, f x) - rule.valueOn f l r‖ ≤
          C * (r - l) ^ (m + 1) / denominator) :
    (uniformCompositeOfOrder m rule denominator hab hN hf bounder hbound
      onePanel).error =
      C * (b - a) ^ (m + 1) / (denominator * (N : ℝ) ^ m) :=
  rfl

/--
Accumulate a fourth-order one-panel theorem over a uniform mesh.

`onePanel` is the complete rule-specific analytic input.  This is the `m = 4` case of
`uniformCompositeOfOrder`.
-/
noncomputable def uniformCompositeFourthOrder
    (rule : QuadratureRule) (denominator : ℝ)
    {f : ℝ → ℝ} {a b C : ℝ} {N : ℕ}
    (hab : a < b) (hN : 0 < N)
    (hf : ContDiffOn ℝ 4 f (Icc a b))
    (bounder : IteratedDerivativeBounderOn 4 f (Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Icc l r ⊆ Icc a b), bounder.bound hlr hsub ≤ C)
    (onePanel :
      ∀ {l r : ℝ}, l < r →
        ContDiffOn ℝ 4 f (Icc l r) →
        (∀ x ∈ Icc l r,
          ‖iteratedDerivWithin 4 f (Icc l r) x‖ ≤ C) →
        ‖(∫ x in l..r, f x) - rule.valueOn f l r‖ ≤
          C * (r - l) ^ 5 / denominator) :
    QuadratureCert f a b :=
  uniformCompositeOfOrder 4 rule denominator hab hN hf bounder hbound onePanel

/-- The value of the accumulated certificate is the exact-real composite sum over the `N`
panels. -/
@[simp]
theorem uniformCompositeFourthOrder_value
    (rule : QuadratureRule) (denominator : ℝ)
    {f : ℝ → ℝ} {a b C : ℝ} {N : ℕ}
    (hab : a < b) (hN : 0 < N)
    (hf : ContDiffOn ℝ 4 f (Icc a b))
    (bounder : IteratedDerivativeBounderOn 4 f (Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Icc l r ⊆ Icc a b), bounder.bound hlr hsub ≤ C)
    (onePanel :
      ∀ {l r : ℝ}, l < r →
        ContDiffOn ℝ 4 f (Icc l r) →
        (∀ x ∈ Icc l r,
          ‖iteratedDerivWithin 4 f (Icc l r) x‖ ≤ C) →
        ‖(∫ x in l..r, f x) - rule.valueOn f l r‖ ≤
          C * (r - l) ^ 5 / denominator) :
    (uniformCompositeFourthOrder rule denominator hab hN hf bounder hbound
      onePanel).value =
      uniformCompositeValue rule f N a b :=
  rfl

/-- The accumulated error budget is `C (b-a)^5 / (D N^4)`: `N` panels of width `(b-a)/N`, each
contributing the one-panel bound `C ((b-a)/N)^5 / D`. -/
@[simp]
theorem uniformCompositeFourthOrder_error
    (rule : QuadratureRule) (denominator : ℝ)
    {f : ℝ → ℝ} {a b C : ℝ} {N : ℕ}
    (hab : a < b) (hN : 0 < N)
    (hf : ContDiffOn ℝ 4 f (Icc a b))
    (bounder : IteratedDerivativeBounderOn 4 f (Icc a b))
    (hbound : ∀ {l r : ℝ} (hlr : l < r)
      (hsub : Icc l r ⊆ Icc a b), bounder.bound hlr hsub ≤ C)
    (onePanel :
      ∀ {l r : ℝ}, l < r →
        ContDiffOn ℝ 4 f (Icc l r) →
        (∀ x ∈ Icc l r,
          ‖iteratedDerivWithin 4 f (Icc l r) x‖ ≤ C) →
        ‖(∫ x in l..r, f x) - rule.valueOn f l r‖ ≤
          C * (r - l) ^ 5 / denominator) :
    (uniformCompositeFourthOrder rule denominator hab hN hf bounder hbound
      onePanel).error =
      C * (b - a) ^ 5 / (denominator * (N : ℝ) ^ 4) :=
  rfl

end QuadratureCert
end CAS.Continuum

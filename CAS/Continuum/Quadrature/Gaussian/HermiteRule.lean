/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.Gaussian.Remainder
public import CAS.Polynomial.CoefficientList

/-!
# Hermite-exact quadrature rules with rational nodes

A `HermiteRule n` on `[-1, 1]` has `n` rational nodes `ξᵢ`, value weights `wᵢ` and slope
weights `vᵢ`. It is valid when the nodes are strictly increasing in `[-1, 1]` and the rule
`∑ (wᵢ p (ξᵢ) + vᵢ p' (ξᵢ))` integrates the monomials of degree below `2n` exactly, a finite
check in `ℚ`. A valid rule integrates every polynomial of degree below `2n` exactly, in
particular the Hermite interpolant of a smooth `g` at its nodes, so the Hermite remainder gives

`|∫₋₁¹ g - ∑ (wᵢ g (ξᵢ) + vᵢ g' (ξᵢ))| ≤ M / (2n)! · ∫₋₁¹ ∏ (x - ξᵢ)²`

for `|g⁽²ⁿ⁾| ≤ M` on `[-1, 1]` (`HermiteRule.abs_integral_sub_le`). The last integral is an
exact rational computed from the nodes (`HermiteRule.nodalSquareIntegral`). Rational nodes
close to the Gauss-Legendre nodes have small slope weights; on a panel `[a, b]` of half-width
`h` the slope terms are then bounded by `h² L ∑ |vᵢ|` with `L ≥ |f'|`, and the rule needs the
integrand only at the rational points `(a + b) / 2 + h ξᵢ`
(`HermiteRule.abs_integral_sub_panel_le`, `HermiteRule.abs_integral_sub_panel_approx_le`).

## Implementation notes

A rule is plain data and may come from anywhere. The theorems assume nothing about it beyond
`q.Valid`, which is decidable: it is a finite conjunction of identities and comparisons between
rationals. `sum_eq_integral_of_natDegree_lt` expands a polynomial in monomials and applies the
moment identities. `abs_integral_sub_le` applies it to the `hermiteInterpolant` of `Hermite` and
bounds `g` minus the interpolant pointwise by `hermite_remainder` of `Remainder`. The panel form
follows by the affine change of variables, with the slope sum bounded separately, and the
composite form adds the panel bounds. The Hermite interpolation remainder is classical; the rule
format, with rational nodes and slope weights checked in `ℚ`, is ours.

## References

* Josef Stoer and Roland Bulirsch, *Introduction to Numerical Analysis*, 3rd ed., Texts in Applied
  Mathematics 12, Springer, New York, 2002, <https://doi.org/10.1007/978-0-387-21738-3>. §2.1.5 for
  Hermite interpolation. The rules with rational nodes and slope weights are ours.
-/

@[expose] public section

namespace CAS.Continuum

open _root_.Polynomial Set _root_.CAS.Polynomial
open scoped BigOperators ContDiff

/-! ### Rules -/

/-- A quadrature rule on `[-1, 1]` with rational nodes, value weights and slope weights. -/
structure HermiteRule (n : ℕ) where
  /-- The nodes `ξᵢ`. -/
  node : Fin n → ℚ
  /-- The weights `wᵢ` of the values `g (ξᵢ)`. -/
  weight : Fin n → ℚ
  /-- The weights `vᵢ` of the slopes `g' (ξᵢ)`. -/
  slope : Fin n → ℚ

namespace HermiteRule

variable {n : ℕ}

/-- The defect of the rule on the monomial `x ^ k`. -/
def momentDefect (q : HermiteRule n) (k : ℕ) : ℚ :=
  (∑ i, (q.weight i * q.node i ^ k + q.slope i * k * q.node i ^ (k - 1))) - unitMoment k

/-- The exact value of `∫₋₁¹ ∏ (x - ξᵢ)²`. -/
def nodalSquareIntegral (q : HermiteRule n) : ℚ :=
  coeffIntegralFrom 0 (nodalSquareCoeffs (List.ofFn q.node))

/-- A valid rule: strictly increasing nodes in `[-1, 1]` and exact moments below degree `2n`. -/
def Valid (q : HermiteRule n) : Prop :=
  (∀ k < 2 * n, q.momentDefect k = 0) ∧ (∀ i j : Fin n, i < j → q.node i < q.node j) ∧
    ∀ i, -1 ≤ q.node i ∧ q.node i ≤ 1

/-- `Decidable` for `q.Valid`, by unfolding `Valid` into bounded quantifiers and comparisons of
rationals and inferring the instance. -/
instance (q : HermiteRule n) : Decidable q.Valid := by
  unfold Valid
  infer_instance

/-- The sum of the absolute slope weights. -/
def slopeMass (q : HermiteRule n) : ℚ := ∑ i, |q.slope i|

/-- For every rule `q`, the real integral `∫₋₁¹ ∏ i, (x - ξᵢ)²` equals the rational
`q.nodalSquareIntegral`. -/
theorem nodalSquareIntegral_eq (q : HermiteRule n) :
    ∫ x in (-1 : ℝ)..1, ∏ i, (x - q.node i) ^ 2 = q.nodalSquareIntegral := by
  have h (x : ℝ) : ∏ i, (x - q.node i) ^ 2 = x ^ 0 * coeffEval (nodalSquareCoeffs
      (List.ofFn q.node)) x := by
    rw [coeffEval_nodalSquareCoeffs, pow_zero, one_mul, List.map_ofFn, List.prod_ofFn]
    rfl
  simp_rw [h]
  exact integral_pow_mul_coeffEval 0 _

/-- A rule with exact moments below degree `2n` integrates every polynomial of degree below
`2n` exactly. -/
theorem sum_eq_integral_of_natDegree_lt (q : HermiteRule n)
    (hq : ∀ k < 2 * n, q.momentDefect k = 0) (p : ℝ[X]) (hp : p.natDegree < 2 * n) :
    ∑ i, ((q.weight i : ℝ) * p.eval (q.node i : ℝ) +
        q.slope i * p.derivative.eval (q.node i : ℝ)) = ∫ x in (-1 : ℝ)..1, p.eval x := by
  have hmom (k : ℕ) (hk : k < 2 * n) :
      ∑ i, ((q.weight i : ℝ) * (q.node i : ℝ) ^ k +
        q.slope i * k * (q.node i : ℝ) ^ (k - 1)) = unitMoment k := by
    exact_mod_cast sub_eq_zero.1 (hq k hk)
  rw [p.as_sum_range' (2 * n) hp]
  simp only [eval_finsetSum, derivative_sum, eval_monomial, derivative_monomial, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  rw [Finset.sum_comm, intervalIntegral.integral_finsetSum fun k _ ↦
    (continuous_const.fun_mul (continuous_pow k)).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [intervalIntegral.integral_const_mul, integral_pow_eq_unitMoment,
    ← hmom k (Finset.mem_range.mp hk), Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The nodes of a valid rule are pairwise distinct real numbers. -/
theorem Valid.injective {q : HermiteRule n} (hq : q.Valid) :
    Function.Injective fun i ↦ (q.node i : ℝ) :=
  Rat.cast_injective.comp (StrictMono.injective fun i j h ↦ hq.2.1 i j h)

/-- The nodes of a valid rule lie in `[-1, 1]`. -/
theorem Valid.mem_Icc {q : HermiteRule n} (hq : q.Valid) (i : Fin n) :
    (q.node i : ℝ) ∈ Icc (-1 : ℝ) 1 :=
  ⟨by exact_mod_cast (hq.2.2 i).1, by exact_mod_cast (hq.2.2 i).2⟩

/-- The error of a valid rule on `[-1, 1]`: for smooth `g` with `|g⁽²ⁿ⁾| ≤ M` on `[-1, 1]`,
`|∫₋₁¹ g - ∑ (wᵢ g (ξᵢ) + vᵢ g' (ξᵢ))| ≤ M / (2n)! · ∫₋₁¹ ∏ (x - ξᵢ)²`. -/
theorem abs_integral_sub_le (q : HermiteRule n) (hn : 0 < n) (hq : q.Valid) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) {M : ℝ}
    (hM : ∀ x ∈ Icc (-1 : ℝ) 1, |iteratedDeriv (2 * n) g x| ≤ M) :
    |(∫ x in (-1 : ℝ)..1, g x) - ∑ i, ((q.weight i : ℝ) * g (q.node i) +
        q.slope i * deriv g (q.node i))| ≤
      M / (2 * n).factorial * q.nodalSquareIntegral := by
  have hinj := hq.injective
  set F : ℕ → ℝ → ℝ := fun k ↦ iteratedDeriv k g with hF
  have hcont : ∀ k < 2 * n, ContinuousOn (F k) (Icc (-1) 1) := fun k _ ↦
    (hg.continuous_iteratedDeriv k (by exact_mod_cast le_top)).continuousOn
  have hder : ∀ k < 2 * n, ∀ z ∈ Ioo (-1 : ℝ) 1, HasDerivAt (F k) (F (k + 1) z) z :=
    fun k _ z _ ↦ by
      simpa only [hF, iteratedDeriv_succ] using
        (hg.differentiable_iteratedDeriv k (by exact_mod_cast WithTop.coe_lt_top _) z).hasDerivAt
  set H := hermiteInterpolant (fun i ↦ (q.node i : ℝ)) (fun i ↦ g (q.node i))
    (fun i ↦ deriv g (q.node i)) with hH
  have hexact := q.sum_eq_integral_of_natDegree_lt hq.1 H
    (hermiteInterpolant_natDegree_lt hn _ _ _)
  have h1 (i : Fin n) : H.eval (q.node i : ℝ) = g (q.node i) :=
    hermiteInterpolant_eval _ hinj _ _ i
  have h2 (i : Fin n) : H.derivative.eval (q.node i : ℝ) = deriv g (q.node i) :=
    hermiteInterpolant_derivative_eval _ hinj _ _ i
  simp only [h1, h2] at hexact
  rw [hexact, ← intervalIntegral.integral_sub (hg.continuous.intervalIntegrable _ _)
    (H.continuous.intervalIntegrable _ _)]
  have hpoint : ∀ x ∈ Icc (-1 : ℝ) 1, |g x - H.eval x| ≤
      M / (2 * n).factorial * ∏ i, (x - q.node i) ^ 2 := by
    intro x hx
    obtain ⟨ξ', hξ', heq⟩ := hermite_remainder (by norm_num : (-1 : ℝ) < 1) hn F hcont hder
      (fun i ↦ (q.node i : ℝ)) hinj hq.mem_Icc x hx
    simp only [hF, iteratedDeriv_zero, iteratedDeriv_one] at heq
    rw [← hH] at heq
    rw [heq, Lagrange.eval_nodal, ← Finset.prod_pow, abs_mul, abs_div, Nat.abs_cast,
      abs_of_nonneg (Finset.prod_nonneg fun i _ ↦ sq_nonneg (x - (q.node i : ℝ)))]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (hM ξ' hξ') (by positivity))
      (Finset.prod_nonneg fun i _ ↦ sq_nonneg _)
  rw [← nodalSquareIntegral_eq, ← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans
    (intervalIntegral.integral_mono_on (by norm_num)
      ((hg.continuous.sub H.continuous).abs.intervalIntegrable _ _) ?_ hpoint)
  exact (continuous_const.mul (continuous_finsetProd _ fun i _ ↦
    (continuous_id.sub continuous_const).pow 2)).intervalIntegrable _ _

/-- The rule on a panel `[a, b]` with centre `m = (a + b) / 2` and half-width `h = (b - a) / 2`:
for smooth `f` with `|f⁽²ⁿ⁾| ≤ M` and `|f'| ≤ L` on `[a, b]`,
`|∫ₐᵇ f - h ∑ wᵢ f (m + h ξᵢ)| ≤ h² L ∑ |vᵢ| + h ^ (2n + 1) M / (2n)! · ∫₋₁¹ ∏ (x - ξᵢ)²`. -/
theorem abs_integral_sub_panel_le (q : HermiteRule n) (hq : q.Valid) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {a b : ℝ} (hab : a < b) {M L : ℝ}
    (hM : ∀ x ∈ Icc a b, |iteratedDeriv (2 * n) f x| ≤ M)
    (hL : ∀ x ∈ Icc a b, |deriv f x| ≤ L) :
    |(∫ x in a..b, f x) -
        (b - a) / 2 * ∑ i, (q.weight i : ℝ) * f ((a + b) / 2 + (b - a) / 2 * q.node i)| ≤
      ((b - a) / 2) ^ 2 * L * q.slopeMass +
        ((b - a) / 2) ^ (2 * n + 1) * (M / (2 * n).factorial * q.nodalSquareIntegral) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- No nodes: the bound is `|∫ₐᵇ f| ≤ M (b - a)`, as `∫₋₁¹ 1 = 2`.
    have hI : (q.nodalSquareIntegral : ℝ) = 2 := by
      rw [← q.nodalSquareIntegral_eq]
      norm_num
    have hbound : ‖∫ x in a..b, f x‖ ≤ M * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (C := M) fun x hx ↦ by
        have hx' : x ∈ Icc a b := Set.Ioc_subset_Icc_self (by rwa [Set.uIoc_of_le hab.le] at hx)
        simpa [Real.norm_eq_abs] using hM x hx'
    rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)] at hbound
    simp only [slopeMass, hI, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, sub_zero,
      Rat.cast_zero, zero_add, Nat.factorial_zero, Nat.cast_one, div_one, pow_one]
    linarith
  set h := (b - a) / 2 with hh
  set m := (a + b) / 2 with hm
  have hpos : 0 < h := by linarith
  set g : ℝ → ℝ := fun t ↦ f (h * t + m) with hg
  have hgsmooth : ContDiff ℝ ∞ g := hf.comp (by fun_prop)
  have hmaps : ∀ t ∈ Icc (-1 : ℝ) 1, h * t + m ∈ Icc a b := fun t ⟨h₁, h₂⟩ ↦ by
    constructor <;> nlinarith
  have hiter (k : ℕ) (t : ℝ) : iteratedDeriv k g t = h ^ k * iteratedDeriv k f (h * t + m) := by
    have hF : ContDiff ℝ k (fun y ↦ f (y + m)) :=
      (hf.comp (by fun_prop)).of_le (by exact_mod_cast le_top)
    have h1 := congrFun (iteratedDeriv_comp_const_mul hF h) t
    rw [show g = fun x ↦ (fun y ↦ f (y + m)) (h * x) from rfl, h1,
      iteratedDeriv_comp_add_const]
  have hM' : ∀ t ∈ Icc (-1 : ℝ) 1, |iteratedDeriv (2 * n) g t| ≤ h ^ (2 * n) * M := by
    intro t ht
    rw [hiter, abs_mul, abs_of_pos (pow_pos hpos _)]
    exact mul_le_mul_of_nonneg_left (hM _ (hmaps t ht)) (pow_pos hpos _).le
  have hderiv (t : ℝ) : deriv g t = h * deriv f (h * t + m) := by
    simpa only [iteratedDeriv_one, pow_one] using hiter 1 t
  have href := q.abs_integral_sub_le hn hq hgsmooth hM'
  have hint : ∫ x in a..b, f x = h * ∫ t in (-1 : ℝ)..1, g t := by
    have h1 := intervalIntegral.integral_comp_mul_add f hpos.ne' m (a := -1) (b := 1)
    rw [hg, h1, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    congr 1 <;> rw [hh, hm] <;> ring
  have hslope : |∑ i, (q.slope i : ℝ) * deriv g (q.node i)| ≤ h * L * q.slopeMass := by
    rw [slopeMass, Rat.cast_sum, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [hderiv, abs_mul, abs_mul, abs_of_pos hpos, Rat.cast_abs]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hL _ (hmaps _ (hq.mem_Icc i)))
      hpos.le) (abs_nonneg _)).trans_eq (by ring)
  have hsplit : (∫ x in a..b, f x) - h * ∑ i, (q.weight i : ℝ) * f (m + h * q.node i) =
      h * ((∫ t in (-1 : ℝ)..1, g t) - ∑ i, ((q.weight i : ℝ) * g (q.node i) +
        q.slope i * deriv g (q.node i))) + h * ∑ i, (q.slope i : ℝ) * deriv g (q.node i) := by
    rw [hint, Finset.sum_add_distrib]
    simp only [hg, add_comm m]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos hpos]
  linear_combination mul_le_mul_of_nonneg_left href hpos.le +
    mul_le_mul_of_nonneg_left hslope hpos.le

/-- The panel rule with approximate node values `yᵢ`, `|f (m + h ξᵢ) - yᵢ| ≤ eᵢ`: the values
add `h ∑ |wᵢ| eᵢ` to the error. -/
theorem abs_integral_sub_panel_approx_le (q : HermiteRule n) (hq : q.Valid)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {a b : ℝ} (hab : a < b) {M L : ℝ}
    (hM : ∀ x ∈ Icc a b, |iteratedDeriv (2 * n) f x| ≤ M)
    (hL : ∀ x ∈ Icc a b, |deriv f x| ≤ L) (y e : Fin n → ℝ)
    (hy : ∀ i, |f ((a + b) / 2 + (b - a) / 2 * q.node i) - y i| ≤ e i) :
    |(∫ x in a..b, f x) - (b - a) / 2 * ∑ i, (q.weight i : ℝ) * y i| ≤
      (b - a) / 2 * ∑ i, |(q.weight i : ℝ)| * e i + (((b - a) / 2) ^ 2 * L * q.slopeMass +
        ((b - a) / 2) ^ (2 * n + 1) * (M / (2 * n).factorial * q.nodalSquareIntegral)) := by
  have hpos : 0 < (b - a) / 2 := by linarith
  have hmain := q.abs_integral_sub_panel_le hq hf hab hM hL
  have hval : |(b - a) / 2 * ∑ i, (q.weight i : ℝ) * f ((a + b) / 2 + (b - a) / 2 * q.node i) -
      (b - a) / 2 * ∑ i, (q.weight i : ℝ) * y i| ≤ (b - a) / 2 * ∑ i, |(q.weight i : ℝ)| * e i := by
    rw [← mul_sub, abs_mul, abs_of_pos hpos, ← Finset.sum_sub_distrib]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ ↦ ?_)) hpos.le
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (hy i) (abs_nonneg _)
  refine (abs_sub_le _ ((b - a) / 2 * ∑ i, (q.weight i : ℝ) *
    f ((a + b) / 2 + (b - a) / 2 * q.node i)) _).trans ?_
  linarith

/-- The `p`th endpoint `a + p (b - a) / P` of the subdivision of `[a, b]` into `P` equal
panels. -/
noncomputable def panelPoint (a b : ℝ) (P p : ℕ) : ℝ := a + p * ((b - a) / P)

/-- The `i`th node `m + h ξᵢ` of the rule on the `p`th of `P` equal panels of `[a, b]`. -/
noncomputable def panelNode (q : HermiteRule n) (a b : ℝ) (P p : ℕ) (i : Fin n) : ℝ :=
  (panelPoint a b P p + panelPoint a b P (p + 1)) / 2 + (b - a) / P / 2 * q.node i

/-- The composite rule on `P` equal panels of `[a, b]` with approximate node values: for
smooth `f` with `|f⁽²ⁿ⁾| ≤ M p` and `|f'| ≤ L p` on the `p`th panel and
`|f (panelNode p i) - y p i| ≤ e p i`, the integral `∫ₐᵇ f` differs from
`∑ₚ h ∑ᵢ wᵢ yₚᵢ`, `h = (b - a) / (2P)`, by at most the sum of the panel errors of
`abs_integral_sub_panel_approx_le`. -/
theorem abs_integral_sub_composite_le (q : HermiteRule n) (hq : q.Valid)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {a b : ℝ} (hab : a < b) {P : ℕ} (hP : 0 < P)
    (M L : ℕ → ℝ)
    (hM : ∀ p < P, ∀ x ∈ Icc (panelPoint a b P p) (panelPoint a b P (p + 1)),
      |iteratedDeriv (2 * n) f x| ≤ M p)
    (hL : ∀ p < P, ∀ x ∈ Icc (panelPoint a b P p) (panelPoint a b P (p + 1)),
      |deriv f x| ≤ L p)
    (y e : ℕ → Fin n → ℝ) (hy : ∀ p < P, ∀ i, |f (q.panelNode a b P p i) - y p i| ≤ e p i) :
    |(∫ x in a..b, f x) -
        ∑ p ∈ Finset.range P, (b - a) / P / 2 * ∑ i, (q.weight i : ℝ) * y p i| ≤
      ∑ p ∈ Finset.range P, ((b - a) / P / 2 * ∑ i, |(q.weight i : ℝ)| * e p i +
        (((b - a) / P / 2) ^ 2 * L p * q.slopeMass +
          ((b - a) / P / 2) ^ (2 * n + 1) *
            (M p / (2 * n).factorial * q.nodalSquareIntegral))) := by
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
  have hstep : 0 < (b - a) / P := div_pos (by linarith) hPpos
  have hlen (p : ℕ) : panelPoint a b P (p + 1) - panelPoint a b P p = (b - a) / P := by
    simp only [panelPoint]
    push_cast
    ring
  have hlt (p : ℕ) : panelPoint a b P p < panelPoint a b P (p + 1) := by
    linarith [hlen p]
  have hsum : ∫ x in a..b, f x =
      ∑ p ∈ Finset.range P, ∫ x in panelPoint a b P p..panelPoint a b P (p + 1), f x := by
    have h0 : panelPoint a b P 0 = a := by simp [panelPoint]
    have hP' : panelPoint a b P P = b := by
      simp only [panelPoint]
      field_simp
      ring
    rw [intervalIntegral.sum_integral_adjacent_intervals fun p _ ↦
      hf.continuous.intervalIntegrable _ _, h0, hP']
  rw [hsum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
  have hp' := Finset.mem_range.mp hp
  have h := q.abs_integral_sub_panel_approx_le hq hf (hlt p) (hM p hp') (hL p hp') (y p)
    (e p) fun i ↦ by simpa only [panelNode, ← hlen p] using hy p hp' i
  rwa [hlen p] at h

end HermiteRule

end CAS.Continuum

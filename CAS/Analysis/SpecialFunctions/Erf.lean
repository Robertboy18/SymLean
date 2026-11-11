/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import CAS.Analysis.SpecialFunctions.BesselJ
public import CAS.Continuum.IntervalEval.Digits

/-!
# The error function

`CAS.erf x = 2 / √π ∫₀ˣ e^(-t²) dt`. Mathlib v4.35 has no error function; we use the
definition of Mathlib PR #34053 (`Real.erf`). We prove the basic API (value at `0`,
oddness, the derivative, continuity, the limit `1` at `+∞`), the interval integral of `e^(-t²)`,
the primitive of every Gaussian `c e^(-α x² + β x + γ)` with `α > 0`, and the Taylor series
`erf x = 2 / √π Σ (-1)ⁿ x^(2n+1) / (n! (2n+1))` (`hasSum_erf`). `erfCheck_sound` gives
certified enclosures of `erf q` at rational points.

## Main results

* `erf_zero`, `erf_neg`, `hasDerivAt_erf`, `continuous_erf`, `tendsto_erf_atTop`.
* `integral_exp_neg_sq`: `∫ t in a..b, e^(-t²) = √π / 2 (erf b - erf a)`.
* `hasDerivAt_gaussianPrimitive`, `integral_gaussian_eq`: the primitive
  `c e^(γ + β² / (4 α)) √π / (2 √α) erf (√α (x - β / (2 α)))` of `c e^(-α x² + β x + γ)`.
* `hasSum_erf`, `erfCheck_sound`.

## Implementation notes

We get the Taylor series by integrating the series of `e^(-t²)` (`hasSum_exp_neg_sq`) term by
term. `erfCheck` is a Boolean checker over `ℚ` that the kernel evaluates: `π` lies in Machin's
interval `DigitsEval.piInterval w`, so `√π ∈ [s₁, s₂]` once `0 < s₁`, `0 ≤ s₂`, `s₁² ≤ π_lo` and
`π_hi ≤ s₂²`; the terms of the series shrink by a factor `1/2` from `N` on once `2 q² ≤ N + 1`,
so the tail is at most twice the `N`-th term (`erf_tail_bound`, from
`norm_tsum_tail_le_of_ratio`); and `[lo, hi]` contains `c (S ± T)` for both ends `c = 2 / s₁`,
`2 / s₂`. `erfCheck_sound` turns it into `lo ≤ erf q ≤ hi`. The command `#cas [N d] (erf q)`
chooses `N`, `w`, `s₁`, `s₂` and the interval outside the kernel.

## References

* NIST Digital Library of Mathematical Functions, §7.2 Definitions, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/7.2>. The definition is (7.2.1).
* NIST Digital Library of Mathematical Functions, §7.6 Series Expansions, Version 1.2.8
  (2026-09-15), <https://dlmf.nist.gov/7.6>. The Taylor series is (7.6.1).
* Christian Oudard, "feat: Add error function (erf) and complementary error function (erfc)",
  Mathlib pull request #34053, 2026,
  <https://github.com/leanprover-community/mathlib4/pull/34053>.
  We take its definition of `Real.erf`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace CAS

/-- The error function `erf x = 2 / √π ∫₀ˣ e^(-t²) dt` (the definition of Mathlib PR #34053). -/
noncomputable def erf (x : ℝ) : ℝ :=
  2 / √Real.pi * ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2))

/-- `erf 0 = 0`. -/
theorem erf_zero : erf 0 = 0 := by simp [erf]

/-- The integrand `t ↦ e^(-t²)` of `erf` is continuous on `ℝ`. -/
theorem continuous_exp_neg_sq : Continuous fun t : ℝ ↦ Real.exp (-(t ^ 2)) := by fun_prop

/-- `erf' x = 2 / √π e^(-x²)`. -/
theorem hasDerivAt_erf (x : ℝ) : HasDerivAt erf (2 / √Real.pi * Real.exp (-(x ^ 2))) x :=
  ((continuous_exp_neg_sq.integral_hasStrictDerivAt 0 x).hasDerivAt).const_mul _

/-- `erf` is differentiable on all of `ℝ`. -/
theorem differentiable_erf : Differentiable ℝ erf := fun x ↦ (hasDerivAt_erf x).differentiableAt

/-- `erf` is continuous on `ℝ`. -/
theorem continuous_erf : Continuous erf := differentiable_erf.continuous

/-- `erf` is odd. -/
theorem erf_neg (x : ℝ) : erf (-x) = -erf x := by
  unfold erf
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := x)
    (fun t : ℝ ↦ Real.exp (-(t ^ 2)))
  simp only [neg_sq, neg_zero] at h
  rw [intervalIntegral.integral_symm (-x) 0, ← h]
  ring

/-- `erf x → 1` as `x → ∞`. -/
theorem tendsto_erf_atTop : Tendsto erf atTop (𝓝 1) := by
  have hint : IntegrableOn (fun t : ℝ ↦ Real.exp (-(t ^ 2))) (Ioi 0) := by
    have := (integrable_exp_neg_mul_sq (b := 1) one_pos).integrableOn (s := Ioi (0 : ℝ))
    simpa using this
  have h := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have hval : ∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 2)) = √Real.pi / 2 := by
    have := integral_gaussian_Ioi 1
    simp only [neg_mul, one_mul, div_one] at this
    exact this
  rw [hval] at h
  have hpi : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have := h.const_mul (2 / √Real.pi)
  rw [show 2 / √Real.pi * (√Real.pi / 2) = 1 by field_simp] at this
  exact this

/-- `∫ t in a..b, e^(-t²) = √π / 2 (erf b - erf a)`. -/
theorem integral_exp_neg_sq (a b : ℝ) :
    ∫ t in a..b, Real.exp (-(t ^ 2)) = √Real.pi / 2 * (erf b - erf a) := by
  have hi : ∀ u v : ℝ, IntervalIntegrable (fun t : ℝ ↦ Real.exp (-(t ^ 2))) volume u v :=
    fun u v ↦ continuous_exp_neg_sq.intervalIntegrable u v
  rw [← intervalIntegral.integral_interval_sub_left (hi 0 b) (hi 0 a)]
  have hpi : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  unfold erf
  field_simp

/-- The primitive of `c e^(-α x² + β x + γ)` for `α > 0`. -/
noncomputable def gaussianPrimitive (α β γ c x : ℝ) : ℝ :=
  c * Real.exp (γ + β ^ 2 / (4 * α)) * √Real.pi / (2 * √α) * erf (√α * (x - β / (2 * α)))

/-- The derivative of the Gaussian primitive is the Gaussian. -/
theorem hasDerivAt_gaussianPrimitive {α : ℝ} (hα : 0 < α) (β γ c x : ℝ) :
    HasDerivAt (gaussianPrimitive α β γ c) (c * Real.exp (-α * x ^ 2 + β * x + γ)) x := by
  have hsα : 0 < √α := Real.sqrt_pos.2 hα
  have hsπ : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hu : HasDerivAt (fun x ↦ √α * (x - β / (2 * α))) (√α * 1) x :=
    ((hasDerivAt_id x).sub_const _).const_mul _
  have h := ((hasDerivAt_erf _).comp x hu).const_mul
    (c * Real.exp (γ + β ^ 2 / (4 * α)) * √Real.pi / (2 * √α))
  refine h.congr_deriv ?_
  have hsq : √α ^ 2 = α := Real.sq_sqrt hα.le
  have hexp : Real.exp (γ + β ^ 2 / (4 * α)) * Real.exp (-((√α * (x - β / (2 * α))) ^ 2)) =
      Real.exp (-α * x ^ 2 + β * x + γ) := by
    rw [← Real.exp_add]
    congr 1
    rw [mul_pow, hsq]
    field_simp
    ring
  rw [← hexp]
  field_simp

/-- `∫ x in a..b, c e^(-α x² + β x + γ) = P b - P a` for the Gaussian primitive `P`. -/
theorem integral_gaussian_eq {α : ℝ} (hα : 0 < α) (β γ c a b : ℝ) :
    ∫ x in a..b, c * Real.exp (-α * x ^ 2 + β * x + γ) =
      gaussianPrimitive α β γ c b - gaussianPrimitive α β γ c a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ hasDerivAt_gaussianPrimitive hα β γ c x)
    ((by fun_prop : Continuous fun x : ℝ ↦ c * Real.exp (-α * x ^ 2 + β * x + γ)).intervalIntegrable
      a b)

/-! ### The Taylor series -/

/-- The `n`-th term `(-1)ⁿ x^(2n+1) / (n! (2n+1))` of the series of `√π / 2 erf x`. -/
noncomputable def erfTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1) ^ n * x ^ (2 * n + 1) / (n.factorial * (2 * n + 1))

/-- `e^(-t²) = Σ (-1)ⁿ t^(2n) / n!`. -/
theorem hasSum_exp_neg_sq (t : ℝ) :
    HasSum (fun n : ℕ ↦ (-1) ^ n * t ^ (2 * n) / n.factorial) (Real.exp (-(t ^ 2))) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (-(t ^ 2))
  rw [← Real.exp_eq_exp_ℝ] at h
  convert h using 1
  funext n
  conv_rhs => rw [neg_pow, ← pow_mul]

/-- The Taylor series of `erf`. -/
theorem hasSum_erf (x : ℝ) : HasSum (fun n ↦ 2 / √Real.pi * erfTerm x n) (erf x) := by
  set g : ℕ → C(ℝ, ℝ) := fun n ↦
    ⟨fun t ↦ (-1) ^ n * t ^ (2 * n) / n.factorial, by fun_prop⟩ with hg
  have hsum : Summable fun n : ℕ ↦
      ‖(g n).restrict (⟨uIcc 0 x, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
    refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
      (Real.summable_pow_div_factorial (x ^ 2))
    rw [ContinuousMap.norm_le _ (by positivity)]
    rintro ⟨t, ht⟩
    have habs : |t| ≤ |x| := by
      simpa [Real.dist_eq] using Real.dist_left_le_of_mem_uIcc ht
    simp only [ContinuousMap.restrict_apply, ContinuousMap.coe_mk, g, Real.norm_eq_abs, abs_div,
      abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    gcongr
    calc |t| ^ (2 * n) ≤ |x| ^ (2 * n) := pow_le_pow_left₀ (abs_nonneg t) habs _
      _ = (x ^ 2) ^ n := by rw [pow_mul, sq_abs]
  have h := intervalIntegral.hasSum_intervalIntegral_of_summable_norm (a := 0) (b := x) hsum
  have hint : ∀ n : ℕ, ∫ t in (0 : ℝ)..x, g n t = erfTerm x n := by
    intro n
    simp only [g, ContinuousMap.coe_mk, erfTerm]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have htsum : (∫ t in (0 : ℝ)..x, ∑' n, g n t) = ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2)) := by
    congr 1
    funext t
    exact (hasSum_exp_neg_sq t).tsum_eq
  simp only [hint, htsum] at h
  exact h.mul_left _

/-- `erfTerm x (n + 1) = erfTerm x n (-x² (2n+1) / ((n+1) (2n+3)))`. -/
theorem erfTerm_succ (x : ℝ) (n : ℕ) :
    erfTerm x (n + 1) = erfTerm x n * (-(x ^ 2) * (2 * n + 1) / ((n + 1) * (2 * n + 3))) := by
  unfold erfTerm
  rw [Nat.factorial_succ]
  push_cast
  have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The series of `erf x` after `N` terms is within twice the `N`-th term once `2 x² ≤ N + 1`. -/
theorem erf_tail_bound (x : ℝ) (N : ℕ) (h : 2 * x ^ 2 ≤ (N : ℝ) + 1) :
    |√Real.pi / 2 * erf x - ∑ n ∈ Finset.range N, erfTerm x n| ≤ 2 * |erfTerm x N| := by
  have hratio : ∀ k, N ≤ k →
      ‖((erfTerm x (k + 1) : ℝ) : ℂ)‖ ≤ 1 / 2 * ‖((erfTerm x k : ℝ) : ℂ)‖ := by
    intro k hk
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, erfTerm_succ,
      abs_mul, mul_comm (1 / 2 : ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
    rw [abs_div, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg x),
      abs_of_pos (by positivity : (0 : ℝ) < 2 * k + 1),
      abs_of_pos (by positivity : (0 : ℝ) < (k + 1) * (2 * k + 3)),
      div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg x]
  obtain ⟨hsum, htail⟩ := CAS.Analysis.SpecialFunctions.Bessel.norm_tsum_tail_le_of_ratio
    (f := fun k ↦ ((erfTerm x k : ℝ) : ℂ)) N (by norm_num) (by norm_num) hratio
  have hsR : Summable (erfTerm x) := Complex.summable_ofReal.1 hsum
  have hE : √Real.pi / 2 * erf x = ∑' n, erfTerm x n := by
    have := ((hasSum_erf x).mul_left (√Real.pi / 2)).tsum_eq
    have hpi : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
    rw [← this]
    congr 1
    funext n
    field_simp
  rw [hE, ← hsR.sum_add_tsum_nat_add N, add_sub_cancel_left]
  have h2 : ‖((∑' k, erfTerm x (k + N) : ℝ) : ℂ)‖ ≤ ‖((erfTerm x N : ℝ) : ℂ)‖ / (1 - 1 / 2) := by
    rw [Complex.ofReal_tsum]
    exact htail
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs] at h2
  have e2 : |erfTerm x N| / (1 - 1 / 2) = 2 * |erfTerm x N| := by ring
  linarith

/-! ### The enclosure checker -/

/-- The `n`-th term of the series in `ℚ`. -/
def erfTermQ (q : ℚ) (n : ℕ) : ℚ :=
  (-1) ^ n * q ^ (2 * n + 1) / (n.factorial * (2 * n + 1))

/-- The partial sum of `N` terms in `ℚ`. -/
def erfPartialQ (q : ℚ) : ℕ → ℚ
  | 0 => 0
  | N + 1 => erfPartialQ q N + erfTermQ q N

/-- The real cast of the rational term `erfTermQ q n` is the real series term `erfTerm q n`. -/
theorem erfTermQ_cast (q : ℚ) (n : ℕ) : ((erfTermQ q n : ℚ) : ℝ) = erfTerm q n := by
  unfold erfTermQ erfTerm
  push_cast
  ring

/-- The real cast of the rational partial sum `erfPartialQ q N` is the real partial sum
`∑ n < N, erfTerm q n`. -/
theorem erfPartialQ_cast (q : ℚ) (N : ℕ) :
    ((erfPartialQ q N : ℚ) : ℝ) = ∑ n ∈ Finset.range N, erfTerm q n := by
  induction N with
  | zero => simp [erfPartialQ]
  | succ N ih => rw [erfPartialQ, Rat.cast_add, ih, erfTermQ_cast, Finset.sum_range_succ]

/-- The checker: `√π ∈ [s₁, s₂]` from Machin's interval at `w` bits, the tail condition, and
`[lo, hi]` contains `(2 / s) (S ± T)` for `s = s₁, s₂`, with `S` the partial sum of `N` terms
and `T` twice the `N`-th term. -/
def erfCheck (q : ℚ) (N w : ℕ) (s₁ s₂ lo hi : ℚ) : Bool :=
  decide (0 < s₁) && decide (0 ≤ s₂) &&
    decide (s₁ ^ 2 ≤ (CAS.Continuum.DigitsEval.piInterval w).lo) &&
    decide ((CAS.Continuum.DigitsEval.piInterval w).hi ≤ s₂ ^ 2) &&
    decide (2 * q ^ 2 ≤ (N : ℚ) + 1) &&
    decide (lo ≤ 2 / s₂ * (erfPartialQ q N - 2 * |erfTermQ q N|)) &&
    decide (lo ≤ 2 / s₁ * (erfPartialQ q N - 2 * |erfTermQ q N|)) &&
    decide (2 / s₂ * (erfPartialQ q N + 2 * |erfTermQ q N|) ≤ hi) &&
    decide (2 / s₁ * (erfPartialQ q N + 2 * |erfTermQ q N|) ≤ hi)

/-- For real `c₁ ≤ c ≤ c₂` and any real `x`, a lower bound `m` of both `c₁ x` and `c₂ x` is a
lower bound of `c x`. -/
theorem le_mul_of_le_both {c c₁ c₂ x m : ℝ} (h₁ : c₁ ≤ c) (h₂ : c ≤ c₂)
    (hm₁ : m ≤ c₁ * x) (hm₂ : m ≤ c₂ * x) : m ≤ c * x := by
  rcases le_total 0 x with hx | hx
  · nlinarith
  · nlinarith

/-- For real `c₁ ≤ c ≤ c₂` and any real `x`, an upper bound `m` of both `c₁ x` and `c₂ x` is an
upper bound of `c x`. -/
theorem mul_le_of_le_both {c c₁ c₂ x m : ℝ} (h₁ : c₁ ≤ c) (h₂ : c ≤ c₂)
    (hm₁ : c₁ * x ≤ m) (hm₂ : c₂ * x ≤ m) : c * x ≤ m := by
  rcases le_total 0 x with hx | hx
  · nlinarith
  · nlinarith

/-- Soundness of the checker: `lo ≤ erf q ≤ hi`. -/
theorem erfCheck_sound {q : ℚ} {N w : ℕ} {s₁ s₂ lo hi : ℚ}
    (h : erfCheck q N w s₁ s₂ lo hi = true) : (lo : ℝ) ≤ erf q ∧ erf q ≤ hi := by
  simp only [erfCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hs₁, hs₂⟩, hlo⟩, hhi⟩, hN⟩, h1⟩, h2⟩, h3⟩, h4⟩ := h
  -- `√π ∈ [s₁, s₂]`.
  have hpi := CAS.Continuum.DigitsEval.piInterval_sound w
  have hs₁R : (0 : ℝ) < s₁ := by exact_mod_cast hs₁
  have hs₂R : (0 : ℝ) ≤ s₂ := by exact_mod_cast hs₂
  have hloR : ((s₁ ^ 2 : ℚ) : ℝ) ≤ ((CAS.Continuum.DigitsEval.piInterval w).lo : ℝ) := by
    exact_mod_cast hlo
  have hhiR : ((CAS.Continuum.DigitsEval.piInterval w).hi : ℝ) ≤ ((s₂ ^ 2 : ℚ) : ℝ) := by
    exact_mod_cast hhi
  push_cast at hloR hhiR
  have hsq₁ : (s₁ : ℝ) ≤ √Real.pi := Real.le_sqrt_of_sq_le (hloR.trans hpi.1)
  have hsq₂ : √Real.pi ≤ s₂ := Real.sqrt_le_iff.2 ⟨hs₂R, hpi.2.trans hhiR⟩
  have hsπ : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  -- `2 / √π ∈ [2 / s₂, 2 / s₁]`.
  have hc₁ : 2 / (s₂ : ℝ) ≤ 2 / √Real.pi := div_le_div_of_nonneg_left (by norm_num) hsπ hsq₂
  have hc₂ : 2 / √Real.pi ≤ 2 / (s₁ : ℝ) := div_le_div_of_nonneg_left (by norm_num) hs₁R hsq₁
  -- The series.
  have hNR : 2 * ((q : ℝ)) ^ 2 ≤ (N : ℝ) + 1 := by exact_mod_cast hN
  have htail := erf_tail_bound (q : ℝ) N hNR
  rw [← erfPartialQ_cast, ← erfTermQ_cast] at htail
  rw [abs_le] at htail
  have he : erf q = 2 / √Real.pi * (√Real.pi / 2 * erf q) := by field_simp
  set S : ℝ := ((erfPartialQ q N : ℚ) : ℝ)
  set T : ℝ := 2 * |((erfTermQ q N : ℚ) : ℝ)|
  have h1R : (lo : ℝ) ≤ 2 / s₂ * (S - T) := by simp only [S, T]; exact_mod_cast h1
  have h2R : (lo : ℝ) ≤ 2 / s₁ * (S - T) := by simp only [S, T]; exact_mod_cast h2
  have h3R : 2 / (s₂ : ℝ) * (S + T) ≤ hi := by simp only [S, T]; exact_mod_cast h3
  have h4R : 2 / (s₁ : ℝ) * (S + T) ≤ hi := by simp only [S, T]; exact_mod_cast h4
  have hcpos : 0 ≤ 2 / √Real.pi := by positivity
  constructor
  · rw [he]
    have : (lo : ℝ) ≤ 2 / √Real.pi * (S - T) := le_mul_of_le_both hc₁ hc₂ h1R h2R
    exact this.trans (mul_le_mul_of_nonneg_left (by linarith [htail.1]) hcpos)
  · rw [he]
    have : 2 / √Real.pi * (S + T) ≤ (hi : ℝ) := mul_le_of_le_both hc₁ hc₂ h3R h4R
    exact (mul_le_mul_of_nonneg_left (by linarith [htail.2]) hcpos).trans this

end CAS

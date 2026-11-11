/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Laplace transforms of exponential polynomials

For `f t = tⁿ e^{a t} g (b t)` with `g ∈ {1, cos, sin, cosh, sinh}` and real `a`, `b`, `s`, the
one-sided Laplace transform `∫ t in Ioi 0, exp (-(s t)) f t` is an explicit rational function of
`s` when `a < s` (`a + b < s` and `a - b < s` for `cosh` and `sinh`). The theorems for these
real transforms state integrability on `Ioi 0` together with the value of the integral. The
transform of a finite sum of such terms (`integral_exp_mul_sum`) is the theorem that
`#cas [laplace t s]` instantiates.

## Main definitions

* `laplacePQ`: the real and imaginary parts of `(u + b i)^m`, by recursion on `m`.
* `LaplaceTerm`: a term `c tⁿ e^{a t} g (b t)`, with its value `LaplaceTerm.eval`, its
  convergence condition `LaplaceTerm.Admissible` and its transform `LaplaceTerm.transform`.

## Main results

* `integral_pow_mul_cexp_neg_mul_Ioi`: `∫₀^∞ tⁿ e^{-w t} dt = n! / w^(n+1)` for `0 < re w`.
* `laplace_exp`, `laplace_cos`, `laplace_sin`, `laplace_cosh`, `laplace_sinh`: the transforms
  of `tⁿ e^{a t} g (b t)`.
* `integral_exp_mul_sum`: the transform of a finite sum of terms.

## Implementation notes

All five transforms come from one complex integral, so a single induction serves every kind
and every power. We prove `∫₀^∞ tⁿ e^{-w t} dt = n! / w^(n+1)` for `0 < re w` by induction on
`n`. Mathlib has the case `n = 0` (`integral_exp_mul_complex_Ioi`); the step integrates by
parts, through the fundamental theorem of calculus on `Ioi 0`
(`integral_Ioi_of_hasDerivAt_of_tendsto'`) for `t^(n+1) e^{-w t}`, which vanishes at `0` and
tends to `0` (`tendsto_pow_mul_cexp_neg_mul`). The rate `w = (s - a) - b i` absorbs the shift
by `a` (the translation rule) and the frequency `b`: the real and imaginary parts of the
integrand are the `cos` and `sin` integrands (`re_pow_mul_cexp_shift`, `im_pow_mul_cexp_shift`).
`laplacePQ` turns `1 / w^(n+1)` into a real rational function of `s` (`one_div_sub_mul_I_pow`),
so the statements stay real. `laplace_exp` is the case `b = 0` of `laplace_cos`, and the `cosh`
and `sinh` transforms are sums of two exponential ones. The formulas are classical.

## References

* NIST Digital Library of Mathematical Functions, §1.14 Integral Transforms, Version 1.2.8
  (2026-09-15), <https://dlmf.nist.gov/1.14>. §1.14(iii): the definition (1.14.17) and the
  translation rule (1.14.21).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real

namespace CAS.Calculus.Laplace


/-- `t ^ n e^{-w t}` is integrable on `(0, ∞)` when `0 < re w`. -/
theorem integrableOn_pow_mul_cexp_neg_mul (n : ℕ) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ n * Complex.exp (-(w * t))) (Ioi 0) := by
  have hreal : IntegrableOn (fun x : ℝ ↦ x ^ (n : ℝ) * Real.exp (-w.re * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith) one_pos hw
  refine (integrable_norm_iff ?_).mp ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · refine hreal.congr_fun (fun t ht ↦ ?_) measurableSet_Ioi
    have ht' : (0 : ℝ) ≤ t := le_of_lt ht
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht',
      Complex.norm_exp, Real.rpow_one, Real.rpow_natCast]
    congr 2
    simp [Complex.mul_re]

/-- `t ^ n e^{-w t} → 0` as `t → ∞` when `0 < re w`. -/
theorem tendsto_pow_mul_cexp_neg_mul (n : ℕ) {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun t : ℝ ↦ (t : ℂ) ^ n * Complex.exp (-(w * t))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) w.re hw
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht,
    Complex.norm_exp, Real.rpow_natCast]
  congr 2
  simp [Complex.mul_re]

/-- `∫₀^∞ tⁿ e^{-w t} dt = n! / w^(n+1)` for `0 < re w`. -/
theorem integral_pow_mul_cexp_neg_mul_Ioi (n : ℕ) {w : ℂ} (hw : 0 < w.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * Complex.exp (-(w * t)) = n.factorial / w ^ (n + 1) := by
  have hw0 : w ≠ 0 := fun h ↦ by simp [h] at hw
  induction n with
  | zero =>
    have h := integral_exp_mul_complex_Ioi (a := -w) (by simpa using hw) 0
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    simpa [neg_mul, div_neg, neg_div] using h
  | succ n ih =>
    -- F t = t^(n+1) e^{-wt}, F' = (n+1) t^n e^{-wt} - w t^(n+1) e^{-wt}
    have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt
        (fun t : ℝ ↦ (t : ℂ) ^ (n + 1) * Complex.exp (-(w * t)))
        (((n + 1 : ℕ) : ℂ) * ((t : ℂ) ^ n * Complex.exp (-(w * t))) -
          w * ((t : ℂ) ^ (n + 1) * Complex.exp (-(w * t)))) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ ↦ (t : ℂ) ^ (n + 1))
          (((n + 1 : ℕ) : ℂ) * (t : ℂ) ^ n) t := by
        simpa using (hasDerivAt_pow (n + 1) (t : ℂ)).comp_ofReal
      have h2 : HasDerivAt (fun t : ℝ ↦ Complex.exp (-(w * t)))
          (Complex.exp (-(w * t)) * (-w)) t := by
        have := (((hasDerivAt_id (t : ℂ)).const_mul w).neg.cexp).comp_ofReal
        simpa using this
      convert h1.mul h2 using 1
      ring
    have hint := integrableOn_pow_mul_cexp_neg_mul n hw
    have hint1 := integrableOn_pow_mul_cexp_neg_mul (n + 1) hw
    have key := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
      ((hint.const_mul _).sub (hint1.const_mul w)) (tendsto_pow_mul_cexp_neg_mul (n + 1) hw)
    rw [integral_sub (hint.const_mul _) (hint1.const_mul w), integral_const_mul,
      integral_const_mul, ih] at key
    simp only [Complex.ofReal_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      not_false_eq_true, zero_pow, zero_mul, sub_zero] at key
    have : w * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (n + 1) * Complex.exp (-(w * t)) =
        ((n + 1 : ℕ) : ℂ) * (n.factorial / w ^ (n + 1)) := by
      linear_combination -key
    have hI : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (n + 1) * Complex.exp (-(w * t)) =
        ((n + 1 : ℕ) : ℂ) * (n.factorial / w ^ (n + 1)) / w := by
      rw [← this]; field_simp
    rw [hI, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The real and imaginary parts of `(u + b i) ^ m`. -/
def laplacePQ (u b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | m + 1 => ((laplacePQ u b m).1 * u - (laplacePQ u b m).2 * b,
      (laplacePQ u b m).2 * u + (laplacePQ u b m).1 * b)

/-- `(u + b i) ^ m = P + Q i` with `(P, Q) = laplacePQ u b m`. -/
theorem laplacePQ_spec (u b : ℝ) (m : ℕ) :
    ((u : ℂ) + b * Complex.I) ^ m = (laplacePQ u b m).1 + (laplacePQ u b m).2 * Complex.I := by
  induction m with
  | zero => simp [laplacePQ]
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [laplacePQ]
    push_cast
    linear_combination ((laplacePQ u b m).2 * b) * Complex.I_sq

/-- `1 / (u - b i) ^ m = (P + Q i) / (u² + b²) ^ m` with `(P, Q) = laplacePQ u b m`, for all
real `u`, `b` (both sides are `0` when `u = b = 0 < m`). -/
theorem one_div_sub_mul_I_pow (u b : ℝ) (m : ℕ) :
    (1 : ℂ) / ((u : ℂ) - b * Complex.I) ^ m =
      ((laplacePQ u b m).1 + (laplacePQ u b m).2 * Complex.I) / ((u ^ 2 + b ^ 2 : ℝ) : ℂ) ^ m := by
  by_cases hw : (u : ℂ) - b * Complex.I = 0
  · have hu : u = 0 := by simpa using congrArg Complex.re hw
    have hb : b = 0 := by simpa using congrArg Complex.im hw
    subst hu hb
    cases m with
    | zero => simp [laplacePQ]
    | succ m => simp
  have hn : ((u ^ 2 + b ^ 2 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have h1 : u ^ 2 + b ^ 2 = 0 := by exact_mod_cast h0
    have hu : u = 0 := (pow_eq_zero_iff two_ne_zero).1 (by linarith [sq_nonneg u, sq_nonneg b])
    have hb : b = 0 := (pow_eq_zero_iff two_ne_zero).1 (by linarith [sq_nonneg u, sq_nonneg b])
    exact hw (by simp [hu, hb])
  rw [← laplacePQ_spec, div_eq_div_iff (pow_ne_zero _ hw) (pow_ne_zero _ hn), one_mul, ← mul_pow]
  congr 1
  push_cast
  linear_combination ((b : ℂ) ^ 2) * Complex.I_sq

/-- The pointwise real part: `e^{-s t} tⁿ e^{a t} cos (b t)`. -/
theorem re_pow_mul_cexp_shift (n : ℕ) (a b s t : ℝ) :
    ((t : ℂ) ^ n * Complex.exp (-((((s - a : ℝ) : ℂ) - (b : ℂ) * Complex.I) * t))).re =
      Real.exp (-(s * t)) * (t ^ n * Real.exp (a * t) * Real.cos (b * t)) := by
  rw [show ((t : ℂ) ^ n) = ((t ^ n : ℝ) : ℂ) by push_cast; rfl]
  rw [Complex.re_ofReal_mul, Complex.exp_re]
  have h1 : (-((((s - a : ℝ) : ℂ) - (b : ℂ) * Complex.I) * t)).re = -((s - a) * t) := by simp
  have h2 : (-((((s - a : ℝ) : ℂ) - (b : ℂ) * Complex.I) * t)).im = b * t := by simp
  rw [h1, h2, show -(s * t) = -((s - a) * t) + -(a * t) by ring, Real.exp_add]
  have : Real.exp (-(a * t)) * Real.exp (a * t) = 1 := by rw [← Real.exp_add]; simp
  linear_combination (-(t ^ n * Real.exp (-((s - a) * t)) * Real.cos (b * t))) * this

/-- The pointwise imaginary part: `e^{-s t} tⁿ e^{a t} sin (b t)`. -/
theorem im_pow_mul_cexp_shift (n : ℕ) (a b s t : ℝ) :
    ((t : ℂ) ^ n * Complex.exp (-((((s - a : ℝ) : ℂ) - (b : ℂ) * Complex.I) * t))).im =
      Real.exp (-(s * t)) * (t ^ n * Real.exp (a * t) * Real.sin (b * t)) := by
  rw [show ((t : ℂ) ^ n) = ((t ^ n : ℝ) : ℂ) by push_cast; rfl]
  rw [Complex.im_ofReal_mul, Complex.exp_im]
  have h1 : (-((((s - a : ℝ) : ℂ) - (b : ℂ) * Complex.I) * t)).re = -((s - a) * t) := by simp
  have h2 : (-((((s - a : ℝ) : ℂ) - (b : ℂ) * Complex.I) * t)).im = b * t := by simp
  rw [h1, h2, show -(s * t) = -((s - a) * t) + -(a * t) by ring, Real.exp_add]
  have : Real.exp (-(a * t)) * Real.exp (a * t) = 1 := by rw [← Real.exp_add]; simp
  linear_combination (-(t ^ n * Real.exp (-((s - a) * t)) * Real.sin (b * t))) * this

/-- Laplace transform of `tⁿ e^{a t} cos (b t)` for `a < s`. -/
theorem laplace_cos (n : ℕ) {a b s : ℝ} (h : a < s) :
    IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (t ^ n * Real.exp (a * t) * Real.cos (b * t)))
        (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (t ^ n * Real.exp (a * t) * Real.cos (b * t)) =
        n.factorial * (laplacePQ (s - a) b (n + 1)).1 / ((s - a) ^ 2 + b ^ 2) ^ (n + 1) := by
  set w : ℂ := ((s - a : ℝ) : ℂ) - (b : ℂ) * Complex.I with hwdef
  have hw : 0 < w.re := by simp [hwdef]; linarith
  have hint := integrableOn_pow_mul_cexp_neg_mul n hw
  refine ⟨IntegrableOn.congr_fun hint.re (fun t _ ↦ re_pow_mul_cexp_shift n a b s t)
    measurableSet_Ioi, ?_⟩
  have key := integral_pow_mul_cexp_neg_mul_Ioi n hw
  have hre := congrArg Complex.re key
  have hire := integral_re hint
  simp only [RCLike.re_to_complex] at hire
  rw [← hire] at hre
  simp only [hwdef, re_pow_mul_cexp_shift] at hre
  rw [hre, div_eq_mul_one_div (n.factorial : ℂ), one_div_sub_mul_I_pow]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_natCast]
  rw [Complex.re_ofReal_mul, Complex.div_ofReal_re]
  simp
  ring

/-- Laplace transform of `tⁿ e^{a t} sin (b t)` for `a < s`. -/
theorem laplace_sin (n : ℕ) {a b s : ℝ} (h : a < s) :
    IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (t ^ n * Real.exp (a * t) * Real.sin (b * t)))
        (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (t ^ n * Real.exp (a * t) * Real.sin (b * t)) =
        n.factorial * (laplacePQ (s - a) b (n + 1)).2 / ((s - a) ^ 2 + b ^ 2) ^ (n + 1) := by
  set w : ℂ := ((s - a : ℝ) : ℂ) - (b : ℂ) * Complex.I with hwdef
  have hw : 0 < w.re := by simp [hwdef]; linarith
  have hint := integrableOn_pow_mul_cexp_neg_mul n hw
  refine ⟨IntegrableOn.congr_fun hint.im (fun t _ ↦ im_pow_mul_cexp_shift n a b s t)
    measurableSet_Ioi, ?_⟩
  have key := integral_pow_mul_cexp_neg_mul_Ioi n hw
  have him := congrArg Complex.im key
  have hiim := integral_im hint
  simp only [RCLike.im_to_complex] at hiim
  rw [← hiim] at him
  simp only [hwdef, im_pow_mul_cexp_shift] at him
  rw [him, div_eq_mul_one_div (n.factorial : ℂ), one_div_sub_mul_I_pow]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_natCast]
  rw [Complex.im_ofReal_mul, Complex.div_ofReal_im]
  simp
  ring

/-- `laplacePQ u 0 m = (u ^ m, 0)`. -/
theorem laplacePQ_zero_right (u : ℝ) (m : ℕ) : laplacePQ u 0 m = (u ^ m, 0) := by
  induction m with
  | zero => simp [laplacePQ]
  | succ m ih => simp [laplacePQ, ih, pow_succ]

/-- Laplace transform of `tⁿ e^{a t}` for `a < s`. -/
theorem laplace_exp (n : ℕ) {a s : ℝ} (h : a < s) :
    IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (t ^ n * Real.exp (a * t))) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (t ^ n * Real.exp (a * t)) =
        n.factorial / (s - a) ^ (n + 1) := by
  have hc := laplace_cos n (b := 0) h
  simp only [zero_mul, Real.cos_zero, mul_one, laplacePQ_zero_right, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hc
  refine ⟨hc.1, hc.2.trans ?_⟩
  have hu : s - a ≠ 0 := sub_ne_zero.2 (ne_of_gt h)
  generalize s - a = u at hu ⊢
  rw [← pow_mul, div_eq_div_iff (pow_ne_zero _ hu) (pow_ne_zero _ hu)]
  ring

/-- Laplace transform of `tⁿ e^{a t} cosh (b t)` for `a + b < s` and `a - b < s`. -/
theorem laplace_cosh (n : ℕ) {a b s : ℝ} (h1 : a + b < s) (h2 : a - b < s) :
    IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (t ^ n * Real.exp (a * t) * Real.cosh (b * t)))
        (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (t ^ n * Real.exp (a * t) * Real.cosh (b * t)) =
        n.factorial / 2 * (1 / (s - (a + b)) ^ (n + 1) + 1 / (s - (a - b)) ^ (n + 1)) := by
  obtain ⟨i1, e1⟩ := laplace_exp n h1
  obtain ⟨i2, e2⟩ := laplace_exp n h2
  have hf : (fun t : ℝ ↦ Real.exp (-(s * t)) * (t ^ n * Real.exp (a * t) * Real.cosh (b * t))) =
      fun t ↦ (1 / 2 : ℝ) * (Real.exp (-(s * t)) * (t ^ n * Real.exp ((a + b) * t))) +
        (1 / 2 : ℝ) * (Real.exp (-(s * t)) * (t ^ n * Real.exp ((a - b) * t))) := by
    funext t
    simp only [Real.cosh_eq, add_mul, sub_mul, Real.exp_add, Real.exp_sub, Real.exp_neg]
    ring
  rw [hf]
  refine ⟨Integrable.add (Integrable.const_mul i1 _) (Integrable.const_mul i2 _), ?_⟩
  rw [integral_add (Integrable.const_mul i1 _) (Integrable.const_mul i2 _), integral_const_mul,
    integral_const_mul, e1, e2]
  ring

/-- Laplace transform of `tⁿ e^{a t} sinh (b t)` for `a + b < s` and `a - b < s`. -/
theorem laplace_sinh (n : ℕ) {a b s : ℝ} (h1 : a + b < s) (h2 : a - b < s) :
    IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (t ^ n * Real.exp (a * t) * Real.sinh (b * t)))
        (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (t ^ n * Real.exp (a * t) * Real.sinh (b * t)) =
        n.factorial / 2 * (1 / (s - (a + b)) ^ (n + 1) - 1 / (s - (a - b)) ^ (n + 1)) := by
  obtain ⟨i1, e1⟩ := laplace_exp n h1
  obtain ⟨i2, e2⟩ := laplace_exp n h2
  have hf : (fun t : ℝ ↦ Real.exp (-(s * t)) * (t ^ n * Real.exp (a * t) * Real.sinh (b * t))) =
      fun t ↦ (1 / 2 : ℝ) * (Real.exp (-(s * t)) * (t ^ n * Real.exp ((a + b) * t))) -
        (1 / 2 : ℝ) * (Real.exp (-(s * t)) * (t ^ n * Real.exp ((a - b) * t))) := by
    funext t
    simp only [Real.sinh_eq, add_mul, sub_mul, Real.exp_add, Real.exp_sub, Real.exp_neg]
    ring
  rw [hf]
  refine ⟨Integrable.sub (Integrable.const_mul i1 _) (Integrable.const_mul i2 _), ?_⟩
  rw [integral_sub (Integrable.const_mul i1 _) (Integrable.const_mul i2 _), integral_const_mul,
    integral_const_mul, e1, e2]
  ring

/-- The kinds of terms: `tⁿ e^{a t}` times `1`, `cos (b t)`, `sin (b t)`, `cosh (b t)` or
`sinh (b t)`. -/
inductive LaplaceKind
  | exp | cos | sin | cosh | sinh
  deriving DecidableEq, Repr

/-- A term `c tⁿ e^{a t} g (b t)`. -/
structure LaplaceTerm where
  /-- The constant factor `c`. -/
  c : ℝ
  /-- The power `n` of `t`. -/
  n : ℕ
  /-- The exponential rate `a`. -/
  a : ℝ
  /-- The frequency `b` of the trigonometric or hyperbolic factor (unused for `exp`). -/
  b : ℝ
  /-- Which factor `g` multiplies `tⁿ e^{a t}`. -/
  kind : LaplaceKind

/-- The value of a term at `t`. -/
noncomputable def LaplaceTerm.eval (T : LaplaceTerm) (t : ℝ) : ℝ :=
  match T.kind with
  | .exp => T.c * (t ^ T.n * Real.exp (T.a * t))
  | .cos => T.c * (t ^ T.n * Real.exp (T.a * t) * Real.cos (T.b * t))
  | .sin => T.c * (t ^ T.n * Real.exp (T.a * t) * Real.sin (T.b * t))
  | .cosh => T.c * (t ^ T.n * Real.exp (T.a * t) * Real.cosh (T.b * t))
  | .sinh => T.c * (t ^ T.n * Real.exp (T.a * t) * Real.sinh (T.b * t))

/-- Where the transform of a term is proved: `a < s`, and `a ± b < s` for `cosh`, `sinh`. -/
def LaplaceTerm.Admissible (T : LaplaceTerm) (s : ℝ) : Prop :=
  match T.kind with
  | .exp | .cos | .sin => T.a < s
  | .cosh | .sinh => T.a + T.b < s ∧ T.a - T.b < s

/-- The transform of a term at `s`. -/
noncomputable def LaplaceTerm.transform (T : LaplaceTerm) (s : ℝ) : ℝ :=
  match T.kind with
  | .exp => T.c * (T.n.factorial / (s - T.a) ^ (T.n + 1))
  | .cos => T.c * (T.n.factorial * (laplacePQ (s - T.a) T.b (T.n + 1)).1 /
      ((s - T.a) ^ 2 + T.b ^ 2) ^ (T.n + 1))
  | .sin => T.c * (T.n.factorial * (laplacePQ (s - T.a) T.b (T.n + 1)).2 /
      ((s - T.a) ^ 2 + T.b ^ 2) ^ (T.n + 1))
  | .cosh => T.c * (T.n.factorial / 2 *
      (1 / (s - (T.a + T.b)) ^ (T.n + 1) + 1 / (s - (T.a - T.b)) ^ (T.n + 1)))
  | .sinh => T.c * (T.n.factorial / 2 *
      (1 / (s - (T.a + T.b)) ^ (T.n + 1) - 1 / (s - (T.a - T.b)) ^ (T.n + 1)))

/-- A constant factor: integrability and the value of the integral scale by `c`. -/
theorem laplace_const_mul {f : ℝ → ℝ} {s v : ℝ} (c : ℝ)
    (h : IntegrableOn (fun t ↦ Real.exp (-(s * t)) * f t) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * f t = v) :
    IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (c * f t)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (c * f t) = c * v := by
  have hf : (fun t ↦ Real.exp (-(s * t)) * (c * f t)) =
      fun t ↦ c * (Real.exp (-(s * t)) * f t) := by
    funext t; ring
  rw [hf]
  exact ⟨Integrable.const_mul h.1 c, by rw [integral_const_mul, h.2]⟩

/-- The transform of one term. -/
theorem LaplaceTerm.laplace (T : LaplaceTerm) {s : ℝ} (h : T.Admissible s) :
    IntegrableOn (fun t ↦ Real.exp (-(s * t)) * T.eval t) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * T.eval t = T.transform s := by
  obtain ⟨c, n, a, b, k⟩ := T
  cases k
  · exact laplace_const_mul c (f := fun t ↦ t ^ n * Real.exp (a * t)) (laplace_exp n h)
  · exact laplace_const_mul c (f := fun t ↦ t ^ n * Real.exp (a * t) * Real.cos (b * t))
      (laplace_cos n h)
  · exact laplace_const_mul c (f := fun t ↦ t ^ n * Real.exp (a * t) * Real.sin (b * t))
      (laplace_sin n h)
  · exact laplace_const_mul c (f := fun t ↦ t ^ n * Real.exp (a * t) * Real.cosh (b * t))
      (laplace_cosh n h.1 h.2)
  · exact laplace_const_mul c (f := fun t ↦ t ^ n * Real.exp (a * t) * Real.sinh (b * t))
      (laplace_sinh n h.1 h.2)

/-- Linearity: the transform of a sum of terms. -/
theorem integral_exp_mul_sum (Ts : List LaplaceTerm) {s : ℝ} (h : ∀ T ∈ Ts, T.Admissible s) :
    IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (Ts.map fun T ↦ T.eval t).sum) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (Ts.map fun T ↦ T.eval t).sum =
        (Ts.map fun T ↦ T.transform s).sum := by
  induction Ts with
  | nil => simp
  | cons T Ts ih =>
    have hT := T.laplace (h T (by simp))
    have hTs := ih (fun T' hT' ↦ h T' (by simp [hT']))
    have hf : (fun t ↦ Real.exp (-(s * t)) * ((T :: Ts).map fun T ↦ T.eval t).sum) =
        fun t ↦ Real.exp (-(s * t)) * T.eval t +
          Real.exp (-(s * t)) * (Ts.map fun T ↦ T.eval t).sum := by
      funext t; simp [mul_add]
    rw [hf]
    refine ⟨Integrable.add hT.1 hTs.1, ?_⟩
    rw [integral_add hT.1 hTs.1, hT.2, hTs.2]
    simp

end CAS.Calculus.Laplace

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.ExpTrigPrimitive
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Fourier coefficients of `xʲ e ^ (a x) cos (k x)` and `xʲ e ^ (a x) sin (k x)`

Integration by parts with the primitives `CAS.ExpTrig.primPair` gives, for `a ^ 2 + b ^ 2 ≠ 0`,
the integrals of `xʲ e ^ (a x) cos (b x)` and `xʲ e ^ (a x) sin (b x)`

* over `[-π, π]` when `sin (b π) = 0` and `cos (b π) = σ` (`integral_sym`, the recursion `sym`),
  so for every integer frequency `b`;
* over `[0, L]` when `sin (b L) = 0` and `cos (b L) = σ` (`integral_half`, the recursion `half`),
  so for `b = n π / L`.

From these come the three Fourier formulas on `[-π, π]`, for every `n`, of a sum of terms
`c xʲ e ^ (a x) cos (k x)` and `c xʲ e ^ (a x) sin (k x)`, and the sine and cosine integrals on
`[0, L]` of a sum of terms `c πᵖ xʲ e ^ (a x)`.

## Main definitions

* `sym`, `half`: the two recursions in `j`, with `wall` for the boundary values on `[-π, π]`.
* `PTerm`, `HTerm`: the terms on `[-π, π]` and on `[0, L]`, with their integrals `PTerm.mean`,
  `PTerm.cosCoeff`, `PTerm.sinCoeff`, `HTerm.mean`, `HTerm.cosCoeff` and `HTerm.sinCoeff`.
* `CAS.Fourier.multipleAngle`: `cos (k x)` and `sin (k x)` as polynomials in `cos x` and `sin x`.

## Main results

* `integral_sym`, `integral_half`: the integrals of one term over `[-π, π]` and over `[0, L]`.
* `fourier_of_eq`: the three Fourier formulas for a function equal to a sum of `PTerm`s.
* `half_of_eq`: the sine and cosine integrals on `[0, L]` of a function equal to a sum of `HTerm`s.
* `cosCoeff_cosT`, `sinCoeff_sinT`, `mean_cosT`, ...: closed forms for the terms `c cos (k x)`
  and `c sin (k x)`.

## Implementation notes

Each integral is the difference of the values of an explicit primitive at the endpoints
(`integral_eq_sub_of_hasDerivAt`), and `primPair_sym` and `primPair_half` evaluate that
difference by the recursions, using only `sin (b π) = 0` or `sin (b L) = 0` and the value `σ` of
the cosine. On `[-π, π]` we write the products `cos (k x) cos (n x)`, `sin (k x) cos (n x)`, ...
as sums of `cos ((n ∓ k) x)` and `sin ((n ∓ k) x)`, so `integral_sym` covers every frequency
except `0` with `a = 0`, which its hypothesis `a ^ 2 + b ^ 2 ≠ 0` excludes. There the integral is
that of `xʲ` (`low` when `n = k`, `high` when `n + k = 0`).

`#cas [fourier x n]` (`CAS.Command.FourierProduct`) takes the terms of a function such as
`sin x ^ 3 cos (2 x)` from its exponential polynomial, and `ring_nf` checks that they add up to
the input after `cos (k x)` and `sin (k x)` are written as polynomials in `cos x` and `sin x`
(`CAS.Fourier.multipleAngle`) and the powers of `sin x` are reduced
(`CAS.Fourier.sin_pow_add_two`). The command runs `sym` and `half` symbolically to print the
closed forms, and the proof unfolds the same recursions. The reduction formulas are classical
integration by parts, and the bookkeeping by `PTerm` and `HTerm` lets one theorem serve every
`n`.
-/

@[expose] public section

namespace CAS.FourierProduct

open Real intervalIntegral MeasureTheory
open CAS.ExpTrig

/-- For functions `g t` continuous for every `t ∈ D`, `∫_u^v` of the sum over the list `D` of
`g t x` is the sum over `D` of `∫_u^v g t x`. -/
theorem integral_list_sum {α : Type*} (D : List α) (g : α → ℝ → ℝ)
    (hg : ∀ t ∈ D, Continuous (g t)) (u v : ℝ) :
    ∫ x in u..v, (D.map fun t ↦ g t x).sum = (D.map fun t ↦ ∫ x in u..v, g t x).sum := by
  induction D with
  | nil => simp
  | cons t D ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [intervalIntegral.integral_add ((hg t (by simp)).intervalIntegrable _ _)
      ((continuous_list_sum D fun s hs ↦ hg s (by simp [hs])).intervalIntegrable _ _),
      ih fun s hs ↦ hg s (by simp [hs])]

/-! ## The interval `[-π, π]` -/

/-- `πʲ e ^ (a π) - (-π)ʲ e ^ (-a π)`. -/
noncomputable def wall (a : ℝ) (j : ℕ) : ℝ := π ^ j * exp (a * π) - (-π) ^ j * exp (-(a * π))

/-- `(∫_{-π}^{π} xʲ e ^ (a x) cos (b x), ∫_{-π}^{π} xʲ e ^ (a x) sin (b x))` when
`sin (b π) = 0` and `cos (b π) = σ`. -/
noncomputable def sym (a b σ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a * σ * wall a 0 / (a ^ 2 + b ^ 2), -(b * σ * wall a 0) / (a ^ 2 + b ^ 2))
  | j + 1 => ((a * σ * wall a (j + 1) -
        (j + 1) * (a * (sym a b σ j).1 + b * (sym a b σ j).2)) / (a ^ 2 + b ^ 2),
      (-(b * σ * wall a (j + 1)) -
        (j + 1) * (a * (sym a b σ j).2 - b * (sym a b σ j).1)) / (a ^ 2 + b ^ 2))

/-- If `sin (b π) = 0` and `cos (b π) = σ`, then for every `j` the two primitives `primPair a b j`
take the values `(sym a b σ j).1` and `(sym a b σ j).2` at `π` minus their values at `-π`. -/
theorem primPair_sym {a b σ : ℝ} (hs : sin (b * π) = 0) (hc : cos (b * π) = σ) :
    ∀ j : ℕ, (primPair a b j).1 π - (primPair a b j).1 (-π) = (sym a b σ j).1 ∧
      (primPair a b j).2 π - (primPair a b j).2 (-π) = (sym a b σ j).2
  | 0 => by
    simp only [primPair, sym, baseCos, baseSin, wall, mul_neg, sin_neg, cos_neg, hs, hc,
      pow_zero, one_mul, neg_zero]
    constructor <;> ring
  | j + 1 => by
    obtain ⟨h1, h2⟩ := primPair_sym (a := a) hs hc j
    simp only [primPair, sym, baseCos, baseSin, wall, mul_neg, sin_neg, cos_neg, hs, hc,
      neg_zero, ← h1, ← h2]
    constructor <;> ring

/-- For `a ^ 2 + b ^ 2 ≠ 0`, `sin (b π) = 0` and `cos (b π) = σ`, the integrals
`∫_{-π}^{π} xʲ e ^ (a x) cos (b x)` and `∫_{-π}^{π} xʲ e ^ (a x) sin (b x)` are the two
components of `sym a b σ j`. -/
theorem integral_sym {a b σ : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) (hs : sin (b * π) = 0)
    (hc : cos (b * π) = σ) (j : ℕ) :
    (∫ x in -π..π, x ^ j * exp (a * x) * cos (b * x)) = (sym a b σ j).1 ∧
      (∫ x in -π..π, x ^ j * exp (a * x) * sin (b * x)) = (sym a b σ j).2 := by
  obtain ⟨h1, h2⟩ := primPair_sym (a := a) hs hc j
  exact ⟨(integral_eq_sub_of_hasDerivAt (fun x _ ↦ (hasDerivAt_primPair h j x).1)
      (Continuous.intervalIntegrable (by fun_prop) _ _)).trans h1,
    (integral_eq_sub_of_hasDerivAt (fun x _ ↦ (hasDerivAt_primPair h j x).2)
      (Continuous.intervalIntegrable (by fun_prop) _ _)).trans h2⟩

/-- `∫_{-π}^{π} xʲ`. -/
noncomputable def polyMean (j : ℕ) : ℝ := (π ^ (j + 1) - (-π) ^ (j + 1)) / (j + 1)

/-- `∫_{-π}^{π} xʲ = polyMean j`. -/
theorem integral_pow_pi (j : ℕ) : ∫ x in -π..π, x ^ j = polyMean j := by
  rw [integral_pow, polyMean]

/-- The integrals with `b = n - k`. -/
noncomputable def low (a : ℚ) (j n k : ℕ) : ℝ × ℝ :=
  if a = 0 ∧ n = k then (polyMean j, 0) else sym a ((n : ℝ) - k) ((-1) ^ n * (-1) ^ k) j

/-- The integrals with `b = n + k`. -/
noncomputable def high (a : ℚ) (j n k : ℕ) : ℝ × ℝ :=
  if a = 0 ∧ n + k = 0 then (polyMean j, 0) else sym a ((n : ℝ) + k) ((-1) ^ n * (-1) ^ k) j

/-- For natural `n` and `k`, `sin ((n - k) π) = 0`. -/
theorem sin_sub_mul_pi (n k : ℕ) : sin (((n : ℝ) - k) * π) = 0 := by
  simp [sub_mul, sin_sub]

/-- For natural `n` and `k`, `cos ((n - k) π) = (-1) ^ n (-1) ^ k`. -/
theorem cos_sub_mul_pi (n k : ℕ) : cos (((n : ℝ) - k) * π) = (-1) ^ n * (-1) ^ k := by
  simp [sub_mul, cos_sub, cos_nat_mul_pi]

/-- For natural `n` and `k`, `sin ((n + k) π) = 0`. -/
theorem sin_add_mul_pi (n k : ℕ) : sin (((n : ℝ) + k) * π) = 0 := by
  simp [add_mul, sin_add]

/-- For natural `n` and `k`, `cos ((n + k) π) = (-1) ^ n (-1) ^ k`. -/
theorem cos_add_mul_pi (n k : ℕ) : cos (((n : ℝ) + k) * π) = (-1) ^ n * (-1) ^ k := by
  simp [add_mul, cos_add, cos_nat_mul_pi]

/-- For `b = 0` and the rational rate `0`, the integrals `∫_{-π}^{π} xʲ e ^ (0 x) cos (b x)` and
`∫_{-π}^{π} xʲ e ^ (0 x) sin (b x)` are `polyMean j` and `0`. -/
theorem integral_degenerate (j : ℕ) {b : ℝ} (hb : b = 0) :
    (∫ x in -π..π, x ^ j * exp ((0 : ℚ) * x) * cos (b * x)) = polyMean j ∧
      (∫ x in -π..π, x ^ j * exp ((0 : ℚ) * x) * sin (b * x)) = 0 := by
  subst hb
  simpa using integral_pow_pi j

/-- For rational `a` and natural `j`, `n`, `k`, the integrals over `[-π, π]` of
`xʲ e ^ (a x) cos ((n - k) x)` and `xʲ e ^ (a x) sin ((n - k) x)` are the two components of
`low a j n k`. -/
theorem integral_low (a : ℚ) (j n k : ℕ) :
    (∫ x in -π..π, x ^ j * exp (a * x) * cos (((n : ℝ) - k) * x)) = (low a j n k).1 ∧
      (∫ x in -π..π, x ^ j * exp (a * x) * sin (((n : ℝ) - k) * x)) = (low a j n k).2 := by
  unfold low
  split_ifs with hd
  · obtain ⟨rfl, rfl⟩ := hd
    exact integral_degenerate j (sub_self _)
  · exact integral_sym (fun h0 ↦ hd (by simpa [sub_eq_zero] using sq_add_sq_eq_zero.mp h0))
      (sin_sub_mul_pi n k) (cos_sub_mul_pi n k) j

/-- For rational `a` and natural `j`, `n`, `k`, the integrals over `[-π, π]` of
`xʲ e ^ (a x) cos ((n + k) x)` and `xʲ e ^ (a x) sin ((n + k) x)` are the two components of
`high a j n k`. -/
theorem integral_high (a : ℚ) (j n k : ℕ) :
    (∫ x in -π..π, x ^ j * exp (a * x) * cos (((n : ℝ) + k) * x)) = (high a j n k).1 ∧
      (∫ x in -π..π, x ^ j * exp (a * x) * sin (((n : ℝ) + k) * x)) = (high a j n k).2 := by
  unfold high
  split_ifs with hd
  · obtain ⟨rfl, hnk⟩ := hd
    exact integral_degenerate j (by exact_mod_cast hnk)
  · exact integral_sym (fun h0 ↦ hd (by exact_mod_cast sq_add_sq_eq_zero.mp h0))
      (sin_add_mul_pi n k) (cos_add_mul_pi n k) j

/-- A term `c xʲ e ^ (a x) cos (k x)` or `c xʲ e ^ (a x) sin (k x)`. -/
inductive PTerm
  | cosT (c : ℚ) (j : ℕ) (a : ℚ) (k : ℕ)
  | sinT (c : ℚ) (j : ℕ) (a : ℚ) (k : ℕ)
  deriving DecidableEq, Repr

namespace PTerm

/-- The term as a function of `x`. -/
noncomputable def eval : PTerm → ℝ → ℝ
  | cosT c j a k, x => c * (x ^ j * exp (a * x) * cos (k * x))
  | sinT c j a k, x => c * (x ^ j * exp (a * x) * sin (k * x))

/-- `∫_{-π}^{π}` of the term. -/
noncomputable def mean : PTerm → ℝ
  | cosT c j a k => c * (high a j 0 k).1
  | sinT c j a k => c * (high a j 0 k).2

/-- `∫_{-π}^{π}` of the term times `cos (n x)`. -/
noncomputable def cosCoeff (n : ℕ) : PTerm → ℝ
  | cosT c j a k => c / 2 * ((low a j n k).1 + (high a j n k).1)
  | sinT c j a k => c / 2 * ((high a j n k).2 - (low a j n k).2)

/-- `∫_{-π}^{π}` of the term times `sin (n x)`. -/
noncomputable def sinCoeff (n : ℕ) : PTerm → ℝ
  | cosT c j a k => c / 2 * ((high a j n k).2 + (low a j n k).2)
  | sinT c j a k => c / 2 * ((low a j n k).1 - (high a j n k).1)

/-- Every term `t.eval` is continuous. -/
theorem continuous_eval (t : PTerm) : Continuous t.eval := by
  cases t <;> exact continuous_const.mul (by fun_prop)

/-- For continuous `u` and `v`, `∫_{-π}^{π} c / 2 (u x + v x)` is `c / 2` times the sum of
`∫_{-π}^{π} u` and `∫_{-π}^{π} v`. -/
theorem integral_half_sum (c : ℝ) {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v) :
    ∫ x in -π..π, c / 2 * (u x + v x) = c / 2 * ((∫ x in -π..π, u x) + ∫ x in -π..π, v x) := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hu.intervalIntegrable _ _) (hv.intervalIntegrable _ _)]

/-- For continuous `u` and `v`, `∫_{-π}^{π} c / 2 (u x - v x)` is `c / 2` times the difference
of `∫_{-π}^{π} u` and `∫_{-π}^{π} v`. -/
theorem integral_half_diff (c : ℝ) {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v) :
    ∫ x in -π..π, c / 2 * (u x - v x) = c / 2 * ((∫ x in -π..π, u x) - ∫ x in -π..π, v x) := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hu.intervalIntegrable _ _) (hv.intervalIntegrable _ _)]

/-- `∫_{-π}^{π} t.eval = t.mean` for every term `t`. -/
theorem integral_eval (t : PTerm) : ∫ x in -π..π, t.eval x = t.mean := by
  cases t <;> simp [eval, mean, ← (integral_high _ _ 0 _).1, ← (integral_high _ _ 0 _).2]

/-- `∫_{-π}^{π} t.eval x cos (n x) = t.cosCoeff n` for every term `t` and every natural `n`. -/
theorem integral_eval_mul_cos (t : PTerm) (n : ℕ) :
    ∫ x in -π..π, t.eval x * cos (n * x) = t.cosCoeff n := by
  cases t
  all_goals
    simp (disch := fun_prop) only [cosCoeff, ← (integral_low _ _ n _).1,
      ← (integral_low _ _ n _).2, ← (integral_high _ _ n _).1, ← (integral_high _ _ n _).2,
      ← integral_half_sum, ← integral_half_diff]
    congr 1 with x
    simp only [eval, sub_mul, add_mul, cos_sub, cos_add, sin_sub, sin_add]
    ring

/-- `∫_{-π}^{π} t.eval x sin (n x) = t.sinCoeff n` for every term `t` and every natural `n`. -/
theorem integral_eval_mul_sin (t : PTerm) (n : ℕ) :
    ∫ x in -π..π, t.eval x * sin (n * x) = t.sinCoeff n := by
  cases t
  all_goals
    simp (disch := fun_prop) only [sinCoeff, ← (integral_low _ _ n _).1,
      ← (integral_low _ _ n _).2, ← (integral_high _ _ n _).1, ← (integral_high _ _ n _).2,
      ← integral_half_sum, ← integral_half_diff]
    congr 1 with x
    simp only [eval, sub_mul, add_mul, cos_sub, cos_add, sin_sub, sin_add]
    ring

end PTerm

/-- `∑ tᵢ (x)`. -/
noncomputable def evalL (D : List PTerm) (x : ℝ) : ℝ := (D.map fun t ↦ t.eval x).sum

/-- The three Fourier formulas on `[-π, π]` for a function equal to `evalL D`, for every `n`. -/
theorem fourier_of_eq {f : ℝ → ℝ} (D : List PTerm) (hf : ∀ x, f x = evalL D x) :
    (∫ x in -π..π, f x) = (D.map PTerm.mean).sum ∧
      (∀ n : ℕ, ∫ x in -π..π, f x * cos (n * x) = (D.map (PTerm.cosCoeff n)).sum) ∧
      ∀ n : ℕ, ∫ x in -π..π, f x * sin (n * x) = (D.map (PTerm.sinCoeff n)).sum := by
  obtain rfl : f = evalL D := funext hf
  simp only [evalL, ← List.sum_map_mul_right]
  refine ⟨?_, fun n ↦ ?_, fun n ↦ ?_⟩
  · simpa only [PTerm.integral_eval] using
      integral_list_sum D (fun t x ↦ t.eval x) (fun t _ ↦ t.continuous_eval) (-π) π
  · simpa only [PTerm.integral_eval_mul_cos] using integral_list_sum D
      (fun t x ↦ t.eval x * cos (n * x)) (fun t _ ↦ t.continuous_eval.mul (by fun_prop)) (-π) π
  · simpa only [PTerm.integral_eval_mul_sin] using integral_list_sum D
      (fun t x ↦ t.eval x * sin (n * x)) (fun t _ ↦ t.continuous_eval.mul (by fun_prop)) (-π) π

/-! ### The terms `c cos (k x)` and `c sin (k x)` -/

/-- `polyMean 0 = 2 π`. -/
theorem polyMean_zero : polyMean 0 = 2 * π := by
  simp only [polyMean]
  ring

/-- `(low 0 0 n k).1` is `2 π` if `n = k` and `0` otherwise. -/
theorem low_fst (n k : ℕ) : (low 0 0 n k).1 = if n = k then 2 * π else 0 := by
  unfold low
  by_cases h : n = k
  · simp [h, polyMean_zero]
  · simp [h, sym, wall]

/-- `(low 0 0 n k).2 = 0`. -/
theorem low_snd (n k : ℕ) : (low 0 0 n k).2 = 0 := by
  unfold low
  split_ifs <;> simp [sym, wall]

/-- `(high 0 0 n k).1` is `2 π` if `n + k = 0` and `0` otherwise. -/
theorem high_fst (n k : ℕ) : (high 0 0 n k).1 = if n + k = 0 then 2 * π else 0 := by
  unfold high
  by_cases h : n + k = 0
  · simp only [h, and_self, ↓reduceIte, polyMean_zero]
  · simp only [h, and_false, ↓reduceIte]
    simp [sym, wall]

/-- `(high 0 0 n k).2 = 0`. -/
theorem high_snd (n k : ℕ) : (high 0 0 n k).2 = 0 := by
  unfold high
  split_ifs <;> simp [sym, wall]

/-- The coefficient `cosCoeff n` of the term `c cos (k x)` is
`(if n = k then c π else 0) + (if n + k = 0 then c π else 0)`. -/
theorem cosCoeff_cosT (c : ℚ) (n k : ℕ) : (PTerm.cosT c 0 0 k).cosCoeff n =
    (if n = k then (c : ℝ) * π else 0) + (if n + k = 0 then (c : ℝ) * π else 0) := by
  rw [PTerm.cosCoeff, low_fst, high_fst]
  split_ifs <;> ring

/-- The coefficient `sinCoeff n` of the term `c sin (k x)` is
`(if n = k then c π else 0) - (if n + k = 0 then c π else 0)`. -/
theorem sinCoeff_sinT (c : ℚ) (n k : ℕ) : (PTerm.sinT c 0 0 k).sinCoeff n =
    (if n = k then (c : ℝ) * π else 0) - (if n + k = 0 then (c : ℝ) * π else 0) := by
  rw [PTerm.sinCoeff, low_fst, high_fst]
  split_ifs <;> ring

/-- The coefficient `sinCoeff n` of the term `c cos (k x)` is `0`. -/
theorem sinCoeff_cosT (c : ℚ) (n k : ℕ) : (PTerm.cosT c 0 0 k).sinCoeff n = 0 := by
  rw [PTerm.sinCoeff, low_snd, high_snd, add_zero, mul_zero]

/-- The coefficient `cosCoeff n` of the term `c sin (k x)` is `0`. -/
theorem cosCoeff_sinT (c : ℚ) (n k : ℕ) : (PTerm.sinT c 0 0 k).cosCoeff n = 0 := by
  rw [PTerm.cosCoeff, low_snd, high_snd, sub_zero, mul_zero]

/-- The integral `mean` of the term `c cos (k x)` is `2 c π` if `k = 0` and `0` otherwise. -/
theorem mean_cosT (c : ℚ) (k : ℕ) :
    (PTerm.cosT c 0 0 k).mean = if k = 0 then 2 * (c : ℝ) * π else 0 := by
  rw [PTerm.mean, high_fst, zero_add]
  split_ifs <;> ring

/-- The integral `mean` of the term `c sin (k x)` is `0`. -/
theorem mean_sinT (c : ℚ) (k : ℕ) : (PTerm.sinT c 0 0 k).mean = 0 := by
  rw [PTerm.mean, high_snd, mul_zero]

/-! ## The interval `[0, L]` -/

/-- `(∫_0^L xʲ e ^ (a x) cos (b x), ∫_0^L xʲ e ^ (a x) sin (b x))` when `sin (b L) = 0` and
`cos (b L) = σ`. -/
noncomputable def half (a b L σ : ℝ) : ℕ → ℝ × ℝ
  | 0 => ((a * σ * exp (a * L) - a) / (a ^ 2 + b ^ 2),
      (b - b * σ * exp (a * L)) / (a ^ 2 + b ^ 2))
  | j + 1 => ((a * σ * L ^ (j + 1) * exp (a * L) -
        (j + 1) * (a * (half a b L σ j).1 + b * (half a b L σ j).2)) / (a ^ 2 + b ^ 2),
      (-(b * σ * L ^ (j + 1) * exp (a * L)) -
        (j + 1) * (a * (half a b L σ j).2 - b * (half a b L σ j).1)) / (a ^ 2 + b ^ 2))

/-- If `sin (b L) = 0` and `cos (b L) = σ`, then for every `j` the two primitives `primPair a b j`
take the values `(half a b L σ j).1` and `(half a b L σ j).2` at `L` minus their values at `0`. -/
theorem primPair_half {a b L σ : ℝ} (hs : sin (b * L) = 0) (hc : cos (b * L) = σ) :
    ∀ j : ℕ, (primPair a b j).1 L - (primPair a b j).1 0 = (half a b L σ j).1 ∧
      (primPair a b j).2 L - (primPair a b j).2 0 = (half a b L σ j).2
  | 0 => by
    simp only [primPair, half, baseCos, baseSin, hs, hc, mul_zero, exp_zero, cos_zero,
      sin_zero]
    constructor <;> ring
  | j + 1 => by
    obtain ⟨h1, h2⟩ := primPair_half (a := a) hs hc j
    simp only [primPair, half, baseCos, baseSin, hs, hc, mul_zero, exp_zero, cos_zero,
      sin_zero, ← h1, ← h2]
    constructor <;> ring

/-- For `a ^ 2 + b ^ 2 ≠ 0`, `sin (b L) = 0` and `cos (b L) = σ`, the integrals
`∫_0^L xʲ e ^ (a x) cos (b x)` and `∫_0^L xʲ e ^ (a x) sin (b x)` are the two components of
`half a b L σ j`. -/
theorem integral_half {a b L σ : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) (hs : sin (b * L) = 0)
    (hc : cos (b * L) = σ) (j : ℕ) :
    (∫ x in 0..L, x ^ j * exp (a * x) * cos (b * x)) = (half a b L σ j).1 ∧
      (∫ x in 0..L, x ^ j * exp (a * x) * sin (b * x)) = (half a b L σ j).2 := by
  obtain ⟨h1, h2⟩ := primPair_half (a := a) hs hc j
  exact ⟨(integral_eq_sub_of_hasDerivAt (fun x _ ↦ (hasDerivAt_primPair h j x).1)
      (Continuous.intervalIntegrable (by fun_prop) _ _)).trans h1,
    (integral_eq_sub_of_hasDerivAt (fun x _ ↦ (hasDerivAt_primPair h j x).2)
      (Continuous.intervalIntegrable (by fun_prop) _ _)).trans h2⟩

/-- A term `c πᵖ xʲ e ^ (a x)`. -/
structure HTerm where
  /-- The rational coefficient `c`. -/
  c : ℚ
  /-- The power `p` of `π`. -/
  p : ℕ
  /-- The power `j` of `x`. -/
  j : ℕ
  /-- The exponential rate `a` in `e ^ (a x)`. -/
  a : ℚ
  deriving DecidableEq, Repr

namespace HTerm

/-- The term as a function of `x`. -/
noncomputable def eval (t : HTerm) (x : ℝ) : ℝ := t.c * π ^ t.p * (x ^ t.j * exp (t.a * x))

/-- `∫_0^L` of the term. -/
noncomputable def mean (L : ℝ) (t : HTerm) : ℝ :=
  t.c * π ^ t.p * if t.a = 0 then L ^ (t.j + 1) / (t.j + 1) else (half t.a 0 L 1 t.j).1

/-- `∫_0^L` of the term times `cos (b x)`. -/
noncomputable def cosCoeff (b L σ : ℝ) (t : HTerm) : ℝ :=
  t.c * π ^ t.p * (half t.a b L σ t.j).1

/-- `∫_0^L` of the term times `sin (b x)`. -/
noncomputable def sinCoeff (b L σ : ℝ) (t : HTerm) : ℝ :=
  t.c * π ^ t.p * (half t.a b L σ t.j).2

/-- Every term `t.eval` is continuous. -/
theorem continuous_eval (t : HTerm) : Continuous t.eval := by
  unfold eval
  fun_prop

/-- `∫_0^L t.eval = t.mean L` for every `L` and every term `t`. -/
theorem integral_eval (L : ℝ) (t : HTerm) : ∫ x in 0..L, t.eval x = t.mean L := by
  unfold eval mean
  rw [intervalIntegral.integral_const_mul]
  split_ifs with ha
  · simp [ha]
  · rw [← (integral_half (a := t.a) (b := 0) (L := L) (σ := 1) (by simpa using ha) (by simp)
      (by simp) t.j).1]
    simp

/-- For `b ≠ 0` with `sin (b L) = 0` and `cos (b L) = σ`,
`∫_0^L t.eval x cos (b x) = t.cosCoeff b L σ` for every term `t`. -/
theorem integral_eval_mul_cos {b L σ : ℝ} (hb : b ≠ 0) (hs : sin (b * L) = 0)
    (hc : cos (b * L) = σ) (t : HTerm) :
    ∫ x in 0..L, t.eval x * cos (b * x) = t.cosCoeff b L σ := by
  rw [cosCoeff, ← (integral_half (a := t.a) (by positivity) hs hc t.j).1,
    ← intervalIntegral.integral_const_mul]
  simp only [eval, mul_assoc]

/-- For `b ≠ 0` with `sin (b L) = 0` and `cos (b L) = σ`,
`∫_0^L t.eval x sin (b x) = t.sinCoeff b L σ` for every term `t`. -/
theorem integral_eval_mul_sin {b L σ : ℝ} (hb : b ≠ 0) (hs : sin (b * L) = 0)
    (hc : cos (b * L) = σ) (t : HTerm) :
    ∫ x in 0..L, t.eval x * sin (b * x) = t.sinCoeff b L σ := by
  rw [sinCoeff, ← (integral_half (a := t.a) (by positivity) hs hc t.j).2,
    ← intervalIntegral.integral_const_mul]
  simp only [eval, mul_assoc]

end HTerm

/-- `∑ tᵢ (x)`. -/
noncomputable def hEvalL (D : List HTerm) (x : ℝ) : ℝ := (D.map fun t ↦ t.eval x).sum

/-- The cosine and sine integrals on `[0, L]` of a function equal to `hEvalL D`, for a
frequency `b ≠ 0` with `sin (b L) = 0`, `cos (b L) = σ`. -/
theorem half_of_eq {f : ℝ → ℝ} (D : List HTerm) (hf : ∀ x, f x = hEvalL D x) (L : ℝ) :
    (∫ x in 0..L, f x) = (D.map (HTerm.mean L)).sum ∧
      ∀ {b σ : ℝ}, b ≠ 0 → sin (b * L) = 0 → cos (b * L) = σ →
        (∫ x in 0..L, f x * cos (b * x)) = (D.map (HTerm.cosCoeff b L σ)).sum ∧
          (∫ x in 0..L, f x * sin (b * x)) = (D.map (HTerm.sinCoeff b L σ)).sum := by
  obtain rfl : f = hEvalL D := funext hf
  simp only [hEvalL, ← List.sum_map_mul_right]
  refine ⟨?_, fun {b σ} hb hs hc ↦ ⟨?_, ?_⟩⟩
  · simpa only [HTerm.integral_eval] using
      integral_list_sum D (fun t x ↦ t.eval x) (fun t _ ↦ t.continuous_eval) 0 L
  · simpa only [HTerm.integral_eval_mul_cos hb hs hc] using integral_list_sum D
      (fun t x ↦ t.eval x * cos (b * x)) (fun t _ ↦ t.continuous_eval.mul (by fun_prop)) 0 L
  · simpa only [HTerm.integral_eval_mul_sin hb hs hc] using integral_list_sum D
      (fun t x ↦ t.eval x * sin (b * x)) (fun t _ ↦ t.continuous_eval.mul (by fun_prop)) 0 L

end CAS.FourierProduct

/-! ## Multiple angles -/

namespace CAS.Fourier

open Real

/-- `(cos (k x), sin (k x))` as polynomials in `c = cos x`, `s = sin x`. -/
noncomputable def multipleAngle (c s : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | k + 1 => ((multipleAngle c s k).1 * c - (multipleAngle c s k).2 * s,
      (multipleAngle c s k).2 * c + (multipleAngle c s k).1 * s)

/-- `multipleAngle (cos x) (sin x) k = (cos (k x), sin (k x))` for every natural `k`. -/
theorem multipleAngle_eq (x : ℝ) : ∀ k : ℕ,
    multipleAngle (cos x) (sin x) k = (cos (k * x), sin (k * x))
  | 0 => by simp [multipleAngle]
  | k + 1 => by
    rw [multipleAngle, multipleAngle_eq x k]
    push_cast
    rw [add_mul, one_mul, cos_add, sin_add]

/-- `cos (k x)` is the first component of `multipleAngle (cos x) (sin x) k`, for natural `k`. This
is the rewrite rule by which `#cas [fourier x n]` writes `cos (k x)` in `cos x` and `sin x`. -/
theorem cos_nat_mul_eq (k : ℕ) (x : ℝ) : cos (k * x) = (multipleAngle (cos x) (sin x) k).1 := by
  rw [multipleAngle_eq]

/-- `sin (k x)` is the second component of `multipleAngle (cos x) (sin x) k`, for natural `k`.
This is the rewrite rule by which `#cas [fourier x n]` writes `sin (k x)` in `cos x` and `sin x`. -/
theorem sin_nat_mul_eq (k : ℕ) (x : ℝ) : sin (k * x) = (multipleAngle (cos x) (sin x) k).2 := by
  rw [multipleAngle_eq]

/-- Reduction modulo `sin ² + cos ² = 1`. -/
theorem sin_pow_add_two (x : ℝ) (n : ℕ) : sin x ^ (n + 2) = sin x ^ n * (1 - cos x ^ 2) := by
  rw [pow_add, ← sin_sq_add_cos_sq x]
  ring

end CAS.Fourier

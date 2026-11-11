/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Primitives of `xᵏ e ^ (a x) cos (b x)` and `xᵏ e ^ (a x) sin (b x)`

For real `a`, `b` with `a ^ 2 + b ^ 2 ≠ 0`, the pair `primPair a b k` of primitives of
`xᵏ e ^ (a x) cos (b x)` and `xᵏ e ^ (a x) sin (b x)` comes from

`e ^ (a x) (a cos (b x) + b sin (b x)) / (a ^ 2 + b ^ 2)` and
`e ^ (a x) (a sin (b x) - b cos (b x)) / (a ^ 2 + b ^ 2)` for `k = 0`,

and integration by parts against `xᵏ⁺¹` (`hasDerivAt_primPair`). With `b = 0` the first
component is a primitive of `xᵏ e ^ (a x)`, and with `a = 0` the two components are primitives
of `xᵏ cos (b x)` and `xᵏ sin (b x)`. `a` and `b` are arbitrary real numbers, so the parameters
may stay symbolic. For `a ≠ 0`, `primExp a k` is the primitive of `xᵏ e ^ (a x)` given by the
same integration by parts without a trigonometric factor (`hasDerivAt_primExp`).
-/

@[expose] public section

namespace CAS.ExpTrig

open Real

/-- The primitive of `e ^ (a x) cos (b x)`. -/
noncomputable def baseCos (a b x : ℝ) : ℝ :=
  exp (a * x) * (a * cos (b * x) + b * sin (b * x)) / (a ^ 2 + b ^ 2)

/-- The primitive of `e ^ (a x) sin (b x)`. -/
noncomputable def baseSin (a b x : ℝ) : ℝ :=
  exp (a * x) * (a * sin (b * x) - b * cos (b * x)) / (a ^ 2 + b ^ 2)

/-- Primitives of `xᵏ e ^ (a x) cos (b x)` and `xᵏ e ^ (a x) sin (b x)`. -/
noncomputable def primPair (a b : ℝ) : ℕ → (ℝ → ℝ) × (ℝ → ℝ)
  | 0 => (baseCos a b, baseSin a b)
  | k + 1 => (fun x ↦ x ^ (k + 1) * baseCos a b x -
        (k + 1) * (a * (primPair a b k).1 x + b * (primPair a b k).2 x) / (a ^ 2 + b ^ 2),
      fun x ↦ x ^ (k + 1) * baseSin a b x -
        (k + 1) * (a * (primPair a b k).2 x - b * (primPair a b k).1 x) / (a ^ 2 + b ^ 2))

/-- For `a ^ 2 + b ^ 2 ≠ 0`, `baseCos a b` has derivative `e ^ (a x) cos (b x)` at every real
`x`. -/
theorem hasDerivAt_baseCos {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) (x : ℝ) :
    HasDerivAt (baseCos a b) (exp (a * x) * cos (b * x)) x := by
  have hb := (hasDerivAt_id' x).const_mul b
  refine ((((hasDerivAt_id' x).const_mul a).exp.fun_mul ((hb.cos.const_mul a).fun_add
    (hb.sin.const_mul b))).div_const (a ^ 2 + b ^ 2)).congr_deriv ?_
  field_simp
  ring

/-- For all real `a` and `b`, `baseSin a b` has derivative `e ^ (a x) sin (b x)` at every real `x`.
No condition is needed: for `a = b = 0` both `baseSin 0 0` and the integrand are `0`. -/
theorem hasDerivAt_baseSin {a b : ℝ} (x : ℝ) :
    HasDerivAt (baseSin a b) (exp (a * x) * sin (b * x)) x := by
  by_cases h : a ^ 2 + b ^ 2 = 0
  · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 :=
      ⟨by nlinarith [sq_nonneg a, sq_nonneg b], by nlinarith [sq_nonneg a, sq_nonneg b]⟩
    have h0 : baseSin 0 0 = fun _ ↦ 0 := funext fun y ↦ by simp [baseSin]
    rw [h0]
    simpa using hasDerivAt_const x (0 : ℝ)
  have hb := (hasDerivAt_id' x).const_mul b
  refine ((((hasDerivAt_id' x).const_mul a).exp.fun_mul ((hb.sin.const_mul a).fun_sub
    (hb.cos.const_mul b))).div_const (a ^ 2 + b ^ 2)).congr_deriv ?_
  field_simp
  ring

/-- `(primPair a b k).1` and `.2` are primitives of `xᵏ e ^ (a x) cos (b x)` and
`xᵏ e ^ (a x) sin (b x)`. -/
theorem hasDerivAt_primPair {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) : ∀ (k : ℕ) (x : ℝ),
    HasDerivAt (primPair a b k).1 (x ^ k * exp (a * x) * cos (b * x)) x ∧
      HasDerivAt (primPair a b k).2 (x ^ k * exp (a * x) * sin (b * x)) x
  | 0, x => by
    simp only [primPair, pow_zero, one_mul]
    exact ⟨hasDerivAt_baseCos h x, hasDerivAt_baseSin x⟩
  | k + 1, x => by
    obtain ⟨hc, hs⟩ := hasDerivAt_primPair h k x
    have hp := hasDerivAt_pow (k + 1) x
    constructor
    · refine ((hp.fun_mul (hasDerivAt_baseCos h x)).fun_sub
        (((hc.const_mul a).fun_add (hs.const_mul b)).const_mul ((k + 1 : ℝ)) |>.div_const
          (a ^ 2 + b ^ 2))).congr_deriv ?_
      unfold baseCos
      push_cast
      field_simp
      try ring
    · refine ((hp.fun_mul (hasDerivAt_baseSin x)).fun_sub
        (((hs.const_mul a).fun_sub (hc.const_mul b)).const_mul ((k + 1 : ℝ)) |>.div_const
          (a ^ 2 + b ^ 2))).congr_deriv ?_
      unfold baseSin
      push_cast
      field_simp
      try ring

/-- Primitives of `xᵏ e ^ (a x)`, by parts: `e ^ (a x) / a`, then
`xᵏ⁺¹ e ^ (a x) / a - (k + 1) / a ∫ xᵏ e ^ (a x)`. -/
noncomputable def primExp (a : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x ↦ exp (a * x) / a
  | k + 1 => fun x ↦ x ^ (k + 1) * exp (a * x) / a - (k + 1) * primExp a k x / a

/-- For `a ≠ 0` and every `k`, `primExp a k` has derivative `xᵏ e ^ (a x)` at every real `x`. -/
theorem hasDerivAt_primExp {a : ℝ} (ha : a ≠ 0) : ∀ (k : ℕ) (x : ℝ),
    HasDerivAt (primExp a k) (x ^ k * exp (a * x)) x
  | 0, x => by
    refine (((hasDerivAt_id' x).const_mul a).exp.div_const a).congr_deriv ?_
    field_simp
  | k + 1, x => by
    have h1 := ((hasDerivAt_pow (k + 1) x).fun_mul ((hasDerivAt_id' x).const_mul a).exp).div_const a
    have h2 := ((hasDerivAt_primExp ha k x).const_mul ((k + 1 : ℝ))).div_const a
    refine (h1.fun_sub h2).congr_deriv ?_
    push_cast
    field_simp
    ring

end CAS.ExpTrig

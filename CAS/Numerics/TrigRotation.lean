/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.TrigTable

/-!
# Fixed-point powers of a rotation

From one fixed-point approximation `w` of `2^p (cos θ, sin θ)`, within `1` in each component
(`TrigApprox p w θ`), the integer recurrence `z₀ = (2^p, 0)`,
`z_{k+1} = round(z_k w / 2^p)` (complex multiplication of Gaussian integers, each component
rounded to the nearest integer) approximates `2^p (cos kθ, sin kθ)` for all multiples at once.
The error grows linearly: it is at most `4k` in each component as long as `8k ≤ 2^p`
(`rotationPower_sound`). This gives the values of `cos ((2m + 1) θ)` and `sin ((2m + 2) θ)` for
every mode `m` of a trigonometric series at a node from a single certified value of `cos θ` and
`sin θ`.

## Implementation notes

We prove the bound for the modulus in the complex plane (`norm_rotationPower_sub_le`) and read
off the components at the end. With the exact values `T = 2^p e^{ikθ}` and `E = 2^p e^{iθ}`, the
error of `z_{k+1}` is the rounding plus `((z_k - T) w + T (w - E)) / 2^p`. A rotation is an
isometry, so the error of `z_k` is carried over without amplification, up to the factor
`|w| / 2^p ≤ 1 + 2^(1-p)` of the approximate rotation, while the error of `w` and the rounding
add at most `3`; under `8k ≤ 2^p` the bound `4k` is therefore an invariant. Computing the
multiples of an angle by repeated multiplication with an approximate `e^{iθ}` is classical; the
bound and its proof are ours. No certificate is involved: `rotationPower_sound` holds for every
`p`, `w` and `k`. The steps use `Int` arithmetic and `roundShift`; `RotationIteration` runs a
floored variant on biased natural numbers, which suits long runs in the kernel.
-/

@[expose] public section

namespace CAS.Numerics

open Complex

/-- One step of the fixed-point rotation: `z ↦ round(z w / 2^p)` on Gaussian integers. -/
def rotationStep (p : ℕ) (w z : ℤ × ℤ) : ℤ × ℤ :=
  (roundShift p (z.1 * w.1 - z.2 * w.2), roundShift p (z.1 * w.2 + z.2 * w.1))

/-- The fixed-point powers `z_k ≈ 2^p (cos kθ, sin kθ)`. -/
def rotationPower (p : ℕ) (w : ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => ((2 ^ p : ℕ), 0)
  | k + 1 => rotationStep p w (rotationPower p w k)

/-- A Gaussian integer as a complex number. -/
private def toComplex (z : ℤ × ℤ) : ℂ := ⟨z.1, z.2⟩

/-- The fixed-point powers stay within `4k` of `2^p e^{ikθ}` in modulus while `8k ≤ 2^p`. -/
private theorem norm_rotationPower_sub_le {p : ℕ} (hp : 1 ≤ p) {w : ℤ × ℤ} {θ : ℝ}
    (hw : TrigApprox p w θ) {k : ℕ} (hk : 8 * k ≤ 2 ^ p) :
    ‖toComplex (rotationPower p w k) - (2 ^ p : ℝ) * exp ((k * θ : ℝ) * I)‖ ≤ 4 * k := by
  induction k with
  | zero => simp [rotationPower, toComplex, Complex.ext_iff, -Complex.ofReal_pow]
  | succ k ih =>
    have hk' : 8 * k ≤ 2 ^ p := by omega
    have ih := ih hk'
    set Z := toComplex (rotationPower p w k) with hZ
    set W := toComplex w with hW
    set E : ℂ := (2 ^ p : ℝ) * exp ((θ : ℝ) * I) with hE
    set T : ℂ := (2 ^ p : ℝ) * exp ((k * θ : ℝ) * I) with hT
    have h2p : (0 : ℝ) < 2 ^ p := by positivity
    have hn : ∀ x : ℝ, ‖((2 ^ p : ℝ) : ℂ) * exp (x * I)‖ = 2 ^ p := fun x ↦ by
      rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos h2p]
    have hWE : ‖W - E‖ ≤ 2 := by
      refine (norm_le_abs_re_add_abs_im _).trans ?_
      simp only [hW, hE, toComplex, sub_re, sub_im, re_ofReal_mul, im_ofReal_mul,
        exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
      linarith [hw.1, hw.2]
    have hWnorm : ‖W‖ ≤ 2 ^ p + 2 := by linarith [norm_sub_norm_le W E, hn θ]
    have hnext : (2 ^ p : ℝ) * exp (((k + 1 : ℕ) * θ : ℝ) * I) = T * E / (2 ^ p : ℝ) := by
      rw [hT, hE]
      have : (((k + 1 : ℕ) * θ : ℝ) : ℂ) * I = ((k * θ : ℝ) : ℂ) * I + ((θ : ℝ) : ℂ) * I := by
        push_cast
        ring
      rw [this, Complex.exp_add]
      field_simp
    set Zn := toComplex (rotationPower p w (k + 1)) with hZn
    have hround : ‖Zn - Z * W / (2 ^ p : ℝ)‖ ≤ 1 := by
      refine (norm_le_abs_re_add_abs_im _).trans ?_
      have r1 := abs_roundShift_sub_le p hp ((rotationPower p w k).1 * w.1 -
        (rotationPower p w k).2 * w.2)
      have r2 := abs_roundShift_sub_le p hp ((rotationPower p w k).1 * w.2 +
        (rotationPower p w k).2 * w.1)
      have e1 : (Zn - Z * W / (2 ^ p : ℝ)).re = (roundShift p ((rotationPower p w k).1 * w.1 -
          (rotationPower p w k).2 * w.2) : ℝ) - ((rotationPower p w k).1 * w.1 -
            (rotationPower p w k).2 * w.2 : ℤ) / 2 ^ p := by
        simp only [hZn, hZ, hW, toComplex, rotationPower, rotationStep, sub_re, div_ofReal_re,
          mul_re]
        push_cast
        ring
      have e2 : (Zn - Z * W / (2 ^ p : ℝ)).im = (roundShift p ((rotationPower p w k).1 * w.2 +
          (rotationPower p w k).2 * w.1) : ℝ) - ((rotationPower p w k).1 * w.2 +
            (rotationPower p w k).2 * w.1 : ℤ) / 2 ^ p := by
        simp only [hZn, hZ, hW, toComplex, rotationPower, rotationStep, sub_im, div_ofReal_im,
          mul_im]
        push_cast
        ring
      rw [e1, e2]
      linarith
    have hsplit : Zn - (2 ^ p : ℝ) * exp (((k + 1 : ℕ) * θ : ℝ) * I) =
        (Zn - Z * W / (2 ^ p : ℝ)) + ((Z - T) * W + T * (W - E)) / (2 ^ p : ℝ) := by
      rw [hnext]
      field_simp
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2p]
    have hmain : ‖(Z - T) * W + T * (W - E)‖ ≤ 4 * k * (2 ^ p + 2) + 2 ^ p * 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, hT, hn]
      exact add_le_add (mul_le_mul ih hWnorm (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left hWE h2p.le)
    have hk8 : (8 * k : ℝ) ≤ 2 ^ p := by exact_mod_cast hk'
    have : ‖(Z - T) * W + T * (W - E)‖ / 2 ^ p ≤ 4 * k + 3 := by
      rw [div_le_iff₀ h2p]
      nlinarith
    rw [Nat.cast_succ]
    linarith

/-- The fixed-point powers approximate `2^p (cos kθ, sin kθ)` within `4k` in each component while
`8k ≤ 2^p`. -/
theorem rotationPower_sound {p : ℕ} (hp : 1 ≤ p) {w : ℤ × ℤ} {θ : ℝ} (hw : TrigApprox p w θ)
    {k : ℕ} (hk : 8 * k ≤ 2 ^ p) :
    |((rotationPower p w k).1 : ℝ) - 2 ^ p * Real.cos (k * θ)| ≤ 4 * k ∧
      |((rotationPower p w k).2 : ℝ) - 2 ^ p * Real.sin (k * θ)| ≤ 4 * k := by
  have h := norm_rotationPower_sub_le hp hw hk
  have hre : (toComplex (rotationPower p w k) - ((2 ^ p : ℝ) : ℂ) * exp ((k * θ : ℝ) * I)).re =
      ((rotationPower p w k).1 : ℝ) - 2 ^ p * Real.cos (k * θ) := by
    rw [sub_re, re_ofReal_mul, exp_ofReal_mul_I_re]
    rfl
  have him : (toComplex (rotationPower p w k) - ((2 ^ p : ℝ) : ℂ) * exp ((k * θ : ℝ) * I)).im =
      ((rotationPower p w k).2 : ℝ) - 2 ^ p * Real.sin (k * θ) := by
    rw [sub_im, im_ofReal_mul, exp_ofReal_mul_I_im]
    rfl
  exact ⟨hre ▸ (abs_re_le_norm _).trans h, him ▸ (abs_im_le_norm _).trans h⟩

end CAS.Numerics

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The Gamma function at the half-integers below `1/2`

Mathlib proves `Γ(n + 1) = n!` (`Real.Gamma_nat_eq_factorial`) and
`Γ(k + 1/2) = (2k - 1)‼ √π / 2^k` (`Real.Gamma_nat_add_half`). `Gamma_half_sub_nat` adds
`Γ(1/2 - k) = (-2)^k √π / (2k - 1)‼`, so that the value of `Γ` at every integer and every
half-integer is one rewrite by a closed formula.

## Main results

* `CAS.Analysis.SpecialFunctions.Gamma_half_sub_nat`: `Γ(1/2 - k) = (-2)^k √π / (2k - 1)‼`.

## Implementation notes

The formula is classical. We prove it by induction on `k` from `Real.Gamma_one_half_eq`:
the step divides `Real.Gamma_add_one` at `1/2 - (k + 1)` by `1/2 - (k + 1) = -(2k + 1)/2` and
uses `(2k + 1)‼ = (2k + 1) (2k - 1)‼`.

## References

* NIST Digital Library of Mathematical Functions, §5.4 Special Values and Extrema, Version 1.2.8
  (2026-09-15), <https://dlmf.nist.gov/5.4>. `n! = Γ(n + 1)` is (5.4.1) and `Γ(1/2) = √π` is
  (5.4.6).
* NIST Digital Library of Mathematical Functions, §5.5 Functional Relations, Version 1.2.8
  (2026-09-15), <https://dlmf.nist.gov/5.5>. The recurrence `Γ(z + 1) = z Γ(z)` is (5.5.1).
-/

public section

namespace CAS.Analysis.SpecialFunctions

open scoped Nat
open Real

/-- `Γ(1/2 - k) = (-2)^k √π / (2k - 1)‼` for every natural `k`. -/
theorem Gamma_half_sub_nat (k : ℕ) :
    Gamma (1 / 2 - k) = (-2) ^ k * √π / ((2 * k - 1 : ℕ)‼ : ℝ) := by
  induction k with
  | zero => simpa using Gamma_one_half_eq
  | succ k ih =>
    have hs : (1 / 2 - ((k + 1 : ℕ) : ℝ)) ≠ 0 := by
      push_cast
      intro h
      linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    have h := Gamma_add_one hs
    rw [show (1 / 2 - ((k + 1 : ℕ) : ℝ)) + 1 = 1 / 2 - k by push_cast; ring, ih] at h
    have key : Gamma (1 / 2 - ((k + 1 : ℕ) : ℝ)) =
        ((-2) ^ k * √π / ((2 * k - 1 : ℕ)‼ : ℝ)) / (1 / 2 - ((k + 1 : ℕ) : ℝ)) := by
      rw [eq_div_iff hs, mul_comm]
      exact h.symm
    have hd : ((2 * (k + 1) - 1 : ℕ)‼ : ℝ) = (2 * k + 1) * ((2 * k - 1 : ℕ)‼ : ℝ) := by
      rcases k with _ | k
      · simp
      · rw [show 2 * (k + 1 + 1) - 1 = (2 * (k + 1) - 1) + 2 by omega,
          Nat.doubleFactorial_add_two]
        push_cast [show 2 * (k + 1) - 1 + 2 = 2 * k + 3 by omega]
        ring
    have hD : ((2 * k - 1 : ℕ)‼ : ℝ) ≠ 0 := by exact_mod_cast (Nat.doubleFactorial_pos _).ne'
    have h2k : (2 * k + 1 : ℝ) ≠ 0 := by positivity
    have hden : (1 / 2 - ((k + 1 : ℕ) : ℝ)) = -(2 * k + 1) / 2 := by
      push_cast
      ring
    rw [key, hd, hden, pow_succ, div_div, div_eq_div_iff
      (mul_ne_zero hD (div_ne_zero (neg_ne_zero.mpr h2k) two_ne_zero)) (mul_ne_zero h2k hD)]
    ring

end CAS.Analysis.SpecialFunctions

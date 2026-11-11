/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.SquareModels.Basic
public import CAS.Numerics.CenteredTaylorCertificates.Bounds
public import CAS.Numerics.IntervalJets

/-!
# A one-sided Taylor bound

`SquareModel.abs_sub_taylor_le` bounds the error of the Taylor polynomial at `a` by the Lagrange
form of the remainder, for `a ≤ x` and with the ordinary iterated derivatives
`iteratedDeriv k f a` as coefficients. The proof identifies this polynomial with Mathlib's
`taylorWithinEval` on `[a, x]` (`taylorJetEval_eq_taylorWithinEval`) and applies
`taylor_mean_remainder_lagrange_iteratedDeriv`. `SquareModel.ceilNat` rounds a rational up to
a natural number (`SquareModel.le_ceilNat`).

## Main results

* `SquareModel.abs_sub_taylor_le`: for `a ≤ x` the Taylor polynomial at `a` approximates `f x`
  within `R (x - a)^{D+1} / (D+1)!` when `|f^(D+1)| ≤ R` on `[a, x]`.
-/

@[expose] public section

namespace CAS.Numerics

open Finset Set CAS.Continuum
open scoped ContDiff

namespace SquareModel

/-- `⌈q⌉` of a nonnegative rational as a natural number. -/
def ceilNat (q : ℚ) : ℕ := ⌈q⌉.toNat

/-- A rational is at most its natural ceiling `ceilNat q`. -/
theorem le_ceilNat (q : ℚ) : (q : ℝ) ≤ ceilNat q := by
  unfold ceilNat
  rw [Int.ceil_toNat]
  exact_mod_cast Nat.le_ceil q

/-- **One-sided Taylor bound**: for `f` of class `C^{D+1}` and `a ≤ x`, the Taylor polynomial at
`a` approximates `f x` within `R (x - a)^{D+1} / (D+1)!` when `|f^(D+1)| ≤ R` on `[a, x]`. -/
theorem abs_sub_taylor_le {f : ℝ → ℝ} {D : ℕ} (hf : ContDiff ℝ (D + 1) f) {a x R : ℝ}
    (hax : a ≤ x) (hR : ∀ y ∈ Icc a x, |iteratedDeriv (D + 1) f y| ≤ R) :
    |f x - ∑ k ∈ range (D + 1), iteratedDeriv k f a / k.factorial * (x - a) ^ k| ≤
      R * (x - a) ^ (D + 1) / (D + 1).factorial := by
  have hT : ∀ s : Set ℝ, UniqueDiffOn ℝ s → a ∈ s →
      ∑ k ∈ range (D + 1), iteratedDeriv k f a / k.factorial * (x - a) ^ k =
        taylorWithinEval f D s a x := by
    intro s hs ha
    rw [← CAS.Numerics.CenteredTaylorCertificates.taylorJetEval_eq_taylorWithinEval
      (hf.of_le (by norm_cast; omega)) hs ha]
    unfold CAS.Continuum.taylorJetEval CAS.Continuum.taylorCoefficientWithin
    refine sum_congr rfl fun k _ ↦ ?_
    rw [iteratedDerivWithin_univ]
    ring
  rcases eq_or_lt_of_le hax with rfl | hlt
  · rw [hT univ uniqueDiffOn_univ (mem_univ a), taylorWithinEval_self]
    simp
  · rw [hT (uIcc a x) (uniqueDiffOn_uIcc hlt.ne) left_mem_uIcc]
    obtain ⟨z, hz, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hlt.ne hf.contDiffOn
    rw [uIoo_of_le hax] at hz
    have hpow : 0 ≤ (x - a) ^ (D + 1) := pow_nonneg (by linarith) _
    rw [heq, abs_div, abs_mul, abs_of_nonneg hpow, Nat.abs_cast]
    gcongr
    exact hR z (Ioo_subset_Icc_self hz)

end SquareModel

end CAS.Numerics

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.TaylorJet

/-!
# Taylor jets of ordinary derivatives

`taylorJetEval_eq_taylorWithinEval` identifies `taylorJetEval n c` applied to the ordinary
Taylor coefficients `taylorCoefficientWithin f univ c` with Mathlib's `taylorWithinEval f n s c`,
for `f` of class `C^n` and any set `s` with unique derivatives that contains `c`. On such a set
the iterated derivatives within `s` at `c` are the ordinary ones, so remainder bounds that
Mathlib states for `taylorWithinEval` on an interval apply to the jet of ordinary derivatives,
as in `SquareModel.abs_sub_taylor_le`.
-/

@[expose] public noncomputable section

namespace CAS.Numerics.CenteredTaylorCertificates

open CAS.Continuum Set
open scoped BigOperators

/-- Ordinary Taylor coefficients recover the within polynomial on every set with unique
derivatives that contains the center. -/
theorem taylorJetEval_eq_taylorWithinEval {f : ℝ → ℝ} {n : ℕ} {s : Set ℝ} {c : ℝ}
    (hf : ContDiff ℝ n f) (hs : UniqueDiffOn ℝ s) (hc : c ∈ s) (x : ℝ) :
    taylorJetEval n c (taylorCoefficientWithin f univ c) x =
      taylorWithinEval f n s c x := by
  rw [taylor_within_apply]
  unfold taylorJetEval
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [iteratedDerivWithin_eq_iteratedDeriv hs
    (hf.of_le (by exact_mod_cast hk')).contDiffAt hc]
  simp only [taylorCoefficientWithin, iteratedDerivWithin_univ, smul_eq_mul]
  ac_rfl

end CAS.Numerics.CenteredTaylorCertificates

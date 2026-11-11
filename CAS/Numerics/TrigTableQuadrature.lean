/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.SpecialFunctions.Trigonometric.CosineQuadrature
public import CAS.Numerics.TrigTableWords

/-!
# Quadrature weights from the sine and cosine tables

The approximate sine weights `quarterSinWeightApprox N n c` of the quarter-period rule read
`cos (m π / (2 N))` at the table index `m = 2 k n`, and when every `c m` is within `ε` of that
cosine they are within `2 ε / N` of the exact weights
(`abs_quarterSinWeight_sub_quarterSinWeightApprox_le`). The scaled cosines of a stored copy of
`trigTable N p` are within `2 ^ (-p)` (`abs_pairedWordEntry_div_sub_cos_le`), so
`abs_quarterSinWeight_sub_pairedWordEntry_le` bounds the weight error by `2 / (N 2 ^ p)`. The
values of `trigPi N p` give the same bound through `abs_trigPi_div_sub_cos_le`.
-/

@[expose] public section

namespace CAS.Numerics

open CAS.Analysis

/-- The sine weights computed from a stored copy of `trigTable N p` are within `2 / (N 2 ^ p)`
of the exact weights. -/
theorem abs_quarterSinWeight_sub_pairedWordEntry_le {N p : ℕ} (hN : 0 < N)
    {words : Binary64WordTree (2 * (4 * N + 1))}
    (h : ∀ k, pairedWordEntry words k = trigTable N p k) (n : ℕ) :
    |quarterSinWeight N n -
        quarterSinWeightApprox N n (fun m ↦ ((pairedWordEntry words ⟨m % (4 * N), by
          have := Nat.mod_lt m (show 0 < 4 * N by omega); omega⟩).1 : ℝ) / 2 ^ p)| ≤
      2 / (N * 2 ^ p) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  refine (abs_quarterSinWeight_sub_quarterSinWeightApprox_le hN n
    (abs_pairedWordEntry_div_sub_cos_le hN h)).trans_eq ?_
  field_simp

end CAS.Numerics

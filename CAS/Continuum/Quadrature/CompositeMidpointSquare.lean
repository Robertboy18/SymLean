/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.MidpointSquare
public import CAS.Continuum.Quadrature.UniformComposite

/-!
# Composite bounds from squared midpoint samples

Summing the one-panel estimate of `MidpointSquare` over a uniform mesh bounds `∫ f ^ 2` by a
finite sum of squared midpoint values and a bound on the variation within each panel
(`integral_sq_le_of_uniform_midpoint_deviation`). The variation contribution decreases like
the square of the mesh width, and a uniform approximation error contributes over the full
interval.
-/

@[expose] public section

open MeasureTheory Set

namespace CAS.Continuum

/-- Sum the midpoint square estimate over a uniform mesh. The variation bound
is local to each open panel, allowing a different differentiable approximation
on each panel. -/
theorem integral_sq_le_of_uniform_midpoint_deviation
    {g : ℝ → ℝ} {a b M ε α β : ℝ} {N : ℕ}
    (hab : a < b) (hN : 0 < N) (hα : 0 < α) (hβ : 0 < β)
    (hvariation : ∀ i : Fin N,
      ∀ x ∈ Ioo (uniformMeshPoint a b N i) (uniformMeshPoint a b N (i + 1)),
        |g x - g ((uniformMeshPoint a b N i + uniformMeshPoint a b N (i + 1)) / 2)| ≤
          M * |x - (uniformMeshPoint a b N i + uniformMeshPoint a b N (i + 1)) / 2| +
            ε) :
    (∫ x in a..b, g x ^ 2) ≤
      (1 + α) * ((b - a) / N) *
        (∑ i : Fin N,
          g ((uniformMeshPoint a b N i + uniformMeshPoint a b N (i + 1)) / 2) ^ 2) +
        (1 + 1 / α) * (1 + β) * M ^ 2 * (b - a) ^ 3 / (12 * (N : ℝ) ^ 2) +
        (1 + 1 / α) * (1 + 1 / β) * ε ^ 2 * (b - a) := by
  by_cases hg : IntervalIntegrable (fun x ↦ g x ^ 2) volume a b
  swap
  · rw [intervalIntegral.integral_undef hg]
    have hba : 0 < b - a := sub_pos.mpr hab
    positivity
  have hpanel (k : ℕ) (hk : k < N) :
      IntervalIntegrable (fun x ↦ g x ^ 2) volume
        (uniformMeshPoint a b N k) (uniformMeshPoint a b N (k + 1)) := hg.mono_set <| by
    rw [uIcc_of_le (uniformMeshPoint_strictMono hab hN).le, uIcc_of_le hab.le]
    exact Icc_uniformMeshPoint_subset hab.le hk
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hpanel
  rw [Finset.sum_range, uniformMeshPoint_zero, uniformMeshPoint_end a b hN] at hsum
  rw [← hsum]
  refine (Finset.sum_le_sum fun (i : Fin N) _ ↦ integral_sq_le_of_midpoint_deviation
    (uniformMeshPoint_strictMono hab hN).le hα hβ (hpanel i i.isLt) (hvariation i)).trans_eq ?_
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [uniformMeshPoint_succ_sub a b hN, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  field_simp

end CAS.Continuum

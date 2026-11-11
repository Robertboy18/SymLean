/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import CAS.Continuum.Quadrature.Gaussian.Hermite
public import CAS.Continuum.Quadrature.Gaussian.IntegralMeanValue
public import CAS.Continuum.Quadrature.Gaussian.Rolle
public import CAS.Continuum.Quadrature.Gaussian.Weighted

/-!
# The Gaussian remainder

Let `a < b` and let `w` be continuous and strictly positive on `[a, b]`.
For a Gaussian rule `Q` with `n > 0` nodes and a function `f ∈ C^{2n}[a, b]` there is
`ξ ∈ [a, b]` with `∫ f w - Q f = f^(2n)(ξ) / (2n)! * ∫ p_n ^ 2 w`, where `p_n` is the nodal
polynomial. The Hermite interpolant `H` of `f` at the nodes has degree below `2n`, so
`Q f = Q H = ∫ H w`. Subtracting a multiple of `p_n ^ 2` from `f - H` introduces one further
zero, and the generalized Rolle theorem of `Rolle` identifies the multiple with
`f^(2n)(ξ) / (2n)!`. The mean-value principle of `IntegralMeanValue` then integrates the
pointwise identity. The derivative order is `2n` for `n` nodes.

## Implementation notes

Derivatives enter through a derivative chain `F` in the sense of `Rolle`, so only smoothness
on the closed interval `[a, b]` is needed. `GaussianRule.remainder` instantiates the chain
with `iteratedDerivWithin k f (Icc a b)`. The identity is the remainder `γ_n f^(2n)(ξ) / (2n)!`,
`γ_n = ∫ p_n ^ 2 w`, of DLMF (3.5.19) and (3.5.20).

Here `n` is the number of nodes. Stewart's Lecture 23 writes `G_n` with the `n + 1` nodes
`x_0, …, x_n`, so his remainder with `f^(2n+2)` and `p_{n+1}` is this one with `n + 1` in place
of `n`.

## References

* NIST Digital Library of Mathematical Functions, §3.5 Quadrature, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/3.5>. (3.5.19) and (3.5.20) for the remainder.
* Philip J. Davis and Philip Rabinowitz, *Methods of Numerical Integration*, 2nd ed.,
  Academic Press, Orlando, 1984, <https://doi.org/10.1016/C2013-0-10566-1>.
* Helmut Brass and Knut Petras, *Quadrature Theory: The Theory of Numerical Integration on a
  Compact Interval*, Mathematical Surveys and Monographs 178, American Mathematical Society,
  Providence, 2011, <https://doi.org/10.1090/surv/178>.
* G. W. Stewart, *Afternotes on Numerical Analysis*, SIAM, Philadelphia, 1996,
  <https://doi.org/10.1137/1.9781611971491>. Lecture 23, which writes `G_n` with the `n + 1` nodes
  `x_0, …, x_n`.
* Josef Stoer and Roland Bulirsch, *Introduction to Numerical Analysis*, 3rd ed., Texts in Applied
  Mathematics 12, Springer, New York, 2002, <https://doi.org/10.1007/978-0-387-21738-3>. §3.6 for
  the remainder through Hermite interpolation.
-/

@[expose] public section

namespace CAS.Continuum

open Polynomial Set MeasureTheory
open scoped BigOperators

noncomputable section

/-- The `n`th derivative of a monic polynomial of degree `n` is the constant `n!`. -/
theorem iterate_derivative_of_monic (p : ℝ[X]) (hp : p.Monic) (n : ℕ)
    (hdegree : p.natDegree = n) :
    derivative^[n] p = C (n.factorial : ℝ) := by
  ext m
  rw [coeff_iterate_derivative]
  by_cases hm : m = 0
  · subst m
    simp [← hdegree, hp.coeff_natDegree, Nat.descFactorial_self]
  · have hc : p.coeff (m + n) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hc, hm]

/-- Pointwise Hermite remainder for a derivative chain `F` on `[a, b]` and `n` distinct nodes
there. At every `x ∈ [a, b]` some `ξ ∈ [a, b]` satisfies
`F 0 x - H x = F (2n) ξ / (2n)! * P x ^ 2`, with `H` the Hermite interpolant of `F 0`, `F 1`
at the nodes and `P` the nodal polynomial. At a node both sides vanish. Otherwise
`G = F 0 - H - c P ^ 2` with `c = (F 0 x - H x) / P x ^ 2` has double zeros at the nodes and
a zero at `x`, so `exists_derivative_chain_zero_of_double_zeros` gives `ξ` with
`G^(2n) ξ = 0`, and `H^(2n) = 0`, `(P ^ 2)^(2n) = (2n)!` unwind this to the claim. -/
theorem hermite_remainder {a b : ℝ} (hab : a < b) {n : ℕ} (hn : 0 < n)
    (F : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ k < 2 * n, ContinuousOn (F k) (Icc a b))
    (hderiv : ∀ k < 2 * n, ∀ z ∈ Ioo a b, HasDerivAt (F k) (F (k + 1) z) z)
    (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (hmem : ∀ i, nodes i ∈ Icc a b) (x : ℝ) (hx : x ∈ Icc a b) :
    ∃ ξ ∈ Icc a b,
      F 0 x - (hermiteInterpolant nodes (fun i ↦ F 0 (nodes i))
        (fun i ↦ F 1 (nodes i))).eval x =
      F (2 * n) ξ / (2 * n).factorial * (Lagrange.nodal Finset.univ nodes).eval x ^ 2 := by
  let H := hermiteInterpolant nodes (fun i ↦ F 0 (nodes i)) (fun i ↦ F 1 (nodes i))
  let P := Lagrange.nodal Finset.univ nodes
  change ∃ ξ ∈ Icc a b, F 0 x - H.eval x = F (2 * n) ξ / (2 * n).factorial * P.eval x ^ 2
  by_cases hxnode : ∃ i, x = nodes i
  · obtain ⟨i, rfl⟩ := hxnode
    refine ⟨a, ⟨le_rfl, hab.le⟩, ?_⟩
    simp [H, P, hermiteInterpolant_eval nodes hnodes,
      Lagrange.eval_nodal_at_node (Finset.mem_univ i)]
  · have hxne : ∀ i, x ≠ nodes i := by simpa using hxnode
    have hpne : P.eval x ≠ 0 :=
      Lagrange.eval_nodal_not_at_node (fun i _ ↦ hxne i)
    let c := (F 0 x - H.eval x) / P.eval x ^ 2
    let G := fun k y ↦ F k y - (derivative^[k] H).eval y -
      c * (derivative^[k] (P ^ 2)).eval y
    have hc : c * P.eval x ^ 2 = F 0 x - H.eval x := div_mul_cancel₀ _ (pow_ne_zero _ hpne)
    have hgcontinuous (k : ℕ) (hk : k < 2 * n) : ContinuousOn (G k) (Icc a b) :=
      ((hcontinuous k hk).sub (derivative^[k] H).continuous.continuousOn).sub
        (continuousOn_const.mul (derivative^[k] (P ^ 2)).continuous.continuousOn)
    have hgderiv (k : ℕ) (hk : k < 2 * n) (z : ℝ) (hz : z ∈ Ioo a b) :
        HasDerivAt (G k) (G (k + 1) z) z := by
      convert
        ((hderiv k hk z hz).sub ((derivative^[k] H).hasDerivAt z)).sub
          (((derivative^[k] (P ^ 2)).hasDerivAt z).const_mul c) using 1
      simp only [G, Function.iterate_succ_apply']
    have hgzero (i : Fin n) : G 0 (nodes i) = 0 ∧ G 1 (nodes i) = 0 := by
      have hp : P.eval (nodes i) = 0 := Lagrange.eval_nodal_at_node (Finset.mem_univ i)
      exact ⟨by simp [G, H, hp, hermiteInterpolant_eval nodes hnodes],
        by simp [G, H, hp, hermiteInterpolant_derivative_eval nodes hnodes, derivative_pow]⟩
    have hgx : G 0 x = 0 := by
      simpa only [G, Function.iterate_zero_apply, eval_pow] using sub_eq_zero.mpr hc.symm
    obtain ⟨ξ, hξ, hgξ⟩ := exists_derivative_chain_zero_of_double_zeros n G
      hgcontinuous hgderiv nodes hnodes hmem hgzero x hx hxne hgx
    have hH : derivative^[2 * n] H = 0 :=
      iterate_derivative_eq_zero (hermiteInterpolant_natDegree_lt hn nodes _ _)
    have hP : derivative^[2 * n] (P ^ 2) = C ((2 * n).factorial : ℝ) :=
      iterate_derivative_of_monic _ (Lagrange.nodal_monic.pow _) _
        (by simp [natDegree_pow, Lagrange.natDegree_nodal])
    have hceq : c = F (2 * n) ξ / (2 * n).factorial := by
      simp only [G, hH, hP, eval_zero, sub_zero, eval_C] at hgξ
      exact (eq_div_iff (by positivity)).mpr (by linarith)
    exact ⟨ξ, hξ, by rw [← hceq, hc]⟩

/-- A `C^m` function on `[a, b]` yields a derivative chain: `iteratedDerivWithin k f (Icc a b)`
is continuous on `[a, b]` for `k ≤ m` and has the next iterated derivative as its derivative
on `(a, b)` for `k < m`. -/
theorem derivative_chain_within {a b : ℝ} (hab : a < b) {m : ℕ}
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ m f (Icc a b)) :
    (∀ k ≤ m, ContinuousOn (iteratedDerivWithin k f (Icc a b)) (Icc a b)) ∧
    (∀ k < m, ∀ z ∈ Ioo a b,
      HasDerivAt (iteratedDerivWithin k f (Icc a b))
        (iteratedDerivWithin (k + 1) f (Icc a b) z) z) := by
  have hu := uniqueDiffOn_Icc hab
  refine ⟨fun k hk ↦ hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hk) hu,
    fun k hk z hz ↦ ?_⟩
  rw [iteratedDerivWithin_succ]
  exact (hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk) hu
    z ⟨hz.1.le, hz.2.le⟩).hasDerivWithinAt.hasDerivAt (Icc_mem_nhds hz.1 hz.2)

/-- Integrated Gaussian remainder for a derivative chain `F` of length `2n`: there is
`ξ ∈ [a, b]` with `∫ F 0 w - Q (F 0) = F (2n) ξ / (2n)! * ∫ P ^ 2 w`, `P` the nodal
polynomial. Exactness gives `Q (F 0) = Q H = ∫ H w`, and `hermite_remainder` together with
`integral_eq_value_mul_of_pointwise_image` handles `∫ (F 0 - H) w`. -/
theorem GaussianRule.remainder_of_derivative_chain {a b : ℝ} (hab : a < b)
    {w : ℝ → ℝ} {hw : ContinuousOn w (uIcc a b)}
    (hwpos : ∀ x ∈ Icc a b, 0 < w x) {n : ℕ} (hn : 0 < n)
    (rule : GaussianRule a b w hw n) (F : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ k ≤ 2 * n, ContinuousOn (F k) (Icc a b))
    (hderiv : ∀ k < 2 * n, ∀ z ∈ Ioo a b, HasDerivAt (F k) (F (k + 1) z) z) :
    ∃ ξ ∈ Icc a b,
      (∫ x in a..b, F 0 x * w x) - rule.value (F 0) =
      F (2 * n) ξ / (2 * n).factorial *
        polynomialIntegral a b w hw ((Lagrange.nodal Finset.univ rule.nodes) ^ 2) := by
  let H := hermiteInterpolant rule.nodes (fun i ↦ F 0 (rule.nodes i))
    (fun i ↦ F 1 (rule.nodes i))
  let P := Lagrange.nodal Finset.univ rule.nodes
  let r := fun x ↦ (F 0 x - H.eval x) * w x
  let φ := fun x ↦ P.eval x ^ 2 * w x / (2 * n).factorial
  have hw' : ContinuousOn w (Icc a b) := by simpa [uIcc_of_le hab.le] using hw
  have hF := hcontinuous 0 (by omega)
  have hFint : IntervalIntegrable (fun x ↦ F 0 x * w x) volume a b :=
    (hF.mul hw').intervalIntegrable_of_Icc hab.le
  have hHint : IntervalIntegrable (fun x ↦ H.eval x * w x) volume a b :=
    (H.continuous.continuousOn.mul hw').intervalIntegrable_of_Icc hab.le
  have hr : IntervalIntegrable r volume a b :=
    ((hF.sub H.continuous.continuousOn).mul hw').intervalIntegrable_of_Icc hab.le
  have hφ : IntervalIntegrable φ volume a b :=
    (((P.continuous.continuousOn.pow 2).mul hw').div_const _).intervalIntegrable_of_Icc hab.le
  have hφnonneg (x : ℝ) (hx : x ∈ Icc a b) : 0 ≤ φ x :=
    div_nonneg (mul_nonneg (sq_nonneg _) (hwpos x hx).le) (by positivity)
  have hφeq : (∫ x in a..b, φ x) =
      polynomialIntegral a b w hw (P ^ 2) / (2 * n).factorial := by
    simp [φ, polynomialIntegral, intervalIntegral.integral_div]
  have hφpos : 0 < ∫ x in a..b, φ x := by
    rw [hφeq]
    exact div_pos (polynomialIntegral_square_pos hab w hw hwpos P Lagrange.nodal_ne_zero)
      (by positivity)
  have himage (x : ℝ) (hx : x ∈ Icc a b) :
      ∃ y ∈ Icc a b, r x = F (2 * n) y * φ x := by
    obtain ⟨y, hy, heq⟩ := hermite_remainder hab hn F
      (fun k hk ↦ hcontinuous k hk.le) hderiv rule.nodes rule.injective
      (fun i ↦ ⟨(rule.interior i).1.le, (rule.interior i).2.le⟩) x hx
    refine ⟨y, hy, ?_⟩
    change (F 0 x - H.eval x) * w x = _
    rw [heq]
    dsimp [φ, P]
    ring
  obtain ⟨ξ, hξ, heq⟩ := integral_eq_value_mul_of_pointwise_image hab hr hφ
    (hcontinuous _ le_rfl) hφnonneg hφpos himage
  have hvalue : rule.value (F 0) = polynomialIntegral a b w hw H := by
    refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans
      (rule.exact H (hermiteInterpolant_natDegree_lt hn rule.nodes _ _))
    rw [show H.eval (rule.nodes i) = F 0 (rule.nodes i) from
      hermiteInterpolant_eval rule.nodes rule.injective _ _ i]
  have hreq : (∫ x in a..b, r x) = (∫ x in a..b, F 0 x * w x) - rule.value (F 0) := by
    rw [hvalue]
    simp only [r, sub_mul, intervalIntegral.integral_sub hFint hHint]
    rfl
  rw [hreq, hφeq] at heq
  exact ⟨ξ, hξ, by rw [heq]; ring⟩

/-- The Gaussian error formula: for `f ∈ C^{2n}[a, b]` there is `ξ ∈ [a, b]` with
`∫ f w - Q f = f^(2n)(ξ) / (2n)! * ∫ P ^ 2 w`, where `f^(2n)` is
`iteratedDerivWithin (2n) f (Icc a b)` and `P` the nodal polynomial. Only smoothness on the
closed interval is needed. -/
theorem GaussianRule.remainder {a b : ℝ}
    {w : ℝ → ℝ} {hw : ContinuousOn w (uIcc a b)}
    (hwpos : ∀ x ∈ Icc a b, 0 < w x) {n : ℕ} (hn : 0 < n)
    (rule : GaussianRule a b w hw n) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (2 * n) f (Icc a b)) :
    ∃ ξ ∈ Icc a b,
      (∫ x in a..b, f x * w x) - rule.value f =
      iteratedDerivWithin (2 * n) f (Icc a b) ξ / (2 * n).factorial *
        polynomialIntegral a b w hw ((Lagrange.nodal Finset.univ rule.nodes) ^ 2) := by
  have hab : a < b := (rule.interior ⟨0, hn⟩).1.trans (rule.interior ⟨0, hn⟩).2
  obtain ⟨hc, hd⟩ := derivative_chain_within hab hf
  simpa only [iteratedDerivWithin_zero] using
    rule.remainder_of_derivative_chain hab hwpos hn
      (fun k ↦ iteratedDerivWithin k f (Icc a b)) hc hd

/-- If `|f^(2n)| ≤ M` on `[a, b]` then `|∫ f w - Q f| ≤ M / (2n)! * ∫ P ^ 2 w`, immediately
from `remainder`. -/
theorem GaussianRule.abs_error_le {a b : ℝ} (hab : a < b)
    {w : ℝ → ℝ} {hw : ContinuousOn w (uIcc a b)}
    (hwpos : ∀ x ∈ Icc a b, 0 < w x) {n : ℕ} (hn : 0 < n)
    (rule : GaussianRule a b w hw n) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (2 * n) f (Icc a b)) {M : ℝ}
    (hM : ∀ x ∈ Icc a b, |iteratedDerivWithin (2 * n) f (Icc a b) x| ≤ M) :
    |(∫ x in a..b, f x * w x) - rule.value f| ≤
      M / (2 * n).factorial *
        polynomialIntegral a b w hw ((Lagrange.nodal Finset.univ rule.nodes) ^ 2) := by
  obtain ⟨ξ, hξ, heq⟩ := rule.remainder hwpos hn hf
  have hfactorial : (0 : ℝ) < (2 * n).factorial := by positivity
  have hmass := polynomialIntegral_square_pos hab w hw hwpos
    (Lagrange.nodal Finset.univ rule.nodes) Lagrange.nodal_ne_zero
  rw [heq, abs_mul, abs_div, abs_of_pos hfactorial, abs_of_pos hmass]
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (hM ξ hξ) hfactorial.le) hmass.le

end
end CAS.Continuum

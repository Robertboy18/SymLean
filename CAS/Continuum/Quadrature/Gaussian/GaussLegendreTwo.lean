/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.Gaussian.Nodal
public import CAS.Continuum.Quadrature.GaussLegendrePeano

/-!
# The two-point Gauss-Legendre rule is the Gaussian rule for the unit weight

The normalized rule `gaussLegendreTwoRule`, weights `1/2` at `(3 ∓ √3)/6`, transported to
`[a,b]`, is a `GaussianRule a b 1 _ 2`.  Conversely every Gaussian rule with two nodes for the
unit weight has the nodes `gaussLegendreTwoLeftPoint a b`, `gaussLegendreTwoRightPoint a b`
and the weights `(b - a)/2`.  The proof compares nodal
polynomials: both are the monic orthogonal polynomial of degree two for Lebesgue measure on
`[a,b]`, so the node sets agree, and exactness on `1` and `x` then fixes the weights.

## Main results

* `gaussLegendreTwoGaussianRule`: the transported two-point rule as a `GaussianRule`.
* `GaussianRule.nodes_eq_gaussLegendreTwo`, `GaussianRule.weights_eq_gaussLegendreTwo`: the
  nodes and weights of any two-node Gaussian rule for the unit weight.
* `GaussianRule.value_eq_gaussLegendreTwoRule_valueOn`: its value is
  `gaussLegendreTwoRule.valueOn`.

## References

* Carl Friedrich Gauss, "Methodus nova integralium valores per approximationem inveniendi",
  *Commentationes Societatis Regiae Scientiarum Gottingensis Recentiores* 3 (1816), pp. 39-76,
  <https://archive.org/details/bub_gb_J6S9H_VYVn4C>.
* Philip J. Davis and Philip Rabinowitz, *Methods of Numerical Integration*, 2nd ed.,
  Academic Press, Orlando, 1984, <https://doi.org/10.1016/C2013-0-10566-1>.
-/

@[expose] public section

open MeasureTheory Set Polynomial

namespace CAS.Continuum

private theorem gaussLegendreTwoLeftNode_pos : 0 < gaussLegendreTwoLeftNode := by
  unfold gaussLegendreTwoLeftNode
  nlinarith [sqrt_three_sq, Real.sqrt_nonneg 3]

private theorem gaussLegendreTwoRightNode_lt_one : gaussLegendreTwoRightNode < 1 := by
  unfold gaussLegendreTwoRightNode
  nlinarith [sqrt_three_sq, Real.sqrt_nonneg 3]

variable {a b : ℝ} {hw : ContinuousOn (fun _ : ℝ ↦ (1 : ℝ)) (uIcc a b)}

/-- The two-point Gauss-Legendre rule transported to `[a,b]`, as a Gaussian rule for the unit
weight. -/
noncomputable def gaussLegendreTwoGaussianRule (hab : a < b) :
    GaussianRule a b (fun _ ↦ 1) hw 2 where
  nodes := ![gaussLegendreTwoLeftPoint a b, gaussLegendreTwoRightPoint a b]
  weights := ![(b - a) / 2, (b - a) / 2]
  injective := by
    have hne := (gaussLegendreTwoLeftPoint_lt_rightPoint hab).ne
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  interior := by
    have hba : 0 < b - a := sub_pos.mpr hab
    have hL := gaussLegendreTwoLeftNode_pos
    have hR := gaussLegendreTwoRightNode_lt_one
    have hLR := gaussLegendreTwoLeftPoint_lt_rightPoint hab
    intro i
    fin_cases i <;> simp only [gaussLegendreTwoLeftPoint, gaussLegendreTwoRightPoint] at hLR ⊢ <;>
      constructor <;> simp <;> nlinarith
  positive := by
    have hba : 0 < b - a := sub_pos.mpr hab
    intro i
    fin_cases i <;> simp [hba]
  exact := by
    intro p hp
    have h := QuadratureRule.valueOn_eq_integral_of_natDegree_le
      gaussLegendreTwoRule.exactUpTo_three p (by omega) a b
    rw [gaussLegendreTwoRule_valueOn_eq_formula] at h
    simp only [Fin.sum_univ_two, polynomialIntegral_apply, mul_one, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    linear_combination h

namespace GaussianRule

private theorem nodal_eval_fin_two (v : Fin 2 → ℝ) (t : ℝ) :
    (Lagrange.nodal Finset.univ v).eval t = (t - v 0) * (t - v 1) := by
  simp [Lagrange.nodal, Fin.prod_univ_two]

/-- Every node of a two-node Gaussian rule for the unit weight on `[a,b]` is one of the two
Gauss-Legendre points `a + (3 ∓ √3)(b - a)/6`. -/
theorem nodes_eq_gaussLegendreTwo (rule : GaussianRule a b (fun _ ↦ 1) hw 2) (i : Fin 2) :
    rule.nodes i = gaussLegendreTwoLeftPoint a b ∨
      rule.nodes i = gaussLegendreTwoRightPoint a b := by
  have hab : a < b := (rule.interior 0).1.trans (rule.interior 0).2
  have hwpos : ∀ x ∈ Icc a b, 0 < (fun _ : ℝ ↦ (1 : ℝ)) x := fun _ _ ↦ one_pos
  have h := (rule.nodal_eq_integralOrthogonalPolynomial hab hwpos).trans
    ((gaussLegendreTwoGaussianRule (hw := hw) hab).nodal_eq_integralOrthogonalPolynomial
      hab hwpos).symm
  have he := congrArg (eval (rule.nodes i)) h
  rw [Lagrange.eval_nodal_at_node (Finset.mem_univ i), nodal_eval_fin_two] at he
  simp only [gaussLegendreTwoGaussianRule, Matrix.cons_val_zero, Matrix.cons_val_one] at he
  exact (mul_eq_zero.mp he.symm).imp sub_eq_zero.mp sub_eq_zero.mp

/-- The two nodes of a two-node Gaussian rule for the unit weight sum to `a + b`. -/
private theorem nodes_add (rule : GaussianRule a b (fun _ ↦ 1) hw 2) :
    rule.nodes 0 + rule.nodes 1 = a + b := by
  have hne : rule.nodes 0 ≠ rule.nodes 1 := rule.injective.ne (by decide)
  have hsum : gaussLegendreTwoLeftPoint a b + gaussLegendreTwoRightPoint a b = a + b := by
    unfold gaussLegendreTwoLeftPoint gaussLegendreTwoRightPoint gaussLegendreTwoLeftNode
      gaussLegendreTwoRightNode
    ring
  rcases rule.nodes_eq_gaussLegendreTwo 0 with h0 | h0 <;>
    rcases rule.nodes_eq_gaussLegendreTwo 1 with h1 | h1
  · exact absurd (h0.trans h1.symm) hne
  · rw [h0, h1, hsum]
  · rw [h0, h1, add_comm, hsum]
  · exact absurd (h0.trans h1.symm) hne

/-- Every weight of a two-node Gaussian rule for the unit weight on `[a,b]` is `(b - a)/2`. -/
theorem weights_eq_gaussLegendreTwo (rule : GaussianRule a b (fun _ ↦ 1) hw 2) (i : Fin 2) :
    rule.weights i = (b - a) / 2 := by
  have hne : rule.nodes 0 - rule.nodes 1 ≠ 0 := sub_ne_zero.mpr (rule.injective.ne (by decide))
  have hsum := rule.nodes_add
  have h0 := rule.exact 1 (by simp)
  have h1 := rule.exact X (by simp)
  simp only [polynomialIntegral_apply, eval_one, eval_X, mul_one, Fin.sum_univ_two,
    intervalIntegral.integral_const, smul_eq_mul, integral_id] at h0 h1
  have hw0 : rule.weights 0 = (b - a) / 2 := by
    apply mul_right_cancel₀ hne
    linear_combination h1 - rule.nodes 1 * h0 - (b - a) / 2 * hsum
  revert i
  exact Fin.forall_fin_two.mpr ⟨hw0, by linarith⟩

/-- A two-node Gaussian rule for the unit weight on `[a,b]` is the transported two-point
Gauss-Legendre rule. -/
theorem value_eq_gaussLegendreTwoRule_valueOn (rule : GaussianRule a b (fun _ ↦ 1) hw 2)
    (f : ℝ → ℝ) :
    rule.value f = gaussLegendreTwoRule.valueOn f a b := by
  have hne : rule.nodes 0 ≠ rule.nodes 1 := rule.injective.ne (by decide)
  rw [gaussLegendreTwoRule_valueOn_eq_formula, value, Fin.sum_univ_two,
    rule.weights_eq_gaussLegendreTwo, rule.weights_eq_gaussLegendreTwo, ← mul_add]
  rcases rule.nodes_eq_gaussLegendreTwo 0 with h0 | h0 <;>
    rcases rule.nodes_eq_gaussLegendreTwo 1 with h1 | h1
  · exact absurd (h0.trans h1.symm) hne
  · rw [h0, h1]
  · rw [h0, h1, add_comm]
  · exact absurd (h0.trans h1.symm) hne

end GaussianRule

end CAS.Continuum

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.Rule

/-!
# Quadrature stability under uniform approximation

Two facts that numerical quadrature often conflates are kept apart:

* a rule may integrate a model function exactly;
* evaluating the rule on a function within `eps` of the model perturbs the
  sampled value by at most `eps` times a stability constant of the rule, and
  by `|b-a|` times that on the interval `a..b`.

For an ordered normalized rule with weights `wᵢ`, the stability constant is
`∑ i, |wᵢ|`.  The result is independent of the concrete rule and of any
floating-point backend.  It feeds directly into `QuadratureCert`: analytic
model error is proved over the whole interval, while sample-value error is
controlled by the same approximation certificate at the rule's nodes
(`QuadratureRule.abs_valueOn_sub_le`, `QuadratureRule.certOfApproxEvaluated`).
-/

@[expose] public section

open MeasureTheory

namespace CAS.Continuum

open CAS.Certificate

namespace QuadratureRule

/-- Sum of the absolute values of a normalized rule's weights. -/
def weightVariation (rule : QuadratureRule) : ℝ :=
  (rule.terms.map fun term ↦ |term.1|).sum

private theorem abs_weightedDifference_le
    (terms : List (ℝ × ℝ))
    (f g : ℝ → ℝ) (eps : ℝ)
    (hnodes : ∀ term ∈ terms, term.2 ∈ Set.Icc (0 : ℝ) 1)
    (happrox : ApproxOn f g (Set.Icc (0 : ℝ) 1) eps) :
    |(terms.map fun term ↦ term.1 * f term.2).sum -
        (terms.map fun term ↦ term.1 * g term.2).sum| ≤
      (terms.map fun term ↦ |term.1|).sum * eps := by
  induction terms with
  | nil => simp
  | cons term terms ih =>
      have hpoint : |f term.2 - g term.2| ≤ eps := by
        simpa [Real.norm_eq_abs] using happrox term.2 (hnodes term (by simp))
      simp only [List.map_cons, List.sum_cons]
      rw [add_sub_add_comm, ← mul_sub, add_mul]
      exact (abs_add_le _ _).trans (add_le_add
        ((abs_mul _ _).trans_le (mul_le_mul_of_nonneg_left hpoint (abs_nonneg _)))
        (ih fun tail htail ↦ hnodes tail (by simp [htail])))

/--
Uniform approximation on `[0,1]` controls the difference between normalized
rule values by `weightVariation * eps`.
-/
theorem abs_normalizedValue_sub_le
    (rule : QuadratureRule) {f g : ℝ → ℝ} {eps : ℝ}
    (happrox : ApproxOn f g (Set.Icc (0 : ℝ) 1) eps) :
    |rule.normalizedValue f - rule.normalizedValue g| ≤
      rule.weightVariation * eps := by
  unfold normalizedValue weightedSum weightVariation
  simp only [List.map_map]
  exact abs_weightedDifference_le rule.terms f g eps
    rule.nodes_mem_unit happrox

private theorem affine_mem_uIcc
    {a b x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    a + x * (b - a) ∈ Set.uIcc a b :=
  (convex_uIcc a b).add_smul_sub_mem Set.left_mem_uIcc Set.right_mem_uIcc hx

/--
On an arbitrary oriented interval, perturbing the integrand uniformly by
`eps` perturbs the transported rule value by at most
`|b-a| * weightVariation * eps`.
-/
theorem abs_valueOn_sub_le
    (rule : QuadratureRule) {f g : ℝ → ℝ} {a b eps : ℝ}
    (happrox : ApproxOn f g (Set.uIcc a b) eps) :
    |rule.valueOn f a b - rule.valueOn g a b| ≤
      |b - a| * (rule.weightVariation * eps) := by
  rw [rule.valueOn_eq_smul_normalizedValue, rule.valueOn_eq_smul_normalizedValue, smul_eq_mul,
    smul_eq_mul, ← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (rule.abs_normalizedValue_sub_le fun x hx ↦ happrox _ (affine_mem_uIcc hx)) (abs_nonneg _)

/--
Evaluate a quadrature rule on the original integrand while using an exactly
integrated nearby model to prove the analytic error.

The first error term controls the difference of the two interval integrals.
The second controls the difference between rule evaluations at their sampled
nodes. A backend may then replace this exact-real sampled value with the
midpoint of an enclosing interval through `QuadratureCert.replaceValue` (or
`QuadratureCert.replaceValueOfInterval` in `Core`).
-/
noncomputable def certOfApproxEvaluated
    (rule : QuadratureRule)
    {a b : ℝ}
    (approx : ApproxCert ℝ ℝ (Set.uIcc a b))
    (hexact : rule.ExactFor fun x ↦ approx.rhs (a + x * (b - a)))
    (hlhs : IntervalIntegrable approx.lhs volume a b)
    (hrhs : IntervalIntegrable approx.rhs volume a b) :
    QuadratureCert approx.lhs a b :=
  (rule.certOfApprox approx hexact hlhs hrhs).replaceValue
    (rule.valueOn approx.lhs a b)
    (|b - a| * (rule.weightVariation * approx.eps))
    (by
      change ‖rule.valueOn approx.rhs a b -
        rule.valueOn approx.lhs a b‖ ≤
          |b - a| * (rule.weightVariation * approx.eps)
      have hvalue := rule.abs_valueOn_sub_le approx.sound
      rw [abs_sub_comm] at hvalue
      simpa [Real.norm_eq_abs] using hvalue)

end QuadratureRule
end CAS.Continuum

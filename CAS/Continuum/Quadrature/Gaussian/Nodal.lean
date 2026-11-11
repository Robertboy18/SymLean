/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.Gaussian.Characterization
public import CAS.Continuum.Quadrature.Gaussian.Remainder
public import CAS.Continuum.Quadrature.PositiveRule

/-!
# Gaussian rules as nodal rules

For `n > 0`, a `GaussianRule a b w hw n` is a positive `NodalRule` with nodes in `(a,b)` and
degree of exactness at least `2n - 1` for the weight `w`. The empty `GaussianRule` has no
exactness condition and does not in general integrate constants. For positive node counts
the dictionary (`GaussianRule.toNodalRule`) has two consequences.

* Gaussian quadrature exists in the language of nodal rules: for a continuous positive weight
  on `[a,b]` and `n ≥ 1` there is a positive rule with `n` nodes in `(a,b)` exact to degree
  `2n - 1` (`exists_nodalRule_gaussian`).
* Any sequence of Gaussian rules with `n + 1` nodes converges on continuous integrands.  This
  is the Pólya-Steklov theorem `NodalRule.tendsto_eval_of_positive` applied to Gaussian rules,
  so no positivity of `w` beyond continuity is used once the rules are given
  (`GaussianRule.tendsto_value`). For a positive weight the rules `gaussianRule` exist, and
  they converge (`gaussian_rules_converge`).

The remainder formula is also restated with the monic orthogonal polynomial in place of the
nodal polynomial (`GaussianRule.remainder_orthogonal`).

## Implementation notes

`GaussianRule.toNodalRule` keeps what the theory of positive rules needs: the nodes, the
positive weights and exactness to degree `2n - 1`. Convergence is then the Pólya-Steklov
theorem `NodalRule.tendsto_eval_of_positive` of `PositiveRule`, which rests on Weierstrass
approximation, and uses no further property of Gaussian rules. Stieltjes's proof for the
weight `1` on `[-1, 1]` compares the rule with Riemann sums instead.

## References

* Carl Friedrich Gauss, "Methodus nova integralium valores per approximationem inveniendi",
  *Commentationes Societatis Regiae Scientiarum Gottingensis Recentiores* 3 (1816), pp. 39-76,
  <https://archive.org/details/bub_gb_J6S9H_VYVn4C>.
* Elwin Bruno Christoffel, "Über die Gaußische Quadratur und eine Verallgemeinerung
  derselben", *Journal für die reine und angewandte Mathematik* 55 (1858), pp. 61-82,
  <https://doi.org/10.1515/crll.1858.55.61>.
* Thomas Jan Stieltjes, "Quelques recherches sur la théorie des quadratures dites mécaniques",
  *Annales scientifiques de l'École Normale Supérieure* (3) 1 (1884), pp. 409-426,
  <https://doi.org/10.24033/asens.245>. §6 for the convergence of the Gauss rule for the
  weight `1` on `[-1, 1]`.
* George Pólya, "Über die Konvergenz von Quadraturverfahren", *Mathematische Zeitschrift* 37
  (1933), pp. 264-286, <https://doi.org/10.1007/BF01474574>. Satz I for convergence on
  continuous functions.
* Gábor Szegő, *Orthogonal Polynomials*, 4th ed., Colloquium Publications 23, American
  Mathematical Society, Providence, 1975, <https://doi.org/10.1090/coll/023>.
* G. W. Stewart, *Afternotes on Numerical Analysis*, SIAM, Philadelphia, 1996,
  <https://doi.org/10.1137/1.9781611971491>. Lecture 23, which writes `G_n` with the `n + 1` nodes
  `x_0, …, x_n`.
-/

@[expose] public section

open MeasureTheory Set Polynomial Filter Topology

namespace CAS.Continuum

/-- `polynomialIntegral a b w hw p` is the integral `∫ₐᵇ p(x) w(x) dx`. -/
@[simp]
theorem polynomialIntegral_apply (a b : ℝ) (w : ℝ → ℝ) (hw : ContinuousOn w (uIcc a b))
    (p : ℝ[X]) : polynomialIntegral a b w hw p = ∫ x in a..b, p.eval x * w x :=
  rfl

namespace GaussianRule

variable {a b : ℝ} {w : ℝ → ℝ} {hw : ContinuousOn w (uIcc a b)} {n : ℕ}

/-- A Gaussian rule as a nodal rule. -/
def toNodalRule (rule : GaussianRule a b w hw n) : NodalRule where
  size := n
  node := rule.nodes
  weight := rule.weights

/-- The nodal form of a Gaussian rule evaluates `f` to the rule's value `rule.value f`. -/
@[simp]
theorem toNodalRule_eval (rule : GaussianRule a b w hw n) (f : ℝ → ℝ) :
    rule.toNodalRule.eval f = rule.value f :=
  rfl

/-- The nodal form of a Gaussian rule is positive. -/
theorem toNodalRule_positive (rule : GaussianRule a b w hw n) : rule.toNodalRule.Positive :=
  fun i ↦ (rule.positive i).le

/-- The nodes of a Gaussian rule lie in the open interval `(a,b)`. -/
theorem toNodalRule_nodesIn (rule : GaussianRule a b w hw n) :
    rule.toNodalRule.NodesIn (Ioo a b) :=
  rule.interior

/-- The nodes of a Gaussian rule lie in `[a,b]`. -/
theorem toNodalRule_nodesIn_Icc (rule : GaussianRule a b w hw n) :
    rule.toNodalRule.NodesIn (Icc a b) :=
  fun i ↦ Ioo_subset_Icc_self (rule.interior i)

/-- A Gaussian rule with `n ≥ 1` nodes has degree of exactness `2n - 1` for `w`. -/
theorem toNodalRule_exactToDegree (rule : GaussianRule a b w hw n) (hn : 0 < n) :
    rule.toNodalRule.ExactToDegree a b w (2 * n - 1) :=
  fun p hp ↦ rule.exact p (by omega)

end GaussianRule

/-- **Gaussian quadrature.**  For a continuous positive weight `w` on `[a,b]`, `a < b`, and
`n ≥ 1`, there is a positive rule with `n` nodes, all in `(a,b)`, that integrates every
polynomial of degree at most `2n - 1` exactly against `w`. -/
theorem exists_nodalRule_gaussian {a b : ℝ} (hab : a < b) {w : ℝ → ℝ}
    (hw : ContinuousOn w (uIcc a b)) (hwpos : ∀ x ∈ Icc a b, 0 < w x) {n : ℕ} (hn : 0 < n) :
    ∃ Q : NodalRule, Q.size = n ∧ Q.Positive ∧ Q.NodesIn (Ioo a b) ∧
      Q.ExactToDegree a b w (2 * n - 1) :=
  let rule := gaussianRule hab w hw hwpos n hn
  ⟨rule.toNodalRule, rfl, rule.toNodalRule_positive, rule.toNodalRule_nodesIn,
    rule.toNodalRule_exactToDegree hn⟩

namespace GaussianRule

variable {a b : ℝ} {w : ℝ → ℝ} {hw : ContinuousOn w (uIcc a b)}

/-- Every sequence of Gaussian rules with `n + 1` nodes for a continuous weight on `[a,b]`
converges to `∫ₐᵇ f w` for continuous `f`. -/
theorem tendsto_value (hab : a ≤ b) (rules : ∀ n : ℕ, GaussianRule a b w hw (n + 1))
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n ↦ (rules n).value f) atTop (𝓝 (∫ x in a..b, f x * w x)) := by
  have hwIcc : ContinuousOn w (Icc a b) := by simpa [uIcc_of_le hab] using hw
  have hdeg : Tendsto (fun n : ℕ ↦ 2 * (n + 1) - 1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ show n ≤ 2 * (n + 1) - 1 by omega) tendsto_id
  exact NodalRule.tendsto_eval_of_positive (Q := fun n ↦ (rules n).toNodalRule) hab hwIcc
    (fun n ↦ (rules n).toNodalRule_positive) (fun n ↦ (rules n).toNodalRule_nodesIn_Icc)
    (fun n ↦ (rules n).toNodalRule_exactToDegree (Nat.succ_pos n)) hdeg hf

/-- The Gaussian remainder with the monic orthogonal polynomial `pₙ` of `w`: for
`f ∈ C^{2n}[a,b]` there is `ξ ∈ [a,b]` with
`∫ f w - Q f = f^(2n)(ξ) / (2n)! * ∫ pₙ² w`. -/
theorem remainder_orthogonal (hab : a < b) (hwpos : ∀ x ∈ Icc a b, 0 < w x) {n : ℕ}
    (hn : 0 < n) (rule : GaussianRule a b w hw n) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (2 * n) f (Icc a b)) :
    ∃ ξ ∈ Icc a b,
      (∫ x in a..b, f x * w x) - rule.value f =
      iteratedDerivWithin (2 * n) f (Icc a b) ξ / (2 * n).factorial *
        polynomialIntegral a b w hw (integralOrthogonalPolynomial a b hab w hw hwpos n ^ 2) := by
  rw [← rule.nodal_eq_integralOrthogonalPolynomial hab hwpos]
  exact rule.remainder hwpos hn hf

end GaussianRule

/-- For continuous `f` and a continuous strictly positive weight on `[a, b]`, the Gaussian
rules with `n + 1` nodes converge to `∫ f w` as `n → ∞`. -/
theorem gaussian_rules_converge {a b : ℝ} (hab : a < b) (w : ℝ → ℝ)
    (hw : ContinuousOn w (uIcc a b)) (hwpos : ∀ x ∈ Icc a b, 0 < w x)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    Tendsto
      (fun n ↦ (gaussianRule hab w hw hwpos (n + 1) (by omega)).value f)
      atTop (𝓝 (∫ x in a..b, f x * w x)) :=
  GaussianRule.tendsto_value hab.le (fun n ↦ gaussianRule hab w hw hwpos (n + 1) (by omega)) hf

end CAS.Continuum

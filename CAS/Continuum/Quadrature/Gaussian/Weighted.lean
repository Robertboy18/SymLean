/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Topology.ContinuousMap.Weierstrass
public import CAS.Continuum.Quadrature.Gaussian.Gaussian

/-!
# Weighted Gaussian rules

`GaussianRule a b w hw n` packages `n` nodes and weights with the facts that the nodes are
distinct and lie in `(a, b)`, the weights are positive, and the rule is exact against `w`
for polynomials with `natDegree < 2n`. For `n > 0` this is exactness through degree `2n - 1`;
when `n = 0` the exactness field is vacuous. `gaussianRule` builds a rule for `n > 0` from
`exists_gaussian_quadrature`. For `n > 0`, exactness on constants makes the total mass of the
rule equal to `∫ w` (`GaussianRule.sum_weights`), so each weight is at most `∫ w`
(`GaussianRule.weight_le_mass`). The rules converge for every continuous integrand by the
Pólya-Steklov theorem for positive rules (`gaussian_rules_converge` in `Nodal`).

## References

* Thomas Jan Stieltjes, "Quelques recherches sur la théorie des quadratures dites mécaniques",
  *Annales scientifiques de l'École Normale Supérieure* (3) 1 (1884), pp. 409-426,
  <https://doi.org/10.24033/asens.245>. §5 for the positivity of the weights.
* Philip J. Davis and Philip Rabinowitz, *Methods of Numerical Integration*, 2nd ed.,
  Academic Press, Orlando, 1984, <https://doi.org/10.1016/C2013-0-10566-1>.
-/

@[expose] public section

namespace CAS.Continuum

open Polynomial MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- A Gaussian rule on `[a, b]` for the weight `w`: `n` distinct nodes in `(a, b)`, positive
weights, and exactness against `w` for every polynomial of degree below `2n`. -/
structure GaussianRule (a b : ℝ) (w : ℝ → ℝ)
    (hw : ContinuousOn w (uIcc a b)) (n : ℕ) where
  /-- The points where the rule evaluates its integrand. -/
  nodes : Fin n → ℝ
  /-- The coefficient multiplying the integrand at each node. -/
  weights : Fin n → ℝ
  /-- The nodes are pairwise distinct, so the Lagrange basis and the Hermite interpolant on
  them exist. -/
  injective : Function.Injective nodes
  /-- Every node lies in the open interval `(a, b)`, where the integrand is sampled. -/
  interior : ∀ i, nodes i ∈ Ioo a b
  /-- Every weight is strictly positive, which makes the rule stable under uniform
  perturbation of the integrand. -/
  positive : ∀ i, 0 < weights i
  /-- The rule integrates every polynomial of degree below `2n` exactly against `w`:
  `∑ i, weights i * p (nodes i) = ∫_a^b p w`. -/
  exact : ∀ p : ℝ[X], p.natDegree < 2 * n →
    ∑ i, weights i * p.eval (nodes i) = polynomialIntegral a b w hw p

/-- The Gaussian rule supplied by `exists_gaussian_quadrature`: nodes at the roots of the
monic orthogonal polynomial `p_n`, weights the Christoffel numbers. -/
def gaussianRule {a b : ℝ} (hab : a < b) (w : ℝ → ℝ)
    (hw : ContinuousOn w (uIcc a b)) (hwpos : ∀ x ∈ Icc a b, 0 < w x)
    (n : ℕ) (hn : 0 < n) : GaussianRule a b w hw n :=
  let h := exists_gaussian_quadrature hab w hw hwpos n hn
  { nodes := h.choose
    weights := interpolatoryWeight (polynomialIntegral a b w hw) h.choose
    injective := h.choose_spec.1
    interior := h.choose_spec.2.1
    positive := h.choose_spec.2.2.1
    exact := h.choose_spec.2.2.2 }

namespace GaussianRule

variable {a b : ℝ} {w : ℝ → ℝ} {hw : ContinuousOn w (uIcc a b)} {n : ℕ}

/-- The rule applied to a real function `f`: the sum over the nodes of the weight times the
value of `f` at that node. -/
def value (rule : GaussianRule a b w hw n) (f : ℝ → ℝ) : ℝ :=
  ∑ i, rule.weights i * f (rule.nodes i)

/-- The weights of a Gaussian rule sum to `∫_a^b w`, since the rule is exact on the constant
`1`. -/
theorem sum_weights (rule : GaussianRule a b w hw n) (hn : 0 < n) :
    ∑ i, rule.weights i = polynomialIntegral a b w hw 1 := by
  simpa using rule.exact 1 (by simp; omega)

/-- Each weight of a Gaussian rule is at most `∫_a^b w`, the sum of all the positive
weights. -/
theorem weight_le_mass (rule : GaussianRule a b w hw n) (i : Fin n) :
    rule.weights i ≤ polynomialIntegral a b w hw 1 := by
  rw [← rule.sum_weights i.pos]
  exact Finset.single_le_sum (fun j _ ↦ (rule.positive j).le) (Finset.mem_univ i)

end GaussianRule

end
end CAS.Continuum

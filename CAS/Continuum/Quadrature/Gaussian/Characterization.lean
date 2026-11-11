/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.Gaussian.Weighted

/-!
# Characterization by Gaussian exactness

For `n > 0`, exactness through degree `2n - 1` determines the nodes and weights up to
reindexing. The weight at a node is the integral of that node's cardinal polynomial
(`weights_eq_interpolatoryWeight`), and the nodal polynomial is orthogonal to every polynomial
of degree below `n` (`nodal_orthogonal`), hence equal to the monic orthogonal polynomial of
`Orthogonal` (`nodal_eq_integralOrthogonalPolynomial`). So independently constructed rules, such
as the explicit Legendre rules, have the same nodal polynomials as the rules built by
projection.

## References

* Elwin Bruno Christoffel, "Über die Gaußische Quadratur und eine Verallgemeinerung
  derselben", *Journal für die reine und angewandte Mathematik* 55 (1858), pp. 61-82,
  <https://doi.org/10.1515/crll.1858.55.61>.
* Gábor Szegő, *Orthogonal Polynomials*, 4th ed., Colloquium Publications 23, American
  Mathematical Society, Providence, 1975, <https://doi.org/10.1090/coll/023>.
-/

@[expose] public section

namespace CAS.Continuum.GaussianRule

open Polynomial Set
open scoped BigOperators

noncomputable section

variable {a b : ℝ} {w : ℝ → ℝ} {hw : ContinuousOn w (uIcc a b)} {n : ℕ}

/-- The weight of a Gaussian rule at node `i` is the Christoffel number, the integral of the
`i`th cardinal polynomial. Apply exactness to that cardinal polynomial, of degree `n - 1`. -/
theorem weights_eq_interpolatoryWeight (rule : GaussianRule a b w hw n)
    (hn : 0 < n) (i : Fin n) :
    rule.weights i = interpolatoryWeight (polynomialIntegral a b w hw) rule.nodes i := by
  have hinj : Set.InjOn rule.nodes (↑(Finset.univ : Finset (Fin n))) :=
    Set.injOn_of_injective rule.injective
  have hdegree : (Lagrange.basis Finset.univ rule.nodes i).natDegree < 2 * n := by
    rw [Lagrange.natDegree_basis hinj (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  have h := rule.exact (Lagrange.basis Finset.univ rule.nodes i) hdegree
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) fun j _ hji ↦ by
    simp [Lagrange.eval_basis_of_ne hji.symm (Finset.mem_univ j)]] at h
  simpa [interpolatoryWeight, Lagrange.eval_basis_self hinj (Finset.mem_univ i)] using h

/-- The nodal polynomial of a Gaussian rule is orthogonal to every polynomial `q` of degree
below `n`. The product has degree below `2n` and vanishes at every node, so its rule value,
and hence its integral, is zero. -/
theorem nodal_orthogonal (rule : GaussianRule a b w hw n)
    (q : ℝ[X]) (hq : q.degree < n) :
    polynomialIntegral a b w hw (Lagrange.nodal Finset.univ rule.nodes * q) = 0 := by
  by_cases hq0 : q = 0
  · simp [hq0]
  have hqd : q.natDegree < n := (natDegree_lt_iff_degree_lt hq0).mpr hq
  have hdegree : (Lagrange.nodal Finset.univ rule.nodes * q).natDegree < 2 * n := by
    have hd : (Lagrange.nodal Finset.univ rule.nodes).natDegree = n := by
      simp [Lagrange.natDegree_nodal]
    exact (natDegree_mul_le).trans_lt (by rw [hd]; omega)
  rw [← rule.exact _ hdegree]
  exact Finset.sum_eq_zero fun i _ ↦ by simp [Lagrange.eval_nodal_at_node (Finset.mem_univ i)]

/-- The nodal polynomial of any Gaussian rule with `n` nodes for a continuous positive weight
is the monic orthogonal polynomial of degree `n`, by `orthogonalPolynomial_unique`. -/
theorem nodal_eq_integralOrthogonalPolynomial (rule : GaussianRule a b w hw n)
    (hab : a < b) (hwpos : ∀ x ∈ Icc a b, 0 < w x) :
    Lagrange.nodal Finset.univ rule.nodes =
      integralOrthogonalPolynomial a b hab w hw hwpos n :=
  orthogonalPolynomial_unique (polynomialIntegral a b w hw)
    (polynomialIntegral_square_pos hab w hw hwpos) n _ Lagrange.nodal_monic
    (by simp [Lagrange.degree_nodal]) rule.nodal_orthogonal

end
end CAS.Continuum.GaussianRule

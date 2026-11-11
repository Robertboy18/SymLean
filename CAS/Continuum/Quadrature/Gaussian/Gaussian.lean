/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.Gaussian.Roots

/-!
# Existence of Gaussian quadrature

For a continuous strictly positive weight `w` on `[a, b]` with `a < b` and every `n > 0`,
`exists_gaussian_quadrature` gives `n` distinct nodes in `(a, b)` and positive weights
such that the rule integrates every polynomial of degree at most `2n - 1` exactly against
`w`. The nodes are the roots of the monic orthogonal polynomial of degree `n`, and the
weights are the integrals of the Lagrange cardinal polynomials, the Christoffel numbers.

## References

* Carl Friedrich Gauss, "Methodus nova integralium valores per approximationem inveniendi",
  *Commentationes Societatis Regiae Scientiarum Gottingensis Recentiores* 3 (1816), pp. 39-76,
  <https://archive.org/details/bub_gb_J6S9H_VYVn4C>.
* Elwin Bruno Christoffel, "Über die Gaußische Quadratur und eine Verallgemeinerung
  derselben", *Journal für die reine und angewandte Mathematik* 55 (1858), pp. 61-82,
  <https://doi.org/10.1515/crll.1858.55.61>.
* Gábor Szegő, *Orthogonal Polynomials*, 4th ed., Colloquium Publications 23, American
  Mathematical Society, Providence, 1975, <https://doi.org/10.1090/coll/023>.
* G. W. Stewart, *Afternotes on Numerical Analysis*, SIAM, Philadelphia, 1996,
  <https://doi.org/10.1137/1.9781611971491>. Lecture 23, which writes `G_n` with the `n + 1` nodes
  `x_0, …, x_n`.
-/

@[expose] public section

namespace CAS.Continuum

open Polynomial Set

noncomputable section

/-- A monic polynomial of degree `n` that splits over `ℝ` and is squarefree has `n` distinct
roots, and any enumeration of them by `Fin n` has nodal polynomial equal to `p` itself. -/
theorem exists_nodes_of_monic_splits_squarefree (p : ℝ[X]) (hp : p.Monic)
    (hsplit : p.Splits) (hsquare : Squarefree p) (n : ℕ)
    (hdegree : p.natDegree = n) :
    ∃ nodes : Fin n → ℝ, Function.Injective nodes ∧
      (∀ i, p.IsRoot (nodes i)) ∧ Lagrange.nodal Finset.univ nodes = p := by
  classical
  let s := p.roots.toFinset
  have hnodup : p.roots.Nodup := nodup_roots (PerfectField.separable_iff_squarefree.mpr hsquare)
  have hcard : s.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnodup, ← hsplit.natDegree_eq_card_roots, hdegree]
  let e : s ≃ Fin n := s.equivFinOfCardEq hcard
  let nodes : Fin n → ℝ := fun i ↦ (e.symm i).val
  have hinj : Function.Injective nodes := Subtype.val_injective.comp e.symm.injective
  have hroot : ∀ i, p.IsRoot (nodes i) := fun i ↦
    (mem_roots hp.ne_zero).mp (Multiset.mem_toFinset.mp (e.symm i).property)
  refine ⟨nodes, hinj, hroot, ?_⟩
  apply eq_of_degree_le_of_eval_finset_eq s
  · simp [Lagrange.degree_nodal, hcard]
  · simp [Lagrange.degree_nodal, degree_eq_natDegree hp.ne_zero, hdegree]
  · rw [Lagrange.nodal_monic, hp]
  · intro x hx
    rw [show x = nodes (e ⟨x, hx⟩) by simp [nodes], Lagrange.eval_nodal_at_node (Finset.mem_univ _)]
    exact (hroot _).symm

/-- Gaussian quadrature with `n > 0` nodes exists for every continuous strictly positive
weight on `[a, b]`, `a < b`: `n` distinct nodes in `(a, b)`, positive weights, and exactness
against `w` for every polynomial of degree below `2n`. The nodes are the roots of the monic
orthogonal polynomial `p_n` and the weights the Christoffel numbers. -/
theorem exists_gaussian_quadrature {a b : ℝ} (hab : a < b)
    (w : ℝ → ℝ) (hw : ContinuousOn w (uIcc a b))
    (hwpos : ∀ x ∈ Icc a b, 0 < w x) (n : ℕ) (hn : 0 < n) :
    ∃ nodes : Fin n → ℝ, Function.Injective nodes ∧
      (∀ i, nodes i ∈ Ioo a b) ∧
      (∀ i, 0 < interpolatoryWeight (polynomialIntegral a b w hw) nodes i) ∧
      ∀ p : ℝ[X], p.natDegree < 2 * n →
        interpolatoryValue (polynomialIntegral a b w hw) nodes p =
          polynomialIntegral a b w hw p := by
  let L := polynomialIntegral a b w hw
  have hpositive := polynomialIntegral_square_pos hab w hw hwpos
  let p := orthogonalPolynomial L hpositive n
  have hp : p.Monic := orthogonalPolynomial_monic L hpositive n
  have hd : p.degree = n := orthogonalPolynomial_degree L hpositive n
  have horth : ∀ q : ℝ[X], q.degree < p.degree → L (p * q) = 0 := fun q hq ↦
    orthogonalPolynomial_orthogonal L hpositive n q (by rwa [← hd])
  obtain ⟨nodes, hinj, hroot, hnodal⟩ := exists_nodes_of_monic_splits_squarefree
    p hp (orthogonal_splits hab w hw hwpos p hp.ne_zero horth)
    (orthogonal_squarefree L hpositive p hp.ne_zero horth) n
    (orthogonalPolynomial_natDegree L hpositive n)
  have horth' : ∀ q : ℝ[X], q.natDegree < n → L (Lagrange.nodal Finset.univ nodes * q) = 0 :=
    fun q hq ↦ hnodal ▸ horth q (hd ▸ degree_le_natDegree.trans_lt (by exact_mod_cast hq))
  exact ⟨nodes, hinj, fun i ↦ orthogonal_root_mem_Ioo hab w hw hwpos p hp.ne_zero horth (hroot i),
    gaussian_weight_pos hn L nodes hinj horth' hpositive, gaussian_exact L nodes hinj horth'⟩

end
end CAS.Continuum

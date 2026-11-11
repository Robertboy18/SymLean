/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Gaussian exactness from orthogonality

Here the integral is only a linear functional `L` on real polynomials. Lagrange
interpolation at `n` distinct nodes gives a rule exact below degree `n`
(`interpolatory_exact`). If `L` vanishes on the nodal polynomial times every polynomial of
degree below `n`, division by the nodal polynomial extends exactness to degrees below `2n`
(`gaussian_exact`), and squares of the cardinal polynomials show the weights are positive
whenever `L` is positive on nonzero squares (`gaussian_weight_pos`).

## Implementation notes

We work with an abstract linear functional `L` rather than an integral. The same lemmas then
serve the weighted integrals of `Integral` and `Gaussian` and the certified rules of
`Legendre.RootCertificates`, which supply the orthogonality hypothesis as vanishing rational
moments. Exactness below degree `2n` divides by the monic nodal polynomial with `modByMonic`
and `divByMonic`. Positivity applies exactness to the square of the `i`th cardinal polynomial,
which is the argument of Stieltjes.

## References

* Thomas Jan Stieltjes, "Quelques recherches sur la théorie des quadratures dites mécaniques",
  *Annales scientifiques de l'École Normale Supérieure* (3) 1 (1884), pp. 409-426,
  <https://doi.org/10.24033/asens.245>. §5 for the positivity of the weights.
-/

@[expose] public section

open Polynomial
open scoped BigOperators

namespace CAS.Continuum

noncomputable section

/-- The interpolatory weight at node `i`: the value of `L` on the `i`th Lagrange cardinal
polynomial of the nodes. -/
def interpolatoryWeight {n : ℕ} (L : ℝ[X] →ₗ[ℝ] ℝ) (nodes : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  L (Lagrange.basis Finset.univ nodes i)

/-- The interpolatory quadrature rule applied to a polynomial: the sum over the nodes of the
interpolatory weight times the value of `p` at that node. -/
def interpolatoryValue {n : ℕ} (L : ℝ[X] →ₗ[ℝ] ℝ) (nodes : Fin n → ℝ)
    (p : ℝ[X]) : ℝ :=
  ∑ i, interpolatoryWeight L nodes i * p.eval (nodes i)

/-- For `n` distinct nodes the interpolatory rule reproduces `L p` whenever `deg p < n`.
Such a `p` equals its own Lagrange interpolant. -/
theorem interpolatory_exact {n : ℕ} (L : ℝ[X] →ₗ[ℝ] ℝ) (nodes : Fin n → ℝ)
    (hnodes : Function.Injective nodes) (p : ℝ[X]) (hp : p.degree < n) :
    interpolatoryValue L nodes p = L p := by
  conv_rhs => rw [Lagrange.eq_interpolate (f := p) (s := Finset.univ)
    (Set.injOn_of_injective hnodes) (by simpa using hp)]
  simp only [Lagrange.interpolate_apply, map_sum, ← smul_eq_C_mul, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- If `L` vanishes on the nodal polynomial times every polynomial of degree below `n`, the
interpolatory rule is exact for `p.natDegree < 2n` (through degree `2n - 1` when `n > 0`).
Divide `p` by the nodal polynomial: the quotient term is killed by `L` and by the rule,
and `interpolatory_exact` handles the remainder. -/
theorem gaussian_exact {n : ℕ} (L : ℝ[X] →ₗ[ℝ] ℝ)
    (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (horth : ∀ q : ℝ[X], q.natDegree < n →
      L (Lagrange.nodal Finset.univ nodes * q) = 0)
    (p : ℝ[X]) (hp : p.natDegree < 2 * n) :
    interpolatoryValue L nodes p = L p := by
  let nodal := Lagrange.nodal Finset.univ nodes
  have hmonic : nodal.Monic := Lagrange.nodal_monic
  have hdeg : nodal.natDegree = n := by simp [nodal, Lagrange.natDegree_nodal]
  have hquot : (p /ₘ nodal).natDegree < n := by
    rw [Polynomial.natDegree_divByMonic p hmonic, hdeg]
    omega
  have hrem : (p %ₘ nodal).degree < n := by
    simpa [nodal, Lagrange.degree_nodal] using degree_modByMonic_lt p hmonic
  have hvals : interpolatoryValue L nodes p = interpolatoryValue L nodes (p %ₘ nodal) :=
    Finset.sum_congr rfl fun i _ ↦ by
      conv_lhs => rw [← modByMonic_add_div p nodal]
      simp [nodal, Lagrange.eval_nodal_at_node]
  have hsplit := congrArg L (modByMonic_add_div p nodal)
  rwa [map_add, horth _ hquot, add_zero, ← interpolatory_exact L nodes hnodes _ hrem, ← hvals]
    at hsplit

/-- Under the orthogonality hypothesis of `gaussian_exact`, if `L (p ^ 2) > 0` for every
`p ≠ 0` then every interpolatory weight is strictly positive. Apply exactness to the square
of the `i`th cardinal polynomial, which has degree `2n - 2` and picks out the weight `i`. -/
theorem gaussian_weight_pos {n : ℕ} (hn : 0 < n) (L : ℝ[X] →ₗ[ℝ] ℝ)
    (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (horth : ∀ q : ℝ[X], q.natDegree < n →
      L (Lagrange.nodal Finset.univ nodes * q) = 0)
    (hpositive : ∀ p : ℝ[X], p ≠ 0 → 0 < L (p ^ 2)) (i : Fin n) :
    0 < interpolatoryWeight L nodes i := by
  let basis := Lagrange.basis Finset.univ nodes i
  have hinj : Set.InjOn nodes (↑(Finset.univ : Finset (Fin n))) :=
    Set.injOn_of_injective hnodes
  have hne : basis ≠ 0 := Lagrange.basis_ne_zero hinj (Finset.mem_univ i)
  have hdeg : (basis ^ 2).natDegree < 2 * n := by
    rw [natDegree_pow, Lagrange.natDegree_basis hinj (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    omega
  have hvalue : interpolatoryValue L nodes (basis ^ 2) = interpolatoryWeight L nodes i := by
    rw [interpolatoryValue, Finset.sum_eq_single i]
    · simp [basis, Lagrange.eval_basis_self hinj (Finset.mem_univ i)]
    · exact fun j _ hji ↦ by simp [basis, Lagrange.eval_basis_of_ne hji.symm (Finset.mem_univ j)]
    · simp
  rw [← hvalue, gaussian_exact L nodes hnodes horth (basis ^ 2) hdeg]
  exact hpositive basis hne

end
end CAS.Continuum

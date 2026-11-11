/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.RealRoot.Interval
public import CAS.Continuum.Quadrature.Legendre.Identification

/-!
# Gaussian rules from rational root certificates

A certified root bracket for a sparse rational polynomial `p` is a `RootBracket`, a
rational interval together with a monotonicity direction, whose decidable check `valid p`
passes. Validity certifies that `p` has exactly one root in the interval
(`RootBracket.existsUnique_root`). Given `n` disjoint certified brackets for a monic `p` of
degree `n`, the roots they isolate are the nodes of a Gaussian rule on `[-1, 1]` as soon as
the moments `∫_{-1}^1 p x * x^k` vanish for `k < n`, that is, as soon as `p` is the monic
Legendre polynomial of degree `n`. `rule` constructs that Gaussian rule, and `nodes_mem`
supplies the enclosures needed to compare its nodes with numerical approximations. The
construction works at every positive order and does not depend on a particular stored table.

## Implementation notes

A certificate is the sparse rational polynomial `p` with one bracket per root, however they
were found. The hypotheses of `rule` are statements about rationals and the explicit polynomial
`realPolynomial p`. `RootBracket.valid`, from `CAS.Polynomial.RealRoot.Interval`, asks for
opposite weak signs of `p` at the bracket ends and one strict sign of an interval enclosure of
`p'` over the bracket. The bracket ends are compared as rationals, `p` is monic of degree `n`,
and the moments `shiftedMoment p k`, exact rationals computed from `∫_{-1}^1 x^k`, vanish for
`k < n`. `orthogonal_of_shiftedMoments` and `nodal_eq` turn the moments into orthogonality of
the nodal polynomial, and the general theory then gives positive weights
(`integral_gaussian_weight_pos`) and exactness (`gaussian_exact`). Orthogonality is all it uses,
so `p` is never compared with `monicPolynomial n` and no node table is stored.

## References

* NIST Digital Library of Mathematical Functions, §3.5(v) Gauss Quadrature, Version 1.2.8
  (2026-09-15), <https://dlmf.nist.gov/3.5.v>. The certified root brackets are ours.
-/

@[expose] public section

namespace CAS.Continuum.Legendre.RootCertificates

open _root_.Polynomial Set
open CAS.Polynomial
open CAS.Polynomial.RealRoot

/-- The real polynomial denoted by a sparse rational polynomial `Sparse.Univariate`, a list of
`(coefficient, exponent)` terms. -/
noncomputable def realPolynomial : Sparse.Univariate → ℝ[X]
  | [] => 0
  | term :: rest =>
      C (term.1 : ℝ) * X ^ term.2 (0 : Fin 1) + realPolynomial rest

/-- Evaluating `realPolynomial p` agrees with the sparse evaluator `Sparse.evalReal`. -/
theorem eval_realPolynomial (p : Sparse.Univariate) (x : ℝ) :
    (realPolynomial p).eval x = Sparse.evalReal p x := by
  induction p with
  | nil => simp [realPolynomial, Sparse.evalReal]
  | cons term rest ih => simp [realPolynomial, Sparse.evalReal, ih]

/-- The moment `∫_{-1}^1 x^k = (1 - (-1)^(k+1)) / (k + 1)` as a rational number. -/
def moment (k : ℕ) : ℚ :=
  (1 - (-1) ^ (k + 1)) / (k + 1)

/-- The rational value of `∫_{-1}^1 p x * x^k` for a sparse polynomial `p`, computed term by
term from `moment`. -/
def shiftedMoment : Sparse.Univariate → ℕ → ℚ
  | [], _ => 0
  | term :: rest, k =>
      term.1 * moment (term.2 (0 : Fin 1) + k) + shiftedMoment rest k

/-- `∫_{-1}^1 c x^k = c * moment k`. -/
theorem integral_C_mul_X_pow (c : ℝ) (k : ℕ) :
    polynomialIntegral (-1) 1 (fun _ ↦ 1) continuousOn_const (C c * X ^ k) =
      c * (moment k : ℝ) := by
  simp [polynomialIntegral, moment]

/-- `∫_{-1}^1 p x * x^k = shiftedMoment p k` for a sparse polynomial `p`. -/
theorem integral_realPolynomial_mul_X_pow (p : Sparse.Univariate) (k : ℕ) :
    polynomialIntegral (-1) 1 (fun _ ↦ 1) continuousOn_const
      (realPolynomial p * X ^ k) = (shiftedMoment p k : ℝ) := by
  induction p with
  | nil => simp [realPolynomial, shiftedMoment]
  | cons term rest ih =>
      simp only [realPolynomial, add_mul, map_add, mul_assoc, ← pow_add,
        integral_C_mul_X_pow, ih, shiftedMoment, Rat.cast_add, Rat.cast_mul]

/-- If `shiftedMoment p k = 0` for all `k < n` then `realPolynomial p` is orthogonal on
`[-1, 1]` to every polynomial of degree below `n`. Expand `q` in monomials. -/
theorem orthogonal_of_shiftedMoments (p : Sparse.Univariate) (n : ℕ)
    (hmoments : ∀ k < n, shiftedMoment p k = 0)
    (q : ℝ[X]) (hq : q.natDegree < n) :
    polynomialIntegral (-1) 1 (fun _ ↦ 1) continuousOn_const
      (realPolynomial p * q) = 0 := by
  classical
  rw [q.as_sum_range' n hq, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  rw [← C_mul_X_pow_eq_monomial, mul_left_comm, ← smul_eq_C_mul, map_smul,
    integral_realPolynomial_mul_X_pow, hmoments k (Finset.mem_range.mp hk)]
  simp

/-- The root isolated by each certified root bracket, one real number per bracket. Validity
of the brackets is all that is needed to define the nodes. -/
noncomputable def nodes {n : ℕ} (p : Sparse.Univariate)
    (brackets : Fin n → RootBracket)
    (hvalid : ∀ i, (brackets i).valid p = true) : Fin n → ℝ :=
  fun i ↦ ((brackets i).existsUnique_root p (hvalid i)).exists.choose

/-- Each node lies in its bracket. -/
theorem nodes_mem {n : ℕ} (p : Sparse.Univariate)
    (brackets : Fin n → RootBracket)
    (hvalid : ∀ i, (brackets i).valid p = true) (i : Fin n) :
    (brackets i).interval.MemReal (nodes p brackets hvalid i) :=
  ((brackets i).existsUnique_root p (hvalid i)).exists.choose_spec.1

/-- Each node is a root of `realPolynomial p`. -/
theorem nodes_root {n : ℕ} (p : Sparse.Univariate)
    (brackets : Fin n → RootBracket)
    (hvalid : ∀ i, (brackets i).valid p = true) (i : Fin n) :
    (realPolynomial p).IsRoot (nodes p brackets hvalid i) :=
  (eval_realPolynomial p _).trans ((brackets i).existsUnique_root p (hvalid i)).exists.choose_spec.2

/-- If the brackets are pairwise disjoint and listed in increasing order, the nodes are
strictly increasing. -/
theorem nodes_strictMono {n : ℕ} (p : Sparse.Univariate)
    (brackets : Fin n → RootBracket)
    (hvalid : ∀ i, (brackets i).valid p = true)
    (hordered : ∀ i j, i < j → (brackets i).interval.hi < (brackets j).interval.lo) :
    StrictMono (nodes p brackets hvalid) := fun i j hij ↦
  (nodes_mem p brackets hvalid i).2.trans_lt
    ((Rat.cast_lt.mpr (hordered i j hij)).trans_le (nodes_mem p brackets hvalid j).1)

/-- For `n` disjoint ordered certified brackets of a monic `p` of degree `n`, the nodal
polynomial of the nodes is `realPolynomial p`. Both are monic of degree `n` and agree at the
`n` distinct nodes. -/
theorem nodal_eq {n : ℕ} (p : Sparse.Univariate)
    (brackets : Fin n → RootBracket)
    (hvalid : ∀ i, (brackets i).valid p = true)
    (hordered : ∀ i j, i < j → (brackets i).interval.hi < (brackets j).interval.lo)
    (hmonic : (realPolynomial p).Monic) (hdegree : (realPolynomial p).natDegree = n) :
    Lagrange.nodal Finset.univ (nodes p brackets hvalid) = realPolynomial p := by
  apply eq_of_degree_le_of_eval_finset_eq
    (Finset.univ.image (nodes p brackets hvalid))
  · simp [Finset.card_image_of_injective _ (nodes_strictMono p brackets hvalid hordered).injective,
      Lagrange.degree_nodal]
  · simp [Lagrange.degree_nodal, degree_eq_natDegree hmonic.ne_zero, hdegree]
  · rw [Lagrange.nodal_monic, hmonic]
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact (Lagrange.eval_nodal_at_node (Finset.mem_univ _)).trans
      (nodes_root p brackets hvalid i).symm

/-- The leading coefficient of `p` is nonzero when `p` has positive degree. -/
theorem leadingCoeff_ne_zero_of_natDegree {n : ℕ} (p : Sparse.Univariate)
    (hdegree : (realPolynomial p).natDegree = n) (hn : 0 < n) :
    (realPolynomial p).leadingCoeff ≠ 0 := by
  refine leadingCoeff_ne_zero.mpr fun h ↦ ?_
  rw [h, natDegree_zero] at hdegree
  omega

/-- Without monicity: for `n > 0` disjoint ordered certified brackets of `p` of degree `n`, the
nodal polynomial of the nodes is `realPolynomial p` divided by its leading coefficient. -/
theorem nodal_eq_C_mul {n : ℕ} (p : Sparse.Univariate)
    (brackets : Fin n → RootBracket)
    (hvalid : ∀ i, (brackets i).valid p = true)
    (hordered : ∀ i j, i < j → (brackets i).interval.hi < (brackets j).interval.lo)
    (hdegree : (realPolynomial p).natDegree = n) (hn : 0 < n) :
    Lagrange.nodal Finset.univ (nodes p brackets hvalid) =
      C (realPolynomial p).leadingCoeff⁻¹ * realPolynomial p := by
  have hc := leadingCoeff_ne_zero_of_natDegree p hdegree hn
  apply eq_of_degree_le_of_eval_finset_eq
    (Finset.univ.image (nodes p brackets hvalid))
  · simp [Finset.card_image_of_injective _ (nodes_strictMono p brackets hvalid hordered).injective,
      Lagrange.degree_nodal]
  · rw [degree_C_mul (inv_ne_zero hc)]
    simp [Lagrange.degree_nodal, degree_eq_natDegree (leadingCoeff_ne_zero.mp hc), hdegree]
  · rw [Lagrange.nodal_monic]
    simp [hc]
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Lagrange.eval_nodal_at_node (Finset.mem_univ _), eval_mul, eval_C,
      (nodes_root p brackets hvalid i).eq_zero, mul_zero]

/-- The Gaussian rule on `[-1, 1]` with nodes at the certified roots and weights the
Christoffel numbers. Needs the brackets inside `(-1, 1)`, `p` monic of degree `n`, and the
vanishing moments `shiftedMoment p k = 0` for `k < n`, which give orthogonality of the nodal
polynomial and hence positivity of the weights and exactness through degree `2n - 1`. -/
noncomputable def rule {n : ℕ} (hn : 0 < n) (p : Sparse.Univariate)
    (brackets : Fin n → RootBracket)
    (hvalid : ∀ i, (brackets i).valid p = true)
    (hordered : ∀ i j, i < j → (brackets i).interval.hi < (brackets j).interval.lo)
    (hinterior : ∀ i, -1 < (brackets i).interval.lo ∧ (brackets i).interval.hi < 1)
    (hmonic : (realPolynomial p).Monic) (hdegree : (realPolynomial p).natDegree = n)
    (hmoments : ∀ k < n, shiftedMoment p k = 0) : Rule n := by
  let r := nodes p brackets hvalid
  have hinj : Function.Injective r := (nodes_strictMono p brackets hvalid hordered).injective
  have horth : ∀ q : ℝ[X], q.natDegree < n →
      polynomialIntegral (-1) 1 (fun _ ↦ 1) continuousOn_const
        (Lagrange.nodal Finset.univ r * q) = 0 := by
    intro q hq
    rw [nodal_eq p brackets hvalid hordered hmonic hdegree]
    exact orthogonal_of_shiftedMoments p n hmoments q hq
  exact
    { nodes := r
      weights := interpolatoryWeight
        (polynomialIntegral (-1) 1 (fun _ ↦ 1) continuousOn_const) r
      injective := hinj
      interior := fun i ↦ by
        have hlo : (-1 : ℝ) < (brackets i).interval.lo := by
          exact_mod_cast (hinterior i).1
        have hhi : ((brackets i).interval.hi : ℝ) < 1 := by
          exact_mod_cast (hinterior i).2
        exact ⟨hlo.trans_le (nodes_mem p brackets hvalid i).1,
          (nodes_mem p brackets hvalid i).2.trans_lt hhi⟩
      positive := integral_gaussian_weight_pos (by norm_num) _ _ (by intro x hx; norm_num)
        hn r hinj horth
      exact := gaussian_exact _ r hinj horth }

end CAS.Continuum.Legendre.RootCertificates

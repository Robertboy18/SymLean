/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.Buchberger
public import CAS.Polynomial.Sparse
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.Ring

/-!
# Gröbner certificates on sparse polynomials

We read a sparse polynomial `MvPoly n` as a polynomial in `MvPolynomial (Fin n) ℚ` and check in
the kernel the hypothesis of Buchberger's criterion (`CAS.Polynomial.Buchberger`) for
`MonomialOrder.lex`, with `X 0` the largest variable. A certificate lists, for each pair `i < j`
of the basis, the quotients of a division of the S-polynomial of `gᵢ` and `gⱼ` by the basis. The
checker recomputes the S-polynomial from the leading terms, checks that it equals the combination
of the quotients, and compares every term of every quotient times the leading monomial of its
divisor with the least common multiple of the two leading monomials.

## Main definitions

* `CAS.Polynomial.Sparse.toMvPolynomial`: the Mathlib polynomial of a sparse polynomial.
* `CAS.Polynomial.Sparse.combinationHolds`: the check of an identity `h = ∑ qₗ gₗ`.
* `CAS.Polynomial.Sparse.groebnerCertified`: the check of a Gröbner certificate.
* `CAS.Polynomial.Sparse.listPolynomial`: a polynomial written as `∑ C c * ∏ xᵢ ^ eᵢ`, which links
  the quoted terms of a certificate to the polynomials of a statement.

## Main results

* `CAS.Polynomial.Sparse.toMvPolynomial_eq_sum_of_combinationHolds`: a checked identity holds in
  `MvPolynomial (Fin n) ℚ`.
* `CAS.Polynomial.Sparse.isGroebner_of_groebnerCertified`: a certified list is a Gröbner basis of
  the ideal it spans.
* `CAS.Polynomial.Sparse.toMvPolynomial_ofTerms`: the polynomial of a quoted list of terms.

## Implementation notes

The kernel checks a certificate by evaluation, so every check is a `Bool` function on lists of
rationals and exponent vectors. We get the ring laws of `toMvPolynomial` from the real evaluation
`mvPolyVal` that the sparse arithmetic already comes with, `MvPolynomial.funext` over `ℝ` and the
injectivity of `ℚ → ℝ`, rather than redoing the sorted-list arithmetic in `MvPolynomial`. The
lexicographic comparison `mvLexLt` is related to Mathlib's order by `toSyn_lt_of_mvLexLt`. Every
pair has an entry: the product and chain criteria, which would skip pairs, are not used.

The quotients are found by untrusted meta code: `CAS.Command.Ideal.groebnerCertificate` divides
the S-polynomial of every pair by the basis and records the quotients, and
`CAS.Command.Ideal.groebnerProperty` has the kernel evaluate `groebnerCertified` on them before it
applies `isGroebner_of_groebnerCertified`.

## References

* Bruno Buchberger, "Ein algorithmisches Kriterium für die Lösbarkeit eines algebraischen
  Gleichungssystems", *Aequationes Mathematicae* 4 (1970), pp. 374-383,
  <https://doi.org/10.1007/BF01844169>. Section 2.3 defines the S-polynomials and Section 3.1
  proves the criterion for power products ordered by degree and then lexicographically; the
  certificate checks the hypothesis of our version for any monomial order,
  `CAS.Polynomial.Buchberger.exists_leadingTerm_dvd_of_sPolynomial`.
-/

@[expose] public section

open CAS.Verified.Expr.Alg
open scoped MonomialOrder

namespace CAS.Polynomial.Sparse

variable {n : ℕ}

/-- The exponent vector of a sparse monomial as a finitely supported function. -/
noncomputable def monomialFinsupp (m : MvMonomial n) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm m

/-- `monomialFinsupp m` has the exponents of `m`: its value at `i` is `m i`. -/
@[simp] theorem monomialFinsupp_apply (m : MvMonomial n) (i : Fin n) :
    monomialFinsupp m i = m i := by
  simp [monomialFinsupp]

/-- The exponent vector of the product `mvMul a b` is the sum of the exponent vectors of `a` and
`b`. -/
theorem monomialFinsupp_mvMul (a b : MvMonomial n) :
    monomialFinsupp (mvMul a b) = monomialFinsupp a + monomialFinsupp b := by
  ext i
  simp only [Finsupp.add_apply, monomialFinsupp_apply, mvMul]

/-- The least common multiple of two monomials. -/
def mvLcm (a b : MvMonomial n) : MvMonomial n := fun i ↦ max (a i) (b i)

/-- The exponent vector of `mvLcm a b` is the supremum of the exponent vectors of `a` and `b`. -/
theorem monomialFinsupp_mvLcm (a b : MvMonomial n) :
    monomialFinsupp (mvLcm a b) = monomialFinsupp a ⊔ monomialFinsupp b := by
  ext i
  simp only [Finsupp.sup_apply, monomialFinsupp_apply, mvLcm]

/-- The truncated difference of two monomials. -/
def mvTsub (a b : MvMonomial n) : MvMonomial n := fun i ↦ a i - b i

/-- The exponent vector of `mvTsub a b` is the truncated difference of the exponent vectors of `a`
and `b`. -/
theorem monomialFinsupp_mvTsub (a b : MvMonomial n) :
    monomialFinsupp (mvTsub a b) = monomialFinsupp a - monomialFinsupp b := by
  ext i
  simp only [Finsupp.tsub_apply, monomialFinsupp_apply, mvTsub]

/-- The monomial with the exponents of a list, `0` past its end. -/
def mvMonomialOfList (es : List ℕ) : MvMonomial n := fun i ↦ es.getD i.val 0

/-- The sparse polynomial of a list of coefficients with exponent lists. -/
def ofTerms (raw : List (ℚ × List ℕ)) : MvPoly n :=
  raw.map fun t ↦ (t.1, mvMonomialOfList t.2)

/-- The Mathlib polynomial of a sparse polynomial: the sum of its terms. -/
noncomputable def toMvPolynomial : MvPoly n → MvPolynomial (Fin n) ℚ
  | [] => 0
  | t :: rest => MvPolynomial.monomial (monomialFinsupp t.2) t.1 + toMvPolynomial rest

/-- The empty sparse polynomial is `0`. -/
@[simp] theorem toMvPolynomial_nil : toMvPolynomial ([] : MvPoly n) = 0 := rfl

/-- `toMvPolynomial (t :: rest)` is the monomial of the term `t` plus `toMvPolynomial rest`. -/
@[simp] theorem toMvPolynomial_cons (t : ℚ × MvMonomial n) (rest : MvPoly n) :
    toMvPolynomial (t :: rest) =
      MvPolynomial.monomial (monomialFinsupp t.2) t.1 + toMvPolynomial rest := rfl

/-- The one-term sparse polynomial `[(c, m)]` is the monomial with exponents `m` and coefficient
`c`. -/
theorem toMvPolynomial_single (c : ℚ) (m : MvMonomial n) :
    toMvPolynomial [(c, m)] = MvPolynomial.monomial (monomialFinsupp m) c := by
  rw [toMvPolynomial_cons, toMvPolynomial_nil, add_zero]

/-- At a real point `v`, the `Finsupp.prod` of `v i ^ e` over `monomialFinsupp m` is the product of
`v i ^ m i` over `List.finRange n`. -/
theorem prod_monomialFinsupp (v : Fin n → ℝ) (m : MvMonomial n) :
    (monomialFinsupp m).prod (fun i e ↦ v i ^ e) =
      ((List.finRange n).map fun i ↦ v i ^ m i).prod := by
  rw [Finsupp.prod_fintype _ (fun i e ↦ v i ^ e) (fun i ↦ pow_zero (v i)), ← Fin.prod_univ_def]
  simp only [monomialFinsupp_apply]

/-- At every real point `v`, the polynomial of `p` mapped to `ℝ` evaluates to the real value
`mvPolyVal` of `p` at `v`. -/
theorem eval_map_toMvPolynomial (v : Fin n → ℝ) (p : MvPoly n) :
    MvPolynomial.eval v (MvPolynomial.map (algebraMap ℚ ℝ) (toMvPolynomial p)) =
      mvPolyVal (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) p := by
  induction p with
  | nil => simp [mvPolyVal]
  | cons t rest ih =>
    rw [toMvPolynomial_cons, map_add, map_add, ih, MvPolynomial.map_monomial,
      MvPolynomial.eval_monomial, prod_monomialFinsupp]
    simp only [mvPolyVal, mvTermVal, mvMonomialVal, eq_ratCast]

/-- Two rational polynomials whose images in `ℝ` agree at every real point are equal. This is
`MvPolynomial.funext` over `ℝ` composed with the injectivity of `MvPolynomial.map` along `ℚ → ℝ`; it
is kept as the one step through which the four identities below (normalization, sum, difference,
product) are read off the real evaluation `mvPolyVal`. -/
theorem eq_of_eval_map {P Q : MvPolynomial (Fin n) ℚ}
    (h : ∀ v : Fin n → ℝ, MvPolynomial.eval v (MvPolynomial.map (algebraMap ℚ ℝ) P) =
      MvPolynomial.eval v (MvPolynomial.map (algebraMap ℚ ℝ) Q)) :
    P = Q :=
  MvPolynomial.map_injective _ (algebraMap ℚ ℝ).injective (MvPolynomial.funext h)

/-- Normalizing a sparse polynomial does not change its polynomial. -/
theorem toMvPolynomial_mvNormalize (p : MvPoly n) :
    toMvPolynomial (mvNormalize p) = toMvPolynomial p :=
  eq_of_eval_map fun v ↦ by simp only [eval_map_toMvPolynomial, mvPolyVal_normalize]

/-- The polynomial of the sparse sum `mvAdd p q` is the sum of the polynomials of `p` and `q`. -/
theorem toMvPolynomial_mvAdd (p q : MvPoly n) :
    toMvPolynomial (mvAdd p q) = toMvPolynomial p + toMvPolynomial q :=
  eq_of_eval_map fun v ↦ by simp only [map_add, eval_map_toMvPolynomial, mvPolyVal_add]

/-- The polynomial of the sparse difference `mvSub p q` is the difference of the polynomials of `p`
and `q`. -/
theorem toMvPolynomial_mvSub (p q : MvPoly n) :
    toMvPolynomial (mvSub p q) = toMvPolynomial p - toMvPolynomial q :=
  eq_of_eval_map fun v ↦ by simp only [map_sub, eval_map_toMvPolynomial, mvPolyVal_sub]

/-- The polynomial of the sparse product `mvMulPoly p q` is the product of the polynomials of `p`
and `q`. -/
theorem toMvPolynomial_mvMulPoly (p q : MvPoly n) :
    toMvPolynomial (mvMulPoly p q) = toMvPolynomial p * toMvPolynomial q :=
  eq_of_eval_map fun v ↦ by simp only [map_mul, eval_map_toMvPolynomial, mvPolyVal_mulPoly]

/-- If `isZero p` holds (the normalization of `p` is empty), the polynomial of `p` is `0`. -/
theorem toMvPolynomial_eq_zero_of_isZero {p : MvPoly n} (h : isZero p = true) :
    toMvPolynomial p = 0 := by
  rw [← toMvPolynomial_mvNormalize, List.isEmpty_iff.mp h, toMvPolynomial_nil]

/-! ## Combinations -/

/-- The combination `∑ qₗ gₗ` of two lists, as far as both go. -/
def mvCombination : List (MvPoly n) → List (MvPoly n) → MvPoly n
  | [], _ => []
  | _ :: _, [] => []
  | q :: qs, g :: gs => mvAdd (mvMulPoly q g) (mvCombination qs gs)

/-- The polynomial of `mvCombination qs gs` is `∑ l < gs.length, qₗ gₗ`, a missing quotient `qₗ`
counting as `[]`, that is `0`. -/
theorem toMvPolynomial_mvCombination : ∀ (qs gs : List (MvPoly n)),
    toMvPolynomial (mvCombination qs gs) =
      ∑ l ∈ Finset.range gs.length, toMvPolynomial (qs.getD l []) * toMvPolynomial (gs.getD l [])
  | [], gs => by simp [mvCombination]
  | _ :: _, [] => by simp [mvCombination]
  | q :: qs, g :: gs => by
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [mvCombination, toMvPolynomial_mvAdd, toMvPolynomial_mvMulPoly,
      toMvPolynomial_mvCombination qs gs, List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- Whether `h = ∑ qₗ gₗ` holds as an identity of sparse polynomials. -/
def combinationHolds (h : MvPoly n) (qs gs : List (MvPoly n)) : Bool :=
  isZero (mvSub h (mvCombination qs gs))

/-- A checked combination holds in `MvPolynomial (Fin n) ℚ`: `h = ∑ qₗ gₗ` over the positions of
`gs`, a missing quotient counting as zero. -/
theorem toMvPolynomial_eq_sum_of_combinationHolds {h : MvPoly n} {qs gs : List (MvPoly n)}
    (hc : combinationHolds h qs gs = true) :
    toMvPolynomial h = ∑ l ∈ Finset.range gs.length,
      toMvPolynomial (qs.getD l []) * toMvPolynomial (gs.getD l []) := by
  have h0 := toMvPolynomial_eq_zero_of_isZero hc
  rw [toMvPolynomial_mvSub, sub_eq_zero, toMvPolynomial_mvCombination] at h0
  exact h0

/-! ## Lexicographic comparison -/

/-- Lexicographic comparison of the exponents from index `k` on, with `fuel` steps. -/
def mvLexLtFrom (a b : MvMonomial n) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, k =>
    if h : k < n then
      decide (a ⟨k, h⟩ < b ⟨k, h⟩) || (a ⟨k, h⟩ == b ⟨k, h⟩ && mvLexLtFrom a b fuel (k + 1))
    else false

/-- `a` is smaller than `b` in the lexicographic order with `X 0` the largest variable. -/
def mvLexLt (a b : MvMonomial n) : Bool := mvLexLtFrom a b n 0

/-- If `a` and `b` agree at every index below `k` and `mvLexLtFrom a b fuel k` holds, then some
index `i` has `a i < b i` with `a` and `b` agreeing below `i`, for every `fuel`. -/
theorem mvLexLtFrom_sound {a b : MvMonomial n} : ∀ (fuel k : ℕ),
    (∀ j : Fin n, j.val < k → a j = b j) → mvLexLtFrom a b fuel k = true →
      ∃ i : Fin n, (∀ j, j < i → a j = b j) ∧ a i < b i
  | 0, _, _, h => by simp [mvLexLtFrom] at h
  | fuel + 1, k, heq, h => by
    by_cases hk : k < n
    · simp only [mvLexLtFrom, hk, ↓reduceDIte, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq] at h
      rcases h with hlt | ⟨hab, hnext⟩
      · exact ⟨⟨k, hk⟩, fun j hj ↦ heq j (Fin.lt_def.mp hj), hlt⟩
      · refine mvLexLtFrom_sound fuel (k + 1) (fun j hj ↦ ?_) hnext
        by_cases hjk : j.val < k
        · exact heq j hjk
        · have hj' : j = ⟨k, hk⟩ :=
            Fin.ext (Nat.le_antisymm (Nat.lt_add_one_iff.mp hj) (Nat.not_lt.mp hjk))
          rw [hj']
          exact hab
    · simp [mvLexLtFrom, hk] at h

/-- `mvLexLt a b` gives `a` below `b` in `MonomialOrder.lex`. -/
theorem toSyn_lt_of_mvLexLt {a b : MvMonomial n} (h : mvLexLt a b = true) :
    monomialFinsupp a ≺[MonomialOrder.lex] monomialFinsupp b := by
  obtain ⟨i, hi, hab⟩ := mvLexLtFrom_sound n 0 (fun j hj ↦ absurd hj (Nat.not_lt_zero _)) h
  rw [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff]
  exact ⟨i, fun j hj ↦ hi j hj, hab⟩

/-! ## Leading terms -/

/-- The monomial of the first term. -/
def headMonomial : MvPoly n → MvMonomial n
  | [] => mvOne n
  | t :: _ => t.2

/-- The coefficient of the first term. -/
def headCoeff : MvPoly n → ℚ
  | [] => 0
  | t :: _ => t.1

/-- The first term has a nonzero coefficient and a monomial lexicographically larger than the
monomial of every other term. -/
def headLeads : MvPoly n → Bool
  | [] => true
  | t :: rest => t.1 != 0 && rest.all fun s ↦ mvLexLt s.2 t.2

/-- Every exponent vector `s` in the support of `toMvPolynomial p` is that of some term of `p`. -/
theorem exists_of_mem_support {p : MvPoly n} {s : Fin n →₀ ℕ}
    (hs : s ∈ (toMvPolynomial p).support) : ∃ t ∈ p, monomialFinsupp t.2 = s := by
  classical
  induction p with
  | nil => simp at hs
  | cons t rest ih =>
    rw [toMvPolynomial_cons] at hs
    rcases Finset.mem_union.mp (MvPolynomial.support_add hs) with h | h
    · exact ⟨t, List.mem_cons_self,
        (Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)).symm⟩
    · obtain ⟨u, hu, rfl⟩ := ih h
      exact ⟨u, List.mem_cons_of_mem _ hu, rfl⟩

/-- When the first term leads, its monomial and coefficient are the degree and the leading
coefficient for `MonomialOrder.lex`. -/
theorem degree_toMvPolynomial_of_headLeads {p : MvPoly n} (hp : headLeads p = true) :
    MonomialOrder.lex.degree (toMvPolynomial p) = monomialFinsupp (headMonomial p) ∧
      MonomialOrder.lex.leadingCoeff (toMvPolynomial p) = headCoeff p := by
  cases p with
  | nil =>
    refine ⟨?_, ?_⟩
    · rw [toMvPolynomial_nil, MonomialOrder.degree_zero]
      ext i
      simp [headMonomial, mvOne]
    · rw [toMvPolynomial_nil, MonomialOrder.leadingCoeff_zero]
      rfl
  | cons t rest =>
    simp only [headLeads, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at hp
    obtain ⟨ht, hall⟩ := hp
    classical
    have hM : MonomialOrder.lex.degree (MvPolynomial.monomial (monomialFinsupp t.2) t.1) =
        monomialFinsupp t.2 := by
      simp only [MonomialOrder.degree_monomial, ht, ↓reduceIte]
    rw [toMvPolynomial_cons]
    by_cases h0 : toMvPolynomial rest = 0
    · rw [h0, add_zero, hM, MonomialOrder.leadingCoeff_monomial]
      exact ⟨rfl, rfl⟩
    · have hlt : MonomialOrder.lex.degree (toMvPolynomial rest) ≺[MonomialOrder.lex]
          MonomialOrder.lex.degree (MvPolynomial.monomial (monomialFinsupp t.2) t.1) := by
        obtain ⟨s, hs, hseq⟩ := exists_of_mem_support (MonomialOrder.lex.degree_mem_support h0)
        rw [hM, ← hseq]
        exact toSyn_lt_of_mvLexLt (hall s hs)
      rw [MonomialOrder.degree_add_of_lt hlt, MonomialOrder.leadingCoeff_add_of_lt hlt, hM,
        MonomialOrder.leadingCoeff_monomial]
      exact ⟨rfl, rfl⟩

/-! ## S-polynomials -/

/-- Mathlib's S-polynomial of two sparse polynomials whose first terms lead. -/
def mvSPolynomial (f g : MvPoly n) : MvPoly n :=
  mvSub (mvMulPoly [(headCoeff g, mvTsub (headMonomial g) (headMonomial f))] f)
    (mvMulPoly [(headCoeff f, mvTsub (headMonomial f) (headMonomial g))] g)

/-- `mvSPolynomial` computes the S-polynomial for `MonomialOrder.lex` when both first terms
lead. -/
theorem toMvPolynomial_mvSPolynomial {f g : MvPoly n} (hf : headLeads f = true)
    (hg : headLeads g = true) :
    toMvPolynomial (mvSPolynomial f g) =
      MonomialOrder.lex.sPolynomial (toMvPolynomial f) (toMvPolynomial g) := by
  obtain ⟨df, cf⟩ := degree_toMvPolynomial_of_headLeads hf
  obtain ⟨dg, cg⟩ := degree_toMvPolynomial_of_headLeads hg
  rw [mvSPolynomial, toMvPolynomial_mvSub, toMvPolynomial_mvMulPoly, toMvPolynomial_mvMulPoly,
    toMvPolynomial_single, toMvPolynomial_single, monomialFinsupp_mvTsub, monomialFinsupp_mvTsub,
    MonomialOrder.sPolynomial, df, dg, cf, cg]

/-- Every term `t` of every `qₗ` has `t · lm(gₗ)` lexicographically below `bound`. -/
def quotientDegreesBelow (bound : MvMonomial n) : List (MvPoly n) → List (MvPoly n) → Bool
  | [], _ => true
  | _ :: _, [] => true
  | q :: qs, g :: gs =>
    q.all (fun t ↦ mvLexLt (mvMul t.2 (headMonomial g)) bound) && quotientDegreesBelow bound qs gs

/-- If `quotientDegreesBelow bound qs gs` holds, then for every position `l < gs.length` and every
term `t` of `qs.getD l []`, the product `mvMul t.2 (headMonomial gₗ)` is below `bound` in
`mvLexLt`. -/
theorem quotientDegreesBelow_spec (bound : MvMonomial n) :
    ∀ (qs gs : List (MvPoly n)), quotientDegreesBelow bound qs gs = true →
      ∀ (l : ℕ), l < gs.length → ∀ t ∈ qs.getD l [],
        mvLexLt (mvMul t.2 (headMonomial (gs.getD l []))) bound = true
  | [], _, _, _, _, _, ht => by simp at ht
  | _ :: _, [], _, _, hl, _, _ => by simp at hl
  | _ :: _, _ :: _, h, 0, _, t, ht => by
    simp only [quotientDegreesBelow, Bool.and_eq_true, List.all_eq_true] at h
    simp only [List.getD_cons_zero] at ht ⊢
    exact h.1 t ht
  | _ :: qs, _ :: gs, h, l + 1, hl, t, ht => by
    simp only [quotientDegreesBelow, Bool.and_eq_true, List.all_eq_true] at h
    simp only [List.getD_cons_succ] at ht ⊢
    exact quotientDegreesBelow_spec bound qs gs h.2 l (by simpa using hl) t ht

/-- The certificate of one pair: `S(f, g) = ∑ qₗ Gₗ` with every `qₗ Gₗ` below the least common
multiple of the leading monomials. -/
def pairCertified (G qs : List (MvPoly n)) (f g : MvPoly n) : Bool :=
  combinationHolds (mvSPolynomial f g) qs G &&
    quotientDegreesBelow (mvLcm (headMonomial f) (headMonomial g)) qs G

/-- The Gröbner certificate of a list: every element has a leading first term and every pair
`i < j` is certified by the quotients `cert[i][j]`. -/
def groebnerCertified (G : List (MvPoly n)) (cert : List (List (List (MvPoly n)))) : Bool :=
  (List.range G.length).all fun i ↦ headLeads (G.getD i []) &&
    (List.range G.length).all fun j ↦
      if i < j then pairCertified G ((cert.getD i []).getD j []) (G.getD i []) (G.getD j [])
      else true

/-- If `groebnerCertified G cert` holds, every element of `G` has a leading first term
(`headLeads`). -/
theorem headLeads_of_groebnerCertified {G : List (MvPoly n)}
    {cert : List (List (List (MvPoly n)))} (hc : groebnerCertified G cert = true) {i : ℕ}
    (hi : i < G.length) : headLeads (G.getD i []) = true := by
  have h := List.all_eq_true.mp hc i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- If `groebnerCertified G cert` holds, then for all positions `i < j` of `G` the quotients
`cert[i][j]` certify the pair `(G[i], G[j])` (`pairCertified`). -/
theorem pairCertified_of_groebnerCertified {G : List (MvPoly n)}
    {cert : List (List (List (MvPoly n)))} (hc : groebnerCertified G cert = true) {i j : ℕ}
    (hi : i < G.length) (hj : j < G.length) (hij : i < j) :
    pairCertified G ((cert.getD i []).getD j []) (G.getD i []) (G.getD j []) = true := by
  have h := List.all_eq_true.mp hc i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  simpa only [hij, ↓reduceIte] using h.2 j hj

/-- The polynomials of a list as a family indexed by positions. -/
noncomputable def listFamily (G : List (MvPoly n)) (l : Fin G.length) : MvPolynomial (Fin n) ℚ :=
  toMvPolynomial (G.getD l.val [])

/-- A Gröbner certificate gives the hypothesis of Buchberger's criterion
`CAS.Polynomial.Buchberger.exists_leadingTerm_dvd_of_sPolynomial` for the family of the list. -/
theorem sPolynomial_listFamily_of_groebnerCertified {G : List (MvPoly n)}
    {cert : List (List (List (MvPoly n)))} (hc : groebnerCertified G cert = true)
    (i j : Fin G.length) (hij : i < j) :
    ∃ q : Fin G.length → MvPolynomial (Fin n) ℚ,
      MonomialOrder.lex.sPolynomial (listFamily G i) (listFamily G j) = ∑ l, q l * listFamily G l ∧
      ∀ l, ∀ t ∈ (q l).support,
        MonomialOrder.lex.toSyn (t + MonomialOrder.lex.degree (listFamily G l)) <
          MonomialOrder.lex.toSyn (MonomialOrder.lex.degree (listFamily G i) ⊔
            MonomialOrder.lex.degree (listFamily G j)) := by
  have hp := pairCertified_of_groebnerCertified hc i.isLt j.isLt (Fin.lt_def.mp hij)
  simp only [pairCertified, Bool.and_eq_true] at hp
  obtain ⟨hcomb, hdeg⟩ := hp
  refine ⟨fun l ↦ toMvPolynomial (((cert.getD i []).getD j []).getD l.val []), ?_, ?_⟩
  · have e := toMvPolynomial_eq_sum_of_combinationHolds hcomb
    rw [toMvPolynomial_mvSPolynomial (headLeads_of_groebnerCertified hc i.isLt)
      (headLeads_of_groebnerCertified hc j.isLt), ← Fin.sum_univ_eq_sum_range] at e
    exact e
  · intro l t ht
    obtain ⟨u, hu, rfl⟩ := exists_of_mem_support ht
    have hdl := (degree_toMvPolynomial_of_headLeads (headLeads_of_groebnerCertified hc l.isLt)).1
    have hdi := (degree_toMvPolynomial_of_headLeads (headLeads_of_groebnerCertified hc i.isLt)).1
    have hdj := (degree_toMvPolynomial_of_headLeads (headLeads_of_groebnerCertified hc j.isLt)).1
    simp only [listFamily]
    simp only [hdl, hdi, hdj]
    rw [← monomialFinsupp_mvMul, ← monomialFinsupp_mvLcm]
    exact toSyn_lt_of_mvLexLt (quotientDegreesBelow_spec _ _ _ hdeg l.val l.isLt u hu)

/-- The range of the family of a list is a set `S` that is the image of the list. -/
theorem range_listFamily {G : List (MvPoly n)} {S : Set (MvPolynomial (Fin n) ℚ)}
    (hS : ∀ f, f ∈ S ↔ ∃ r ∈ G, toMvPolynomial r = f) : Set.range (listFamily G) = S := by
  ext f
  rw [hS, Set.mem_range]
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨G.getD l.val [], by rw [List.getD_eq_getElem _ _ l.isLt]; exact List.getElem_mem _,
      rfl⟩
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hr
    exact ⟨⟨l, hl⟩, by rw [listFamily, List.getD_eq_getElem _ _ hl]⟩

/-! ## Bridge to written polynomials -/

/-- `∏ xᵢ ^ eᵢ` over two lists, as far as both go. -/
noncomputable def listMonomial : List (MvPolynomial (Fin n) ℚ) → List ℕ → MvPolynomial (Fin n) ℚ
  | _, [] => 1
  | [], _ :: _ => 1
  | x :: xs, e :: es => x ^ e * listMonomial xs es

/-- `∑ C c * ∏ xᵢ ^ eᵢ` over a list of coefficients with exponent lists. -/
noncomputable def listPolynomial (xs : List (MvPolynomial (Fin n) ℚ)) :
    List (ℚ × List ℕ) → MvPolynomial (Fin n) ℚ
  | [] => 0
  | t :: rest => MvPolynomial.C t.1 * listMonomial xs t.2 + listPolynomial xs rest

/-- For a family `x` of `k` polynomials and an exponent list `es`, the product of `x i ^ es[i]`
(with exponent `0` past the end of `es`) is `listMonomial (List.ofFn x) es`. -/
theorem prod_ofFn_pow_getD : ∀ (k : ℕ) (x : Fin k → MvPolynomial (Fin n) ℚ) (es : List ℕ),
    (List.ofFn fun i ↦ x i ^ es.getD i.val 0).prod = listMonomial (List.ofFn x) es
  | 0, _, [] => by simp [listMonomial]
  | 0, _, _ :: _ => by simp [listMonomial]
  | _ + 1, _, [] => by simp [listMonomial]
  | k + 1, x, e :: es => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons]
    simp only [listMonomial, Fin.val_zero, List.getD_cons_zero, Fin.val_succ,
      List.getD_cons_succ]
    rw [← prod_ofFn_pow_getD k (fun i ↦ x i.succ) es]

/-- The monomial with coefficient `c` and the exponents of the list `es` is
`C c * listMonomial (List.ofFn X) es`, the product written over the variables
`X 0, …, X (n - 1)`. -/
theorem monomial_monomialFinsupp_mvMonomialOfList (c : ℚ) (es : List ℕ) :
    MvPolynomial.monomial (monomialFinsupp (mvMonomialOfList (n := n) es)) c =
      MvPolynomial.C c * listMonomial (List.ofFn MvPolynomial.X) es := by
  rw [MvPolynomial.monomial_eq,
    Finsupp.prod_fintype _ (fun i e ↦ (MvPolynomial.X i : MvPolynomial (Fin n) ℚ) ^ e)
      (fun i ↦ pow_zero _)]
  simp only [monomialFinsupp_apply, mvMonomialOfList]
  rw [← List.prod_ofFn, prod_ofFn_pow_getD]

/-- The polynomial of `ofTerms raw` is `listPolynomial xs raw` when `xs` lists the variables
`X 0, …, X (n - 1)`. -/
theorem toMvPolynomial_ofTerms (xs : List (MvPolynomial (Fin n) ℚ))
    (hxs : List.ofFn MvPolynomial.X = xs) (raw : List (ℚ × List ℕ)) :
    toMvPolynomial (ofTerms raw) = listPolynomial xs raw := by
  subst hxs
  induction raw with
  | nil => rfl
  | cons t rest ih =>
    change MvPolynomial.monomial (monomialFinsupp (mvMonomialOfList t.2)) t.1 +
        toMvPolynomial (ofTerms rest) =
      MvPolynomial.C t.1 * listMonomial (List.ofFn MvPolynomial.X) t.2 +
        listPolynomial (List.ofFn MvPolynomial.X) rest
    rw [monomial_monomialFinsupp_mvMonomialOfList, ih]

/-- The set `{g}` is the image of `[r]` when `toMvPolynomial r = g`. -/
theorem mem_singleton_iff_exists_toMvPolynomial {r : MvPoly n} {g : MvPolynomial (Fin n) ℚ}
    (h : toMvPolynomial r = g) :
    ∀ f, f ∈ ({g} : Set (MvPolynomial (Fin n) ℚ)) ↔ ∃ s ∈ [r], toMvPolynomial s = f := by
  intro f
  simp only [Set.mem_singleton_iff, List.mem_singleton, exists_eq_left, h]
  exact eq_comm

/-- The set `insert g S` is the image of `r :: G` when `toMvPolynomial r = g` and `S` is the
image of `G`. -/
theorem mem_insert_iff_exists_toMvPolynomial {r : MvPoly n} {G : List (MvPoly n)}
    {g : MvPolynomial (Fin n) ℚ} {S : Set (MvPolynomial (Fin n) ℚ)} (h : toMvPolynomial r = g)
    (hS : ∀ f, f ∈ S ↔ ∃ s ∈ G, toMvPolynomial s = f) :
    ∀ f, f ∈ insert g S ↔ ∃ s ∈ r :: G, toMvPolynomial s = f := by
  intro f
  rw [Set.mem_insert_iff, hS f]
  simp only [List.mem_cons, exists_eq_or_imp, h]
  exact or_congr_left eq_comm

/-! ## The Gröbner property -/

/-- A list `G` of sparse polynomials with a Gröbner certificate is a Gröbner basis for the
lexicographic order: the leading term of every nonzero element of the ideal of the polynomials
of `G` is divisible by the leading term of one of them. -/
theorem isGroebner_of_groebnerCertified {G : List (MvPoly n)}
    {cert : List (List (List (MvPoly n)))} (hc : groebnerCertified G cert = true)
    {S : Set (MvPolynomial (Fin n) ℚ)} (hS : ∀ f, f ∈ S ↔ ∃ r ∈ G, toMvPolynomial r = f) :
    ∀ p ∈ Ideal.span S, p ≠ 0 →
      ∃ g ∈ S, MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm p := by
  rw [← range_listFamily hS]
  intro p hp hp0
  obtain ⟨i, hi⟩ := CAS.Polynomial.Buchberger.exists_leadingTerm_dvd_of_sPolynomial
    (sPolynomial_listFamily_of_groebnerCertified hc) hp hp0
  exact ⟨listFamily G i, Set.mem_range_self i, hi⟩

end CAS.Polynomial.Sparse

end

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-!
# Buchberger's criterion

A family `g` of multivariate polynomials over a field is a Gröbner basis for a monomial order
`m` when the leading term of every nonzero element of the ideal it spans is divisible by the
leading term of a member of the family. We prove Buchberger's criterion: this holds as soon as
every S-polynomial `m.sPolynomial (g i) (g j)` has a standard representation `∑ l, q l * g l`,
one in which every term `t` of every `q l` has `t + m.degree (g l)` strictly below
`m.degree (g i) ⊔ m.degree (g j)`. A division of the S-polynomial by the family that leaves the
remainder zero gives such a representation, and the bases of `#cas [groebner]` are certified this
way.

## Main results

* `CAS.Polynomial.Buchberger.exists_degree_le_of_sPolynomial`: under the criterion, every nonzero
  `p` of the ideal has a nonzero member `g i` with `m.degree (g i) ≤ m.degree p`.
* `CAS.Polynomial.Buchberger.exists_degree_le_of_sPolynomial_lt`: the same from the pairs `i < j`
  of a linearly ordered index type.
* `CAS.Polynomial.Buchberger.exists_leadingTerm_dvd_of_sPolynomial`: the conclusion with leading
  terms, `m.leadingTerm (g i) ∣ m.leadingTerm p`.

## Implementation notes

Mathlib has S-polynomials and the cancellation lemma `MonomialOrder.sPolynomial_decomposition'`,
but no Gröbner bases, so we prove the criterion here. Buchberger's own proof shows, by induction
over the power products, that every polynomial reduces to a unique normal form; we take the route
through the cancellation lemma instead, which needs only a standard representation of every
S-polynomial. For `δ` in `m.syn` we work in the `K`-span of the products `monomial s 1 * g i`
of degree at most `δ`, and in the span of those of degree below `δ`. An element of the first span
is a combination of members shifted to the degree `δ` plus an element of the second. When its
coefficient at `δ` vanishes, the cancellation lemma writes the shifted part as a combination of
S-polynomials of shifted members, `MonomialOrder.sPolynomial_monomial_mul` takes the shifts out,
and the standard representations put the whole element below `δ`. Well-founded induction on `δ`
ends at a member whose leading monomial divides that of `p`.

## References

* Bruno Buchberger, "Ein algorithmisches Kriterium für die Lösbarkeit eines algebraischen
  Gleichungssystems", *Aequationes Mathematicae* 4 (1970), pp. 374-383,
  <https://doi.org/10.1007/BF01844169>. Section 2.3 defines the S-polynomials, and Section 3.1
  proves, for power products ordered by degree and then lexicographically, that when every
  S-polynomial of a basis reduces to zero, every reduction of a polynomial by the basis ends at the
  same normal form.
* Bruno Buchberger, "An Algorithmic Criterion for the Solvability of a System of Algebraic
  Equations", translated by Michael Abramson and Robert Lumbert, in Bruno Buchberger and Franz
  Winkler (eds.), *Gröbner Bases and Applications*, London Mathematical Society Lecture Note
  Series 251, Cambridge University Press, Cambridge, 1998,
  <https://doi.org/10.1017/CBO9780511565847.034>. The English translation of the 1970 article.
-/

public section

namespace CAS.Polynomial.Buchberger

open MvPolynomial
open scoped MonomialOrder

variable {σ K ι : Type*} [Field K] {m : MonomialOrder σ} {g : ι → MvPolynomial σ K}

variable (m g) in
/-- The products `monomial s 1 * g i` whose degree `s + degree (g i)` satisfies `P`. -/
private def products (P : m.syn → Prop) : Set (MvPolynomial σ K) :=
  {f | ∃ i s, f = monomial s 1 * g i ∧ P (m.toSyn (s + m.degree (g i)))}

variable (m g) in
/-- `g i` shifted to the degree `d`. -/
private noncomputable def shifted (d : σ →₀ ℕ) (i : ι) : MvPolynomial σ K :=
  monomial (d - m.degree (g i)) 1 * g i

private theorem smul_monomial_one_mul (c : K) (s : σ →₀ ℕ) (f : MvPolynomial σ K) :
    c • (monomial s 1 * f) = monomial s c * f := by
  rw [← smul_mul_assoc, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

private theorem smul_mem_spanned {P : m.syn → Prop} (c : K) (i : ι) (s : σ →₀ ℕ)
    (h : P (m.toSyn (s + m.degree (g i)))) :
    monomial s c * g i ∈ Submodule.span K (products m g P) := by
  rw [← smul_monomial_one_mul]
  exact Submodule.smul_mem _ c (Submodule.subset_span
    (show monomial s 1 * g i ∈ products m g P from ⟨i, s, rfl, h⟩))

private theorem monomial_mul_mem {P Q : m.syn → Prop} {u : σ →₀ ℕ} (c : K)
    (hPQ : ∀ x, P x → Q (m.toSyn u + x)) {f : MvPolynomial σ K}
    (hf : f ∈ Submodule.span K (products m g P)) :
    monomial u c * f ∈ Submodule.span K (products m g Q) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, s, rfl, hs⟩ := hf
    rw [← mul_assoc, MvPolynomial.monomial_mul_monomial, mul_one]
    refine smul_mem_spanned c i (u + s) ?_
    rw [add_assoc, map_add]
    exact hPQ _ hs
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hx

private theorem upTo_mono {δ δ' : m.syn} (h : δ ≤ δ') {f : MvPolynomial σ K}
    (hf : f ∈ Submodule.span K (products m g (· ≤ δ))) :
    f ∈ Submodule.span K (products m g (· ≤ δ')) := by
  refine Submodule.span_mono ?_ hf
  rintro _ ⟨i, s, rfl, hs⟩
  exact ⟨i, s, rfl, le_trans hs h⟩

private theorem degree_le_of_mem {δ : m.syn} {f : MvPolynomial σ K}
    (hf : f ∈ Submodule.span K (products m g (· ≤ δ))) : m.toSyn (m.degree f) ≤ δ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, s, rfl, hs⟩ := hf
    refine m.degree_mul_le.trans (le_trans ?_ hs)
    rw [map_add, map_add]
    exact add_le_add (m.degree_monomial_le _) le_rfl
  | zero =>
    rw [m.degree_zero, map_zero]
    exact bot_le
  | add x y _ _ hx hy => exact m.degree_add_le.trans (sup_le hx hy)
  | smul a x _ hx => exact m.degree_smul_le.trans hx

private theorem exists_lt_of_mem_below {δ : m.syn} {f : MvPolynomial σ K}
    (hf : f ∈ Submodule.span K (products m g (· < δ))) :
    f = 0 ∨ ∃ δ' < δ, f ∈ Submodule.span K (products m g (· ≤ δ')) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, s, rfl, hs⟩ := hf
    exact Or.inr ⟨_, hs, Submodule.subset_span
      (show monomial s 1 * g i ∈ products m g (· ≤ m.toSyn (s + m.degree (g i))) from
        ⟨i, s, rfl, le_rfl⟩)⟩
  | zero => exact Or.inl rfl
  | add x y _ _ hx hy =>
    rcases hx with rfl | ⟨δ₁, h₁, hx⟩
    · rwa [zero_add]
    rcases hy with rfl | ⟨δ₂, h₂, hy⟩
    · rw [add_zero]
      exact Or.inr ⟨δ₁, h₁, hx⟩
    exact Or.inr ⟨max δ₁ δ₂, max_lt h₁ h₂, Submodule.add_mem _
      (upTo_mono (le_max_left _ _) hx) (upTo_mono (le_max_right _ _) hy)⟩
  | smul a x _ hx =>
    rcases hx with rfl | ⟨δ', h', hx⟩
    · exact Or.inl (smul_zero a)
    · exact Or.inr ⟨δ', h', Submodule.smul_mem _ a hx⟩

private theorem coeff_eq_zero_of_mem_below {δ : m.syn} {f : MvPolynomial σ K}
    (hf : f ∈ Submodule.span K (products m g (· < δ))) : f.coeff (m.toSyn.symm δ) = 0 := by
  rcases exists_lt_of_mem_below hf with rfl | ⟨δ', h', hf'⟩
  · rfl
  · apply m.coeff_eq_zero_of_lt
    rw [AddEquiv.apply_symm_apply]
    exact lt_of_le_of_lt (degree_le_of_mem hf') h'

private theorem mul_mem_below {ε : m.syn} {q : MvPolynomial σ K} {l : ι}
    (h : ∀ t ∈ q.support, m.toSyn (t + m.degree (g l)) < ε) :
    q * g l ∈ Submodule.span K (products m g (· < ε)) := by
  rw [q.as_sum, Finset.sum_mul]
  exact Submodule.sum_mem _ fun t ht ↦ smul_mem_spanned (P := (· < ε)) _ l t (h t ht)

variable [Fintype ι]

private theorem exists_decomposition {δ : m.syn} {f : MvPolynomial σ K}
    (hf : f ∈ Submodule.span K (products m g (· ≤ δ))) :
    ∃ c : ι → K, (∀ i, c i ≠ 0 → m.degree (g i) ≤ m.toSyn.symm δ) ∧
      f - ∑ i, c i • shifted m g (m.toSyn.symm δ) i ∈
        Submodule.span K (products m g (· < δ)) := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, s, rfl, hs⟩ := hf
    rcases lt_or_eq_of_le hs with hlt | heq
    · refine ⟨0, fun i hi ↦ (hi rfl).elim, ?_⟩
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, sub_zero]
      exact Submodule.subset_span (show monomial s 1 * g i ∈ products m g (· < δ) from
        ⟨i, s, rfl, hlt⟩)
    · have hd : s + m.degree (g i) = m.toSyn.symm δ := by
        rw [← heq, AddEquiv.symm_apply_apply]
      refine ⟨fun j ↦ if j = i then 1 else 0, fun j hj ↦ ?_, ?_⟩
      · obtain rfl : j = i := by
          by_contra hne
          exact hj (ite_eq_right hne)
        rw [← hd]
        exact le_add_self
      · simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
          ↓reduceIte, shifted]
        have hs' : s = m.toSyn.symm δ - m.degree (g i) := by
          rw [← hd, add_tsub_cancel_right]
        rw [← hs', sub_self]
        exact Submodule.zero_mem _
  | zero =>
    refine ⟨0, fun i hi ↦ (hi rfl).elim, ?_⟩
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, sub_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    obtain ⟨c₁, hc₁, h₁⟩ := hx
    obtain ⟨c₂, hc₂, h₂⟩ := hy
    refine ⟨c₁ + c₂, fun i hi ↦ ?_, ?_⟩
    · by_cases h : c₁ i = 0
      · rw [Pi.add_apply, h, zero_add] at hi
        exact hc₂ i hi
      · exact hc₁ i h
    · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, add_sub_add_comm]
      exact Submodule.add_mem _ h₁ h₂
  | smul a x _ hx =>
    obtain ⟨c, hc, h⟩ := hx
    refine ⟨a • c, fun i hi ↦ hc i fun h0 ↦ hi (by rw [Pi.smul_apply, h0, smul_zero]), ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum, ← smul_sub]
    exact Submodule.smul_mem _ a h

private theorem sum_mem_upTo {δ : m.syn} {c : ι → K}
    (hc : ∀ i, c i ≠ 0 → m.degree (g i) ≤ m.toSyn.symm δ) :
    ∑ i, c i • shifted m g (m.toSyn.symm δ) i ∈ Submodule.span K (products m g (· ≤ δ)) := by
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  by_cases h : c i = 0
  · rw [h, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨i, m.toSyn.symm δ - m.degree (g i), rfl, ?_⟩
    exact ((congrArg (⇑m.toSyn) (tsub_add_cancel_of_le (hc i h))).trans
      (m.toSyn.apply_symm_apply δ)).le

private theorem sum_mem_below
    (hS : ∀ i j, ∃ q : ι → MvPolynomial σ K,
      m.sPolynomial (g i) (g j) = ∑ l, q l * g l ∧
      ∀ l, ∀ t ∈ (q l).support,
        m.toSyn (t + m.degree (g l)) < m.toSyn (m.degree (g i) ⊔ m.degree (g j)))
    {δ : m.syn} {c : ι → K} (hc : ∀ i, c i ≠ 0 → m.degree (g i) ≤ m.toSyn.symm δ)
    (hcoeff : (∑ i, c i • shifted m g (m.toSyn.symm δ) i).coeff (m.toSyn.symm δ) = 0) :
    ∑ i, c i • shifted m g (m.toSyn.symm δ) i ∈ Submodule.span K (products m g (· < δ)) := by
  classical
  by_cases hS0 : ∑ i, c i • shifted m g (m.toSyn.symm δ) i = 0
  · rw [hS0]
    exact Submodule.zero_mem _
  have hlt : m.toSyn (m.degree (∑ i, c i • shifted m g (m.toSyn.symm δ) i)) < δ := by
    refine lt_of_le_of_ne (degree_le_of_mem (sum_mem_upTo hc)) fun heq ↦ ?_
    have hdeg := m.toSyn.injective (heq.trans (m.toSyn.apply_symm_apply δ).symm)
    refine m.leadingCoeff_ne_zero_iff.mpr hS0 ?_
    rw [MonomialOrder.leadingCoeff, hdeg]
    exact hcoeff
  have hd : ∀ i ∈ Finset.univ,
      m.toSyn (m.degree (c i • shifted m g (m.toSyn.symm δ) i)) = δ ∨
        c i • shifted m g (m.toSyn.symm δ) i = 0 := by
    intro i _
    by_cases h : c i = 0 ∨ g i = 0
    · right
      rcases h with h | h
      · rw [h, zero_smul]
      · rw [shifted, h, mul_zero, smul_zero]
    · left
      rw [not_or] at h
      rw [shifted, smul_monomial_one_mul, m.degree_mul ((MvPolynomial.monomial_eq_zero
        (s := m.toSyn.symm δ - m.degree (g i))).not.mpr h.1) h.2, m.degree_monomial,
        ite_eq_right h.1, tsub_add_cancel_of_le (hc i h.1), AddEquiv.apply_symm_apply]
  obtain ⟨a, ha⟩ : ∃ a : ι → ι → K, ∑ i, c i • shifted m g (m.toSyn.symm δ) i =
      ∑ i, ∑ j, a i j • m.sPolynomial (c i • shifted m g (m.toSyn.symm δ) i)
        (c j • shifted m g (m.toSyn.symm δ) j) :=
    m.sPolynomial_decomposition' _ hd hlt
  rw [ha]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ ?_
  rcases eq_or_ne (c i) 0 with hi | hi
  · rw [hi, zero_smul, m.sPolynomial_left_zero]
    exact Submodule.zero_mem _
  rcases eq_or_ne (c j) 0 with hj | hj
  · rw [hj, zero_smul, m.sPolynomial_right_zero]
    exact Submodule.zero_mem _
  rw [shifted, shifted, smul_monomial_one_mul, smul_monomial_one_mul, m.sPolynomial_monomial_mul,
    tsub_add_cancel_of_le (hc i hi), tsub_add_cancel_of_le (hc j hj), sup_idem]
  obtain ⟨q, hq, hqdeg⟩ := hS i j
  rw [hq, Finset.mul_sum]
  refine Submodule.sum_mem _ fun l _ ↦ ?_
  have hl : q l * g l ∈ Submodule.span K
      (products m g (· < m.toSyn (m.degree (g i) ⊔ m.degree (g j)))) := mul_mem_below (hqdeg l)
  have h1 : m.toSyn (m.toSyn.symm δ - m.degree (g i) ⊔ m.degree (g j)) +
      m.toSyn (m.degree (g i) ⊔ m.degree (g j)) = δ := by
    rw [← map_add m.toSyn, tsub_add_cancel_of_le (sup_le (hc i hi) (hc j hj)),
      AddEquiv.apply_symm_apply]
  refine monomial_mul_mem _ ?_ hl
  intro x hx
  exact lt_of_lt_of_eq (add_lt_add_of_le_of_lt le_rfl hx) h1

private theorem exists_degree_le_of_mem
    (hS : ∀ i j, ∃ q : ι → MvPolynomial σ K,
      m.sPolynomial (g i) (g j) = ∑ l, q l * g l ∧
      ∀ l, ∀ t ∈ (q l).support,
        m.toSyn (t + m.degree (g l)) < m.toSyn (m.degree (g i) ⊔ m.degree (g j))) :
    ∀ δ : m.syn, ∀ p ∈ Submodule.span K (products m g (· ≤ δ)), p ≠ 0 →
      ∃ i, g i ≠ 0 ∧ m.degree (g i) ≤ m.degree p := by
  intro δ
  induction δ using WellFoundedLT.induction with
  | ind δ ih =>
    intro p hp hp0
    obtain ⟨c, hc, hrest⟩ := exists_decomposition hp
    by_cases hcoeff : p.coeff (m.toSyn.symm δ) = 0
    · have hsum : (∑ i, c i • shifted m g (m.toSyn.symm δ) i).coeff (m.toSyn.symm δ) = 0 := by
        have h := coeff_eq_zero_of_mem_below hrest
        rw [MvPolynomial.coeff_sub, hcoeff, zero_sub, neg_eq_zero] at h
        exact h
      have hbelow : p ∈ Submodule.span K (products m g (· < δ)) := by
        rw [← sub_add_cancel p (∑ i, c i • shifted m g (m.toSyn.symm δ) i)]
        exact Submodule.add_mem _ hrest (sum_mem_below hS hc hsum)
      rcases exists_lt_of_mem_below hbelow with h0 | ⟨δ', hδ', hp'⟩
      · exact absurd h0 hp0
      · exact ih δ' hδ' p hp' hp0
    · have hdeg : m.degree p = m.toSyn.symm δ := by
        apply m.toSyn.injective
        rw [AddEquiv.apply_symm_apply]
        exact le_antisymm (degree_le_of_mem hp)
          ((m.toSyn.apply_symm_apply δ).symm.trans_le
            (m.le_degree (MvPolynomial.mem_support_iff.mpr hcoeff)))
      have hsum : (∑ i, c i • shifted m g (m.toSyn.symm δ) i).coeff (m.toSyn.symm δ) ≠ 0 := by
        have h := coeff_eq_zero_of_mem_below hrest
        rw [MvPolynomial.coeff_sub, sub_eq_zero] at h
        rwa [← h]
      rw [MvPolynomial.coeff_sum] at hsum
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
      have hi' : (c i • shifted m g (m.toSyn.symm δ) i).coeff (m.toSyn.symm δ) ≠ 0 := hi
      have hci : c i ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hi'
        exact hi' rfl
      have hgi : g i ≠ 0 := by
        intro h0
        rw [shifted, h0, mul_zero, smul_zero] at hi'
        exact hi' rfl
      exact ⟨i, hgi, (hc i hci).trans hdeg.ge⟩

omit [Fintype ι] in
private theorem exists_mem_upTo {p : MvPolynomial σ K} (hp : p ∈ Ideal.span (Set.range g)) :
    ∃ δ, p ∈ Submodule.span K (products m g (· ≤ δ)) := by
  induction hp using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, rfl⟩ := hf
    have h := smul_mem_spanned (m := m) (g := g) (P := (· ≤ m.toSyn (0 + m.degree (g i))))
      (1 : K) i 0 le_rfl
    rw [← MvPolynomial.C_apply, MvPolynomial.C_1, one_mul] at h
    exact ⟨_, h⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨δ₁, h₁⟩ := hx
    obtain ⟨δ₂, h₂⟩ := hy
    exact ⟨max δ₁ δ₂, Submodule.add_mem _ (upTo_mono (le_max_left _ _) h₁)
      (upTo_mono (le_max_right _ _) h₂)⟩
  | smul a x _ hx =>
    obtain ⟨δ, h⟩ := hx
    rw [smul_eq_mul]
    induction a using MvPolynomial.induction_on' with
    | monomial u b =>
      refine ⟨m.toSyn u + δ, monomial_mul_mem (P := (· ≤ δ)) b ?_ h⟩
      intro y hy
      exact add_le_add le_rfl hy
    | add p q hp hq =>
      obtain ⟨δ₁, h₁⟩ := hp
      obtain ⟨δ₂, h₂⟩ := hq
      rw [add_mul]
      exact ⟨max δ₁ δ₂, Submodule.add_mem _ (upTo_mono (le_max_left _ _) h₁)
        (upTo_mono (le_max_right _ _) h₂)⟩

/-- Buchberger's criterion: if every S-polynomial `m.sPolynomial (g i) (g j)` of a finite family
is a combination `∑ l, q l * g l` in which every term `t` of every `q l` has
`t + m.degree (g l) ≺[m] m.degree (g i) ⊔ m.degree (g j)`, then every nonzero `p` of the ideal
of the family has a nonzero member `g i` with `m.degree (g i) ≤ m.degree p`, so that the leading
monomial of `g i` divides that of `p`. -/
theorem exists_degree_le_of_sPolynomial
    (hS : ∀ i j, ∃ q : ι → MvPolynomial σ K,
      m.sPolynomial (g i) (g j) = ∑ l, q l * g l ∧
      ∀ l, ∀ t ∈ (q l).support, t + m.degree (g l) ≺[m] m.degree (g i) ⊔ m.degree (g j))
    {p : MvPolynomial σ K} (hp : p ∈ Ideal.span (Set.range g)) (hp0 : p ≠ 0) :
    ∃ i, g i ≠ 0 ∧ m.degree (g i) ≤ m.degree p := by
  obtain ⟨δ, hδ⟩ := exists_mem_upTo (m := m) hp
  exact exists_degree_le_of_mem hS δ p hδ hp0

/-- Buchberger's criterion for a family indexed by a linear order, from the pairs `i < j`. -/
theorem exists_degree_le_of_sPolynomial_lt [LinearOrder ι]
    (hS : ∀ i j, i < j → ∃ q : ι → MvPolynomial σ K,
      m.sPolynomial (g i) (g j) = ∑ l, q l * g l ∧
      ∀ l, ∀ t ∈ (q l).support, t + m.degree (g l) ≺[m] m.degree (g i) ⊔ m.degree (g j))
    {p : MvPolynomial σ K} (hp : p ∈ Ideal.span (Set.range g)) (hp0 : p ≠ 0) :
    ∃ i, g i ≠ 0 ∧ m.degree (g i) ≤ m.degree p := by
  refine exists_degree_le_of_sPolynomial (fun i j ↦ ?_) hp hp0
  rcases lt_trichotomy i j with h | rfl | h
  · exact hS i j h
  · refine ⟨0, ?_, fun l t ht ↦ ?_⟩
    · rw [m.sPolynomial_self]
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    · simp at ht
  · obtain ⟨q, hq, hdeg⟩ := hS j i h
    refine ⟨-q, ?_, fun l t ht ↦ ?_⟩
    · rw [m.sPolynomial_antisymm, hq]
      simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    · rw [Pi.neg_apply, MvPolynomial.support_neg] at ht
      rw [sup_comm]
      exact hdeg l t ht

/-- Buchberger's criterion as the defining property of a Gröbner basis: under the hypothesis of
`exists_degree_le_of_sPolynomial_lt`, the leading term of every nonzero `p` of the ideal of the
family is divisible by the leading term of a member of the family. -/
theorem exists_leadingTerm_dvd_of_sPolynomial [LinearOrder ι]
    (hS : ∀ i j, i < j → ∃ q : ι → MvPolynomial σ K,
      m.sPolynomial (g i) (g j) = ∑ l, q l * g l ∧
      ∀ l, ∀ t ∈ (q l).support, t + m.degree (g l) ≺[m] m.degree (g i) ⊔ m.degree (g j))
    {p : MvPolynomial σ K} (hp : p ∈ Ideal.span (Set.range g)) (hp0 : p ≠ 0) :
    ∃ i, m.leadingTerm (g i) ∣ m.leadingTerm p := by
  obtain ⟨i, hgi, hle⟩ := exists_degree_le_of_sPolynomial_lt hS hp hp0
  refine ⟨i, ?_⟩
  rw [MonomialOrder.leadingTerm, MonomialOrder.leadingTerm, MvPolynomial.monomial_dvd_monomial]
  exact ⟨Or.inr hle, (m.isUnit_leadingCoeff.mpr hgi).dvd⟩

end CAS.Polynomial.Buchberger

end

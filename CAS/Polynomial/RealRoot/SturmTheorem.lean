/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import CAS.Polynomial.RealRoot.SturmTheorem.Recurrence

/-!
# Sturm's theorem for accepted sparse certificates

For an accepted `SturmCertificate` of `p` and rational endpoints `a ≤ b` that are not roots of
`p`, `variationDifference a b` is the number of distinct real roots of `p` in the open interval
`(a, b)`, counted with Mathlib's `Polynomial.rootSet` (`variationDifference_eq_rootSet_ncard`).

The executable checker is in `Sturm.lean`; the function-variation and recurrence lemmas are in
`SturmTheorem/Variation.lean` and `SturmTheorem/Recurrence.lean`.

## Implementation notes

We follow Sturm's proof (nos. 3 to 6 of the memoir). At a root of `p`, `p` and `p'` have opposite
signs just before the root and equal signs just after it, so the variation drops by one there
(`eventually_simpleRoot_head_signs`, `accepted_first_root_variation_drop`; no. 4). Sturm reads
these signs off the Taylor expansion of `p` at the root; we use Mathlib's sign lemmas for a
function with nonzero derivative (`eventually_nhdsWithin_sign_eq_of_deriv_pos` and
`eventually_nhdsWithin_sign_eq_of_deriv_neg`). A zero of another member leaves the variation
unchanged (no. 5), so the variation is constant on intervals without roots of `p`
(`accepted_variation_eq_on_root_free_Icc`), and the unit drops add up over the finitely many
roots (`eq_add_ncard_of_finite_unit_drops`; no. 6).

The terminal of an accepted chain is a nonzero constant, so the theorem applies only to
polynomials without repeated roots. Basu, Pollack and Roy prove Sturm's theorem for every nonzero
polynomial [BPR, Theorem 2.62] as the case `Q = 1` of Tarski's theorem (Theorem 2.73), which they
derive from an identity for the Cauchy index (Theorem 2.70); we do not use that route.

## References

* C. Sturm, "Mémoire sur la résolution des équations numériques", *Mémoires présentés par divers
  savans à l'Académie royale des sciences de l'Institut de France, Sciences mathématiques et
  physiques* 6 (1835), pp. 271-318, <https://archive.org/details/mmoirespresent06scie>.
  The rule (no. 2) and its proof (nos. 3 to 6).
* Saugata Basu, Richard Pollack and Marie-Françoise Roy, *Algorithms in Real Algebraic Geometry*,
  2nd ed., Algorithms and Computation in Mathematics 10, Springer, Berlin, 2006,
  <https://doi.org/10.1007/3-540-33099-2>. Section 2.2.2 and Theorems 2.62, 2.70 and 2.73,
  numbered as in the authors' online version; Section 2.7 credits Sturm with Theorem 2.70 for
  square-free `P` and for `Q = P'`.
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Filter Set
open scoped Topology
open Sparse

namespace SturmCertificate

/--
The first member of an accepted certificate has exactly the same real
polynomial semantics as the requested sparse polynomial.
-/
theorem accepted_first_evalReal
    {polynomial first derivative : Sparse.Univariate}
    {tail : List Sparse.Univariate} {quotients : List Sparse.Univariate}
    (hvalid :
      valid polynomial
        { chain := first :: derivative :: tail
          quotients := quotients } = true)
    (x : ℝ) :
    Sparse.evalReal first x = Sparse.evalReal polynomial x := by
  simp only [← Sparse.eval_toRealPolynomial, Sparse.toRealPolynomial, first_polynomial hvalid]

/-- Function-level form of `accepted_first_evalReal`. -/
theorem accepted_first_evalReal_eq
    {polynomial first derivative : Sparse.Univariate}
    {tail : List Sparse.Univariate} {quotients : List Sparse.Univariate}
    (hvalid :
      valid polynomial
        { chain := first :: derivative :: tail
          quotients := quotients } = true) :
    Sparse.evalReal first = Sparse.evalReal polynomial :=
  funext (accepted_first_evalReal hvalid)

/--
The interpreted second polynomial of an accepted chain is the analytic
derivative of the requested first polynomial.
-/
theorem accepted_second_is_derivative
    {polynomial first derivative : Sparse.Univariate}
    {tail : List Sparse.Univariate} {quotients : List Sparse.Univariate}
    (hvalid :
      valid polynomial
        { chain := first :: derivative :: tail
          quotients := quotients } = true) (x : ℝ) :
    Sparse.evalReal derivative x =
      deriv (Sparse.evalReal polynomial) x := by
  rw [(Sparse.hasDerivAt_evalReal polynomial x).deriv]
  simp only [← Sparse.eval_toRealPolynomial, Sparse.toRealPolynomial, second_polynomial hvalid]

/--
An accepted chain gives the expected analytic derivative at every point,
stated as `HasDerivAt`.
-/
theorem accepted_first_hasDerivAt_second
    {polynomial first derivative : Sparse.Univariate}
    {tail : List Sparse.Univariate} {quotients : List Sparse.Univariate}
    (hvalid :
      valid polynomial
        { chain := first :: derivative :: tail
          quotients := quotients } = true) (x : ℝ) :
    HasDerivAt (Sparse.evalReal polynomial)
      (Sparse.evalReal derivative x) x := by
  rw [accepted_second_is_derivative hvalid x]
  exact (Sparse.hasDerivAt_evalReal polynomial x).differentiableAt.hasDerivAt

/--
At a simple root, the first function has the opposite sign to its derivative
on the left and the same sign on the right.
-/
theorem eventually_simpleRoot_head_signs
    {first derivative : ℝ → ℝ} {root : ℝ}
    (hderiv : HasDerivAt first (derivative root) root)
    (hroot : first root = 0)
    (hsimple : derivative root ≠ 0)
    (hcontinuous : ContinuousAt derivative root) :
    (∃ sign : SignType,
      sign ≠ 0 ∧
      (∀ᶠ x in 𝓝[<] root,
        SignType.sign (first x) = -sign ∧
          SignType.sign (derivative x) = sign) ∧
      (∀ᶠ x in 𝓝[>] root,
        SignType.sign (first x) = sign ∧
          SignType.sign (derivative x) = sign)) := by
  rcases lt_or_gt_of_ne hsimple with hnegative | hpositive
  · have hfirst := eventually_nhdsWithin_sign_eq_of_deriv_neg (by rwa [hderiv.deriv]) hroot
    have hderivative := hcontinuous.eventually_lt continuousAt_const hnegative
    refine ⟨-1, by decide, ?_, ?_⟩ <;>
      filter_upwards [nhdsWithin_le_nhds hfirst, nhdsWithin_le_nhds hderivative,
        self_mem_nhdsWithin] with x hxFirst hxDerivative hx
    · simp [hxFirst, sign_pos (sub_pos.mpr hx), sign_neg hxDerivative]
    · simp [hxFirst, sign_neg (sub_neg.mpr hx), sign_neg hxDerivative]
  · have hfirst := eventually_nhdsWithin_sign_eq_of_deriv_pos (by rwa [hderiv.deriv]) hroot
    have hderivative := continuousAt_const.eventually_lt hcontinuous hpositive
    refine ⟨1, by decide, ?_, ?_⟩ <;>
      filter_upwards [nhdsWithin_le_nhds hfirst, nhdsWithin_le_nhds hderivative,
        self_mem_nhdsWithin] with x hxFirst hxDerivative hx
    · simp [hxFirst, sign_neg (sub_neg.mpr hx), sign_pos hxDerivative]
    · simp [hxFirst, sign_pos (sub_pos.mpr hx), sign_pos hxDerivative]

/--
The local first-root step of Sturm's theorem.

If the variation of the suffix beginning with the derivative is locally
constant, crossing a simple root of the first function lowers the full
variation by exactly one.
-/
theorem firstPolynomial_simpleRoot_variation_drop
    {first derivative : ℝ → ℝ} {tail : List (ℝ → ℝ)}
    {root : ℝ} {suffixVariation : Nat}
    (hderiv : HasDerivAt first (derivative root) root)
    (hroot : first root = 0)
    (hsimple : derivative root ≠ 0)
    (hcontinuous : ContinuousAt derivative root)
    (hsuffix :
      ∀ᶠ x in 𝓝 root,
        functionVariationAt (derivative :: tail) x =
          suffixVariation) :
    (∀ᶠ x in 𝓝[<] root,
      functionVariationAt (first :: derivative :: tail) x =
        suffixVariation + 1) ∧
    (∀ᶠ x in 𝓝[>] root,
      functionVariationAt (first :: derivative :: tail) x =
        suffixVariation) := by
  obtain ⟨sign, hsign, hleft, hright⟩ :=
    eventually_simpleRoot_head_signs hderiv hroot hsimple hcontinuous
  constructor
  · filter_upwards [hleft, nhdsWithin_le_nhds hsuffix] with x hx hsuffixAt
    rw [functionVariationAt_cons_ne (by simpa using hsign) hsign hx.1 hx.2
      (mt SignType.neg_eq_self_iff.mp hsign), hsuffixAt]
  · filter_upwards [hright, nhdsWithin_le_nhds hsuffix] with x hx hsuffixAt
    rw [functionVariationAt_cons_eq hsign hx.1 hx.2, hsuffixAt]

/--
An accepted square-free Sturm recurrence has a unit downward variation jump at
each root of its first polynomial.

Unlike `firstPolynomial_simpleRoot_variation_drop`, this theorem has
no externally supplied suffix-constancy or simple-root hypothesis.  Both are
deduced from recurrence validity, including the checker's nonzero-constant
terminal condition via `recurrence_terminal_nonzero`.
-/
theorem accepted_first_root_variation_drop
    {polynomial first derivative : Sparse.Univariate}
    {tail : List Sparse.Univariate} {quotients : List Sparse.Univariate}
    {root : ℝ}
    (hvalid :
      valid polynomial
        { chain := first :: derivative :: tail
          quotients := quotients } = true)
    (hroot : Sparse.evalReal polynomial root = 0) :
    (∀ᶠ x in 𝓝[<] root,
      functionVariationAt
          ((first :: derivative :: tail).map Sparse.evalReal) x =
        functionVariationAt
            ((derivative :: tail).map Sparse.evalReal) root + 1) ∧
    (∀ᶠ x in 𝓝[>] root,
      functionVariationAt
          ((first :: derivative :: tail).map Sparse.evalReal) x =
        functionVariationAt
            ((derivative :: tail).map Sparse.evalReal) root) := by
  have hchainValid := recurrence_valid_of_valid hvalid
  have hfirstRoot := (accepted_first_evalReal hvalid root).trans hroot
  have hderivativeNonzero : Sparse.evalReal derivative root ≠ 0 := fun h ↦
    recurrence_consecutive_no_common_root hchainValid root ⟨hfirstRoot, h⟩
  cases quotients with
  | nil => simp [recurrenceValid] at hchainValid
  | cons quotient quotients =>
      have hfirstDerivative :
          HasDerivAt (Sparse.evalReal first) (Sparse.evalReal derivative root) root :=
        (accepted_first_evalReal_eq hvalid).symm ▸ accepted_first_hasDerivAt_second hvalid root
      simpa using firstPolynomial_simpleRoot_variation_drop hfirstDerivative hfirstRoot
        hderivativeNonzero (Sparse.continuous_evalReal derivative).continuousAt
        (recurrence_variation_eventually_eq_of_head_ne_zero
          (recurrence_tail_valid hchainValid) hderivativeNonzero)

/--
Certificate-facing root-free interval constancy.  The hypothesis is stated for
the requested polynomial, while the conclusion uses the certificate's actual
chain.
-/
theorem accepted_variation_eq_on_root_free_Icc
    {polynomial first derivative : Sparse.Univariate}
    {tail : List Sparse.Univariate} {quotients : List Sparse.Univariate}
    (hvalid :
      valid polynomial
        { chain := first :: derivative :: tail
          quotients := quotients } = true)
    {a b : ℝ} (hab : a ≤ b)
    (hrootFree :
      ∀ x ∈ Icc a b, Sparse.evalReal polynomial x ≠ 0) :
    functionVariationAt
        ((first :: derivative :: tail).map Sparse.evalReal) a =
      functionVariationAt
        ((first :: derivative :: tail).map Sparse.evalReal) b :=
  recurrence_variation_eq_on_root_free_Icc (recurrence_valid_of_valid hvalid) hab
    fun x hx hfirstRoot ↦ hrootFree x hx ((accepted_first_evalReal hvalid x).symm ▸ hfirstRoot)

/--
Analytic Sturm theorem for an accepted square-free recurrence.

The endpoint variation difference counts distinct real roots in the open
interval.  Roots are represented by Mathlib's `Polynomial.rootSet`, so the
right-hand side is the cardinality of a finite set of real roots, not a
certificate field.

The checker's terminal conditions rule out a common root of consecutive chain
members; in particular, every root of the first polynomial is simple.
-/
theorem accepted_variation_eq_add_rootSet_ncard
    {polynomial first derivative : Sparse.Univariate}
    {tail : List Sparse.Univariate} {quotients : List Sparse.Univariate}
    (hvalid :
      valid polynomial
        { chain := first :: derivative :: tail
          quotients := quotients } = true)
    {a b : ℝ} (hab : a ≤ b)
    (ha : Sparse.evalReal polynomial a ≠ 0)
    (hb : Sparse.evalReal polynomial b ≠ 0) :
    functionVariationAt
        ((first :: derivative :: tail).map Sparse.evalReal) a =
      functionVariationAt
          ((first :: derivative :: tail).map Sparse.evalReal) b +
        ((Sparse.toRealPolynomial polynomial).rootSet ℝ ∩ Ioo a b).ncard := by
  have hpolynomial : Sparse.toRealPolynomial polynomial ≠ 0 := by
    intro hzero
    apply ha
    rw [← Sparse.eval_toRealPolynomial, hzero, Polynomial.eval_zero]
  have hrootIff (x : ℝ) :
      x ∈ (Sparse.toRealPolynomial polynomial).rootSet ℝ ↔ Sparse.evalReal polynomial x = 0 := by
    rw [Polynomial.mem_rootSet_of_ne hpolynomial, Polynomial.coe_aeval_eq_eval,
      Sparse.eval_toRealPolynomial]
  refine eq_add_ncard_of_finite_unit_drops _ _ (Polynomial.rootSet_finite _ ℝ) ?_ ?_ (a := a)
    (b := b) hab (mt (hrootIff a).mp ha) (mt (hrootIff b).mp hb)
  · intro left right hleftRight hleft hright hbetween
    refine accepted_variation_eq_on_root_free_Icc hvalid hleftRight fun x hx hxRoot ↦ ?_
    replace hxRoot := (hrootIff x).mpr hxRoot
    rcases hx.1.eq_or_lt with rfl | hxl
    · exact hleft hxRoot
    rcases hx.2.eq_or_lt with rfl | hxr
    · exact hright hxRoot
    exact hbetween x ⟨hxl, hxr⟩ hxRoot
  · exact fun root hroot ↦ ⟨_, accepted_first_root_variation_drop hvalid ((hrootIff root).mp hroot)⟩

/--
Exact rational endpoint form of the analytic Sturm theorem.

For a checked chain and non-root rational endpoints, the executable variation
difference is exactly the number of distinct real roots in the corresponding
open real interval.
-/
theorem accepted_variationDifference_eq_rootSet_ncard
    {polynomial first derivative : Sparse.Univariate}
    {tail : List Sparse.Univariate} {quotients : List Sparse.Univariate}
    (hvalid :
      valid polynomial
        { chain := first :: derivative :: tail
          quotients := quotients } = true)
    {a b : Rat} (hab : a ≤ b)
    (ha : Sparse.evalRat polynomial a ≠ 0)
    (hb : Sparse.evalRat polynomial b ≠ 0) :
    (show SturmCertificate from
      { chain := first :: derivative :: tail
        quotients := quotients }).variationDifference a b =
      ((Sparse.toRealPolynomial polynomial).rootSet ℝ ∩
        Ioo (a : ℝ) (b : ℝ)).ncard := by
  have hglobal := accepted_variation_eq_add_rootSet_ncard hvalid (a := (a : ℝ)) (b := (b : ℝ))
    (by exact_mod_cast hab) (by simpa [Sparse.evalReal_ratCast] using ha)
    (by simpa [Sparse.evalReal_ratCast] using hb)
  simp only [variationDifference, variationAt_eq_functionVariationAt]
  omega

/--
**Sturm's theorem** for an accepted `SturmCertificate`: for rational endpoints `a ≤ b` that are
not roots of `polynomial`, `variationDifference a b` is the number of distinct real roots of
`polynomial` in the open interval `(a, b)`.
-/
theorem variationDifference_eq_rootSet_ncard
    (polynomial : Sparse.Univariate)
    (certificate : SturmCertificate)
    (hvalid : certificate.valid polynomial = true)
    {a b : Rat} (hab : a ≤ b)
    (ha : Sparse.evalRat polynomial a ≠ 0)
    (hb : Sparse.evalRat polynomial b ≠ 0) :
    certificate.variationDifference a b =
      ((Sparse.toRealPolynomial polynomial).rootSet ℝ ∩
        Ioo (a : ℝ) (b : ℝ)).ncard := by
  rcases certificate with ⟨_ | ⟨first, _ | ⟨derivative, tail⟩⟩, quotients⟩
  · simp [valid] at hvalid
  · simp [valid] at hvalid
  · exact accepted_variationDifference_eq_rootSet_ncard hvalid hab ha hb

end SturmCertificate

end CAS.Polynomial.RealRoot

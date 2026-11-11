/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.RealRoot.SturmTheorem.Variation

/-!
# Analytic properties of Sturm recurrences

The exact sparse recurrence checked by `Sturm.lean`, read as an identity of real polynomial
functions. Common roots propagate to the terminal member
(`recurrence_common_root_reaches_terminal`), consecutive entries have no common root when the
terminal member is nonvanishing (`recurrence_consecutive_no_common_root`), and the chain
variation is locally constant away from roots of its head
(`recurrence_variation_eventually_eq_of_head_ne_zero`, `recurrence_variation_eq_on_root_free_Icc`).

These results form the recurrence-level analytic input to the accepted
certificate theorems in `SturmTheorem.lean`.

## Implementation notes

The arguments are Sturm's (nos. 4 and 5 of the memoir). By the recurrences a common root of two
consecutive members is a root of the next member, and so of every later one
(`recurrence_common_root_reaches_terminal`), which the nonzero constant terminal excludes. Where a
member other than the head vanishes, the recurrence makes its two neighbours nonzero and of
opposite signs, so the three signs contribute exactly one variation whatever the sign of the
middle member (`functionVariationAt_skip_middle_of_opposite`). Sturm compares the signs at
`b - u` and `b + u` for a small `u`; we prove by induction along the chain that the variation is
locally constant at every point that is not a root of the head
(`recurrence_variation_eventually_eq_of_head_ne_zero`), and pass to a closed interval by its
connectedness (`recurrence_variation_eq_on_root_free_Icc`).

## References

* C. Sturm, "Mémoire sur la résolution des équations numériques", *Mémoires présentés par divers
  savans à l'Académie royale des sciences de l'Institut de France, Sciences mathématiques et
  physiques* 6 (1835), pp. 271-318, <https://archive.org/details/mmoirespresent06scie>.
  The propagation of a common root of consecutive members (nos. 4 and 5) and the zeros of
  intermediate members (no. 5).
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Filter Set
open scoped Topology
open Sparse

namespace SturmCertificate

/-- Sparse negation is ordinary negation after interpretation over `ℝ`. -/
theorem toRealPolynomial_mvNeg (polynomial : Sparse.Univariate) :
    Sparse.toRealPolynomial (Verified.Expr.Alg.mvNeg polynomial) =
      -Sparse.toRealPolynomial polynomial := by
  have hrat :
      Sparse.toRatPolynomial (Verified.Expr.Alg.mvNeg polynomial) =
        -Sparse.toRatPolynomial polynomial := by
    induction polynomial with
    | nil => simp [Verified.Expr.Alg.mvNeg, Sparse.toRatPolynomial]
    | cons term rest ih =>
        simp only [Verified.Expr.Alg.mvNeg, List.map_cons, Sparse.toRatPolynomial, map_neg]
          at ih ⊢
        rw [ih, neg_add]
  simp [Sparse.toRealPolynomial, hrat]

/-- Real evaluation of the signed remainder used by the Sturm checker. -/
theorem evalReal_signedRemainder :
    ∀ (tail : List Sparse.Univariate) (x : ℝ),
      Sparse.evalReal (signedRemainder tail) x =
        match tail with
        | [] => 0
        | next :: _ => -Sparse.evalReal next x
  | [], x => by simp [signedRemainder, Sparse.zero, Sparse.evalReal]
  | next :: tail, x => by
      simpa [signedRemainder, Sparse.eval_toRealPolynomial] using
        congrArg (Polynomial.eval x) (toRealPolynomial_mvNeg next)

/-- Pointwise real identity for any accepted recurrence suffix head. -/
theorem recurrence_head_evalReal
    {dividend divisor quotient : Sparse.Univariate}
    {tail quotients : List Sparse.Univariate}
    (hvalid :
      recurrenceValid (dividend :: divisor :: tail)
        (quotient :: quotients) = true)
    (x : ℝ) :
    Sparse.evalReal dividend x =
      Sparse.evalReal divisor x * Sparse.evalReal quotient x +
        Sparse.evalReal (signedRemainder tail) x := by
  simp only [← Sparse.eval_toRealPolynomial, Sparse.toRealPolynomial,
    recurrence_head_identity hvalid, Polynomial.map_add, Polynomial.map_mul, Polynomial.eval_add,
    Polynomial.eval_mul]

/--
A common root of two consecutive members propagates through every checked
suffix and reaches a valid terminal member.
-/
theorem recurrence_common_root_reaches_terminal :
    ∀ {first second : Sparse.Univariate}
      {tail quotients : List Sparse.Univariate},
      recurrenceValid (first :: second :: tail) quotients = true →
      ∀ {x : ℝ},
        Sparse.evalReal first x = 0 →
        Sparse.evalReal second x = 0 →
        ∃ last,
          recurrenceValid [last] [] = true ∧
            Sparse.evalReal last x = 0 := by
  intro first second tail
  induction tail generalizing first second with
  | nil =>
      intro quotients hvalid x _ hsecond
      obtain _ | ⟨quotient, _ | ⟨next, more⟩⟩ := quotients
      · simp [recurrenceValid] at hvalid
      · exact ⟨second, recurrence_tail_valid hvalid, hsecond⟩
      · simpa [recurrenceValid] using recurrence_tail_valid hvalid
  | cons third rest ih =>
      intro quotients hvalid x hfirst hsecond
      obtain _ | ⟨quotient, quotients⟩ := quotients
      · simp [recurrenceValid] at hvalid
      refine ih (recurrence_tail_valid hvalid) hsecond ?_
      simpa [hfirst, hsecond, evalReal_signedRemainder] using recurrence_head_evalReal hvalid x

/--
No two consecutive members of a checked recurrence chain have a common real
root: such a root would propagate to its checked nonzero constant terminal.
-/
theorem recurrence_consecutive_no_common_root
    {first second : Sparse.Univariate}
    {tail quotients : List Sparse.Univariate}
    (hvalid :
      recurrenceValid (first :: second :: tail) quotients = true) :
    ∀ x,
      ¬(Sparse.evalReal first x = 0 ∧
        Sparse.evalReal second x = 0) := by
  intro x hcommon
  obtain ⟨last, hlastValid, hlastRoot⟩ :=
    recurrence_common_root_reaches_terminal hvalid hcommon.1 hcommon.2
  exact recurrence_terminal_nonzero hlastValid x hlastRoot

/-- Nonzero opposite real values have two distinct nonzero signs. -/
theorem exists_opposite_signs
    {left right : ℝ} (hequality : left = -right)
    (hright : right ≠ 0) :
    ∃ leftSign rightSign,
      leftSign ≠ 0 ∧
        rightSign ≠ 0 ∧
        SignType.sign left = leftSign ∧
        SignType.sign right = rightSign ∧
        leftSign ≠ rightSign := by
  rcases lt_or_gt_of_ne hright with hnegative | hpositive
  · exact ⟨1, -1, by decide, by decide, hequality ▸ sign_pos (neg_pos.mpr hnegative),
      sign_neg hnegative, by decide⟩
  · exact ⟨-1, 1, by decide, by decide, hequality ▸ sign_neg (neg_lt_zero.mpr hpositive),
      sign_pos hpositive, by decide⟩

/--
For a checked recurrence chain, the full variation is locally constant at every
point where the current head is not a root. Internal zeros are handled by the
opposite-neighbour recurrence law and the checked nonzero constant terminal.
-/
theorem recurrence_variation_eventually_eq_of_head_ne_zero
    {first : Sparse.Univariate}
    {tail quotients : List Sparse.Univariate}
    (hvalid :
      recurrenceValid (first :: tail) quotients = true)
    {x : ℝ} (hfirst : Sparse.evalReal first x ≠ 0) :
    ∀ᶠ y in 𝓝 x,
      functionVariationAt
          ((first :: tail).map Sparse.evalReal) y =
        functionVariationAt
          ((first :: tail).map Sparse.evalReal) x := by
  cases tail with
  | nil => exact Filter.Eventually.of_forall fun y ↦ by simp
  | cons second rest =>
      cases quotients with
      | nil => simp [recurrenceValid] at hvalid
      | cons quotient quotients =>
          have hsuffixValid := recurrence_tail_valid hvalid
          by_cases hsecond : Sparse.evalReal second x = 0
          · cases rest with
            | nil =>
                cases quotients with
                | nil => exact (recurrence_terminal_nonzero hsuffixValid x hsecond).elim
                | cons next more => simp [recurrenceValid] at hsuffixValid
            | cons third remaining =>
                have hthird : Sparse.evalReal third x ≠ 0 := fun hthirdZero ↦
                  recurrence_consecutive_no_common_root hsuffixValid x ⟨hsecond, hthirdZero⟩
                cases quotients with
                | nil => simp [recurrenceValid] at hsuffixValid
                | cons next more =>
                    have hneighbors : Sparse.evalReal first x = -Sparse.evalReal third x := by
                      simpa [hsecond, evalReal_signedRemainder] using
                        recurrence_head_evalReal hvalid x
                    obtain ⟨firstSign, thirdSign, hfirstSignNonzero, hthirdSignNonzero,
                      hfirstSign, hthirdSign, hopposite⟩ := exists_opposite_signs hneighbors hthird
                    filter_upwards [eventually_sign_eq_of_continuousAt
                        (Sparse.continuous_evalReal first).continuousAt hfirst,
                      eventually_sign_eq_of_continuousAt
                        (Sparse.continuous_evalReal third).continuousAt hthird,
                      recurrence_variation_eventually_eq_of_head_ne_zero
                        (recurrence_tail_valid hsuffixValid) hthird] with
                      y hfirstAtY hthirdAtY hsuffixAtY
                    simp only [List.map_cons] at hsuffixAtY ⊢
                    rw [functionVariationAt_skip_middle_of_opposite hfirstSignNonzero
                        hthirdSignNonzero (hfirstAtY.trans hfirstSign)
                        (hthirdAtY.trans hthirdSign) hopposite,
                      functionVariationAt_skip_middle_of_opposite hfirstSignNonzero
                        hthirdSignNonzero hfirstSign hthirdSign hopposite, hsuffixAtY]
          · filter_upwards [eventually_sign_eq_of_continuousAt
                (Sparse.continuous_evalReal first).continuousAt hfirst,
              eventually_sign_eq_of_continuousAt
                (Sparse.continuous_evalReal second).continuousAt hsecond,
              recurrence_variation_eventually_eq_of_head_ne_zero hsuffixValid hsecond] with
              y hfirstAtY hsecondAtY hsuffixAtY
            exact functionVariationAt_cons_stable hfirst hsecond hfirstAtY hsecondAtY hsuffixAtY
termination_by tail.length

/--
On a closed interval containing no root of the head polynomial, a valid Sturm
recurrence has the same variation at both endpoints.

The proof restricts the variation function to the interval.  The preceding
suffix induction makes that restricted function locally constant, and
preconnectedness of a real interval then makes it constant.
-/
theorem recurrence_variation_eq_on_root_free_Icc
    {first : Sparse.Univariate}
    {tail quotients : List Sparse.Univariate}
    (hvalid :
      recurrenceValid (first :: tail) quotients = true)
    {a b : ℝ} (hab : a ≤ b)
    (hrootFree :
      ∀ x ∈ Icc a b, Sparse.evalReal first x ≠ 0) :
    functionVariationAt
        ((first :: tail).map Sparse.evalReal) a =
      functionVariationAt
        ((first :: tail).map Sparse.evalReal) b := by
  have : PreconnectedSpace (Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  have hlocallyConstant : IsLocallyConstant fun x : Icc a b ↦
      functionVariationAt ((first :: tail).map Sparse.evalReal) x := by
    rw [IsLocallyConstant.iff_eventually_eq]
    exact fun x ↦ continuous_subtype_val.continuousAt.eventually
      (recurrence_variation_eventually_eq_of_head_ne_zero hvalid (hrootFree x x.property))
  exact hlocallyConstant.apply_eq_of_preconnectedSpace ⟨a, left_mem_Icc.mpr hab⟩
    ⟨b, right_mem_Icc.mpr hab⟩

end SturmCertificate

end CAS.Polynomial.RealRoot

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.RealRoot.RootList

/-!
# The number of real roots of a polynomial

`#cas [roots x]` proves a complete list of the real roots of a polynomial: each listed open
interval contains exactly one root, each listed rational is a root, and there are no others
(`of_exprRootCheck`). The same check makes the intervals pairwise disjoint and the rationals
distinct and outside the intervals (`separatedCheck_of_exprRootCheck`), so the list has as many
entries as there are real roots, which gives `Fintype.card (p.rootSet ℝ)`
(`card_rootSet_of_exprRootCheck`). Mathlib's `rootSet 0` is empty, while every real is a zero of
the zero polynomial, so the theorem also asks for a rational at which the polynomial does not
vanish (`nonzeroAtCheck`).

## Main results

* `card_of_rootList`: the cardinality of a finite set of reals from a separated complete list of
  isolating intervals and points.
* `card_rootSet_of_exprRootCheck`: `Fintype.card (p.rootSet ℝ)` from a root list of a checked
  expression that evaluates as `p`.
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Set
open _root_.Polynomial

/-- A one-variable polynomial expression that does not vanish at the rational `q`. -/
def nonzeroAtCheck (expr : Verified.Expr (Fin 1)) (q : ℚ) : Bool :=
  match Verified.Expr.Alg.mvPolyOf? expr with
  | some poly => Sparse.evalRat poly q != 0
  | none => false

/-- A passing `nonzeroAtCheck` gives a rational point where the expression is nonzero. -/
theorem eval_ne_zero_of_nonzeroAtCheck {expr : Verified.Expr (Fin 1)} {q : ℚ}
    (h : nonzeroAtCheck expr q = true) :
    expr.eval ![(q : ℝ)] ≠ 0 := by
  unfold nonzeroAtCheck at h
  split at h
  · rename_i poly hpoly
    rw [← evalReal_eq_eval_of_mvPolyOf? expr poly hpoly, Sparse.evalReal_ratCast]
    exact_mod_cast bne_iff_ne.mp h
  · cases h

/-- **Counting a separated root list.** A finite set of reals in which each listed open interval
contains exactly one element, each listed rational is an element, and every element is listed,
has as many elements as the list, when the entries are pairwise disjoint. -/
theorem card_of_rootList {S : Set ℝ} [Fintype S] {intervals : List (ℚ × ℚ)} {points : List ℚ}
    (hI : ∀ I ∈ intervals, ∃! x, x ∈ Ioo (I.1 : ℝ) I.2 ∧ x ∈ S)
    (hP : ∀ r ∈ points, (r : ℝ) ∈ S)
    (hS : ∀ x ∈ S, (∃ r ∈ points, x = r) ∨ ∃ I ∈ intervals, x ∈ Ioo (I.1 : ℝ) I.2)
    (hsep : separatedCheck intervals points = true) :
    Fintype.card S = intervals.length + points.length := by
  simp only [separatedCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hsep
  obtain ⟨⟨hpair, hnodup⟩, hout⟩ := hsep
  choose root hroot using fun i : Fin intervals.length ↦ (hI _ (List.getElem_mem i.2)).exists
  let f : Fin intervals.length ⊕ Fin points.length → S := fun
    | .inl i => ⟨root i, (hroot i).2⟩
    | .inr j => ⟨(points[j] : ℝ), hP _ (List.getElem_mem j.2)⟩
  have hdisj : ∀ i j : Fin intervals.length, i ≠ j → ∀ x : ℝ,
      x ∈ Ioo ((intervals[i]).1 : ℝ) (intervals[i]).2 →
      x ∉ Ioo ((intervals[j]).1 : ℝ) (intervals[j]).2 := by
    intro i j hij x hx hx'
    have h : (intervals[i]).2 ≤ (intervals[j]).1 ∨ (intervals[j]).2 ≤ (intervals[i]).1 := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact List.pairwise_iff_getElem.mp hpair i j i.2 j.2 h
      · exact (List.pairwise_iff_getElem.mp hpair j i j.2 i.2 h).symm
    rcases h with h | h
    · linarith [hx.2, hx'.1, (Rat.cast_le (K := ℝ)).mpr h]
    · linarith [hx.1, hx'.2, (Rat.cast_le (K := ℝ)).mpr h]
  have hpoint : ∀ (i : Fin intervals.length) (j : Fin points.length),
      ((points[j] : ℚ) : ℝ) ∉ Ioo ((intervals[i]).1 : ℝ) (intervals[i]).2 := by
    intro i j ⟨h1, h2⟩
    rcases hout _ (List.getElem_mem j.2) _ (List.getElem_mem i.2) with h | h
    · exact (Rat.cast_lt.mp h1).not_ge h
    · exact (Rat.cast_lt.mp h2).not_ge h
  have hf : Function.Bijective f := by
    constructor
    · rintro (i | j) (i' | j') h <;> simp only [f, Subtype.mk.injEq] at h
      · exact congrArg _ (not_not.mp fun hne ↦ hdisj i i' hne _ (hroot i).1 (h ▸ (hroot i').1))
      · exact absurd (h ▸ (hroot i).1) (hpoint i j')
      · exact absurd (h ▸ (hroot i').1) (hpoint i' j)
      · exact congrArg _ (Fin.ext (hnodup.getElem_inj_iff.mp (by exact_mod_cast h)))
    · rintro ⟨x, hx⟩
      rcases hS x hx with ⟨r, hr, rfl⟩ | ⟨I, hI', hxI⟩
      · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hr
        exact ⟨.inr ⟨j, hj⟩, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hI'
        exact ⟨.inl ⟨i, hi⟩,
          Subtype.ext ((hI _ (List.getElem_mem hi)).unique (hroot ⟨i, hi⟩) ⟨hxI, hx⟩)⟩
  rw [← Fintype.card_of_bijective hf, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]

/-- **The number of real roots.** The complete root list of a checked expression that
evaluates as `aeval x p` and does not vanish at `q` counts the distinct real roots of `p`. -/
theorem card_rootSet_of_exprRootCheck {T : Type*} [CommRing T] [Algebra T ℝ] {p : T[X]}
    {expr : Verified.Expr (Fin 1)} {cert : RootListCertificate}
    {intervals : List (ℚ × ℚ)} {points : List ℚ} (q : ℚ)
    (heval : ∀ x : ℝ, aeval x p = expr.eval ![x])
    (h : exprRootCheck expr cert intervals points = true) (hq : nonzeroAtCheck expr q = true) :
    Fintype.card (p.rootSet ℝ) = intervals.length + points.length := by
  have hp : p.map (algebraMap T ℝ) ≠ 0 := fun h0 ↦ eval_ne_zero_of_nonzeroAtCheck hq <| by
    rw [← heval, aeval_def, ← eval_map, h0, eval_zero]
  have hmem : ∀ x : ℝ, x ∈ p.rootSet ℝ ↔ expr.eval ![x] = 0 := fun x ↦ by
    rw [mem_rootSet', heval, and_iff_right hp]
  obtain ⟨hA, hB, hC⟩ := of_exprRootCheck h
  exact card_of_rootList (fun I hI ↦ by simpa only [hmem] using hA I hI)
    (fun r hr ↦ (hmem r).mpr (hB r hr)) (fun x hx ↦ hC x ((hmem x).mp hx))
    (separatedCheck_of_exprRootCheck h)

end CAS.Polynomial.RealRoot

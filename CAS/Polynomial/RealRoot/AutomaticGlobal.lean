/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.RealRoot.CauchyBound
public import CAS.Polynomial.RealRoot.RadicalGenerator
public import CAS.Polynomial.RealRoot.SturmAtlas

/-!
# Checked global real-root isolation certificates

Root isolation without a user-supplied outer search interval: a
`GlobalPolynomialIsolationCertificate` adds to the square-free radical a checked Cauchy bound
(`CauchyBoundCertificate`) whose symmetric rational interval the Sturm subdivision covers.
`valid` checks every stage and the outer interval, and the noncomputable projection
`toGlobalRootAtlas` exposes the ordinary theorem that every real root of the original polynomial
is covered by a root-bearing atlas patch, each of which contains a unique root. Two patches may
contain the same root, so the atlas does not count roots.

SymLean checks such certificates when a caller supplies them; it has no generator for them. The
root and sign commands use their own root-list search (`RootIsolation.generate`) and the
root-list checkers of `RootList` and `SignReduce` instead.
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Set

/-- Complete checked evidence for automatic global real-root isolation. -/
structure GlobalPolynomialIsolationCertificate where
  /-- Checked square-free surrogate with the original polynomial's real zero set. -/
  radical : RadicalCertificate
  /-- Cauchy certificate enclosing every root of the square-free surrogate. -/
  bound : CauchyBoundCertificate
  /-- Root-classifying subdivision of the Cauchy interval, absent only for degree zero. -/
  subdivision : Option SturmSubdivisionCertificate
deriving DecidableEq

namespace GlobalPolynomialIsolationCertificate

/-- Independent checker for every stage and the generated outer interval. -/
def valid (original : Sparse.Univariate)
    (certificate : GlobalPolynomialIsolationCertificate) : Bool :=
  certificate.radical.valid original &&
    certificate.bound.valid certificate.radical.radical &&
    match certificate.subdivision with
    | none => decide (certificate.bound.degree = 0)
    | some subdivision =>
        subdivision.valid certificate.radical.radical &&
          decide
            (subdivision.subdivision.interval.lo =
                -certificate.bound.bound ∧
              subdivision.subdivision.interval.hi =
                certificate.bound.bound)

/-- Global isolation validity includes a checked squarefree radical and a root bound
for that radical, before either subdivision branch is considered. -/
theorem valid_head
    (original : Sparse.Univariate)
    (certificate : GlobalPolynomialIsolationCertificate)
    (hvalid : certificate.valid original = true) :
    certificate.radical.valid original = true ∧
      certificate.bound.valid certificate.radical.radical = true := by
  simp only [valid, Bool.and_eq_true] at hvalid
  exact ⟨hvalid.1.1, hvalid.1.2⟩

/-- Patch-index type selected by the checked rootless or subdivided branch. -/
def Index (certificate : GlobalPolynomialIsolationCertificate) : Type :=
  match certificate.subdivision with
  | none => Empty
  | some subdivision =>
      SturmSubdivisionCertificate.LeafIndex subdivision

/--
Project accepted finite evidence to a complete root atlas for the original
polynomial.
-/
noncomputable def toGlobalRootAtlas
    {original : Sparse.Univariate}
    (certificate : GlobalPolynomialIsolationCertificate)
    (hvalid : certificate.valid original = true) :
    GlobalRootAtlas certificate.Index original := by
  rcases certificate.valid_head original hvalid with
    ⟨hradical, hbound⟩
  cases hsubdivision : certificate.subdivision with
  | none =>
      simp only [Index, hsubdivision]
      have hdegree : certificate.bound.degree = 0 := by
        simp only [valid, Bool.and_eq_true, hsubdivision,
          decide_eq_true_eq] at hvalid
        exact hvalid.2
      exact
        { domain := ∅
          atlas :=
            { region := fun index ↦ nomatch index
              covers := Set.empty_subset _
              valid := fun index ↦ nomatch index }
          containsRoots := by
            intro x hx
            have hradicalRoot :
                Sparse.evalReal certificate.radical.radical x = 0 :=
              (certificate.radical.evalReal_eq_zero_iff
                original hradical x).mp hx
            exact
              (certificate.bound.evalReal_ne_zero_of_degree_eq_zero
                hbound hdegree x hradicalRoot).elim }
  | some subdivision =>
      simp only [Index, hsubdivision]
      have htail :
          subdivision.valid certificate.radical.radical = true ∧
            (subdivision.subdivision.interval.lo =
                -certificate.bound.bound ∧
              subdivision.subdivision.interval.hi =
                certificate.bound.bound) := by
        simp only [valid, Bool.and_eq_true, hsubdivision,
          decide_eq_true_eq] at hvalid
        exact hvalid.2
      let radicalAtlas :=
        subdivision.toRootAtlas htail.1
      let originalAtlas :=
        radicalAtlas.transportAlongRadical certificate.radical hradical
      exact
        { domain :=
            Icc
              (subdivision.subdivision.interval.lo : ℝ)
              (subdivision.subdivision.interval.hi : ℝ)
          atlas := originalAtlas
          containsRoots := by
            intro x hx
            have hradicalRoot :
                Sparse.evalReal certificate.radical.radical x = 0 :=
              (certificate.radical.evalReal_eq_zero_iff
                original hradical x).mp hx
            have habs :=
              certificate.bound.abs_lt_bound hbound hradicalRoot
            constructor
            · rw [htail.2.1]
              simpa only [Rat.cast_neg] using (abs_lt.mp habs).1.le
            · rw [htail.2.2]
              exact (abs_lt.mp habs).2.le }

end GlobalPolynomialIsolationCertificate

end CAS.Polynomial.RealRoot

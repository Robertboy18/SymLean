/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.RealRoot.SturmTheorem
public import CAS.Continuum.Interval.Rational.Basic

/-!
# Checked Sturm subdivisions

A `SturmSubdivision` is a binary tree of rational intervals, each node split at a rational
point. `SturmSubdivision.valid` checks the finite evidence:

* child intervals exactly partition their parent;
* every subdivision endpoint is not a root of the requested polynomial; and
* the exact Sturm variation count of a parent is the sum of the child counts.

The combinatorial results (`leaf_count_le_one`, `exists_leaf_of_mem`) use only the checker.
Combined with an accepted Sturm chain in a `SturmSubdivisionCertificate`, the analytic Sturm
theorem turns the count of the outer interval into its real-root count
(`nodeCount_eq_rootSet_ncard`).

## Implementation notes

A subdivision whose leaves hold at most one root each records Sturm's separation of the roots
(no. 15 of the memoir): he substitutes intermediate numbers in an interval with several roots
until each root lies alone between two limits. The checker does not depend on how the split
points were chosen. SymLean has no generator for subdivisions: they are checked when a caller
supplies them, inside a `PolynomialIsolationCertificate` or a
`GlobalPolynomialIsolationCertificate`.

## References

* C. Sturm, "Mémoire sur la résolution des équations numériques", *Mémoires présentés par divers
  savans à l'Académie royale des sciences de l'Institut de France, Sciences mathématiques et
  physiques* 6 (1835), pp. 271-318, <https://archive.org/details/mmoirespresent06scie>.
  The separation of the roots by intermediate substitutions (no. 15, pp. 291-292).
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open CAS.Continuum

/-- A finite binary partition of one rational interval. -/
inductive SturmSubdivision where
  | leaf (interval : RationalInterval)
  | split (interval : RationalInterval) (midpoint : Rat)
      (left right : SturmSubdivision)
deriving DecidableEq

namespace SturmSubdivision

/-- The rational interval represented by the root of a subdivision tree. -/
def interval : SturmSubdivision → RationalInterval
  | .leaf I => I
  | .split I _ _ _ => I

/-- Exact variation drop attached to the root interval of a tree. -/
def nodeCount (sturm : SturmCertificate) (tree : SturmSubdivision) : Nat :=
  sturm.variationDifference tree.interval.lo tree.interval.hi

/-- Rational leaf intervals, in left-to-right tree order. -/
def leaves : SturmSubdivision → List RationalInterval
  | .leaf I => [I]
  | .split _ _ left right => left.leaves ++ right.leaves

/-- Exact checker for every node of a proposed rational subdivision. -/
def valid (polynomial : Sparse.Univariate) (sturm : SturmCertificate) :
    SturmSubdivision → Bool
  | .leaf I =>
      decide (I.lo < I.hi ∧
        Sparse.evalRat polynomial I.lo ≠ 0 ∧
        Sparse.evalRat polynomial I.hi ≠ 0 ∧
        sturm.variationDifference I.lo I.hi ≤ 1)
  | .split I midpoint left right =>
      decide (I.lo < midpoint ∧
        midpoint < I.hi ∧
        left.interval.lo = I.lo ∧
        left.interval.hi = midpoint ∧
        right.interval.lo = midpoint ∧
        right.interval.hi = I.hi ∧
        Sparse.evalRat polynomial midpoint ≠ 0) &&
      valid polynomial sturm left &&
      valid polynomial sturm right &&
      decide (nodeCount sturm (.split I midpoint left right) =
        nodeCount sturm left + nodeCount sturm right)

/-- A valid subdivision has non-root endpoints at its root interval. -/
theorem endpoints_nonzero_of_valid
    (polynomial : Sparse.Univariate) (sturm : SturmCertificate)
    (tree : SturmSubdivision)
    (hvalid : tree.valid polynomial sturm = true) :
    Sparse.evalRat polynomial tree.interval.lo ≠ 0 ∧
      Sparse.evalRat polynomial tree.interval.hi ≠ 0 := by
  induction tree with
  | leaf I =>
      simp only [valid, decide_eq_true_eq] at hvalid
      exact ⟨hvalid.2.1, hvalid.2.2.1⟩
  | split I midpoint left right ihLeft ihRight =>
      simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hvalid
      obtain ⟨⟨⟨⟨-, -, hlo, -, -, hhi, -⟩, hleft⟩, hright⟩, -⟩ := hvalid
      exact ⟨hlo ▸ (ihLeft hleft).1, hhi ▸ (ihRight hright).2⟩

/-- Every listed leaf of a valid subdivision is itself accepted. -/
theorem leaf_valid_of_mem
    (polynomial : Sparse.Univariate) (sturm : SturmCertificate)
    (tree : SturmSubdivision)
    (hvalid : tree.valid polynomial sturm = true)
    {leaf : RationalInterval} (hleaf : leaf ∈ tree.leaves) :
    (SturmSubdivision.leaf leaf).valid polynomial sturm = true := by
  induction tree with
  | leaf I => exact List.mem_singleton.mp hleaf ▸ hvalid
  | split I midpoint left right ihLeft ihRight =>
      simp only [valid, Bool.and_eq_true] at hvalid
      rcases List.mem_append.mp hleaf with hleaf | hleaf
      · exact ihLeft hvalid.1.1.2 hleaf
      · exact ihRight hvalid.1.2 hleaf

/--
Every accepted leaf has computed variation difference at most one.
Interpreting this as a real-root count additionally requires validity of the Sturm chain.
-/
theorem leaf_count_le_one
    (polynomial : Sparse.Univariate) (sturm : SturmCertificate)
    (tree : SturmSubdivision)
    (hvalid : tree.valid polynomial sturm = true)
    {leaf : RationalInterval} (hleaf : leaf ∈ tree.leaves) :
    sturm.variationDifference leaf.lo leaf.hi ≤ 1 :=
  (of_decide_eq_true (tree.leaf_valid_of_mem polynomial sturm hvalid hleaf)).2.2.2

/-- The leaves of a valid subdivision cover its outer closed interval. -/
theorem exists_leaf_of_mem
    (polynomial : Sparse.Univariate) (sturm : SturmCertificate)
    (tree : SturmSubdivision)
    (hvalid : tree.valid polynomial sturm = true)
    {x : ℝ}
    (hx : x ∈ Set.Icc (tree.interval.lo : ℝ)
        (tree.interval.hi : ℝ)) :
    ∃ leaf ∈ tree.leaves,
      x ∈ Set.Icc (leaf.lo : ℝ) (leaf.hi : ℝ) := by
  induction tree with
  | leaf I => exact ⟨I, List.mem_singleton_self I, hx⟩
  | split I midpoint left right ihLeft ihRight =>
      simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hvalid
      obtain ⟨⟨⟨⟨-, -, hlo, hleftHi, hrightLo, hhi, -⟩, hleft⟩, hright⟩, -⟩ := hvalid
      rcases le_total x midpoint with hxm | hxm
      · obtain ⟨leaf, hleaf, hxLeaf⟩ := ihLeft hleft ⟨hlo ▸ hx.1, hleftHi ▸ hxm⟩
        exact ⟨leaf, List.mem_append_left _ hleaf, hxLeaf⟩
      · obtain ⟨leaf, hleaf, hxLeaf⟩ := ihRight hright ⟨hrightLo ▸ hxm, hhi ▸ hx.2⟩
        exact ⟨leaf, List.mem_append_right _ hleaf, hxLeaf⟩

end SturmSubdivision

/-- An accepted Sturm chain paired with a checked rational subdivision. -/
structure SturmSubdivisionCertificate where
  /-- Exact Sturm chain shared by every node and leaf count in the subdivision. -/
  sturm : SturmCertificate
  /-- Checked interval tree whose leaf counts partition the outer root count. -/
  subdivision : SturmSubdivision
deriving DecidableEq

namespace SturmSubdivisionCertificate

/-- Check both the exact Sturm chain and its proposed interval subdivision. -/
def valid (polynomial : Sparse.Univariate)
    (certificate : SturmSubdivisionCertificate) : Bool :=
  certificate.sturm.valid polynomial &&
    certificate.subdivision.valid polynomial certificate.sturm

/-- Acceptance exposes validity of the exact Sturm chain. -/
theorem sturm_valid {polynomial : Sparse.Univariate}
    {certificate : SturmSubdivisionCertificate}
    (hvalid : certificate.valid polynomial = true) :
    certificate.sturm.valid polynomial = true :=
  (Bool.and_eq_true_iff.mp hvalid).1

/--
The root count computed at an accepted subdivision's outer interval is exactly
the cardinality of the Mathlib real root set in that open interval.
-/
theorem nodeCount_eq_rootSet_ncard
    {polynomial : Sparse.Univariate}
    {certificate : SturmSubdivisionCertificate}
    (hvalid : certificate.valid polynomial = true) :
    certificate.subdivision.nodeCount certificate.sturm =
      ((Sparse.toRealPolynomial polynomial).rootSet ℝ ∩
        Set.Ioo
          (certificate.subdivision.interval.lo : ℝ)
          (certificate.subdivision.interval.hi : ℝ)).ncard := by
  obtain ⟨hlo, hhi⟩ := certificate.subdivision.endpoints_nonzero_of_valid polynomial
    certificate.sturm (Bool.and_eq_true_iff.mp hvalid).2
  exact certificate.sturm.variationDifference_eq_rootSet_ncard polynomial
    (certificate.sturm_valid hvalid) certificate.subdivision.interval.hle hlo hhi

end SturmSubdivisionCertificate

end CAS.Polynomial.RealRoot

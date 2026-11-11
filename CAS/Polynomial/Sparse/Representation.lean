/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Operators -- shake: keep

/-!
# Ordered sparse rational polynomials

The executable representation of sparse rational polynomials. A monomial in `n` variables is an
exponent vector `Fin n → Nat`, and a raw polynomial is a list of rational coefficients paired with
monomials. The list representation keeps reflection and certificate checking executable.

The raw type does not encode canonicality. `mvNormalize` establishes the
invariant used by downstream algorithms:

* every coefficient is nonzero;
* each exponent vector occurs at most once;
* terms are sorted in descending graded lexicographic order.

Unsupported expression heads are rejected by `mvPolyOf?`; they are never
treated as polynomial variables. Real-valued soundness belongs to
`CAS.Polynomial.Sparse.Semantics`.

## Implementation notes

We normalize by merging runs. `mvNormalize` drops zero coefficients, computes the sort key of every
monomial once (`mvKey`: the total degree followed by the exponents), splits the terms into runs
that are already strictly descending, and merges the runs pairwise, adding the coefficients of
equal monomials. A canonical list is a single run, so normalizing it again is linear; adding two
canonical polynomials is one merge; and a product of canonical polynomials merges its scaled rows,
which are runs because graded lexicographic order is a monomial order. The recursions are
structural or bounded by fuel, so the kernel evaluates the normalizer in reflection proofs.

Addition, subtraction, scaling, multiplication, and powers normalize their outputs. Termwise
negation preserves canonicality but does not normalize raw input. `mvLeadingTerm?` reads the
greatest term of the list as it stands, without merging equal monomials or dropping zero
coefficients, and `mvLeadingTermNormalized?` normalizes first.

## References

* David A. Cox, John Little and Donal O'Shea, *Ideals, Varieties, and Algorithms*, 4th ed.,
  Undergraduate Texts in Mathematics, Springer, Cham, 2015,
  <https://doi.org/10.1007/978-3-319-16721-3>. Chapter 2, Gröbner Bases, pp. 49-119.
-/

@[expose] public section

namespace CAS

namespace Verified.Expr

namespace Alg

/-! ## Ordered multivariate representation

The exponent vector fixes a stable variable order. The chosen graded
lexicographic order compares total degree first and then compares coordinates
from `0` upward. This order determines leading terms throughout exact division.
-/

/-- An exponent-vector monomial over `n` ordered variables. -/
abbrev MvMonomial (n : Nat) := Fin n → Nat

/--
A raw sparse rational-coefficient polynomial over `n` ordered variables.

Use `mvNormalize` before relying on uniqueness, nonzero coefficients, or term
order. The carrier is raw so that generated certificates can be checked
without carrying proof fields through every computation.
-/
abbrev MvPoly (n : Nat) := List (Rat × MvMonomial n)

/-- The constant-one monomial. -/
def mvOne (n : Nat) : MvMonomial n :=
  fun _ ↦ 0

/-- The monomial for the `i`-th ordered variable. -/
def mvVar {n : Nat} (i : Fin n) : MvMonomial n :=
  fun j ↦ if j = i then 1 else 0

/-- Multiply exponent-vector monomials by adding exponents componentwise. -/
def mvMul {n : Nat} (a b : MvMonomial n) : MvMonomial n :=
  fun i ↦ a i + b i

/-- Raise an exponent-vector monomial to a natural power. -/
def mvPowMonomial {n : Nat} (mono : MvMonomial n) (exponent : Nat) :
    MvMonomial n :=
  fun i ↦ mono i * exponent

/--
Monomial divisibility: every exponent of `a` is at most the matching exponent
of `b`.
-/
def mvDivides {n : Nat} (a b : MvMonomial n) : Bool :=
  (List.finRange n).all (fun i ↦ a i ≤ b i)

/-- Quotient monomial `b/a`, if `a` divides `b`. -/
def mvQuotient? {n : Nat} (a b : MvMonomial n) : Option (MvMonomial n) :=
  if mvDivides a b then
    some (fun i ↦ b i - a i)
  else
    none

/-- Total degree of an exponent-vector monomial. -/
def mvTotalDegree {n : Nat} (m : MvMonomial n) : Nat :=
  (List.finRange n).foldl (fun acc i ↦ acc + m i) 0

/--
The sort key of a monomial: its total degree followed by its exponents from variable `0` up.
Keys compare lexicographically exactly as their monomials compare in graded lexicographic order,
and equal keys come from equal monomials.
-/
def mvKey {n : Nat} (m : MvMonomial n) : List Nat :=
  let exponents := (List.finRange n).map m
  exponents.sum :: exponents

/--
Graded lexicographic comparison: total degree first, then the exponents from variable `0` up,
a larger exponent being greater.
-/
def mvGrlexCompare {n : Nat} (a b : MvMonomial n) : Ordering :=
  List.compareLex compare (mvKey a) (mvKey b)

/--
Reflect a symbolic expression into an ordered multivariate monomial if it is
one.

This recognizes products and powers of ordered variables. It rejects
transcendental heads and non-variable factors because the sparse polynomial
algorithms operate only on the polynomial fragment.
-/
def mvMonomialOf? {n : Nat} : Verified.Expr (Fin n) → Option (MvMonomial n)
  | .nat 1 => some (mvOne n)
  | .int 1 => some (mvOne n)
  | .var i => some (mvVar i)
  | .mul a b => do
      let ma ← mvMonomialOf? a
      let mb ← mvMonomialOf? b
      some (mvMul ma mb)
  | .pow a k => do
      let ma ← mvMonomialOf? a
      pure <| mvPowMonomial ma k
  | _ => none

/-- Whether the monomial of term `a` is strictly greater than that of term `b` in graded
lexicographic order. -/
def mvTermGreater {n : Nat}
    (a b : Rat × MvMonomial n) : Bool :=
  match mvGrlexCompare a.2 b.2 with
  | .gt => true
  | _ => false

/-- Select the term with the greatest monomial among `best` and the remaining terms, keeping the
earlier term on ties. -/
def mvLeadingTermAux {n : Nat} :
    Rat × MvMonomial n → MvPoly n → Rat × MvMonomial n
  | best, [] => best
  | best, term :: rest =>
      let best' := if mvTermGreater term best then term else best
      mvLeadingTermAux best' rest

/--
Greatest represented term under graded lexicographic order, without normalization.
Use `mvLeadingTermNormalized?` to combine duplicate monomials and discard zero terms first.
-/
def mvLeadingTerm? {n : Nat} : MvPoly n → Option (Rat × MvMonomial n)
  | [] => none
  | term :: rest => some (mvLeadingTermAux term rest)

/-- A term paired with the key of its monomial, the unit that `mvNormalize` sorts. -/
abbrev MvKeyedTerm (n : Nat) := List Nat × Rat × MvMonomial n

/--
Merge two lists of keyed terms, each strictly descending by key, into one strictly descending
list. Terms with equal keys are combined by adding their coefficients, and a zero sum is dropped.
The fuel bounds the recursion; the total length of the two lists is enough, and if the fuel runs
out the remaining terms are appended unmerged.
-/
def mvMergeKeyed {n : Nat} : Nat → List (MvKeyedTerm n) → List (MvKeyedTerm n) →
    List (MvKeyedTerm n)
  | 0, as, bs => as ++ bs
  | _ + 1, [], bs => bs
  | _ + 1, a :: as, [] => a :: as
  | fuel + 1, a :: as, b :: bs =>
      match List.compareLex compare a.1 b.1 with
      | .gt => a :: mvMergeKeyed fuel as (b :: bs)
      | .lt => b :: mvMergeKeyed fuel (a :: as) bs
      | .eq =>
          let c := a.2.1 + b.2.1
          if c = 0 then mvMergeKeyed fuel as bs else (a.1, c, a.2.2) :: mvMergeKeyed fuel as bs

/-- Split keyed terms into maximal runs that are strictly descending by key. -/
def mvRuns {n : Nat} : List (MvKeyedTerm n) → List (List (MvKeyedTerm n))
  | [] => []
  | t :: rest =>
      match mvRuns rest with
      | (u :: run) :: runs =>
          if List.compareLex compare t.1 u.1 = .gt then (t :: u :: run) :: runs
          else [t] :: (u :: run) :: runs
      | runs => [t] :: runs

/-- Merge neighbouring runs in pairs, halving their number. -/
def mvMergePairs {n : Nat} (fuel : Nat) :
    List (List (MvKeyedTerm n)) → List (List (MvKeyedTerm n))
  | [] => []
  | [run] => [run]
  | a :: b :: rest => mvMergeKeyed fuel a b :: mvMergePairs fuel rest

/--
Merge runs into one by rounds of `mvMergePairs`. The number of rounds is bounded by `passes`,
and the number of runs is enough; if the rounds run out the runs are concatenated.
-/
def mvMergeRuns {n : Nat} (fuel : Nat) :
    Nat → List (List (MvKeyedTerm n)) → List (MvKeyedTerm n)
  | _, [] => []
  | _, [run] => run
  | 0, a :: b :: rest => (a :: b :: rest).flatten
  | passes + 1, a :: b :: rest => mvMergeRuns fuel passes (mvMergePairs fuel (a :: b :: rest))

/--
Canonicalize a sparse polynomial: drop zero coefficients, key every monomial once, and merge
the strictly descending runs of the input, adding the coefficients of equal monomials. The
result has nonzero coefficients and distinct monomials in descending graded lexicographic order.
Canonical input is one run and costs a single pass.
-/
def mvNormalize {n : Nat} (poly : MvPoly n) : MvPoly n :=
  let keyed := (poly.filter fun term ↦ term.1 ≠ 0).map fun term ↦ (mvKey term.2, term)
  let size := keyed.length
  (mvMergeRuns size size (mvRuns keyed)).map Prod.snd

/-- Add ordered multivariate polynomials and canonicalize the result. Two canonical inputs are
two runs, so the sum is a single merge. -/
def mvAdd {n : Nat} (p q : MvPoly n) : MvPoly n :=
  mvNormalize (p ++ q)

/-- Negate coefficients termwise, preserving canonicality when the input is canonical. -/
def mvNeg {n : Nat} (p : MvPoly n) : MvPoly n :=
  p.map fun term ↦ (-term.1, term.2)

/-- Subtract ordered multivariate polynomials and canonicalize the result. -/
def mvSub {n : Nat} (p q : MvPoly n) : MvPoly n :=
  mvAdd p (mvNeg q)

/-- Multiply every term by a scalar and monomial, then canonicalize. -/
def mvScaleMonomial {n : Nat} (coeff : Rat) (mono : MvMonomial n) (p : MvPoly n) :
    MvPoly n :=
  mvNormalize <| p.map fun term ↦ (coeff * term.1, mvMul mono term.2)

/-- Multiply ordered multivariate polynomials and canonicalize the result. When `q` is canonical,
each scaled row `tp * q` is a strictly descending run and the product merges the rows. -/
def mvMulPoly {n : Nat} (p q : MvPoly n) : MvPoly n :=
  mvNormalize <| p.flatMap fun tp ↦
    q.map fun tq ↦ (tp.1 * tq.1, mvMul tp.2 tq.2)

/-- Power of an ordered multivariate polynomial. -/
def mvPowPoly {n : Nat} (p : MvPoly n) : Nat → MvPoly n
  | 0 => [(1, mvOne n)]
  | k + 1 => mvMulPoly p (mvPowPoly p k)

/--
Leading term after canonicalization. This ignores zero coefficients introduced
by raw input lists before selecting the leading monomial.
-/
def mvLeadingTermNormalized? {n : Nat} (poly : MvPoly n) :
    Option (Rat × MvMonomial n) :=
  mvLeadingTerm? (mvNormalize poly)

/-- The value of a polynomial that is a single constant term. -/
def mvConstant? {n : Nat} : MvPoly n → Option Rat
  | [(c, m)] => if m = mvOne n then some c else none
  | _ => none

/--
Reflect a symbolic polynomial expression into the ordered multivariate
representation. A quotient is reflected when its divisor is a nonzero constant.

Unsupported heads such as `sin`, `exp`, `log`, and `sqrt` return `none` instead
of becoming opaque factors: the sparse polynomial algorithms should run only
on the polynomial fragment.
-/
def mvPolyOf? {n : Nat} : Verified.Expr (Fin n) → Option (MvPoly n)
  | .nat k =>
      if k = 0 then some [] else some [((k : Rat), mvOne n)]
  | .int z =>
      if z = 0 then some [] else some [((z : Rat), mvOne n)]
  | .rat num den =>
      let q := Rat.divInt num (den : Int)
      if q = 0 then some [] else some [(q, mvOne n)]
  | .var i => some [(1, mvVar i)]
  | .add a b => do
      let pa ← mvPolyOf? a
      let pb ← mvPolyOf? b
      some (mvAdd pa pb)
  | .sub a b => do
      let pa ← mvPolyOf? a
      let pb ← mvPolyOf? b
      some (mvSub pa pb)
  | .neg a => do
      let pa ← mvPolyOf? a
      some (mvNeg pa)
  | .mul a b => do
      let pa ← mvPolyOf? a
      let pb ← mvPolyOf? b
      some (mvMulPoly pa pb)
  | .pow a k =>
      match mvMonomialOf? a with
      | some mono => some [(1, mvPowMonomial mono k)]
      | none => do
          let pa ← mvPolyOf? a
          some (mvPowPoly pa k)
  | .div a b => do
      let pa ← mvPolyOf? a
      let pb ← mvPolyOf? b
      let c ← mvConstant? pb
      if c = 0 then none else some (mvMulPoly pa [(c⁻¹, mvOne n)])
  | _ => none

end Alg

end Verified.Expr
end CAS

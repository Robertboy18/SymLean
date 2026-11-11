/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.Sparse.Semantics

/-!
# Multivariate polynomial gcd candidates

Greatest-common-divisor candidates `gcd` for sparse multivariate polynomials over `ℚ`, the exact
quotients `exactQuotient?` and `exactQuotientExpr?`, and the monic scaling `monic`. They only
propose: no theorem relates an output to a divisibility statement.

## Implementation notes

We compute gcds by the classical recursive method. A polynomial in the variables `x₀, …, xₙ₋₁` is
read as a univariate polynomial in `x₀` whose coefficients are polynomials in the remaining
variables. The content of each input (the gcd of those coefficients, computed recursively) is
divided out, and the primitive parts are reduced by a pseudo-remainder sequence whose remainders
are made primitive after every step, which keeps the coefficients small. By Gauss's lemma the gcd
is the product of the gcd of the two contents and the last nonzero primitive remainder. Exact
division reduces leading terms in graded lexicographic order.

The closed-form canonicalizer (`Canonical.propose`) uses a cancellation only after
`Canonical.Reduction.valid` has checked the two factorization identities on the sparse
representation; the equation-hint route of `cas` certifies the multiplier it obtains from
`exactQuotientExpr?` with `linear_combination`; and the algebra commands, which call `gcd` and
`exactQuotient?` through `CAS.Command.Algebra.gcdPoly` and `CAS.Command.Algebra.exactDiv?`, print
only statements whose proofs the kernel checks. A wrong or fuel-exhausted answer can therefore
cost a cancellation, never soundness. All loops are structurally recursive on explicit fuel so
that the kernel evaluates them without well-founded recursion.

## References

* Keith O. Geddes, Stephen R. Czapor and George Labahn, *Algorithms for Computer Algebra*, Kluwer
  Academic Publishers, Dordrecht, 1992, <https://doi.org/10.1007/b102438>. Chapter 7, Polynomial
  GCD Computation, pp. 279-335.
-/

@[expose] public section

namespace CAS.Polynomial.Sparse.Multivariate

open CAS.Verified.Expr.Alg

/-- Degree of a sparse polynomial in the coordinate `i`; the zero polynomial has degree `0`. -/
def degreeIn {n : Nat} (i : Fin n) (p : MvPoly n) : Nat :=
  p.foldl (fun degree term ↦ max degree (term.2 i)) 0

/-- Coefficient of `x_i ^ d` in the canonical polynomial `p`, a polynomial free of `x_i`. It is
canonical without normalization: the terms of `p` of degree `d` in `x_i` keep their graded
lexicographic order when `x_i` is removed from all of them. -/
def coefficientIn {n : Nat} (i : Fin n) (d : Nat) (p : MvPoly n) : MvPoly n :=
  p.filterMap fun term ↦
    if term.2 i = d then some (term.1, fun j ↦ if j = i then 0 else term.2 j) else none

/-- Leading coefficient of the canonical polynomial `p` read as a polynomial in `x_i`. -/
def leadingCoefficientIn {n : Nat} (i : Fin n) (p : MvPoly n) : MvPoly n :=
  coefficientIn i (degreeIn i p) p

/-- The nonzero coefficients of the canonical polynomial `p` read as a polynomial in `x_i`. -/
def coefficientsIn {n : Nat} (i : Fin n) (p : MvPoly n) : List (MvPoly n) :=
  (List.range (degreeIn i p + 1)).filterMap fun d ↦
    let coefficient := coefficientIn i d p
    if coefficient.isEmpty then none else some coefficient

/-- Multiply a sparse polynomial by the monomial `x_i ^ e`. -/
def shiftIn {n : Nat} (i : Fin n) (e : Nat) (p : MvPoly n) : MvPoly n :=
  mvScaleMonomial 1 (mvPowMonomial (mvVar i) e) p

/-- Scale a sparse polynomial so that its leading coefficient in graded lexicographic order is
`1`; the zero polynomial stays zero. -/
def monic {n : Nat} (p : MvPoly n) : MvPoly n :=
  match mvLeadingTerm? (mvNormalize p) with
  | none => []
  | some lead => mvScaleMonomial (1 / lead.1) (mvOne n) p

/-- Fuel-bounded pseudo-division loop in the coordinate `i`.

Each step replaces the remainder `r` by `lc(b) * r - lc(r) * x_i ^ (deg r - deg b) * b`, where the
leading coefficients and degrees are taken in `x_i`, until the degree of `r` drops below that of
`b`. Every step lowers the degree of `r` in `x_i`, so `deg a + 1` steps suffice for a dividend
`a`. -/
def pseudoRemainderAux {n : Nat} (i : Fin n) (b leadB : MvPoly n) (degreeB : Nat) :
    Nat → MvPoly n → MvPoly n
  | 0, r => r
  | fuel + 1, r =>
      if r.isEmpty then
        r
      else
        let degreeR := degreeIn i r
        if degreeR < degreeB then
          r
        else
          pseudoRemainderAux i b leadB degreeB fuel
            (mvSub (mvMulPoly leadB r)
              (mvMulPoly (shiftIn i (degreeR - degreeB) (leadingCoefficientIn i r)) b))

/-- Pseudo-remainder of `a` by the nonzero polynomial `b` with respect to `x_i`: a polynomial of
the form `lc(b) ^ s * a - q * b` whose degree in `x_i` is below that of `b`. -/
def pseudoRemainder {n : Nat} (i : Fin n) (a b : MvPoly n) : MvPoly n :=
  pseudoRemainderAux i b (leadingCoefficientIn i b) (degreeIn i b) (degreeIn i a + 1) a

/-- Fuel-bounded exact division by leading-term reduction in graded lexicographic order.

The accumulated quotient is returned when the remainder reaches zero. The division fails when the
leading monomial of the remainder is not divisible by the leading monomial of the divisor or the
fuel runs out with a nonzero remainder. -/
def exactQuotientAux {n : Nat} (b : MvPoly n) (leadB : Rat × MvMonomial n) :
    Nat → MvPoly n → MvPoly n → Option (MvPoly n)
  | 0, quotient, remainder => if remainder.isEmpty then some quotient else none
  | fuel + 1, quotient, remainder =>
      match mvLeadingTerm? remainder with
      | none => some quotient
      | some leadR => do
          let mono ← mvQuotient? leadB.2 leadR.2
          let coeff := leadR.1 / leadB.1
          exactQuotientAux b leadB fuel (mvAdd quotient [(coeff, mono)])
            (mvSub remainder (mvScaleMonomial coeff mono b))

/-- Upper bound `(d + 1) ^ n` on the number of monomials of total degree at most `d` in `n`
variables; it bounds the steps of an exact division whose dividend has leading total degree `d`,
since every intermediate remainder stays within that degree. -/
def monomialBound (n d : Nat) : Nat :=
  (d + 1) ^ n

/-- Exact quotient `a / b` of sparse polynomials, or `none` when `b` is zero or does not divide
`a`. -/
def exactQuotient? {n : Nat} (a b : MvPoly n) : Option (MvPoly n) :=
  let a := mvNormalize a
  let b := mvNormalize b
  match mvLeadingTerm? b with
  | none => none
  | some leadB =>
      let degree := match mvLeadingTerm? a with
        | none => 0
        | some leadA => mvTotalDegree leadA.2
      exactQuotientAux b leadB (monomialBound n degree) [] a

/-- Exact quotient of two polynomial expressions over `Fin n`: both are reflected into the sparse
representation (`mvPolyOf?`), divided (`exactQuotient?`), and the quotient is rendered back as an
ordered polynomial expression (`mvPolyExpr`). The result is `none` when an expression is not a
polynomial in its variables, the divisor is zero, or the division is not exact. -/
def exactQuotientExpr? {n : Nat} (dividend divisor : Verified.Expr (Fin n)) :
    Option (Verified.Expr (Fin n)) := do
  let quotient ← exactQuotient? (← mvPolyOf? dividend) (← mvPolyOf? divisor)
  pure (mvPolyExpr quotient)

/-- Content of `p` with respect to `x_i`: the gcd, computed by `gcd`, of its coefficients read as
polynomials in the remaining variables. -/
def contentWith {n : Nat} (gcd : MvPoly n → MvPoly n → MvPoly n) (i : Fin n)
    (p : MvPoly n) : MvPoly n :=
  (coefficientsIn i p).foldl gcd []

/-- Primitive part of `p` with respect to `x_i`, made monic. If the exact division by the content
fails, which only a defect of the candidate generation could cause, `p` itself is returned
monic. -/
def primitivePartWith {n : Nat} (gcd : MvPoly n → MvPoly n → MvPoly n) (i : Fin n)
    (p : MvPoly n) : MvPoly n :=
  monic ((exactQuotient? p (contentWith gcd i p)).getD p)

/-- Fuel-bounded primitive pseudo-remainder sequence in `x_i`.

The arguments are the two current primitive polynomials, the first of degree at least that of the
second after the swap step. Each round replaces them by the second polynomial and the primitive
part of their pseudo-remainder, and the last nonzero polynomial is the gcd of the primitive
inputs. -/
def primitiveRemainderSequence {n : Nat} (gcd : MvPoly n → MvPoly n → MvPoly n) (i : Fin n) :
    Nat → MvPoly n → MvPoly n → MvPoly n
  | 0, a, _ => primitivePartWith gcd i a
  | fuel + 1, a, b =>
      if b.isEmpty then
        primitivePartWith gcd i a
      else if degreeIn i a < degreeIn i b then
        primitiveRemainderSequence gcd i fuel b a
      else
        primitiveRemainderSequence gcd i fuel b
          (primitivePartWith gcd i (pseudoRemainder i a b))

/-- Gcd candidate of two sparse polynomials in the listed variables, by recursion on the list.

With no variables left the inputs are constants, whose gcd is `1` unless both are zero. Otherwise
the first listed variable is the main variable: the contents of the two inputs are extracted with
the gcd of the remaining variables, and the primitive parts enter the primitive remainder
sequence. The result is canonical and monic: the gcd of the contents and the last primitive
remainder are monic, and so is their product, because the leading term of a product is the
product of the leading terms. -/
def gcdIn {n : Nat} : List (Fin n) → MvPoly n → MvPoly n → MvPoly n
  | [], a, b =>
      if (mvNormalize a).isEmpty && (mvNormalize b).isEmpty then [] else [(1, mvOne n)]
  | i :: rest, a, b =>
      let a := mvNormalize a
      let b := mvNormalize b
      if a.isEmpty then
        monic b
      else if b.isEmpty then
        monic a
      else
        let gcdRest : MvPoly n → MvPoly n → MvPoly n := fun p q ↦ gcdIn rest p q
        let contentA := contentWith gcdRest i a
        let contentB := contentWith gcdRest i b
        mvMulPoly (gcdRest contentA contentB)
          (primitiveRemainderSequence gcdRest i (degreeIn i a + degreeIn i b + 2)
            (monic ((exactQuotient? a contentA).getD a))
            (monic ((exactQuotient? b contentB).getD b)))

/-- Monic gcd candidate of two sparse polynomials in all `n` coordinates. -/
def gcd {n : Nat} (a b : MvPoly n) : MvPoly n :=
  gcdIn (List.finRange n) a b

end CAS.Polynomial.Sparse.Multivariate

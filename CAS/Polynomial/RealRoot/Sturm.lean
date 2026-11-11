/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import CAS.Polynomial.ExactDivision

/-!
# Exact Sturm-chain certificates

The executable algebraic half of certified Sturm root counting. A `SturmCertificate` contains a
proposed polynomial chain and the quotients relating consecutive entries. The checker `valid`
verifies:

* the chain begins with `p` and `p'`;
* every recurrence has the Sturm sign convention
  `sᵢ₋₁ = qᵢ sᵢ - sᵢ₊₁`;
* remainders strictly decrease in degree; and
* the terminal polynomial is a nonzero constant.

Endpoint signs are exact rational `SignType.sign` computations (`variationAt`,
`variationDifference`). The analytic bridge `SturmCertificate.variationDifference_eq_rootSet_ncard`
in `SturmTheorem.lean` identifies the variation difference with the number of roots.

## Implementation notes

Each recurrence is checked as an exact division with remainder (`DivisionResult.valid`) whose
remainder is the negated next member (`signedRemainder`). The signed remainder sequence of `p`
and `p'`, the Sturm sequence of `p` [BPR, Definition 1.15 and Section 2.2.2], passes this check;
since a zero divisor carries no degree condition, other chains with a zero member pass it too. We
check a proposed chain and never compute one: SymLean has no generator for `SturmCertificate`,
and the root commands use the root lists of `RootList.lean` instead.

Through the recurrences a common root of `p` and `p'` would be a root of every member, the
terminal included, so only a polynomial without repeated roots has a certificate. This is the
case of Sturm's rule (no. 2 of the memoir). For a polynomial with repeated roots,
`PolynomialIsolationCertificate` pairs a square-free polynomial with the same real roots
(`RadicalCertificate`) with a chain for that polynomial. This is the reduction that Sturm recalls
at the start of no. 18 (p. 305); we do not use his extension of the rule to repeated roots.

`variationAt` omits zero values before it counts sign changes, as Sturm does when an
intermediate member vanishes at an endpoint (no. 8).

## References

* C. Sturm, "Mémoire sur la résolution des équations numériques", *Mémoires présentés par divers
  savans à l'Académie royale des sciences de l'Institut de France, Sciences mathématiques et
  physiques* 6 (1835), pp. 271-318, <https://archive.org/details/mmoirespresent06scie>.
  The rule for an equation without repeated roots (nos. 1 and 2), intermediate members that
  vanish at an endpoint (no. 8), and the reduction of an equation with repeated roots to
  equations without them (start of no. 18, p. 305).
* Saugata Basu, Richard Pollack and Marie-Françoise Roy, *Algorithms in Real Algebraic Geometry*,
  2nd ed., Algorithms and Computation in Mathematics 10, Springer, Berlin, 2006,
  <https://doi.org/10.1007/3-540-33099-2>. Definition 1.15 and Section 2.2.2, numbered as in the
  authors' online version.
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Sparse

/-- A proposed exact Sturm chain and its Euclidean quotients. -/
structure SturmCertificate where
  /-- Polynomial sequence beginning with `p, p'` and ending in a nonzero constant. -/
  chain : List Sparse.Univariate
  /-- Euclidean quotients certifying each signed-remainder recurrence in `chain`. -/
  quotients : List Sparse.Univariate
deriving DecidableEq

namespace SturmCertificate

/-- Signed Euclidean remainder represented by the next Sturm-chain member. -/
def signedRemainder : List Sparse.Univariate → Sparse.Univariate
  | [] => Sparse.zero
  | next :: _ => Verified.Expr.Alg.mvNeg next

/-- Exact checker for every Euclidean recurrence in a chain suffix.

The terminal member must pass both the normalized degree and nonzero tests and
the derivative and value-at-zero tests. The latter pair supplies the semantic
facts used by `recurrence_terminal_nonzero`, without unfolding the sparse
term-order implementation. -/
def recurrenceValid :
    List Sparse.Univariate → List Sparse.Univariate → Bool
  | [last], [] =>
      !Sparse.isZero last &&
        decide (Sparse.Univariate.degree last = 0) &&
        Sparse.isZero
          (Sparse.derivative (0 : Fin 1) last) &&
        decide (Sparse.evalRat last 0 ≠ 0)
  | dividend :: divisor :: tail, quotient :: quotients =>
      let division : Sparse.Univariate.DivisionResult :=
        { quotient := quotient
          remainder := signedRemainder tail }
      division.valid dividend divisor &&
        recurrenceValid (divisor :: tail) quotients
  | _, _ => false

/-- Exact checker for the initial derivative pair and every Sturm recurrence. -/
def valid (polynomial : Sparse.Univariate)
    (certificate : SturmCertificate) : Bool :=
  match certificate.chain with
  | first :: derivative :: _ =>
      Sparse.identityHolds first polynomial &&
        Sparse.identityHolds derivative
          (Sparse.derivative (0 : Fin 1) polynomial) &&
        recurrenceValid certificate.chain certificate.quotients
  | _ => false

/-- An accepted certificate starts with the requested polynomial. -/
theorem first_polynomial {polynomial first derivative : Sparse.Univariate}
    {tail : List Sparse.Univariate} {quotients : List Sparse.Univariate}
    (hvalid :
      valid polynomial
        { chain := first :: derivative :: tail
          quotients := quotients } = true) :
    Sparse.toRatPolynomial first =
      Sparse.toRatPolynomial polynomial := by
  simp only [valid, Bool.and_eq_true] at hvalid
  exact Sparse.toRatPolynomial_eq_of_isZero_sub _ _
    (by simpa [Sparse.identityHolds] using hvalid.1.1)

/-- An accepted certificate's second entry is the formal derivative candidate. -/
theorem second_polynomial {polynomial first derivative : Sparse.Univariate}
    {tail : List Sparse.Univariate} {quotients : List Sparse.Univariate}
    (hvalid :
      valid polynomial
        { chain := first :: derivative :: tail
          quotients := quotients } = true) :
    Sparse.toRatPolynomial derivative =
      Sparse.toRatPolynomial
        (Sparse.derivative (0 : Fin 1) polynomial) := by
  simp only [valid, Bool.and_eq_true] at hvalid
  exact Sparse.toRatPolynomial_eq_of_isZero_sub _ _
    (by simpa [Sparse.identityHolds] using hvalid.1.2)

/--
The head recurrence of an accepted recurrence suffix is an exact Mathlib
polynomial identity.
-/
theorem recurrence_head_identity
    {dividend divisor quotient : Sparse.Univariate}
    {tail : List Sparse.Univariate}
    {quotients : List Sparse.Univariate}
    (hvalid :
      recurrenceValid (dividend :: divisor :: tail)
        (quotient :: quotients) = true) :
    Sparse.toRatPolynomial dividend =
      Sparse.toRatPolynomial divisor *
          Sparse.toRatPolynomial quotient +
        Sparse.toRatPolynomial (signedRemainder tail) :=
  Sparse.Univariate.DivisionResult.polynomial_identity dividend divisor _
    (Bool.and_eq_true_iff.mp hvalid).1

/-- Validity descends to the next recurrence suffix. -/
theorem recurrence_tail_valid
    {dividend divisor quotient : Sparse.Univariate}
    {tail quotients : List Sparse.Univariate}
    (hvalid :
      recurrenceValid (dividend :: divisor :: tail)
        (quotient :: quotients) = true) :
    recurrenceValid (divisor :: tail) quotients = true :=
  (Bool.and_eq_true_iff.mp hvalid).2

/--
An accepted terminal suffix denotes a nonzero constant real function.

The executable checker validates both a zero formal derivative and a nonzero
value at rational zero.  The mean value theorem then supplies the global
semantic conclusion without depending on the sparse term-order implementation.
-/
theorem recurrence_terminal_nonzero
    {last : Sparse.Univariate}
    (hvalid : recurrenceValid [last] [] = true) :
    ∀ x : ℝ, Sparse.evalReal last x ≠ 0 := by
  simp only [recurrenceValid, Bool.and_eq_true,
    Bool.not_eq_true_eq_eq_false, decide_eq_true_eq] at hvalid
  intro x hx
  have hconst := is_const_of_deriv_eq_zero
    (fun y ↦ (Sparse.hasDerivAt_evalReal last y).differentiableAt)
    (fun y ↦ (Sparse.hasDerivAt_evalReal last y).deriv.trans
      (Sparse.evalReal_eq_zero_of_isZero hvalid.1.2 y)) x 0
  have h := Sparse.evalReal_ratCast last 0
  rw [Rat.cast_zero, ← hconst, hx] at h
  exact hvalid.2 (by exact_mod_cast h.symm)

/-- Full certificate acceptance exposes validity of its recurrence chain. -/
theorem recurrence_valid_of_valid
    {polynomial first derivative : Sparse.Univariate}
    {tail : List Sparse.Univariate} {quotients : List Sparse.Univariate}
    (hvalid :
      valid polynomial
        { chain := first :: derivative :: tail
          quotients := quotients } = true) :
    recurrenceValid (first :: derivative :: tail) quotients = true :=
  (Bool.and_eq_true_iff.mp hvalid).2

/-- Count adjacent changes in a zero-free sign list. -/
def signVariations : List SignType → Nat
  | [] | [_] => 0
  | first :: second :: rest =>
      (if first = second then 0 else 1) +
        signVariations (second :: rest)

/-- Exact Sturm-chain endpoint variation after zero values are omitted. -/
def variationAt (certificate : SturmCertificate) (x : Rat) : Nat :=
  signVariations <|
    certificate.chain.filterMap fun polynomial ↦
      let sign := SignType.sign (Sparse.evalRat polynomial x)
      if sign = 0 then none else some sign

/--
Raw variation drop between two rational endpoints.

This uses `Nat` subtraction, so the result is truncated to zero when the
variation at `right` exceeds the variation at `left`. By itself this
computation is not a certified root count. The theorem
`SturmCertificate.variationDifference_eq_rootSet_ncard` supplies that
interpretation only for an accepted certificate, ordered endpoints satisfying
`left ≤ right`, and endpoints at which the polynomial is nonzero; it counts
distinct roots in the open interval.
-/
def variationDifference (certificate : SturmCertificate)
    (left right : Rat) : Nat :=
  certificate.variationAt left - certificate.variationAt right

end SturmCertificate

end CAS.Polynomial.RealRoot

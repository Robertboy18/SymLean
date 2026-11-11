/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.Sparse

/-!
# Certified square-free radicals

A `RadicalCertificate` for a polynomial `p` proposes a polynomial `q` with the same real roots as
`p`, each of them a simple root of `q` (`evalReal_eq_zero_iff`, `derivative_ne_zero_at_root`). The
Sturm checker accepts only polynomials without repeated roots, so a polynomial with repeated roots
is counted through such a `q`: `PolynomialIsolationCertificate` and
`GlobalPolynomialIsolationCertificate` check their Sturm subdivisions on `q`, the atlas region
`Region.equivalent` carries a region of `q` over to `p`, and a `RootListCertificate` holds one
for its quotient when the quotient is not square-free (`RootListCertificate.radical`).

For original polynomial `p` and proposed radical `q`, the certificate checks

* `p = q * a`;
* `q^N = p * b` for some positive `N`; and
* `u*q + v*q' = 1`.

## Implementation notes

The algorithm that computes a gcd or square-free part need not be trusted: the checker `valid`
decides these finite sparse identities exactly. The first two identities prove equality of zero
sets. The Bézout identity proves that every root of `q` is simple. Together they make `q` the
separable part of `p` in the sense of [BPR, Section 10.1], unique up to a constant factor, which
Lemma 10.13 there identifies as `p / gcd(p, p')`. The generator `RadicalCertificate.generate?`
is in `RadicalGenerator.lean`.

## References

* Saugata Basu, Richard Pollack and Marie-Françoise Roy, *Algorithms in Real Algebraic Geometry*,
  2nd ed., Algorithms and Computation in Mathematics 10, Springer, Berlin, 2006,
  <https://doi.org/10.1007/3-540-33099-2>. Section 10.1 and Lemma 10.13, numbered as in the
  authors' online version.
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Sparse

/-- Finite exact evidence that `radical` is a square-free radical of `p`. -/
structure RadicalCertificate where
  /-- Proposed nonzero square-free polynomial with the same zero set as the original. -/
  radical : Sparse.Univariate
  /-- Cofactor `a` in the checked identity `p = radical * a`. -/
  originalOverRadical : Sparse.Univariate
  /-- Positive exponent `N` used to prove the reverse zero-set inclusion. -/
  exponent : ℕ+
  /-- Cofactor `b` in the checked identity `radical ^ N = p * b`. -/
  radicalPowerOverOriginal : Sparse.Univariate
  /-- Coefficient `u` of `radical` in the checked Bézout identity. -/
  bezoutLeft : Sparse.Univariate
  /-- Coefficient `v` of `radical'` in the checked Bézout identity. -/
  bezoutRight : Sparse.Univariate
deriving DecidableEq

namespace RadicalCertificate

/-- Exact checker for root-set equality and square-freeness evidence. -/
def valid (original : Sparse.Univariate)
    (certificate : RadicalCertificate) : Bool :=
  !Sparse.isZero certificate.radical &&
    Sparse.identityHolds original
      (Verified.Expr.Alg.mvMulPoly certificate.radical
        certificate.originalOverRadical) &&
    Sparse.identityHolds
      (Verified.Expr.Alg.mvPowPoly certificate.radical
        (certificate.exponent : Nat))
      (Verified.Expr.Alg.mvMulPoly original
        certificate.radicalPowerOverOriginal) &&
    Sparse.identityHolds
      (Verified.Expr.Alg.mvAdd
        (Verified.Expr.Alg.mvMulPoly certificate.bezoutLeft
          certificate.radical)
        (Verified.Expr.Alg.mvMulPoly certificate.bezoutRight
          (Sparse.derivative (0 : Fin 1) certificate.radical)))
      (Sparse.monomial 1 0)

private theorem valid_components (original : Sparse.Univariate)
    (certificate : RadicalCertificate)
    (hvalid : certificate.valid original = true) :
    Sparse.isZero certificate.radical = false ∧
      Sparse.identityHolds original
          (Verified.Expr.Alg.mvMulPoly certificate.radical
            certificate.originalOverRadical) = true ∧
      Sparse.identityHolds
          (Verified.Expr.Alg.mvPowPoly certificate.radical
            (certificate.exponent : Nat))
          (Verified.Expr.Alg.mvMulPoly original
            certificate.radicalPowerOverOriginal) = true ∧
      Sparse.identityHolds
          (Verified.Expr.Alg.mvAdd
            (Verified.Expr.Alg.mvMulPoly certificate.bezoutLeft
              certificate.radical)
            (Verified.Expr.Alg.mvMulPoly certificate.bezoutRight
              (Sparse.derivative (0 : Fin 1) certificate.radical)))
          (Sparse.monomial 1 0) = true := by
  simpa only [valid, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, and_assoc] using hvalid

/-- A valid radical certificate proves equality of the original and radical zero sets. -/
theorem evalReal_eq_zero_iff (original : Sparse.Univariate)
    (certificate : RadicalCertificate)
    (hvalid : certificate.valid original = true) (x : ℝ) :
    Sparse.evalReal original x = 0 ↔
      Sparse.evalReal certificate.radical x = 0 := by
  obtain ⟨-, horiginal, hpower, -⟩ := certificate.valid_components original hvalid
  have h1 := Sparse.evalReal_eq_of_isZero_sub (by simpa [Sparse.identityHolds] using horiginal) x
  have h2 := Sparse.evalReal_eq_of_isZero_sub (by simpa [Sparse.identityHolds] using hpower) x
  rw [Sparse.evalReal_mul] at h1 h2
  rw [Sparse.evalReal_pow] at h2
  constructor
  · intro hzero
    exact (pow_eq_zero_iff certificate.exponent.ne_zero).mp (by rw [h2, hzero, zero_mul])
  · intro hzero
    rw [h1, hzero, zero_mul]

/-- Every root of a valid radical is simple. -/
theorem derivative_ne_zero_at_root (original : Sparse.Univariate)
    (certificate : RadicalCertificate)
    (hvalid : certificate.valid original = true) {x : ℝ}
    (hroot : Sparse.evalReal certificate.radical x = 0) :
    Sparse.evalReal
        (Sparse.derivative (0 : Fin 1) certificate.radical) x ≠ 0 := by
  obtain ⟨-, -, -, hbezout⟩ := certificate.valid_components original hvalid
  have h := Sparse.evalReal_eq_of_isZero_sub (by simpa [Sparse.identityHolds] using hbezout) x
  intro hderivative
  rw [Sparse.evalReal_add, Sparse.evalReal_mul, Sparse.evalReal_mul, hroot, hderivative,
    mul_zero, mul_zero, zero_add] at h
  norm_num [Sparse.monomial, Sparse.evalReal, Sparse.univariateMonomial,
    Verified.Expr.Alg.mvOne] at h

end RadicalCertificate

end CAS.Polynomial.RealRoot

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.MathlibBridge
public import CAS.Polynomial.Sparse.Division

/-!
# Checked exact polynomial division

A checker for proposed divisions of univariate sparse polynomials over `ℚ`, with its soundness.
`DivisionResult.valid` accepts a quotient and a remainder when the identity
`dividend = divisor * quotient + remainder` holds after canonical normalization and, for a nonzero
divisor, the remainder is zero or has smaller degree; a zero divisor is accepted with no degree
condition on the remainder. `DivisionResult.evalReal_identity` turns an accepted division into
the identity at every real point, and `DivisionResult.polynomial_identity` into the identity in
Mathlib's `Polynomial ℚ`.

## Implementation notes

The checker does not depend on where the quotient and remainder come from. `generate` proposes
them with `Sparse.Univariate.divide`; the Sturm certificates carry their own quotients, which
`SturmCertificate.recurrenceValid` checks with `DivisionResult.valid` and
`SturmCertificate.recurrence_head_identity` turns into identities with
`DivisionResult.polynomial_identity`. We prove the real identity from the evaluation lemmas of the
sparse arithmetic and get the identity in `Polynomial ℚ` from it by `Polynomial.funext`.
-/

@[expose] public section

namespace CAS.Polynomial

namespace Sparse.Univariate.DivisionResult

/-- Executable checker for the Euclidean identity and remainder-degree condition. -/
def valid (dividend divisor : Sparse.Univariate)
    (certificate : Sparse.Univariate.DivisionResult) : Bool :=
  Sparse.isZero
      (Verified.Expr.Alg.mvSub dividend
        (Verified.Expr.Alg.mvAdd
          (Verified.Expr.Alg.mvMulPoly divisor certificate.quotient)
          certificate.remainder)) &&
    (Sparse.isZero divisor ||
      Sparse.isZero certificate.remainder ||
      decide
        (Sparse.Univariate.degree certificate.remainder <
          Sparse.Univariate.degree divisor))

/-- An accepted certificate proves the pointwise real Euclidean identity. -/
theorem evalReal_identity (dividend divisor : Sparse.Univariate)
    (certificate : Sparse.Univariate.DivisionResult)
    (hvalid : certificate.valid dividend divisor = true) (x : ℝ) :
    Sparse.evalReal dividend x =
      Sparse.evalReal divisor x * Sparse.evalReal certificate.quotient x +
        Sparse.evalReal certificate.remainder x := by
  have hzero := Sparse.evalReal_eq_zero_of_isZero (Bool.and_eq_true_iff.mp hvalid).1 x
  rw [Sparse.evalReal_sub, Sparse.evalReal_add, Sparse.evalReal_mul] at hzero
  linarith

/-- An accepted certificate proves the exact Mathlib polynomial identity over `ℚ`. -/
theorem polynomial_identity (dividend divisor : Sparse.Univariate)
    (certificate : Sparse.Univariate.DivisionResult)
    (hvalid : certificate.valid dividend divisor = true) :
    Sparse.toRatPolynomial dividend =
      Sparse.toRatPolynomial divisor *
          Sparse.toRatPolynomial certificate.quotient +
        Sparse.toRatPolynomial certificate.remainder := by
  refine Polynomial.funext fun x ↦ ?_
  have h := certificate.evalReal_identity dividend divisor hvalid x
  simp only [Sparse.evalReal_ratCast] at h
  simp only [Sparse.eval_toRatPolynomial, Polynomial.eval_add, Polynomial.eval_mul]
  exact_mod_cast h

/-- Candidate certificate produced by the shared sparse long-division routine. -/
def generate (dividend divisor : Sparse.Univariate) :
    Sparse.Univariate.DivisionResult :=
  Sparse.Univariate.divide dividend divisor

end Sparse.Univariate.DivisionResult

end CAS.Polynomial

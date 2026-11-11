/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Chebyshev, Hermite and Bernoulli polynomials

Each command below runs in the build inside `#guard_msgs`, which checks its report; each report's
theorem is kernel-checked when the command runs. Each call of a polynomial in a variable proves
the monomial expansion of Mathlib's own polynomial:

* `#cas (ChebyshevT n x)`, `#cas (ChebyshevU n x)` (Mathematica's `ChebyshevT[n, x]`,
  `ChebyshevU[n, x]`): `Polynomial.Chebyshev.T R n` (`Polynomial.Chebyshev.U R n`) in every
  commutative ring `R : Type`;
* `#cas (HermiteHe n x)`: Mathlib's `Polynomial.hermite n`, the probabilists' polynomial;
* `#cas (HermiteH n x)`: Mathematica's physicists' `HermiteH[n, x] = √2 ^ n Heₙ (√2 x)`, stated
  through Mathlib's `Polynomial.hermite`;
* `#cas (BernoulliB n x)` (Mathematica's `BernoulliB[n, x]`): Mathlib's `Polynomial.bernoulli n`.

The variable may have any name, the degree is any closed integer expression, and
`#cas [expand]` prints the same polynomial. At a rational `q` in place of the variable the call
proves the exact value, and `#cas [N d] (ChebyshevT n q)` (and the other families) adds its first
`d` significant digits, truncated toward zero, with their decimal bounds in the theorem. It
prints `v = digits` when the digits are exact and `v ≈ digits` otherwise. Every other argument of
`#cas [N d]` reaches the existing handlers, as the Legendre and `π` checks show. The degrees are
at most 80 for `ChebyshevT`, `ChebyshevU` and `HermiteHe`, and at most 60 for `HermiteH` and
`BernoulliB`.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/-! ### Chebyshev polynomials, in every commutative ring -/
/--
info: #cas (ChebyshevT 0 x)
Domain: Polynomial.Chebyshev.T R 0, every commutative ring R : Type
Input (polynomial in x): ChebyshevT 0 x
Output (polynomial with integer coefficients): 1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Monomial expansion of ChebyshevT 0
        Proposition: ∀ (R : Type) [inst : CommRing R], Polynomial.Chebyshev.T R 0 = 1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (ChebyshevT 0 x)

/--
info: #cas (ChebyshevT 1 x)
Domain: Polynomial.Chebyshev.T R 1, every commutative ring R : Type
Input (polynomial in x): ChebyshevT 1 x
Output (polynomial with integer coefficients): x

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Monomial expansion of ChebyshevT 1
        Proposition: ∀ (R : Type) [inst : CommRing R], Polynomial.Chebyshev.T R 1 = Polynomial.X
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (ChebyshevT 1 x)

set_option linter.style.longLine false in
/--
info: #cas (ChebyshevT 5 x)
Domain: Polynomial.Chebyshev.T R 5, every commutative ring R : Type
Input (polynomial in x): ChebyshevT 5 x
Output (polynomial with integer coefficients): 16*x^5 - 20*x^3 + 5*x

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Monomial expansion of ChebyshevT 5
        Proposition: ∀ (R : Type) [inst : CommRing R],
          Polynomial.Chebyshev.T R 5 = 16 * Polynomial.X ^ 5 - 20 * Polynomial.X ^ 3 + 5 * Polynomial.X
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (ChebyshevT 5 x)

/--
info: #cas (ChebyshevU 4 x)
Domain: Polynomial.Chebyshev.U R 4, every commutative ring R : Type
Input (polynomial in x): ChebyshevU 4 x
Output (polynomial with integer coefficients): 16*x^4 - 12*x^2 + 1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Monomial expansion of ChebyshevU 4
        Proposition: ∀ (R : Type) [inst : CommRing R],
          Polynomial.Chebyshev.U R 4 = 16 * Polynomial.X ^ 4 - 12 * Polynomial.X ^ 2 + 1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (ChebyshevU 4 x)

/-! ### Hermite polynomials: Mathlib's probabilists' Heₙ and Mathematica's physicists' Hₙ -/
/--
info: #cas (HermiteHe 4 x)
Domain: Polynomial.hermite 4 (probabilists'), ℤ[X]
Input (polynomial in x): HermiteHe 4 x
Output (polynomial with integer coefficients): x^4 - 6*x^2 + 3

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Monomial expansion of HermiteHe 4
        Proposition: Polynomial.hermite 4 = Polynomial.X ^ 4 - 6 * Polynomial.X ^ 2 + 3
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (HermiteHe 4 x)

/--
info: #cas (HermiteH 0 x)
Domain: √2 ^ 0 Polynomial.hermite 0 (√2 x) (physicists'), x ∈ ℝ
Input (polynomial in x): HermiteH 0 x
Output (polynomial with integer coefficients): 1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Monomial expansion of HermiteH 0
        Proposition: ∀ (x : ℝ), √2 ^ 0 * (Polynomial.aeval (√2 * x)) (Polynomial.hermite 0) = 1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (HermiteH 0 x)

/--
info: #cas (HermiteH 1 x)
Domain: √2 ^ 1 Polynomial.hermite 1 (√2 x) (physicists'), x ∈ ℝ
Input (polynomial in x): HermiteH 1 x
Output (polynomial with integer coefficients): 2*x

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Monomial expansion of HermiteH 1
        Proposition: ∀ (x : ℝ), √2 ^ 1 * (Polynomial.aeval (√2 * x)) (Polynomial.hermite 1) = 2 * x
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (HermiteH 1 x)

/--
info: #cas (HermiteH 4 x)
Domain: √2 ^ 4 Polynomial.hermite 4 (√2 x) (physicists'), x ∈ ℝ
Input (polynomial in x): HermiteH 4 x
Output (polynomial with integer coefficients): 16*x^4 - 48*x^2 + 12

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Monomial expansion of HermiteH 4
        Proposition: ∀ (x : ℝ),
          √2 ^ 4 * (Polynomial.aeval (√2 * x)) (Polynomial.hermite 4) = 16 * x ^ 4 - 48 * x ^ 2 + 12
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (HermiteH 4 x)

set_option linter.style.longLine false in
/--
info: #cas (HermiteH 5 x)
Domain: √2 ^ 5 Polynomial.hermite 5 (√2 x) (physicists'), x ∈ ℝ
Input (polynomial in x): HermiteH 5 x
Output (polynomial with integer coefficients): 32*x^5 - 160*x^3 + 120*x

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Monomial expansion of HermiteH 5
        Proposition: ∀ (x : ℝ),
          √2 ^ 5 * (Polynomial.aeval (√2 * x)) (Polynomial.hermite 5) = 32 * x ^ 5 - 160 * x ^ 3 + 120 * x
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (HermiteH 5 x)

/-! ### Bernoulli polynomials -/
/--
info: #cas (BernoulliB 0 x)
Domain: Polynomial.bernoulli 0, x ∈ ℝ
Input (polynomial in x): BernoulliB 0 x
Output (polynomial with exact rational coefficients): 1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Monomial expansion of BernoulliB 0
        Proposition: ∀ (x : ℝ), (Polynomial.aeval x) (Polynomial.bernoulli 0) = 1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (BernoulliB 0 x)

/--
info: #cas (BernoulliB 1 x)
Domain: Polynomial.bernoulli 1, x ∈ ℝ
Input (polynomial in x): BernoulliB 1 x
Output (polynomial with exact rational coefficients): x - 1/2

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Monomial expansion of BernoulliB 1
        Proposition: ∀ (x : ℝ), (Polynomial.aeval x) (Polynomial.bernoulli 1) = x - 1 / 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (BernoulliB 1 x)

set_option linter.style.longLine false in
/--
info: #cas (BernoulliB 4 x)
Domain: Polynomial.bernoulli 4, x ∈ ℝ
Input (polynomial in x): BernoulliB 4 x
Output (polynomial with exact rational coefficients): x^4 - 2*x^3 + x^2 - 1/30

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Monomial expansion of BernoulliB 4
        Proposition: ∀ (x : ℝ), (Polynomial.aeval x) (Polynomial.bernoulli 4) = x ^ 4 - 2 * x ^ 3 + x ^ 2 - 1 / 30
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (BernoulliB 4 x)

/-! ### Any variable, degrees as integer expressions, `[expand]` -/
/--
info: #cas (HermiteHe 3 t)
Domain: Polynomial.hermite 3 (probabilists'), ℤ[X]
Input (polynomial in t): HermiteHe 3 t
Output (polynomial with integer coefficients): t^3 - 3*t

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (HermiteHe 3 t)

/--
info: #cas (ChebyshevT (2 + 1) x)
Domain: Polynomial.Chebyshev.T R 3, every commutative ring R : Type
Input (polynomial in x): ChebyshevT 3 x
Output (polynomial with integer coefficients): 4*x^3 - 3*x

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (ChebyshevT (2 + 1) x)

/--
info: #cas [expand]
Domain: Polynomial.bernoulli 2, y ∈ ℝ
Input (polynomial in y): BernoulliB 2 y
Output (polynomial with exact rational coefficients): y^2 - y + 1/6

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [expand] (BernoulliB 2 y)

/-! ### Values at rational points -/
/--
info: #cas (ChebyshevT 5 (1/2))
Domain: ChebyshevT polynomial at a rational point
Input (scalar ℝ): ChebyshevT 5 (1/2)
Output (exact rational value): 1/2

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Exact value of ChebyshevT 5
        Proposition: Polynomial.eval (1 / 2) (Polynomial.Chebyshev.T ℝ 5) = 1 / 2
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (ChebyshevT 5 (1/2))

/--
info: #cas [N 10]
Domain: ChebyshevT polynomial at a rational point
Input (scalar ℝ): (ChebyshevT 5 (1/3))
Output (exact rational value and its first 10 significant digits, truncated): 241/243 ≈ 0.9917695473

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Exact value and digits of ChebyshevT 5
        Proposition: Polynomial.eval (1 / 3) (Polynomial.Chebyshev.T ℝ 5) = 241 / 243 ∧
          9917695473 / 10 ^ 10 ≤ Polynomial.eval (1 / 3) (Polynomial.Chebyshev.T ℝ 5) ∧
            Polynomial.eval (1 / 3) (Polynomial.Chebyshev.T ℝ 5) < (9917695473 + 1) / 10 ^ 10
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 10] (ChebyshevT 5 (1/3))

/--
info: #cas [N 10]
Domain: ChebyshevU polynomial at a rational point
Input (scalar ℝ): (ChebyshevU 3 (-1/2))
Output (exact rational value and its first 10 significant digits, truncated): 1 = 1.000000000

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Exact value and digits of ChebyshevU 3
        Proposition: Polynomial.eval (-(1 / 2)) (Polynomial.Chebyshev.U ℝ 3) = 1 ∧
          1000000000 / 10 ^ 9 ≤ Polynomial.eval (-(1 / 2)) (Polynomial.Chebyshev.U ℝ 3) ∧
            Polynomial.eval (-(1 / 2)) (Polynomial.Chebyshev.U ℝ 3) < (1000000000 + 1) / 10 ^ 9
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 10] (ChebyshevU 3 (-1/2))

set_option linter.style.longLine false in
/--
info: #cas [N 10]
Domain: HermiteH polynomial at a rational point
Input (scalar ℝ): (HermiteH 3 (1/2))
Output (exact rational value and its first 10 significant digits, truncated): -5 = -5.000000000

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Exact value and digits of HermiteH 3
        Proposition: √2 ^ 3 * (Polynomial.aeval (√2 * (1 / 2))) (Polynomial.hermite 3) = -5 ∧
          -(5000000000 + 1) / 10 ^ 9 < √2 ^ 3 * (Polynomial.aeval (√2 * (1 / 2))) (Polynomial.hermite 3) ∧
            √2 ^ 3 * (Polynomial.aeval (√2 * (1 / 2))) (Polynomial.hermite 3) ≤ -5000000000 / 10 ^ 9
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 10] (HermiteH 3 (1/2))

/--
info: #cas [N 10]
Domain: HermiteHe polynomial at a rational point
Input (scalar ℝ): (HermiteHe 3 2)
Output (exact rational value and its first 10 significant digits, truncated): 2 = 2.000000000

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Exact value and digits of HermiteHe 3
        Proposition: (Polynomial.aeval 2) (Polynomial.hermite 3) = 2 ∧
          2000000000 / 10 ^ 9 ≤ (Polynomial.aeval 2) (Polynomial.hermite 3) ∧
            (Polynomial.aeval 2) (Polynomial.hermite 3) < (2000000000 + 1) / 10 ^ 9
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 10] (HermiteHe 3 2)

/--
info: #cas [N 10]
Domain: BernoulliB polynomial at a rational point
Input (scalar ℝ): (BernoulliB 2 (1/2))
Output (exact rational value and its first 10 significant digits, truncated): -1/12 ≈ -0.08333333333

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Exact value and digits of BernoulliB 2
        Proposition: (Polynomial.aeval (1 / 2)) (Polynomial.bernoulli 2) = -(1 / 12) ∧
          -(8333333333 + 1) / 10 ^ 11 < (Polynomial.aeval (1 / 2)) (Polynomial.bernoulli 2) ∧
            (Polynomial.aeval (1 / 2)) (Polynomial.bernoulli 2) ≤ -8333333333 / 10 ^ 11
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 10] (BernoulliB 2 (1/2))

/--
info: #cas [N 2]
Domain: HermiteH polynomial at a rational point
Input (scalar ℝ): (HermiteH 6 2)
Output (exact rational value and its first 2 significant digits, truncated): -824 ≈ -8.2 × 10^2

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Exact value and digits of HermiteH 6
        Proposition: √2 ^ 6 * (Polynomial.aeval (√2 * 2)) (Polynomial.hermite 6) = -824 ∧
          -(82 + 1) * 10 ^ 1 < √2 ^ 6 * (Polynomial.aeval (√2 * 2)) (Polynomial.hermite 6) ∧
            √2 ^ 6 * (Polynomial.aeval (√2 * 2)) (Polynomial.hermite 6) ≤ -82 * 10 ^ 1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 2] (HermiteH 6 2)

/--
info: #cas [N 10]
Domain: HermiteHe polynomial at a rational point
Input (scalar ℝ): (HermiteHe 3 0)
Output (exact rational value): 0

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Exact value of HermiteHe 3
        Proposition: (Polynomial.aeval 0) (Polynomial.hermite 3) = 0
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 10] (HermiteHe 3 0)

/--
info: #cas [N 10]
Domain: ChebyshevT polynomial at a rational point
Input (scalar ℝ): (ChebyshevT 3 0)
Output (exact rational value): 0

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Exact value of ChebyshevT 3
        Proposition: Polynomial.eval 0 (Polynomial.Chebyshev.T ℝ 3) = 0
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 10] (ChebyshevT 3 0)

/--
info: #cas [N 10]
Domain: BernoulliB polynomial at a rational point
Input (scalar ℝ): (BernoulliB 1 (1/2))
Output (exact rational value): 0

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Exact value of BernoulliB 1
        Proposition: (Polynomial.aeval (1 / 2)) (Polynomial.bernoulli 1) = 0
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 10] (BernoulliB 1 (1/2))

/-! ### Other arguments of `#cas [N d]` reach the existing handlers -/
set_option linter.style.longLine false in
/--
info: #cas [N 10]
Domain: Legendre polynomial at a rational point
Input (scalar ℝ): (LegendreP 2 (1/2))
Output (exact rational value and its first 10 significant digits, truncated): -1/8 = -0.1250000000

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Exact value and digits of the Legendre polynomial
        Proposition: Polynomial.eval (1 / 2) (CAS.Analysis.SpecialFunctions.legendre 2) = -(1 / 8) ∧
          -(1250000000 + 1) / 10 ^ 10 < Polynomial.eval (1 / 2) (CAS.Analysis.SpecialFunctions.legendre 2) ∧
            Polynomial.eval (1 / 2) (CAS.Analysis.SpecialFunctions.legendre 2) ≤ -1250000000 / 10 ^ 10
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Analysis.SpecialFunctions.legendre_eval_ratCast
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 10] (LegendreP 2 (1/2))

/--
info: #cas [N 5]
Domain: closed real expression
Input (scalar ℝ): (pi)
Output (first 5 significant digits, truncated): 3.1415

[CAS.Command.details] More details
  [CAS.Command.computation] Certified numerical evaluation
    Working precision: 56 bits, 29 series terms, 51 logarithm terms
    Guarantee: every printed digit is a digit of the real value, truncated toward zero
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Certified decimal digits
        Proposition: 31415 / 10 ^ 4 ≤ Real.pi ∧ Real.pi < (31415 + 1) / 10 ^ 4
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.DigitsEval.eval_sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 5] (pi)

/-! ### Refusals -/
/--
error: ChebyshevT accepts degrees up to 80
-/
#guard_msgs in
#cas (ChebyshevT 81 x)

/--
error: BernoulliB accepts degrees up to 60
-/
#guard_msgs in
#cas (BernoulliB 61 x)

/--
error: `[N d]` evaluates `ChebyshevT n x` at a number; `#cas (ChebyshevT 3 x)` gives the polynomial
-/
#guard_msgs in
#cas [N 10] (ChebyshevT 3 x)

/--
error: HermiteH accepts degrees up to 60
-/
#guard_msgs in
#cas [N 10] (HermiteH 61 1)

/--
error: N accepts between 1 and 2000 digits
-/
#guard_msgs in
#cas [N 0] (ChebyshevT 2 1)

/--
error: N accepts between 1 and 2000 digits
-/
#guard_msgs in
#cas [N 2001] (ChebyshevT 2 1)

/--
error: HermiteH takes 2 arguments, as in `HermiteH n x`; the call has 1
-/
#guard_msgs in
#cas (HermiteH 3)

/--
error: BernoulliB takes 1 or 2 arguments, as in `BernoulliB n` or `BernoulliB n x`; the call has 3
-/
#guard_msgs in
#cas (BernoulliB 2 x y)

/--
error: ChebyshevT takes a natural number as the degree; `-1` is negative
-/
#guard_msgs in
#cas (ChebyshevT (-1) x)

set_option linter.style.longLine false in
/--
error: the second argument of `ChebyshevT n x` is a variable, for the polynomial, or a rational number, for its value
-/
#guard_msgs in
#cas (ChebyshevT 2 (x + 1))

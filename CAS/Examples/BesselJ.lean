/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Certified digits of the Bessel function `J_n`

Each command below runs in the build inside `#guard_msgs`, which checks its report; each report's
theorem is kernel-checked when the command runs.

`#cas [N d] (BesselJ n q)` (Mathematica's `N[BesselJ[n, q], d]`) encloses Mathlib's
`Complex.besselJ` at an integer order `n` and a rational point `q`: it proves
`∃ r : ℝ, Complex.besselJ ((n : ℤ) : ℂ) ((q : ℚ) : ℂ) = r ∧ lo ≤ r ∧ r ≤ hi ∧ hi - lo ≤ 1 / 10 ^ d`
and prints the decimal enclosure `[lo, hi]`; its width is part of the theorem. At `q = 0` the
enclosure is a point and the output is the exact value (`J₀ (0) = 1`, `Jₙ (0) = 0` otherwise). A
negative order uses `J₋ₙ = (-1) ^ n Jₙ` (Mathlib's `Complex.besselJ_neg_int`). The limits are
`|n| ≤ 50`, `|q| ≤ 50` with a denominator of at most 1000, and `1 ≤ d ≤ 30`; other inputs are
refused, and every other argument of `#cas [N d]` reaches the existing handlers, as the last
checks show.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/-! ### Values -/
set_option linter.style.longLine false in
/--
info: #cas [N 10]
Domain: Bessel function J_n at a rational point
Input (scalar ℝ): (BesselJ 0 1)
Output (decimal enclosure of width at most 10^-10, with 8 terms of the series): [0.76519768655, 0.76519768656]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of BesselJ 0 1
        Proposition: ∃ r,
          Complex.besselJ ↑0 ↑1 = ↑r ∧
            ↑(15303953731 / 20000000000) ≤ r ∧
              r ≤ ↑(4782485541 / 6250000000) ∧ ↑(4782485541 / 6250000000) - ↑(15303953731 / 20000000000) ≤ 1 / 10 ^ 10
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 10] (BesselJ 0 1)

set_option linter.style.longLine false in
/--
info: #cas [N 10]
Domain: Bessel function J_n at a rational point
Input (scalar ℝ): (BesselJ 2 10)
Output (decimal enclosure of width at most 10^-10, with 22 terms of the series): [0.25463031368, 0.25463031369]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of BesselJ 2 10
        Proposition: ∃ r,
          Complex.besselJ ↑2 ↑10 = ↑r ∧
            ↑(3182878921 / 12500000000) ≤ r ∧
              r ≤ ↑(25463031369 / 100000000000) ∧
                ↑(25463031369 / 100000000000) - ↑(3182878921 / 12500000000) ≤ 1 / 10 ^ 10
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 10] (BesselJ 2 10)

set_option linter.style.longLine false in
/--
info: #cas [N 5]
Domain: Bessel function J_n at a rational point
Input (scalar ℝ): (BesselJ (-3) (1/2))
Output (decimal enclosure of width at most 10^-5, with 3 terms of the series): [-0.002564, -0.002563]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of BesselJ -3 1/2
        Proposition: ∃ r,
          Complex.besselJ ↑(-3) ↑(1 / 2) = ↑r ∧
            ↑(-(641 / 250000)) ≤ r ∧ r ≤ ↑(-(2563 / 1000000)) ∧ ↑(-(2563 / 1000000)) - ↑(-(641 / 250000)) ≤ 1 / 10 ^ 5
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 5] (BesselJ (-3) (1/2))

set_option linter.style.longLine false in
/--
info: #cas [N 5]
Domain: Bessel function J_n at a rational point
Input (scalar ℝ): (BesselJ (-2) (1/2))
Output (decimal enclosure of width at most 10^-5, with 3 terms of the series): [0.030604, 0.030605]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of BesselJ -2 1/2
        Proposition: ∃ r,
          Complex.besselJ ↑(-2) ↑(1 / 2) = ↑r ∧
            ↑(7651 / 250000) ≤ r ∧ r ≤ ↑(6121 / 200000) ∧ ↑(6121 / 200000) - ↑(7651 / 250000) ≤ 1 / 10 ^ 5
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 5] (BesselJ (-2) (1/2))

set_option linter.style.longLine false in
/--
info: #cas [N 30]
Domain: Bessel function J_n at a rational point
Input (scalar ℝ): (BesselJ 0 50)
Output (decimal enclosure of width at most 10^-30, with 97 terms of the series): [0.0558123276692518150047504785294, 0.0558123276692518150047504785295]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of BesselJ 0 50
        Proposition: ∃ r,
          Complex.besselJ ↑0 ↑50 = ↑r ∧
            ↑(279061638346259075023752392647 / 5000000000000000000000000000000) ≤ r ∧
              r ≤ ↑(111624655338503630009500957059 / 2000000000000000000000000000000) ∧
                ↑(111624655338503630009500957059 / 2000000000000000000000000000000) -
                    ↑(279061638346259075023752392647 / 5000000000000000000000000000000) ≤
                  1 / 10 ^ 30
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 30] (BesselJ 0 50)

set_option linter.style.longLine false in
/--
info: #cas [N 20]
Domain: Bessel function J_n at a rational point
Input (scalar ℝ): (BesselJ 1 (-7/3))
Output (decimal enclosure of width at most 10^-20, with 15 terms of the series): [-0.533700789836125818642, -0.533700789836125818641]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of BesselJ 1 -7/3
        Proposition: ∃ r,
          Complex.besselJ ↑1 ↑(-(7 / 3)) = ↑r ∧
            ↑(-(266850394918062909321 / 500000000000000000000)) ≤ r ∧
              r ≤ ↑(-(533700789836125818641 / 1000000000000000000000)) ∧
                ↑(-(533700789836125818641 / 1000000000000000000000)) -
                    ↑(-(266850394918062909321 / 500000000000000000000)) ≤
                  1 / 10 ^ 20
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 20] (BesselJ 1 (-7/3))

/-! ### At zero: the exact value -/
/--
info: #cas [N 5]
Domain: Bessel function J_n at a rational point
Input (scalar ℝ): (BesselJ 0 0)
Output (exact value): 1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of BesselJ 0 0
        Proposition: ∃ r, Complex.besselJ ↑0 ↑0 = ↑r ∧ ↑1 ≤ r ∧ r ≤ ↑1 ∧ ↑1 - ↑1 ≤ 1 / 10 ^ 5
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 5] (BesselJ 0 0)

/--
info: #cas [N 5]
Domain: Bessel function J_n at a rational point
Input (scalar ℝ): (BesselJ (-3) 0)
Output (exact value): 0

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of BesselJ -3 0
        Proposition: ∃ r, Complex.besselJ ↑(-3) ↑0 = ↑r ∧ ↑0 ≤ r ∧ r ≤ ↑0 ∧ ↑0 - ↑0 ≤ 1 / 10 ^ 5
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 5] (BesselJ (-3) 0)

/-! ### Refusals: the limits -/
/--
error: BesselJ accepts at most 30 digits
-/
#guard_msgs in
#cas [N 31] (BesselJ 0 1)

/--
error: N accepts between 1 and 2000 digits
-/
#guard_msgs in
#cas [N 0] (BesselJ 0 1)

/--
error: BesselJ accepts integer orders
-/
#guard_msgs in
#cas [N 5] (BesselJ (1/2) 1)

/--
error: BesselJ accepts orders with |n| ≤ 50
-/
#guard_msgs in
#cas [N 5] (BesselJ 51 1)

/--
error: BesselJ accepts rational points with |q| ≤ 50 and a denominator of at most 1000
-/
#guard_msgs in
#cas [N 5] (BesselJ 0 51)

/--
error: BesselJ accepts rational points with |q| ≤ 50 and a denominator of at most 1000
-/
#guard_msgs in
#cas [N 5] (BesselJ 0 (1/1001))

/-! ### Other arguments of `N` reach the existing handlers -/
/--
info: #cas [N 5]
Domain: ChebyshevT polynomial at a rational point
Input (scalar ℝ): (ChebyshevT 3 (1/2))
Output (exact rational value and its first 5 significant digits, truncated): -1 = -1.0000

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Exact value and digits of ChebyshevT 3
        Proposition: Polynomial.eval (1 / 2) (Polynomial.Chebyshev.T ℝ 3) = -1 ∧
          -(10000 + 1) / 10 ^ 4 < Polynomial.eval (1 / 2) (Polynomial.Chebyshev.T ℝ 3) ∧
            Polynomial.eval (1 / 2) (Polynomial.Chebyshev.T ℝ 3) ≤ -10000 / 10 ^ 4
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 5] (ChebyshevT 3 (1/2))

set_option linter.style.longLine false in
/--
info: #cas [N 5]
Domain: Legendre polynomial at a rational point
Input (scalar ℝ): (LegendreP 3 (1/2))
Output (exact rational value and its first 5 significant digits, truncated): -7/16 = -0.43750

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Exact value and digits of the Legendre polynomial
        Proposition: Polynomial.eval (1 / 2) (CAS.Analysis.SpecialFunctions.legendre 3) = -(7 / 16) ∧
          -(43750 + 1) / 10 ^ 5 < Polynomial.eval (1 / 2) (CAS.Analysis.SpecialFunctions.legendre 3) ∧
            Polynomial.eval (1 / 2) (CAS.Analysis.SpecialFunctions.legendre 3) ≤ -43750 / 10 ^ 5
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Analysis.SpecialFunctions.legendre_eval_ratCast
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [N 5] (LegendreP 3 (1/2))

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

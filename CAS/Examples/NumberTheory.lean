/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Number theory: `powerMod`, `chineseRemainder`, `continuedFraction`, `divisors`, …

The number theory calls and modes of `CAS.Command.NumberTheory`. Each command runs in the build
inside `#guard_msgs`, which checks its report; each report's theorem is kernel-checked when the
command runs. Modular powers are proved by repeated squaring, at a cost that grows with the number
of digits of the exponent.

Primality certificates and integer factorization are Hex's: `#cas (primeQ n)`,
`#cas (moebiusMu n)` and `#cas [factorInteger] n` refuse here, and run in `CASHex/Examples.lean`
in the optional Hex build.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

-- PrimeQ, FactorInteger and MoebiusMu need Hex (CASHex.NumberTheory)
set_option linter.style.longLine false in
/--
error: primeQ needs Hex (`-Khex=on`): primality certificates and integer factorization come from Hex; build with `lake -R -Khex=on build CASHex` and `import CASHex.NumberTheory`
-/
#guard_msgs (error, drop info) in
#cas (primeQ 2305843009213693951)

set_option linter.style.longLine false in
/--
error: factorInteger needs Hex (`-Khex=on`): primality certificates and integer factorization come from Hex; build with `lake -R -Khex=on build CASHex` and `import CASHex.NumberTheory`
-/
#guard_msgs (error, drop info) in
#cas [factorInteger] 360

set_option linter.style.longLine false in
/--
error: moebiusMu needs Hex (`-Khex=on`): primality certificates and integer factorization come from Hex; build with `lake -R -Khex=on build CASHex` and `import CASHex.NumberTheory`
-/
#guard_msgs (error, drop info) in
#cas (moebiusMu 30)

-- PowerMod, ModularInverse, ChineseRemainder, ExtendedGCD, JacobiSymbol
/--
info: #cas (powerMod 2 123456789123456789123456789 1000000007)
Domain: ℕ
Input (natural numbers): 2^123456789123456789123456789 mod 1000000007
Output (modular power): 612059118

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] modular power
        Proposition: 2 ^ 123456789123456789123456789 % 1000000007 = 612059118
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (powerMod 2 123456789123456789123456789 1000000007)

/--
info: #cas (powerMod 3 1000 7)
Domain: ℕ
Input (natural numbers): 3^1000 mod 7
Output (modular power): 4

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (powerMod 3 1000 7)

/--
info: #cas (modularInverse 3 11)
Domain: ZMod 11
Input (integer and modulus): 3 mod 11
Output (modular inverse): 4

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] modular inverse
        Proposition: 3 * 4 = 1 ∧ 3⁻¹ = 4
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (modularInverse 3 11)

/--
info: #cas (modularInverse 6 9)
Domain: ZMod 9
Input (integer and modulus): 6 mod 9
Output (no inverse): none: gcd = 3

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (modularInverse 6 9)

/--
info: #cas (modularInverse (-3) 7)
Domain: ZMod 7
Input (integer and modulus): -3 mod 7
Output (modular inverse): 2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (modularInverse (-3) 7)

set_option linter.style.longLine false in
/--
info: #cas [chineseRemainder]
Domain: ℕ
Input (natural numbers): x ≡ 2 mod 3, x ≡ 3 mod 5, x ≡ 2 mod 7
Output (all solutions): 23 mod 105

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] all solutions
        Proposition: 23 < 105 ∧ ∀ (y : ℕ), (∀ p ∈ [(3, 2), (5, 3), (7, 2)], y ≡ p.2 [MOD p.1]) ↔ y ≡ 23 [MOD 105]
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [chineseRemainder] ([2, 3, 2], [3, 5, 7])

/--
info: #cas [extendedGCD]
Domain: ℕ
Input (natural numbers): (240, 46)
Output (gcd and Bézout coefficients): 2, [-9, 47]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [extendedGCD] (240, 46)

/--
info: #cas (jacobiSymbol 1001 9907)
Domain: ℤ × ℕ
Input (an integer and an odd natural number): (1001 / 9907)
Output (Jacobi symbol): -1

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Jacobi symbol
        Proposition: jacobiSym 1001 9907 = -1
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas (jacobiSymbol 1001 9907)

/--
info: #cas (jacobiSymbol (-1) 7)
Domain: ℤ × ℕ
Input (an integer and an odd natural number): (-1 / 7)
Output (Jacobi symbol): -1

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (jacobiSymbol (-1) 7)

/--
error: jacobiSymbol: expected an odd natural number
-/
#guard_msgs (error, drop info) in
#cas (jacobiSymbol 2 4)

set_option linter.style.longLine false in
/--
info: #cas [chineseRemainder]
Domain: ℕ
Input (natural numbers): x ≡ 2 mod 4, x ≡ 4 mod 6
Output (all solutions): 10 mod 12

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] all solutions
        Proposition: 10 < 12 ∧ ∀ (y : ℕ), (∀ p ∈ [(4, 2), (6, 4)], y ≡ p.2 [MOD p.1]) ↔ y ≡ 10 [MOD 12]
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [chineseRemainder] ([2, 4], [4, 6])

/--
info: #cas [chineseRemainder]
Domain: ℕ
Input (natural numbers): x ≡ 1 mod 4, x ≡ 2 mod 6
Output (no solution): none: x ≡ 1 mod 4 and x ≡ 2 mod 6 disagree modulo 2

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] no solution
        Proposition: ¬∃ y, ∀ p ∈ [(4, 1), (6, 2)], y ≡ p.2 [MOD p.1]
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [chineseRemainder] ([1, 2], [4, 6])

/--
error: powerMod: the modulus must be positive
-/
#guard_msgs (error, drop info) in
#cas (powerMod 2 10 0)

-- Divisors, DivisorSigma, EulerPhi, Binomial, Factorial, Fibonacci, IntegerDigits
set_option linter.style.longLine false in
/--
info: #cas [divisors]
Domain: ℕ
Input (natural numbers): 360
Output (divisors): [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 30, 36, 40, 45, 60, 72, 90, 120, 180, 360]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [divisors] 360

/--
info: #cas [divisors]
Domain: ℕ
Input (natural numbers): 1000000
Output (divisors): [1, 2, 4, 5, 8, 10, 16, 20, 25, 32, 40, 50, 64, 80, 100, 125, 160, 200, 250,
-/
#guard_msgs (info, whitespace := lax, substring := true) in
#cas [divisors] 1000000

/--
info: #cas (divisorSigma 1 360)
Domain: ℕ
Input (natural numbers): 360
Output (divisorSigma 1): 1170

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (divisorSigma 1 360)

/--
info: #cas (eulerPhi 360)
Domain: ℕ
Input (natural numbers): 360
Output (eulerPhi): 96

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (eulerPhi 360)

/--
info: #cas (binomial 100 50)
Domain: ℕ
Input (natural numbers): (100, 50)
Output (binomial): 100891344545564193334812497256

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (binomial 100 50)

/--
info: #cas (factorial 30)
Domain: ℕ
Input (natural numbers): 30
Output (factorial): 265252859812191058636308480000000

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (factorial 30)

/--
info: #cas (fibonacci 100)
Domain: ℕ
Input (natural numbers): 100
Output (fibonacci): 354224848179261915075

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas (fibonacci 100)

set_option linter.style.longLine false in
/--
info: #cas [integerDigits]
Domain: ℕ
Input (natural numbers): 1234 in base 2
Output (digits, most significant first (Mathlib's Nat.digits lists them in reverse)): [1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] digits, most significant first (Mathlib's Nat.digits lists them in reverse)
        Proposition: Nat.digits 2 1234 = [0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1]
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [integerDigits] (1234, 2)

/--
error: divisors: the divisors are certified for n < 10^12; `10 ^ 12` is beyond that bound
-/
#guard_msgs (error, drop info) in
#cas [divisors] (10 ^ 12)

-- ContinuedFraction, FromContinuedFraction
/--
info: #cas [continuedFraction]
Domain: ℚ
Input (rational number): 415/93
Output (continued fraction): [4; 2, 6, 7]

[CAS.Command.details] More details
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Value of the continued fraction
        Proposition: 415 / 93 = 4 + 1 / (2 + 1 / (6 + 1 / 7)) ∧ (∀ a ∈ [2, 6, 7], 1 ≤ a) ∧ 2 ≤ 7
        Validation: proof term checked by the kernel against this proposition
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
-/
#guard_msgs in
#cas [continuedFraction] (415/93)

/--
info: #cas [continuedFraction]
Domain: ℚ
Input (rational number): 314159/100000
Output (continued fraction): [3; 7, 15, 1, 25, 1, 7, 4]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [continuedFraction] (3.14159)

/--
info: #cas [fromContinuedFraction]
Domain: ℚ
Input (continued fraction): [4, 2, 6, 7]
Output (rational number): 415/93

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fromContinuedFraction] [4, 2, 6, 7]

-- Regressions
/--
info: #cas [chineseRemainder]
Domain: ℕ
Input (natural numbers): x ≡ 5 mod 3
Output (all solutions): 2 mod 3

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [chineseRemainder] ([5], [3])

/--
info: #cas [integerDigits]
Domain: ℕ
Input (natural numbers): 0 in base 10
Output (digits, most significant first (Mathlib's Nat.digits lists them in reverse)): []

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [integerDigits] (0, 10)

/--
info: #cas [continuedFraction]
Domain: ℚ
Input (rational number): -7/3
Output (continued fraction): [-3; 1, 2]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [continuedFraction] (-7/3)

/--
info: #cas [continuedFraction]
Domain: ℚ
Input (rational number): 5
Output (continued fraction): [5]

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [continuedFraction] (5)

/--
info: #cas [fromContinuedFraction]
Domain: ℚ
Input (continued fraction): [1, 1, 1]
Output (rational number): 3/2

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [fromContinuedFraction] [1, 1, 1]

/--
error: fromContinuedFraction: the list is empty
-/
#guard_msgs (error, drop info) in
#cas [fromContinuedFraction] []

/--
error: modularInverse: the modulus must be at least 2
-/
#guard_msgs (error, drop info) in
#cas (modularInverse 3 1)


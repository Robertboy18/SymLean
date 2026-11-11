/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Number theory

The compiled examples of the docstrings of the NumberTheory family: the calls of Euler's totient,
divisor sums, binomial coefficients, factorials, Fibonacci numbers, modular powers and inverses,
the Jacobi symbol, primality and the Möbius function, and the modes of prime factorizations,
divisors, simultaneous congruences, Bézout coefficients, continued fractions and digits. Each
section pins the report lines that a docstring shows and proves its theorem, and checks the axioms
of that proof.

The calls `primeQ n` and `moebiusMu n` and the mode `factorInteger` need Hex. Their docstring
examples run in `CASHex/Examples.lean`, in the build with `-Khex=on`; their sections here pin the
refusal of the default build and prove the theorems that take a printed result as a hypothesis.
The Möbius function needs `import Mathlib.NumberTheory.ArithmeticFunction.Moebius`.
-/

@[expose] public section

namespace CAS.Examples.Reference.NumberTheory

set_option linter.hashCommand false

/-! ## factorInteger -/

theorem largest_prime_factor
    (h : Nat.primeFactorsList 600851475143 = [71, 839, 1471, 6857]) :
    ∀ p ∈ Nat.primeFactorsList 600851475143, p ≤ 6857 := by
  rw [h]
  decide

/--
info: 'CAS.Examples.Reference.NumberTheory.largest_prime_factor' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms largest_prime_factor

/--
factorInteger needs Hex (`-Khex=on`): primality certificates and integer factorization come from
Hex; build with `lake -R -Khex=on build CASHex` and `import CASHex.NumberTheory`
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [factorInteger] 360

/-! ## primeQ -/

/--
primeQ needs Hex (`-Khex=on`): primality certificates and integer factorization come from Hex;
build with `lake -R -Khex=on build CASHex` and `import CASHex.NumberTheory`
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (primeQ 97)

/-! ## divisors -/

/--
Output (divisors): [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 30, 36, 40, 45, 60, 72, 90,
120, 180, 360]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [divisors] 360

/--
Output (divisors): [1, 2, 3, 4, 6, 12]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [divisors] 12

theorem divisors_twelve : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by
  cas

/--
info: 'CAS.Examples.Reference.NumberTheory.divisors_twelve' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms divisors_twelve

/--
divisors: the divisors are certified for n < 10^12; `10^12` is beyond that bound
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [divisors] (10^12)

/--
divisors: expected a positive natural number
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [divisors] 0

/-! ## divisorSigma -/

/--
Output (divisorSigma 1): 1170
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (divisorSigma 1 360)

/--
Output (divisorSigma 2): 210
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (divisorSigma 2 12)

/--
Output (divisorSigma 0): 24
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (divisorSigma 0 360)

theorem sigma_two_twelve : ArithmeticFunction.sigma 2 12 = 210 := by
  cas

/--
info: 'CAS.Examples.Reference.NumberTheory.sigma_two_twelve' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sigma_two_twelve

/--
divisorSigma: expected a positive natural number
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (divisorSigma 1 0)

/-! ## eulerPhi -/

/--
Output (eulerPhi): 96
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (eulerPhi 360)

/--
Output (eulerPhi): 40
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (eulerPhi 100)

theorem totient_thirty_six : Nat.totient 36 = 12 := by
  cas

/--
info: 'CAS.Examples.Reference.NumberTheory.totient_thirty_six' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms totient_thirty_six

/--
error: eulerPhi counts the residues coprime to n ≤ 100000 without Hex; for `1000003`,
`import CASHex.NumberTheory` computes φ from the factorization
-/
#guard_msgs (whitespace := lax) in
#cas (eulerPhi 1000003)

-- The refusal quotes the argument as written, not its value.
/--
error: eulerPhi counts the residues coprime to n ≤ 100000 without Hex; for `1000000 + 3`,
`import CASHex.NumberTheory` computes φ from the factorization
-/
#guard_msgs (whitespace := lax) in
#cas (eulerPhi (1000000 + 3))

/-! ## moebiusMu -/

theorem squarefree_thirty (h : ArithmeticFunction.moebius 30 = -1) : Squarefree 30 := by
  rw [← ArithmeticFunction.moebius_ne_zero_iff_squarefree, h]
  norm_num

/--
info: 'CAS.Examples.Reference.NumberTheory.squarefree_thirty' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms squarefree_thirty

/--
moebiusMu needs Hex (`-Khex=on`): primality certificates and integer factorization come from Hex;
build with `lake -R -Khex=on build CASHex` and `import CASHex.NumberTheory`
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (moebiusMu 1001)

/-! ## modularInverse -/

/--
Output (modular inverse): 4
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (modularInverse 3 11)

/--
Output (modular inverse): 2753
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (modularInverse 17 3120)

/--
Output (modular inverse): 2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (modularInverse (-3) 7)

/--
Output (no inverse): none: gcd = 3
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (modularInverse 6 9)

theorem inverse_three_mod_eleven : (3 : ZMod 11)⁻¹ = 4 := by
  cas

/--
info: 'CAS.Examples.Reference.NumberTheory.inverse_three_mod_eleven' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms inverse_three_mod_eleven

/--
modularInverse: the modulus must be at least 2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (modularInverse 3 1)

/-! ## powerMod -/

/--
Output (modular power): 4
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (powerMod 3 1000 7)

/--
Output (modular power): 612059118
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (powerMod 2 123456789123456789123456789 1000000007)

/--
Output (modular power): 2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (powerMod 2 100 7)

theorem three_pow_mod_seven : 3 ^ 1000 % 7 = 4 := by
  cas

/--
info: 'CAS.Examples.Reference.NumberTheory.three_pow_mod_seven' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms three_pow_mod_seven

/--
powerMod: the modulus must be positive
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (powerMod 2 10 0)

/--
powerMod takes 3 arguments, as in `powerMod a b m`; the call has 2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (powerMod 2 10)

/-! ## chineseRemainder -/

/--
Output (all solutions): 23 mod 105
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [chineseRemainder] ([2, 3, 2], [3, 5, 7])

/--
Output (all solutions): 10 mod 12
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [chineseRemainder] ([2, 4], [4, 6])

/--
Output (no solution): none: x ≡ 1 mod 4 and x ≡ 2 mod 6 disagree modulo 2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [chineseRemainder] ([1, 2], [4, 6])

/--
Output (all solutions): 2 mod 3
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [chineseRemainder] ([5], [3])

theorem sunzi_next
    (h : 23 < 105 ∧ ∀ y : ℕ, (∀ p ∈ ([(3, 2), (5, 3), (7, 2)] : List (ℕ × ℕ)),
      y ≡ p.2 [MOD p.1]) ↔ y ≡ 23 [MOD 105]) :
    ∀ p ∈ ([(3, 2), (5, 3), (7, 2)] : List (ℕ × ℕ)), 128 ≡ p.2 [MOD p.1] :=
  (h.2 128).2 (by decide)

/--
info: 'CAS.Examples.Reference.NumberTheory.sunzi_next' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms sunzi_next

/--
chineseRemainder: expected as many residues as moduli
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [chineseRemainder] ([2, 3], [3, 5, 7])

/-! ## extendedGCD -/

/--
Output (gcd and Bézout coefficients): 2, [-9, 47]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [extendedGCD] (240, 46)

/--
Output (gcd and Bézout coefficients): 1, [-367, 2]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [extendedGCD] (17, 3120)

theorem bezout_240_46 : Nat.gcd 240 46 = 2 ∧ (240 : ℤ) * (-9) + 46 * 47 = 2 := by
  cas

/--
info: 'CAS.Examples.Reference.NumberTheory.bezout_240_46' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bezout_240_46

/--
extendedGCD: expected a natural number
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [extendedGCD] (-240, 46)

/-! ## continuedFraction -/

/--
Output (continued fraction): [4; 2, 6, 7]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [continuedFraction] (415/93)

/--
Output (continued fraction): [3; 7, 15, 1, 25, 1, 7, 4]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [continuedFraction] (3.14159)

/--
Output (continued fraction): [-3; 1, 2]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [continuedFraction] (-7/3)

theorem continued_fraction_415_93 : (415 / 93 : ℚ) = 4 + 1 / (2 + 1 / (6 + 1 / 7)) := by
  cas

/--
info: 'CAS.Examples.Reference.NumberTheory.continued_fraction_415_93' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms continued_fraction_415_93

/--
continuedFraction: expected an exact rational literal, such as 415/93, -7/3 or 3.14159
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [continuedFraction] (sqrt 2)

/-! ## fromContinuedFraction -/

/--
Output (rational number): 415/93
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fromContinuedFraction] [4, 2, 6, 7]

/--
Output (rational number): 3/2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fromContinuedFraction] [1, 1, 1]

theorem from_continued_fraction_ones : (3 / 2 : ℚ) = 1 + 1 / (1 + 1 / 1) := by
  cas

/--
info: 'CAS.Examples.Reference.NumberTheory.from_continued_fraction_ones' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms from_continued_fraction_ones

/--
fromContinuedFraction: the list is empty
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fromContinuedFraction] []

/--
fromContinuedFraction: the terms after the first must be positive
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fromContinuedFraction] [1, 0, 2]

/-! ## integerDigits -/

/--
Output (digits, most significant first (Mathlib's Nat.digits lists them in reverse)):
[1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [integerDigits] (1234, 2)

/--
Output (digits, most significant first (Mathlib's Nat.digits lists them in reverse)):
[2, 0, 2, 6]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [integerDigits] 2026

/--
Output (digits, most significant first (Mathlib's Nat.digits lists them in reverse)): []
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [integerDigits] (0, 10)

theorem digits_1234 : Nat.digits 2 1234 = [0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1] := by
  cas

/--
info: 'CAS.Examples.Reference.NumberTheory.digits_1234' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms digits_1234

/--
integerDigits: the base must be at least 2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [integerDigits] (1234, 1)

/-! ## binomial -/

/--
Output (binomial): 100891344545564193334812497256
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (binomial 100 50)

/--
Output (binomial): 120
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (binomial 10 3)

/--
Output (binomial): 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (binomial 3 10)

theorem choose_ten_three : Nat.choose 10 3 = 120 := by
  cas

/--
info: 'CAS.Examples.Reference.NumberTheory.choose_ten_three' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms choose_ten_three

/--
binomial takes a natural number as its first argument; `-3` is negative
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (binomial (-3) 2)

/--
binomial takes 2 arguments, as in `binomial n k`; the call has 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (binomial 10)

/-! ## factorial -/

/--
Output (factorial): 265252859812191058636308480000000
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (factorial 30)

/--
Output (factorial): 3628800
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (factorial 10)

/--
Output (factorial): 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (factorial 0)

theorem factorial_ten : Nat.factorial 10 = 3628800 := by
  cas

/--
info: 'CAS.Examples.Reference.NumberTheory.factorial_ten' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms factorial_ten

/--
factorial takes a natural number as its argument; `-1` is negative
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (factorial (-1))

/-! ## fibonacci -/

/--
Output (fibonacci): 354224848179261915075
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (fibonacci 100)

/--
Output (fibonacci): 6765
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (fibonacci 20)

theorem fib_twenty : Nat.fib 20 = 6765 := by
  cas

/--
info: 'CAS.Examples.Reference.NumberTheory.fib_twenty' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms fib_twenty

/--
fibonacci takes a natural number as its argument; `-5` is negative
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (fibonacci (-5))

/-! ## jacobiSymbol -/

/--
Output (Jacobi symbol): -1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (jacobiSymbol 1001 9907)

/--
Output (Jacobi symbol): 1
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (jacobiSymbol 2 15)

/--
Output (Jacobi symbol): 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (jacobiSymbol 6 9)

theorem not_square_mod_9907 : ¬IsSquare ((1001 : ℤ) : ZMod 9907) :=
  ZMod.nonsquare_of_jacobiSym_eq_neg_one (by cas)

/--
info: 'CAS.Examples.Reference.NumberTheory.not_square_mod_9907' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms not_square_mod_9907

/--
jacobiSymbol: expected an odd natural number
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas (jacobiSymbol 2 4)

end CAS.Examples.Reference.NumberTheory

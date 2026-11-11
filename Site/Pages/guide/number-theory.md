+++
id = "number-theory"
kind = "guide"
title = "Number theory"
summary = "Primes, factorizations, divisors, congruences, digits and continued fractions, each with a theorem about Mathlib’s definitions."
related_guides = ["hex", "algebra", "sums", "tactics"]
tutorials = ["first-hour", "proving"]
+++

In number theory the answers quickly get too big to check by hand, and that’s when I’m most tempted to trust a computer algebra system blindly. Here you don’t have to. You can work with primes and factorizations, divisors, congruences, digits, continued fractions and the usual combinatorial numbers, and each answer is a theorem about Mathlib’s definitions, such as `Nat.divisors`, `Nat.ModEq`, `Nat.digits` or `Nat.primeFactorsList`. Its proof checks the answer instead of trusting the search that found it. Primality and integer factorization come from the optional [Hex library](guide:hex), which has the kernel replay a primality certificate for every prime.

::: commands
### Primes and factorizations
- primeQ
- factorInteger
- moebiusMu
### Divisors and arithmetic functions
- divisors
- divisorSigma
- eulerPhi
### Modular arithmetic
- powerMod
- modularInverse
- chineseRemainder
- extendedGCD
- jacobiSymbol
### Digits and continued fractions
- integerDigits
- continuedFraction
- fromContinuedFraction
### Combinatorial numbers
- binomial
- factorial
- fibonacci
:::

The *Sunzi Suanjing* asks for a number with the remainders 2, 3 and 2 on division by 3, 5 and 7. The answer is complete. The theorem says more than that 23 works: the solutions are exactly the numbers $23 + 105 k$:

```lean
#cas [chineseRemainder] ([2, 3, 2], [3, 5, 7])
```

A modular power with an exponent of 27 digits. The proof is repeated squaring, so it never builds the full power, and its size grows with the number of digits of the exponent:

```lean
#cas (powerMod 2 123456789123456789123456789 1000000007)
```

Without Hex, `primeQ`, `factorInteger` and `moebiusMu` refuse, and the message says how to turn Hex on. Even with Hex the factor search has a budget, and when it runs out the command claims nothing. The divisor commands certify $n < 10^{12}$, `eulerPhi` without Hex counts up to $n \le 100000$, and `binomial`, `factorial` and `fibonacci` compute values of at most 10000 digits. `continuedFraction` takes rational numbers only, since an irrational number has an infinite expansion.

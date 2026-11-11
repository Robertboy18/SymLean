+++
id = "factorInteger"
kind = "mode"
title = "factorInteger"
summary = "The prime factorization of a natural number $n \\ge 2$ with a theorem about `Nat.primeFactorsList`, through the optional Hex library."
forms = ["CAS.Command.casFactorIntegerCommand"]
see_also = ["divisors", "primeQ", "moebiusMu", "eulerPhi", "factor", "hex"]
tutorials = ["proving"]
+++

::: usage
`#cas [factorInteger] ‹n›`
: gives the prime factorization of the natural number ‹n› ≥ 2 and proves `Nat.primeFactorsList ‹n› = [p₁, …, pₖ]`, with Hex.
:::

`factorInteger` finds the prime factors of an integer and proves the result about Mathlib’s `Nat.primeFactorsList`. We didn’t write the hard part ourselves. Integer factorization and primality certificates are the work of Hex, the Lean FRO’s verified computer algebra. Hex finds the factors and a certificate that each one is prime, and the kernel checks the product and replays the certificates.

Hex is optional, and the build of this site leaves it out. So the outputs on this page that need Hex are quoted from `CASHex/Examples.lean`, which the Hex build compiles. To turn Hex on, fetch it with the commands in the [Hex guide](guide:hex), build it with `lake -R -Khex=on build CASHex`, and start your file with `import CASHex.NumberTheory`.

## Details and Options

- ‹n› is a natural number with $n \ge 2$: a literal such as `360`, or a closed integer expression such as `(2^61 + 1)`. The command refuses 0 and 1, whose `Nat.primeFactorsList` is `[]`.
- The theorem is `Nat.primeFactorsList n = [p₁, …, pₖ]`: Mathlib’s list of the prime factors of $n$ with multiplicity, in increasing order.
- Hex’s factor search proposes the factors, by trial division and Pollard’s $p - 1$ and rho methods. The kernel checks that their product is $n$ and that the list is sorted, and replays Hex’s primality certificate for each distinct factor, a recursive certificate of Pocklington steps and cube-root steps of Brillhart, Lehmer and Selfridge. The uniqueness of prime factorization then gives the theorem (`CASHex.NumberTheory.primeFactorsList_eq_of_prod`).
- The report prints the product `p₁^e₁*⋯` and the pairs `(p, e)`, as Mathematica’s `FactorInteger` does.
- Hex’s factor search has a fixed budget. When it runs out, the command refuses and claims nothing.
- There are no options. Without Hex the command refuses, and the message says how to turn Hex on.

## Examples

### Basic Examples

The four prime factors of 600851475143, with the theorem that the kernel checked:

```lean quote=CASHex/Examples.lean
#cas [factorInteger] 600851475143
```

### Scope

A product of two primes of ten digits, the twin primes $10^9 + 7$ and $10^9 + 9$:

```lean quote=CASHex/Examples.lean
#cas [factorInteger] 1000000016000000063
```

### Applications

A proof can take the printed theorem as a hypothesis and read the factors off the list, here the largest one. This cell needs no Hex:

```lean
theorem largest_prime_factor
    (h : Nat.primeFactorsList 600851475143 = [71, 839, 1471, 6857]) :
    ∀ p ∈ Nat.primeFactorsList 600851475143, p ≤ 6857 := by
  rw [h]
  decide

#print axioms largest_prime_factor
```

---

Each entry of the list is prime, by Mathlib’s `Nat.prime_of_mem_primeFactorsList`:

```lean
theorem prime_6857 (h : Nat.primeFactorsList 600851475143 = [71, 839, 1471, 6857]) :
    Nat.Prime 6857 :=
  Nat.prime_of_mem_primeFactorsList (n := 600851475143) (by rw [h]; simp)
```

### Properties and Relations

Below $10^{12}$, [[divisors]] needs no Hex, and the primes among the divisors are the prime factors. For $360 = 2^3 \cdot 3^2 \cdot 5$:

```lean
#cas [divisors] 360
```

---

The factorization gives the number of divisors, $(3 + 1)(2 + 1)(1 + 1) = 24$, and Euler’s $\varphi(360) = 360 \cdot \tfrac{1}{2} \cdot \tfrac{2}{3} \cdot \tfrac{4}{5} = 96$. [[divisorSigma]] and [[eulerPhi]] compute both without Hex:

```lean
#cas (divisorSigma 0 360)
```

```lean
#cas (eulerPhi 360)
```

### Possible Issues

Without Hex the command refuses, and the message says how to turn Hex on:

```lean error
#cas [factorInteger] 360
```

### Neat Examples

$2^{61} + 1$ is divisible by 3 because 61 is odd, and the cofactor $\tfrac{2^{61} + 1}{3}$ is a prime of 18 digits, a Wagstaff prime:

```lean quote=CASHex/Examples.lean
#cas [factorInteger] 2305843009213693953
```

---

Next to it, $2^{61} - 1$ is a Mersenne prime. With Hex, bare [[cas]] proves it with the same kind of certificate:

```lean quote=CASHex/Examples.lean
theorem mersenne_61_prime : Nat.Prime (2 ^ 61 - 1) := by
  cas
```

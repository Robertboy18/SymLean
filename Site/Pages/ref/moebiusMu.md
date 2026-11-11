+++
id = "moebiusMu"
kind = "call"
title = "moebiusMu"
summary = "The Möbius function $\\mu(n)$ of a positive integer from its prime factorization, through the optional Hex library."
calls = ["moebiusMu"]
see_also = ["factorInteger", "eulerPhi", "divisorSigma", "divisors", "primeQ", "hex"]
guide = "number-theory"
tutorials = ["proving"]
imports = ["Mathlib.NumberTheory.ArithmeticFunction.Moebius"]
+++

::: usage
`#cas (moebiusMu ‹n›)`
: gives the Möbius function $\mu(n)$ of the positive natural number ‹n›, one of −1, 0 and 1, and proves `ArithmeticFunction.moebius ‹n› = ‹μ›`, with Hex.
:::

`moebiusMu` evaluates the Möbius function and proves the value of Mathlib’s `ArithmeticFunction.moebius`. Everything about $\mu(n)$ is in the prime factors of ‹n›: it is $0$ when a prime repeats, and $(-1)^k$ when ‹n› is a product of $k$ distinct primes. So the real work is the factorization, and for that we use Hex, the Lean FRO’s verified computer algebra.

Hex is optional, and the build of this site leaves it out. The outputs on this page that need Hex are quoted from `CASHex/Examples.lean`, which the Hex build compiles. To turn Hex on, fetch it with the commands in the [Hex guide](guide:hex), build it with `lake -R -Khex=on build CASHex`, and start your file with `import CASHex.NumberTheory`.

## Details and Options

- ‹n› is a positive natural number, a literal or a closed integer expression, and $\mu(1) = 1$.
- The theorem is `ArithmeticFunction.moebius n = μ` for Mathlib’s Möbius function, with μ one of $-1$, 0 and 1.
- The proof starts from the factorization `Nat.primeFactorsList n = [p₁, …]` of [[factorInteger]]. When the $k$ primes are distinct, $n$ is squarefree (`Nat.squarefree_iff_nodup_primeFactorsList`) and $\mu = (-1)^k$ (`ArithmeticFunction.moebius_apply_of_squarefree`). A repeated prime gives $\mu = 0$ (`ArithmeticFunction.moebius_eq_zero_of_not_squarefree`).
- When Hex’s factor search runs out of budget, the call refuses and claims nothing.
- A theorem about `ArithmeticFunction.moebius` needs `import Mathlib.NumberTheory.ArithmeticFunction.Moebius`, which this page imports.
- There are no options. Without Hex the call refuses, and the message says how to turn Hex on.

## Examples

### Basic Examples

$30 = 2 \cdot 3 \cdot 5$ has three distinct prime factors, so $\mu(30) = (-1)^3 = -1$:

```lean quote=CASHex/Examples.lean
#cas (moebiusMu 30)
```

### Scope

$360 = 2^3 \cdot 3^2 \cdot 5$ has repeated prime factors, so $\mu(360) = 0$:

```lean quote=CASHex/Examples.lean
#cas (moebiusMu 360)
```

### Applications

A proof can take the printed theorem as a hypothesis. $\mu(n) \ne 0$ says that $n$ is squarefree (`ArithmeticFunction.moebius_ne_zero_iff_squarefree`). This cell needs no Hex:

```lean
theorem squarefree_thirty (h : ArithmeticFunction.moebius 30 = -1) : Squarefree 30 := by
  rw [← ArithmeticFunction.moebius_ne_zero_iff_squarefree, h]
  norm_num

#print axioms squarefree_thirty
```

### Properties and Relations

The values of $\mu$ add up to 0 over the divisors of every $n > 1$. [[divisors]] needs no Hex, and for 12 the values at $1, 2, 3, 4, 6, 12$ are $1, -1, -1, 0, 1, 0$:

```lean
#cas [divisors] 12
```

---

Euler’s totient is a sum over the divisors with the Möbius function, $\varphi(n) = \sum_{d \mid n} \mu(d)\,\tfrac{n}{d}$. For 360 only the squarefree divisors count, the divisors of 30, and $360 - 180 - 120 - 72 + 60 + 36 + 24 - 12 = 96$, the value of [[eulerPhi]]:

```lean
#cas (eulerPhi 360)
```

### Possible Issues

Without Hex the call refuses, and the message says how to turn Hex on:

```lean error
#cas (moebiusMu 1001)
```

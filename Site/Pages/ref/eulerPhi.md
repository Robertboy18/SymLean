+++
id = "eulerPhi"
kind = "call"
title = "eulerPhi"
summary = "Euler’s totient $\\varphi(n)$, the number of residues modulo $n$ coprime to $n$, with a theorem about Mathlib’s `Nat.totient`."
calls = ["eulerPhi"]
see_also = ["divisorSigma", "moebiusMu", "factorInteger", "divisors", "powerMod"]
guide = "number-theory"
tutorials = ["proving"]
+++

::: usage
`#cas (eulerPhi ‹n›)`
: gives Euler’s totient $\varphi(n)$ of the natural number ‹n›, the number of $0 \le i < n$ coprime to ‹n›, and proves `Nat.totient ‹n› = ‹t›`.
:::

`eulerPhi` computes Euler’s totient, the number of residues modulo $n$ that are coprime to $n$. The theorem is about Mathlib’s `Nat.totient` itself, not a function of our own, so a proof about the totient can use the printed value directly.

## Details and Options

- ‹n› is a natural number, a literal or a closed integer expression such as `2 ^ 10`. $\varphi(0) = 0$ and $\varphi(1) = 1$.
- The theorem is `Nat.totient n = t`. Without Hex, `CAS.NumberTheory.totient_eq_rangeSum` writes $\varphi(n)$ as a sum of indicators of $\gcd(n, d) = 1$ over $[0, n)$, which the kernel evaluates, and $n \le 100000$.
- With `import CASHex.NumberTheory`, Hex factors $n$, and `CAS.NumberTheory.totient_eq_of_primeFactorsList` computes $\varphi(n) = n / \prod p \cdot \prod (p - 1)$ from the kernel-checked list of prime factors. The bound on $n$ is then the budget of Hex’s factor search.
- A closed expression is evaluated with numbers of at most 10000 digits, the most that a call computes.
- The call is evaluated when it is the whole input of `#cas`.
- There are no options.

## Examples

### Basic Examples

Forty of the residues modulo 100 are coprime to 100, and the theorem says so:

```lean
#cas (eulerPhi 100)
```

### Scope

A closed integer expression is evaluated first. Modulo $2^{10}$ the coprime residues are the odd ones, half of them:

```lean
#cas (eulerPhi (2 ^ 10))
```

---

Mathlib sets $\varphi(0) = 0$:

```lean
#cas (eulerPhi 0)
```

---

An expression may pass through large numbers, here $10^{9000}$, and the argument is its value, 100:

```lean
#cas (eulerPhi (10 ^ 9000 / 10 ^ 8998))
```

### Applications

In a proof, [[cas]] proves the equation:

```lean
theorem totient_thirty_six : Nat.totient 36 = 12 := by
  cas

#print axioms totient_thirty_six
```

### Properties and Relations

The product formula $\varphi(n) = n / \prod p \cdot \prod (p - 1)$ runs over the distinct primes $p$ of $n$. For $360 = 2^3 \cdot 3^2 \cdot 5$ it gives $\tfrac{360}{30} \cdot 1 \cdot 2 \cdot 4 = 96$:

```lean
#cas (eulerPhi 360)
```

### Possible Issues

Without Hex the count runs over all of $[0, n)$, and the call takes $n \le 100000$. The message names the import that computes $\varphi$ from the factorization:

```lean error
#cas (eulerPhi 1000003)
```

---

The expression `10 ^ 10000 / 10 ^ 9998` has the value 100, but $10^{10000}$ has 10001 digits:

```lean error
#cas (eulerPhi (10 ^ 10000 / 10 ^ 9998))
```

---

A call inside another call is not evaluated, since [[gamma]] is evaluated only as the whole input of `#cas`:

```lean error
#cas (eulerPhi (gamma 3))
```

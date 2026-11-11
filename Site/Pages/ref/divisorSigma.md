+++
id = "divisorSigma"
kind = "call"
title = "divisorSigma"
summary = "The sum $\\sigma_k(n)$ of the $k$-th powers of the divisors of $n$, with a theorem about Mathlib’s `ArithmeticFunction.sigma`."
calls = ["divisorSigma"]
see_also = ["divisors", "eulerPhi", "moebiusMu", "factorInteger"]
guide = "number-theory"
tutorials = ["proving"]
+++

::: usage
`#cas (divisorSigma ‹k› ‹n›)`
: gives the sum $\sigma_k(n)$ of the ‹k›-th powers of the divisors of the positive natural number ‹n› and proves `ArithmeticFunction.sigma ‹k› ‹n› = ‹s›`.
:::

`divisorSigma` computes the divisor functions: $\sigma_0(n)$ counts the divisors of $n$, and $\sigma_1(n)$ adds them up. The theorem is about Mathlib’s `ArithmeticFunction.sigma`. What I like about the proof is that the kernel checks the divisors with a counting certificate and no factorization at all, so how hard $n$ is to factor never comes into it.

## Details and Options

- ‹k› and ‹n› are natural numbers, literals or closed integer expressions, with $1 \le n < 10^{12}$ and $k < 2^{32}$, the exponents for which the kernel evaluates the powers $d^k$ of the certificate.
- The theorem is `ArithmeticFunction.sigma k n = s`, by `CAS.NumberTheory.sigma_eq_of_cert`. The kernel checks the list of divisors of $n$ with a counting certificate, $\lfloor \sqrt{n} \rfloor$ divisions and no factorization, and sums their $k$-th powers.
- The value has at most 10000 digits, the most that a call computes.
- [[divisors]] prints the list of divisors with the same certificate.
- The call is evaluated when it is the whole input of `#cas`.
- There are no options.

## Examples

### Basic Examples

The sum of the divisors of 360. $\sigma_1$ is multiplicative, and $\sigma_1(p^e) = 1 + p + \cdots + p^e$ on a prime power, so the sum is $\sigma_1(2^3)\,\sigma_1(3^2)\,\sigma_1(5) = 15 \cdot 13 \cdot 6 = 1170$:

```lean
#cas (divisorSigma 1 360)
```

### Scope

With $k = 0$ the call counts the divisors. $360 = 2^3 \cdot 3^2 \cdot 5$ has $4 \cdot 3 \cdot 2 = 24$ of them:

```lean
#cas (divisorSigma 0 360)
```

---

The sum of the squares of the divisors of 12:

```lean
#cas (divisorSigma 2 12)
```

### Applications

In a proof, [[cas]] proves the equation:

```lean
theorem sigma_two_twelve : ArithmeticFunction.sigma 2 12 = 210 := by
  cas

#print axioms sigma_two_twelve
```

### Properties and Relations

[[divisors]] lists the divisors of 12, and the sum of their squares is $1 + 4 + 9 + 16 + 36 + 144 = 210$:

```lean
#cas [divisors] 12
```

### Possible Issues

Every natural number divides 0, and Mathlib sets `ArithmeticFunction.sigma k 0 = 0`. The call takes positive $n$ only:

```lean error
#cas (divisorSigma 1 0)
```

---

The value has at most 10000 digits. The prime 999999937 has $\sigma_{4000} = 1 + 999999937^{4000}$, with 36000 digits:

```lean error
#cas (divisorSigma 4000 999999937)
```

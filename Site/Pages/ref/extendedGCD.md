+++
id = "extendedGCD"
kind = "mode"
title = "extendedGCD"
summary = "The gcd of two natural numbers with Bézout coefficients $s$ and $t$, and a theorem that $a s + b t = \\gcd(a, b)$."
forms = ["CAS.Command.casExtendedGCDCommand"]
see_also = ["chineseRemainder", "modularInverse", "powerMod", "continuedFraction", "polynomialGCD"]
tutorials = ["proving"]
+++

::: usage
`#cas [extendedGCD] (‹a›, ‹b›)`
: gives the gcd g of the natural numbers ‹a› and ‹b› with integers s and t such that ‹a› s + ‹b› t = g, and proves both facts.
:::

Whenever I need to invert a number modulo another, solve a linear equation $a x + b y = c$ in integers, or merge two congruences, what I really need is a pair of Bézout coefficients. `extendedGCD` runs the extended Euclidean algorithm and prints the answer the way Mathematica’s `ExtendedGCD` does, as `g, [s, t]`. The theorem carries the two facts I end up using: $g$ is Mathlib’s `Nat.gcd a b`, and $a s + b t = g$ in $\mathbb{Z}$.

## Details and Options

- ‹a› and ‹b› are natural numbers: literals, or closed integer expressions such as `2^32`. The coefficients $s$ and $t$ are integers.
- The theorem is `Nat.gcd a b = g ∧ (a : ℤ) * s + b * t = g`. The kernel evaluates the gcd (`decide +kernel`), and `norm_num` checks the equation.
- The coefficients are those of the extended Euclidean algorithm.
- There are no options.

## Examples

### Basic Examples

The gcd of 240 and 46 is 2, and $240 \cdot (-9) + 46 \cdot 47 = 2$:

```lean
#cas [extendedGCD] (240, 46)
```

### Scope

Swapping 240 and 46 swaps the coefficients:

```lean
#cas [extendedGCD] (46, 240)
```

---

A zero: $\gcd(0, 5) = 5 = 0 \cdot 0 + 5 \cdot 1$:

```lean
#cas [extendedGCD] (0, 5)
```

---

Closed expressions, here $2^{10}$ and $3^6$:

```lean
#cas [extendedGCD] (2^10, 3^6)
```

### Applications

The theorem, with the axioms its proof uses:

```lean
theorem bezout_240_46 : Nat.gcd 240 46 = 2 ∧ (240 : ℤ) * (-9) + 46 * 47 = 2 := by
  cas

#print axioms bezout_240_46
```

---

RSA with the primes 61 and 53 has $n = 3233$ and $\varphi(n) = 60 \cdot 52 = 3120$. For the public exponent $e = 17$, the coefficient $-367$ gives the private exponent $d = 3120 - 367 = 2753$, which [[modularInverse]] returns directly:

```lean
#cas [extendedGCD] (17, 3120)
```

```lean
#cas (modularInverse 17 3120)
```

---

Encrypting the message 65 with $e$ and decrypting it with $d$ gives it back:

```lean
#cas (powerMod 65 17 3233)
```

```lean
#cas (powerMod 2790 2753 3233)
```

### Properties and Relations

The quotients of Euclid’s algorithm on 240 and 46 are the terms of the continued fraction of $\tfrac{240}{46}$:

```lean
#cas [continuedFraction] (240/46)
```

### Possible Issues

The arguments are natural numbers. Since $\gcd(-a, b) = \gcd(a, b)$, the coefficients for $-a$ are those for $a$ with the sign of $s$ reversed:

```lean error
#cas [extendedGCD] (-240, 46)
```

---

The mode takes exactly two numbers:

```lean error
#cas [extendedGCD] (12, 18, 30)
```

### Neat Examples

Consecutive Fibonacci numbers are the slowest case of Euclid’s algorithm, and their coefficients are Fibonacci numbers again:

```lean
#cas [extendedGCD] (89, 55)
```

---

For the Fermat prime $65537 = 2^{16} + 1$ and $2^{32}$, the identity $65537 \cdot 65535 = 2^{32} - 1$ gives the coefficients:

```lean
#cas [extendedGCD] (65537, 2^32)
```

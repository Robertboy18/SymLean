+++
id = "polynomialGCD"
kind = "mode"
title = "polynomialGCD"
summary = "Gives the monic gcd of two polynomials in one variable, with a theorem about Mathlib’s `gcd` in `ℚ[X]`."
forms = ["CAS.Command.casPolynomialGCDCommand"]
see_also = ["polynomialLCM", "polynomialQuotient", "polynomialRemainder", "factor", "extendedGCD"]
guide = "polynomials"
tutorials = ["first-hour"]
+++

::: usage
`#cas [polynomialGCD] (‹p›, ‹q›)`
: gives the monic greatest common divisor $g$ of the polynomials ‹p› and ‹q› and proves `gcd p q = g` in Mathlib’s `ℚ[X]`.
:::

`polynomialGCD` finds the common factor of two polynomials without factoring either of them. The theorem is about Mathlib’s `gcd` in `ℚ[X]`, the normalized gcd of its `NormalizedGCDMonoid`, which is monic.

The proof is a certificate, so the kernel never reruns the Euclidean algorithm. The gcd $g$ divides $p$ and $q$ with explicit cofactors, and the Bézout identity $s p + t q = g$ shows that every common divisor of $p$ and $q$ divides $g$. So the kernel checks three polynomial identities and a monicity, however long the Euclidean algorithm ran.

## Details and Options

- The theorem is `gcd p q = g` in `ℚ[X]`, with the variable read as `Polynomial.X`. The two inputs have the same single variable, which need not be `x`.
- The gcd is monic, also for inputs with integer coefficients: where the common factor is $2x + 1$, the gcd is $x + \tfrac{1}{2}$.
- The proof checks `g ∣ p` and `g ∣ q` with explicit cofactors, the Bézout identity `s * p + t * q = g` with the coefficients `s` and `t` of the extended Euclidean algorithm, and the monicity of `g`.
- The inputs are polynomials with rational coefficients in one variable, not both zero.
- The tactic [[cas]] proves `gcd p q = g` goals in `ℚ[X]`, written either way round, and it refuses a wrong gcd with the right one in its message.
- [[polynomialLCM]] gives the lcm, and [[extendedGCD]] the gcd of natural numbers with its Bézout coefficients.

## Examples

### Basic Examples

The common factor of $x^2 - 1$ and $(x - 1)^2$:

```lean
#cas [polynomialGCD] (x^2 - 1, x^2 - 2*x + 1)
```

---

Coprime polynomials have gcd $1$:

```lean
#cas [polynomialGCD] (x^3 - 1, x^2 + 1)
```

### Scope

The gcd is monic, also when the inputs have integer coefficients. Here the common factor is $2x + 1$:

```lean
#cas [polynomialGCD] (2*x^2 + 3*x + 1, 4*x^2 - 1)
```

---

The gcd of $0$ and $q$ is the monic multiple of $q$:

```lean
#cas [polynomialGCD] (0, x^2 - 1)
```

### Applications

The first example as a theorem about Mathlib’s `gcd`. Only the three standard axioms are used:

```lean
open Polynomial in
theorem gcd_of_quadratics : gcd (X ^ 2 - 1 : ℚ[X]) (X ^ 2 - 2 * X + 1) = X - 1 := by
  cas

#print axioms gcd_of_quadratics
```

---

The tactic `cas` takes the equation either way round:

```lean
open Polynomial in
example : X - 1 = gcd (X ^ 2 - 1 : ℚ[X]) (X ^ 2 - 2 * X + 1) := by
  cas
```

### Properties and Relations

[[polynomialLCM]] gives the least common multiple. The product of the gcd $x - 1$ and the lcm is the product $(x^2 - 1)(x - 1)^2$ of the two monic inputs:

```lean
#cas [polynomialLCM] (x^2 - 1, x^2 - 2*x + 1)
```

---

[[together]] finds a common denominator with gcds. Here $x^2 - 1$ and $x - 1$ share the factor $x - 1$:

```lean
#cas [together] (1/(x^2-1) + 1/(x-1))
```

### Possible Issues

The mode works in one variable:

```lean error
#cas [polynomialGCD] (x^2 - 1, y - 1)
```

---

Mathlib’s `gcd 0 0` is $0$, which is not monic. Give at least one nonzero polynomial:

```lean error
#cas [polynomialGCD] (0, 0)
```

---

The tactic `cas` refuses a wrong gcd and gives the right one:

```lean error
open Polynomial in
example : gcd (X ^ 2 - 1 : ℚ[X]) (X - 1) = X + 1 := by
  cas
```

### Neat Examples

The gcd of $x^m - 1$ and $x^n - 1$ is $x^{\gcd(m, n)} - 1$:

```lean
#cas [polynomialGCD] (x^12 - 1, x^18 - 1)
```

+++
id = "polynomialLCM"
kind = "mode"
title = "polynomialLCM"
summary = "Gives the monic lcm of two nonzero polynomials in one variable, with a theorem about Mathlib’s `lcm` in `ℚ[X]`."
forms = ["CAS.Command.casPolynomialLCMCommand"]
see_also = ["polynomialGCD", "together", "factor", "denominator"]
guide = "polynomials"
tutorials = ["first-hour"]
+++

::: usage
`#cas [polynomialLCM] (‹p›, ‹q›)`
: gives the monic least common multiple $l$ of the nonzero polynomials ‹p› and ‹q› and proves `lcm p q = l` in Mathlib’s `ℚ[X]`.
:::

You meet a polynomial lcm every time you put fractions over a common denominator. `polynomialLCM` computes it in $\mathbb{Q}[X]$, and the theorem is about Mathlib’s `lcm` in `ℚ[X]`, the normalized lcm, which is monic.

The proof goes through the gcd. Both polynomials divide $l$ with explicit cofactors, the gcd $g$ comes with the certificate of [[polynomialGCD]], and $g \cdot l$ divides $p q$. From that, Mathlib’s `gcd_mul_lcm` shows that $l$ divides `lcm p q`.

## Details and Options

- The theorem is `lcm p q = l` in `ℚ[X]`, with the variable read as `Polynomial.X`. The two inputs have the same single variable.
- The lcm is monic, so it can have fractions as coefficients when the inputs have integer ones.
- The inputs are nonzero polynomials with rational coefficients in one variable. Mathlib sets `lcm 0 p = 0`, and a zero input is refused.
- The product of the gcd and the lcm is $p q$ divided by the leading coefficients of $p$ and $q$.
- The tactic [[cas]] proves `lcm p q = l` goals in `ℚ[X]`, and it refuses a wrong lcm with the right one in its message.

## Examples

### Basic Examples

The lcm of $x^2 - 1$ and $(x - 1)^2$ is $(x - 1)^2 (x + 1)$, expanded:

```lean
#cas [polynomialLCM] (x^2 - 1, x^2 - 2*x + 1)
```

---

The two polynomials share the factor $x - 1$, so the lcm has degree $4$ and not $5$:

```lean
#cas [polynomialLCM] (x^2 - 1, x^3 - 1)
```

### Scope

The lcm is monic, so here it is $x^2 - \tfrac{1}{4}$ and not $4x^2 - 1$:

```lean
#cas [polynomialLCM] (2*x + 1, 4*x^2 - 1)
```

### Applications

The first example as a theorem about Mathlib’s `lcm`. Only the three standard axioms are used:

```lean
open Polynomial in
theorem lcm_of_quadratics :
    lcm (X ^ 2 - 1 : ℚ[X]) (X ^ 2 - 2 * X + 1) = X ^ 3 - X ^ 2 - X + 1 := by
  cas

#print axioms lcm_of_quadratics
```

---

[[together]] puts a sum of fractions over a common denominator. Here it is the lcm $x^2 - 1$ of the denominators $x^2 - 1$ and $x - 1$, in factored form:

```lean
#cas [together] (1/(x^2-1) + 1/(x-1))
```

### Properties and Relations

[[polynomialGCD]] gives the gcd $x - 1$ of the first example. Its product with the lcm is $(x^2 - 1)(x - 1)^2$:

```lean
#cas [polynomialGCD] (x^2 - 1, x^2 - 2*x + 1)
```

### Possible Issues

Mathlib’s `lcm 0 p` is $0$, and a zero input is refused:

```lean error
#cas [polynomialLCM] (0, x)
```

---

The product $(x^2 - 1)(x - 1) = x^3 - x^2 - x + 1$ is a common multiple of $x^2 - 1$ and $x - 1$, but not the least one. The tactic [[cas]] refuses it, with the lcm in its message:

```lean error
open Polynomial in
example : lcm (X ^ 2 - 1 : ℚ[X]) (X - 1) = X ^ 3 - X ^ 2 - X + 1 := by
  cas
```

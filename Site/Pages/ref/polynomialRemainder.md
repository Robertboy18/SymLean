+++
id = "polynomialRemainder"
kind = "mode"
title = "polynomialRemainder"
summary = "Gives the remainder of a division of polynomials in one variable, with a theorem about `%` in `ℚ[X]`."
forms = ["CAS.Command.casPolynomialRemainderCommand"]
see_also = ["polynomialQuotient", "polynomialQuotientRemainder", "polynomialGCD", "member"]
guide = "polynomials"
tutorials = ["first-hour"]
+++

::: usage
`#cas [polynomialRemainder] (‹p›, ‹q›)`
: gives the remainder $r$ of the division of the polynomial ‹p› by the nonzero polynomial ‹q› and proves `p / q = s ∧ p % q = r` in Mathlib’s `ℚ[X]`.
:::

`polynomialRemainder` gives you the remainder of polynomial long division. It is also a divisibility test, since ‹q› divides ‹p› exactly when the remainder is $0$. The report prints the remainder, and the theorem under it is the one of [[polynomialQuotientRemainder]], which states the quotient and the remainder together, about Mathlib’s `/` and `%` on `ℚ[X]`.

## Details and Options

- The theorem is `p / q = s ∧ p % q = r` in `ℚ[X]`, with the variable read as `Polynomial.X`, proved as for [[polynomialQuotientRemainder]].
- The remainder has a smaller degree than ‹q›, and it is $0$ exactly when ‹q› divides ‹p›.
- For a divisor $x - a$, the remainder is the value of ‹p› at $a$.
- The divisor ‹q› is nonzero. Mathlib’s division is total, with `p % 0 = p`, and a zero divisor is refused.
- The tactic [[cas]] proves `p % q = r` goals in `ℚ[X]`.
- For polynomials in several variables, [[member]] reduces modulo a Gröbner basis.

## Examples

### Basic Examples

The remainder $0$ shows that $x^2 + x + 1$ divides $x^5 + x + 1$:

```lean
#cas [polynomialRemainder] (x^5 + x + 1, x^2 + x + 1)
```

---

A remainder of a division by a linear polynomial is a number:

```lean
#cas [polynomialRemainder] (x^3 + 1, 2*x - 1)
```

### Applications

The second example as a theorem about Mathlib’s `%`. The remainder is the constant polynomial `C (9 / 8)`, and only the three standard axioms are used:

```lean
open Polynomial in
theorem remainder_by_linear : (X ^ 3 + 1 : ℚ[X]) % (2 * X - 1) = C (9 / 8) := by
  cas

#print axioms remainder_by_linear
```

### Properties and Relations

[[polynomialQuotient]] gives the quotient $x^3 - x^2 + 1$ of the first example:

```lean
#cas [polynomialQuotient] (x^5 + x + 1, x^2 + x + 1)
```

---

The remainder of $x^3 + 1$ by $x - 2$ is its value at $2$:

```lean
#cas [polynomialRemainder] (x^3 + 1, x - 2)
```

```lean
open Polynomial in
example : (X ^ 3 + 1 : ℚ[X]).eval 2 = 9 := by
  cas
```

---

When the remainder is $0$, the divisor is a gcd of the two. Here it is monic, and [[polynomialGCD]] gives it back:

```lean
#cas [polynomialGCD] (x^5 + x + 1, x^2 + x + 1)
```

### Possible Issues

Mathlib sets `p % 0 = p`, and a zero divisor is refused:

```lean error
#cas [polynomialRemainder] (x^2, 0)
```

### Neat Examples

The remainder of $x^{10} - 1$ by $x^3 - 1$ is $x^{10 \bmod 3} - 1$:

```lean
#cas [polynomialRemainder] (x^10 - 1, x^3 - 1)
```

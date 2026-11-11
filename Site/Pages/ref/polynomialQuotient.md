+++
id = "polynomialQuotient"
kind = "mode"
title = "polynomialQuotient"
summary = "Gives the quotient of a division of polynomials in one variable, with a theorem about `/` in `ℚ[X]`."
forms = ["CAS.Command.casPolynomialQuotientCommand"]
see_also = ["polynomialRemainder", "polynomialQuotientRemainder", "polynomialGCD", "apart"]
guide = "polynomials"
tutorials = ["first-hour"]
+++

::: usage
`#cas [polynomialQuotient] (‹p›, ‹q›)`
: gives the quotient $s$ of the division of the polynomial ‹p› by the nonzero polynomial ‹q› and proves `p / q = s ∧ p % q = r` in Mathlib’s `ℚ[X]`.
:::

`polynomialQuotient` gives you the quotient of polynomial long division. The report prints the quotient, and the theorem under it is the one of [[polynomialQuotientRemainder]], which states the quotient and the remainder together, about Mathlib’s `/` and `%` on `ℚ[X]`. So the theorem has the remainder in it even when you only asked for the quotient.

## Details and Options

- The theorem is `p / q = s ∧ p % q = r` in `ℚ[X]`, with the variable read as `Polynomial.X`, proved as for [[polynomialQuotientRemainder]].
- The quotient $s$ satisfies $p = s q + r$ with $\deg r < \deg q$. It is exact, $p = s q$, when the remainder is $0$.
- The divisor ‹q› is nonzero. Mathlib’s division is total, with `p / 0 = 0`, and a zero divisor is refused.
- The tactic [[cas]] proves `p / q = s` goals in `ℚ[X]`.

## Examples

### Basic Examples

The division of $x^4 - 1$ by $x^2 + 1$ is exact:

```lean
#cas [polynomialQuotient] (x^4 - 1, x^2 + 1)
```

---

A divisor that is not monic gives fractions:

```lean
#cas [polynomialQuotient] (x^3 + 1, 2*x - 1)
```

### Scope

When the divisor has the larger degree, the quotient is $0$:

```lean
#cas [polynomialQuotient] (x + 1, x^2 + 1)
```

### Applications

The first example as a theorem about Mathlib’s `/`. Only the three standard axioms are used:

```lean
open Polynomial in
theorem quotient_by_quadratic : (X ^ 4 - 1 : ℚ[X]) / (X ^ 2 + 1) = X ^ 2 - 1 := by
  cas

#print axioms quotient_by_quadratic
```

### Properties and Relations

[[polynomialRemainder]] gives the other part of the division. Here it is $\tfrac{9}{8}$, so $x^3 + 1 = (\tfrac{1}{2}x^2 + \tfrac{1}{4}x + \tfrac{1}{8})(2x - 1) + \tfrac{9}{8}$:

```lean
#cas [polynomialRemainder] (x^3 + 1, 2*x - 1)
```

---

[[polynomialQuotientRemainder]] gives both:

```lean
#cas [polynomialQuotientRemainder] (x^3 + 1, 2*x - 1)
```

---

For real numbers, [[cancel]] divides out the common factor of $(x^2 - 1)/(x - 1)$. Lean’s division of reals is total ($1/0 = 0$), so the result comes with the conditions $x - 1 \ne 0$ and $x \ne 0$:

```lean
#cas [cancel] ((x^2-1)/(x-1) + 1/x)
```

### Possible Issues

Mathlib sets `p / 0 = 0`, and a zero divisor is refused:

```lean error
#cas [polynomialQuotient] (x^2, 0)
```

### Neat Examples

Dividing $x^5 - 1$ by $x - 1$ gives the geometric sum $1 + x + x^2 + x^3 + x^4$:

```lean
#cas [polynomialQuotient] (x^5 - 1, x - 1)
```

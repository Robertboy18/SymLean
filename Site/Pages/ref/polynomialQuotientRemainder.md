+++
id = "polynomialQuotientRemainder"
kind = "mode"
title = "polynomialQuotientRemainder"
summary = "Gives the quotient and the remainder of a division of polynomials, with a theorem about `/` and `%` in `ℚ[X]`."
forms = ["CAS.Command.casPolynomialQuotientRemainderCommand"]
see_also = ["polynomialQuotient", "polynomialRemainder", "polynomialGCD", "apart"]
guide = "polynomials"
tutorials = ["first-hour"]
+++

::: usage
`#cas [polynomialQuotientRemainder] (‹p›, ‹q›)`
: gives the quotient $s$ and the remainder $r$ of the division of the polynomial ‹p› by the nonzero polynomial ‹q› and proves `p / q = s ∧ p % q = r` in Mathlib’s `ℚ[X]`.
:::

`polynomialQuotientRemainder` is polynomial long division with a proof attached. The output is the pair $[s, r]$ with $p = s q + r$ and $\deg r < \deg q$, and the theorem is about Mathlib’s `/` and `%` on `ℚ[X]`.

For the proof we divide by the monic polynomial $q / c$, where $c$ is the leading coefficient of $q$. The identity $p = s' (q / c) + r$ and the degree bound determine the quotient and the remainder by Mathlib’s `Polynomial.div_modByMonic_unique`, and `Polynomial.div_def` and `Polynomial.mod_def` relate them to `/` and `%`.

## Details and Options

- The theorem is `p / q = s ∧ p % q = r` in `ℚ[X]`, with the variable read as `Polynomial.X`. The two inputs have the same single variable.
- The remainder has a smaller degree than ‹q›. When ‹q› has a larger degree than ‹p›, the quotient is $0$ and the remainder is ‹p›.
- The divisor ‹q› is nonzero. Mathlib’s division is total, with `p / 0 = 0` and `p % 0 = p`, and a zero divisor is refused.
- The tactic [[cas]] proves `p / q = s` and `p % q = r` goals in `ℚ[X]`. It proves each part of the conjunction, so you prove the conjunction as `⟨by cas, by cas⟩`.
- [[polynomialQuotient]] and [[polynomialRemainder]] print one of the two, with the same theorem.

## Examples

### Basic Examples

A division by $2x - 1$. The quotient has fractions as coefficients:

```lean
#cas [polynomialQuotientRemainder] (x^3 + 1, 2*x - 1)
```

### Scope

The zero polynomial divided by $x + 1$:

```lean
#cas [polynomialQuotientRemainder] (0, x + 1)
```

---

When the divisor has the larger degree, the quotient is $0$ and the remainder is the dividend:

```lean
#cas [polynomialQuotientRemainder] (x + 1, x^2 + 1)
```

### Applications

The first example as a theorem about Mathlib’s `/` and `%`, one part at a time. Only the three standard axioms are used:

```lean
open Polynomial in
theorem division_by_linear :
    (X ^ 3 + 1 : ℚ[X]) / (2 * X - 1) = C (1 / 2) * X ^ 2 + C (1 / 4) * X + C (1 / 8) ∧
      (X ^ 3 + 1 : ℚ[X]) % (2 * X - 1) = C (9 / 8) :=
  ⟨by cas, by cas⟩

#print axioms division_by_linear
```

### Properties and Relations

[[polynomialQuotient]] prints the quotient alone:

```lean
#cas [polynomialQuotient] (x^3 + 1, 2*x - 1)
```

---

[[polynomialRemainder]] prints the remainder alone:

```lean
#cas [polynomialRemainder] (x^3 + 1, 2*x - 1)
```

---

[[apart]] splits off the polynomial part of a rational function. For $x^3/(x^2 + 1)$ it is the quotient $x$ of $x^3$ by $x^2 + 1$, and the remainder $-x$ stays over $x^2 + 1$:

```lean
#cas [apart] (x^3/(x^2+1))
```

### Possible Issues

The divisor must be nonzero:

```lean error
#cas [polynomialQuotientRemainder] (x^2, 0)
```

### Neat Examples

Dividing $x^{10} - 1$ by $x^3 - 1$ leaves $x^{10 \bmod 3} - 1 = x - 1$:

```lean
#cas [polynomialQuotientRemainder] (x^10 - 1, x^3 - 1)
```

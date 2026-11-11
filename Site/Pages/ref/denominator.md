+++
id = "denominator"
kind = "mode"
title = "denominator"
summary = "Gives the factored denominator of a rational expression brought to one fraction, with the conditions of the identity."
forms = ["CAS.Command.casDenominatorCommand"]
see_also = ["numerator", "together", "apart"]
guide = "algebra"
tutorials = ["first-hour"]
+++

::: usage
`#cas [denominator] ‹e›`
: gives the denominator $D$ of the fraction $N/D$ that `together` makes of the rational expression ‹e›, with the conditions under which $N/D$ equals ‹e›.
:::

`denominator` puts a rational expression over a common denominator and gives you that denominator. The theorem is the one of [[together]], so what is proved is the whole identity $e = N/D$.

The denominator stays factored as far as the input factors it. The conditions are the divisors of the input: Lean’s division is total ($1/0 = 0$), so $e = N/D$ can fail where a divisor vanishes, and the theorem assumes that none of them does.

## Details and Options

- The theorem is that of `#cas [together] ‹e›`: $\forall x_1, \dots, x_n,\; d_1 \ne 0 \to \dots \to d_k \ne 0 \to e = N/D$, over the divisors $d_1, \dots, d_k$ of $e$ as written.
- $D$ is a product of powers of pairwise coprime polynomials obtained from the divisors by gcds. When no divisor of $e$ has a variable, $D$ is a number.
- The input is a rational expression as for [[together]]: real variables and rational numbers combined by `+`, `-`, `*`, `/` and natural powers, with polynomial divisors.
- [[numerator]] gives $N$, and [[apart]] splits a fraction over the factors of its denominator.

## Examples

### Basic Examples

A difference of two reciprocals:

```lean
#cas [denominator] (1/(x-1) - 1/(x+1))
```

---

With numbers as divisors, the denominator is a number and there is no condition:

```lean
#cas [denominator] (x/2 + y/3)
```

### Scope

The denominator is not the product of the divisors. Here $x^2 - 1$ and $x - 1$ share the factor $x - 1$, which appears once:

```lean
#cas [denominator] (1/(x^2-1) + 1/(x-1))
```

---

The gcd $x + 1$ of the two divisors splits $x^2 - 1$, so the denominator is a product of $x - 1$ and $x + 1$:

```lean
#cas [denominator] (x/(x^2 - 1) + 1/(x + 1))
```

### Applications

The first example as a theorem, with a condition for each divisor. Only the three standard axioms are used:

```lean
theorem difference_of_reciprocals (x : ℝ) (h₁ : x - 1 ≠ 0) (h₂ : x + 1 ≠ 0) :
    1 / (x - 1) - 1 / (x + 1) = 2 / ((x - 1) * (x + 1)) := by
  cas

#print axioms difference_of_reciprocals
```

### Properties and Relations

[[numerator]] gives the other part of the same fraction:

```lean
#cas [numerator] (1/(x-1) - 1/(x+1))
```

---

[[together]] prints the whole fraction:

```lean
#cas [together] (x/2 + y/3)
```

---

[[apart]] goes back to partial fractions over the factors of the denominator:

```lean
#cas [apart] (1/((x - 1)*(x + 1)))
```

### Possible Issues

A divisor must be a polynomial. Multiply the inner fraction out first. For $x \ne 0$ the expression is $x/(x + 1)$:

```lean error
#cas [denominator] (1/(1 + 1/x))
```

---

Functions other than the field operations are refused:

```lean error
#cas [denominator] (sin x / x)
```

+++
id = "numerator"
kind = "mode"
title = "numerator"
summary = "Gives the numerator of a rational expression brought to one fraction, with the conditions of the identity."
forms = ["CAS.Command.casNumeratorCommand"]
see_also = ["denominator", "together", "cancel"]
guide = "algebra"
tutorials = ["first-hour"]
+++

::: usage
`#cas [numerator] ‹e›`
: gives the numerator $N$ of the fraction $N/D$ that `together` makes of the rational expression ‹e›, with the conditions under which $N/D$ equals ‹e›.
:::

`numerator` brings a rational expression to one fraction and gives you its numerator. A numerator means little until you know which fraction it belongs to, so the theorem is the one of [[together]]: the report says which fraction that is and where it equals the input.

Lean’s division is total ($1/0 = 0$), so the identity $e = N/D$ holds where the divisors of $e$ are nonzero, and the conditions say so. At a zero of a divisor, the numerator tells you nothing about $e$.

## Details and Options

- The theorem is that of `#cas [together] ‹e›`: $\forall x_1, \dots, x_n,\; d_1 \ne 0 \to \dots \to d_k \ne 0 \to e = N/D$, over the divisors $d_1, \dots, d_k$ of $e$ as written.
- $N$ is expanded and has no common factor with $D$.
- The input is a rational expression as for [[together]]: real variables and rational numbers combined by `+`, `-`, `*`, `/` and natural powers, with polynomial divisors.
- [[denominator]] gives $D$, and [[together]] the whole fraction.

## Examples

### Basic Examples

The numerator of $1/x + 1/y$:

```lean
#cas [numerator] (1/x + 1/y)
```

---

The numerator is expanded:

```lean
#cas [numerator] (x/(x^2 - 1) + 1/(x + 1))
```

### Scope

The fraction is in lowest terms first, so the common factor $x - y$ is gone:

```lean
#cas [numerator] ((x^3 - y^3)/(x^2 - y^2))
```

---

Numbers as divisors:

```lean
#cas [numerator] (x/2 + y/3)
```

### Applications

Multiplying by the denominator clears the fractions. The theorem needs both conditions, and only the three standard axioms are used:

```lean
theorem numerator_cleared (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (1 / x + 1 / y) * (x * y) = x + y := by
  cas

#print axioms numerator_cleared
```

---

The numerator $2x - 1$ of the second example vanishes at $x = \tfrac{1}{2}$, where no divisor does, and so the expression vanishes there:

```lean
example : (1 / 2 : ℝ) / ((1 / 2) ^ 2 - 1) + 1 / (1 / 2 + 1) = 0 := by
  norm_num
```

### Properties and Relations

[[together]] prints the whole fraction, with the same theorem:

```lean
#cas [together] (1/x + 1/y)
```

---

[[denominator]] gives the other part. For $x/2 + y/3$ it is $6$:

```lean
#cas [denominator] (x/2 + y/3)
```

### Possible Issues

Only rational expressions are accepted. [[simplify]] accepts `sqrt`:

```lean error
#cas [numerator] (sqrt x / x)
```

---

A divisor must be a polynomial. Multiply the inner fraction out first. For $x \ne 0$ the expression is $x/(x + 1)$:

```lean error
#cas [numerator] (1/(1 + 1/x))
```

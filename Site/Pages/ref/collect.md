+++
id = "collect"
kind = "mode"
title = "collect"
summary = "Writes a polynomial as a sum of powers of one variable, with coefficients in the other variables."
forms = ["CAS.Command.casCollectCommand"]
see_also = ["coefficient", "coefficientList", "exponent", "expand"]
guide = "algebra"
tutorials = ["first-hour"]
+++

::: usage
`#cas [collect ‹x›] ‹e›`
: writes the polynomial ‹e› as a sum of powers of ‹x› whose coefficients are expanded polynomials in the other variables, and proves that the two are equal.
:::

A polynomial with several parameters is often easier to read once its terms are grouped by the powers of one variable, the way you would write $a^2 x^2 + (2a + b)\,x + 1$ on paper. `collect` does that regrouping. The theorem is an identity for all real values of all the variables, proved by `ring`, so there are no conditions to carry around.

## Details and Options

- The theorem is $\forall x, y, \dots,\; e = \sum_k c_k x^k$ about Mathlib’s real numbers, where the $c_k$ are the printed coefficients, proved by `ring1`.
- The input is a polynomial with rational coefficients in real variables, and ‹x› is one of them. A quotient by a term with a variable is refused.
- The terms are printed from the highest power of ‹x› down, and a coefficient that is a sum is put in parentheses.
- [[coefficient]] gives one coefficient and [[coefficientList]] all of them, with theorems about Mathlib’s `Polynomial.coeff`. [[exponent]] gives the degree.
- The tactic [[cas]] proves these identities.

## Examples

### Basic Examples

A quadratic in $x$ with the parameters $a$ and $b$:

```lean
#cas [collect x] ((1 + a*x)^2 + b*x)
```

---

The terms are gathered by the powers of $x$:

```lean
#cas [collect x] (x*y + x^2*y + x + y^2*x^2)
```

### Scope

The same polynomial collected in $y$:

```lean
#cas [collect y] (x*y + x^2*y + x + y^2*x^2)
```

### Applications

The first example as a theorem, for all real `x`, `a` and `b`. Only the three standard axioms are used:

```lean
theorem collect_in_x (x a b : ℝ) :
    (1 + a * x) ^ 2 + b * x = a ^ 2 * x ^ 2 + (2 * a + b) * x + 1 := by
  cas

#print axioms collect_in_x
```

### Properties and Relations

[[expand]] gives the monomials one by one:

```lean
#cas [expand] ((x + 1)^3 * (y - 2))
```

`collect` groups them by the powers of $x$:

```lean
#cas [collect x] ((x + 1)^3 * (y - 2))
```

---

[[coefficient]] reads off one coefficient:

```lean
#cas [coefficient x 2] ((x + y)^3)
```

---

[[coefficientList]] reads off all of them, the constant term first:

```lean
#cas [coefficientList x] (a*x^2 + b*x + c)
```

---

[[exponent]] gives the degree in $x$. It is $2$ where $a \ne 0$:

```lean
#cas [exponent x] (a*x^2 + x + 1)
```

### Possible Issues

A quotient by a term with a variable is refused:

```lean error
#cas [collect x] (1/x + x)
```

---

For a rational function, [[apart]] splits off the polynomial part:

```lean
#cas [apart] (x^3/(x^2+1))
```

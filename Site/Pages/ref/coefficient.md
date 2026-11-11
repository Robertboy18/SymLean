+++
id = "coefficient"
kind = "mode"
title = "coefficient"
summary = "Gives the coefficient of a power of one variable in a polynomial, with a theorem about `Polynomial.coeff`."
forms = ["CAS.Command.casCoefficientCommand"]
see_also = ["coefficientList", "collect", "exponent", "expand"]
guide = "polynomials"
tutorials = ["first-hour"]
+++

::: usage
`#cas [coefficient ‹x› ‹k›] ‹e›`
: gives the coefficient of `‹x› ^ ‹k›` in the polynomial ‹e› and proves it about Mathlib’s `Polynomial.coeff`.
:::

`coefficient` reads off one coefficient of a polynomial without making you keep the whole expansion. The theorem is about Mathlib’s polynomials: ‹x› is read as `Polynomial.X`, and the statement is `P.coeff k = c`.

Any other variable enters as a constant. For $(x + y)^3$ and $k = 2$ the theorem is `∀ y : ℝ, ((X + C y) ^ 3).coeff 2 = 3 * y`, in $\mathbb{R}[X]$, with $y$ inside the polynomial as the constant `C y`.

## Details and Options

- The theorem is `P.coeff k = c` in `ℚ[X]` when ‹e› has no other variable, and `∀ y … : ℝ, P.coeff k = c` in `ℝ[X]`, with the other variables as constants `C y`, when it has.
- The input is a polynomial with rational coefficients, as for [[collect]], and ‹k› is a natural number literal.
- A quotient by a term with a variable is refused.
- The tactic [[cas]] proves `coeff` goals in `ℚ[X]`, and it refuses a wrong value with the right one in its message.
- [[coefficientList]] gives all the coefficients, and [[exponent]] the degree.

## Examples

### Basic Examples

The coefficient of $x^2$ in $(x + y)^3$. The other variable stays in the coefficient:

```lean
#cas [coefficient x 2] ((x + y)^3)
```

---

A binomial coefficient, $\binom{5}{2} = 10$:

```lean
#cas [coefficient x 2] ((x + 1)^5)
```

### Scope

The factor $2$ of $2x$ comes in with its third power, $\binom{5}{3} \cdot 2^3 = 80$:

```lean
#cas [coefficient x 3] ((1 + 2*x)^5)
```

### Applications

The binomial coefficient as a theorem about `Polynomial.coeff`. Only the three standard axioms are used:

```lean
open Polynomial in
theorem binomial_coefficient_two : ((X + 1) ^ 5 : ℚ[X]).coeff 2 = 10 := by
  cas

#print axioms binomial_coefficient_two
```

### Properties and Relations

[[coefficientList]] gives all the coefficients at once, the constant term first:

```lean
#cas [coefficientList x] ((x + 1)^3 - x/2)
```

---

[[collect]] shows every coefficient in place:

```lean
#cas [collect x] ((1 + a*x)^2 + b*x)
```

---

[[exponent]] gives the degree. The $x^3$ terms cancel here:

```lean
#cas [exponent x] ((x + 1)^3 - x^3)
```

### Possible Issues

A quotient by a term with a variable is refused:

```lean error
#cas [coefficient x 1] (1/x)
```

---

Lean’s total division makes $1/(1 + x \cdot (1/x))$ equal to $\tfrac{1}{2}$ for $x \ne 0$ and to $1$ at $x = 0$. It is not a polynomial, and it is refused:

```lean error
#cas [coefficient x 0] (1 / (1 + x * (1 / x)))
```

---

The tactic `cas` refuses a wrong coefficient and gives the right one:

```lean error
open Polynomial in
example : ((X + 1) ^ 5 : ℚ[X]).coeff 2 = 5 := by
  cas
```

+++
id = "exponent"
kind = "mode"
title = "exponent"
summary = "Gives the degree of a polynomial in one variable, with a theorem about `Polynomial.natDegree`."
forms = ["CAS.Command.casExponentCommand"]
see_also = ["coefficient", "coefficientList", "collect", "roots"]
guide = "polynomials"
tutorials = ["first-hour"]
+++

::: usage
`#cas [exponent ‹x›] ‹e›`
: gives the degree of the polynomial ‹e› in ‹x› and proves it about Mathlib’s `Polynomial.natDegree`.
:::

The degree of a polynomial isn’t always the one you see on the page, because terms can cancel. `exponent` reads the degree off the expanded form, after the cancellations, so $(x + 1)^3 - x^3$ has degree $2$. The theorem is `P.natDegree = d` about Mathlib’s polynomials.

Parameters make this more delicate than it looks. When the leading coefficient involves the other variables it could be zero, so the theorem assumes that it isn’t. For $a x^2 + x + 1$ the theorem is `∀ a : ℝ, a ≠ 0 → (C a * X ^ 2 + X + 1).natDegree = 2`, and the report prints the condition $a \ne 0$. I would much rather see that condition spelled out than get a degree that is wrong for one value of $a$.

## Details and Options

- The theorem is `P.natDegree = d`, where `P` is ‹e› read as a polynomial as for [[coefficient]]: in `ℚ[X]`, or in `ℝ[X]` for all values of the other variables, which enter as constants `C y`.
- When the leading coefficient $c$ involves the other variables, the statement is $c \ne 0 \to$ `P.natDegree = d`.
- The degree is that of the expanded polynomial, so terms that cancel do not count.
- The zero polynomial is refused. Mathlib sets `natDegree 0 = 0` and `degree 0 = ⊥`.
- The input is a polynomial with rational coefficients, as for [[collect]]. A quotient by a term with a variable is refused.
- The tactic [[cas]] proves `natDegree` goals in `ℚ[X]`, and it refuses a wrong degree with the right one in its message.

## Examples

### Basic Examples

The $x^3$ terms cancel, and the degree is $2$:

```lean
#cas [exponent x] ((x + 1)^3 - x^3)
```

---

With a parameter in the leading coefficient, the degree comes with a condition:

```lean
#cas [exponent x] (a*x^2 + x + 1)
```

### Scope

A product is expanded first, and its degree is the sum of the degrees of its factors:

```lean
#cas [exponent x] ((x^2 + 1)^5 * (x - 1))
```

### Applications

The first example as a theorem about `Polynomial.natDegree`. Only the three standard axioms are used:

```lean
open Polynomial in
theorem degree_of_difference : ((X + 1) ^ 3 - X ^ 3 : ℚ[X]).natDegree = 2 := by
  cas

#print axioms degree_of_difference
```

### Properties and Relations

[[coefficient]] gives the leading coefficient, the coefficient of $x^d$:

```lean
#cas [coefficient x 2] ((x + 1)^3 - x^3)
```

---

[[coefficientList]] has one entry more than the degree:

```lean
#cas [coefficientList x] ((x + 1)^3 - x/2)
```

---

A polynomial of degree $5$:

```lean
#cas [exponent x] ((x - 1)^2 * (x + 2) * (x^2 - 2))
```

It has at most $5$ roots. [[roots]] finds $4$ real ones, since $1$ is a double root:

```lean
#cas [roots x] ((x - 1)^2 * (x + 2) * (x^2 - 2))
```

### Possible Issues

The zero polynomial is refused:

```lean error
#cas [exponent x] (0)
```

---

The tactic `cas` refuses a wrong degree and gives the right one:

```lean error
open Polynomial in
example : (X ^ 3 + 1 : ℚ[X]).natDegree = 2 := by
  cas
```

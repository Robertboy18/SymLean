+++
id = "cancel"
kind = "mode"
title = "cancel"
summary = "Cancels common factors in each summand of a rational expression, with the conditions under which the result agrees."
forms = ["CAS.Command.casCancelCommand"]
see_also = ["together", "simplify", "factor", "polynomialGCD"]
guide = "algebra"
tutorials = ["first-hour"]
+++

::: usage
`#cas [cancel] ‹e›`
: cancels the common factors of numerator and denominator in each summand of the rational expression ‹e› and gives the conditions under which the result equals ‹e›.
:::

`cancel` reduces each fraction in a sum on its own and keeps the terms apart, which is what I want when a sum reads better term by term. [[together]] would make one fraction of it.

The catch is the factor you cancel. Cancelling a factor $d$ is valid only where $d \ne 0$, and in Lean this matters, because division is total. At $x = 1$ the quotient $(x^2 - 1)/(x - 1)$ is $0/0 = 0$, while $x + 1$ is $2$. So the theorem has a condition for each divisor of the input.

## Details and Options

- The theorem has the form $\forall x_1, \dots, x_n,\; d_1 \ne 0 \to \dots \to d_k \ne 0 \to e = e'$, where $d_1, \dots, d_k$ are the divisors of $e$ as written and $e'$ is the printed sum. It is proved by `field_simp` and `ring`.
- The input is a rational expression as for [[together]]: real variables and rational numbers combined by `+`, `-`, `*`, `/` and natural powers, with polynomial divisors.
- The summands are not brought to a common denominator.
- The conditions are all the divisors, also those of summands where nothing cancels. A proof may need fewer (see Applications).
- [[simplify]] cancels common factors in expressions with elementary functions as well.
- The tactic [[cas]] proves these identities, with the conditions as hypotheses.

## Examples

### Basic Examples

The first summand reduces to $x + 1$, and $1/x$ stays:

```lean
#cas [cancel] ((x^2-1)/(x-1) + 1/x)
```

### Scope

Two variables:

```lean
#cas [cancel] ((x^3 - y^3)/(x - y) + 1/y)
```

---

A difference of two quotients, each reduced on its own:

```lean
#cas [cancel] ((x^2 - y^2)/(x - y) - (x^3 - 1)/(x - 1))
```

### Applications

The first example as a theorem. Only $x - 1 \ne 0$ is needed, since $1/x$ is on both sides, and only the three standard axioms are used:

```lean
theorem cancel_then_add (x : ℝ) (h : x - 1 ≠ 0) :
    (x ^ 2 - 1) / (x - 1) + 1 / x = x + 1 + 1 / x := by
  cas

#print axioms cancel_then_add
```

---

Without that condition the cancellation is false in Lean. At $x = 1$ the left side is $0/0 = 0$ and the right side is $2$:

```lean
example : ¬ ∀ x : ℝ, (x ^ 2 - 1) / (x - 1) = x + 1 := by
  intro h
  have := h 1
  norm_num at this
```

### Properties and Relations

[[together]] makes one fraction of the same sum:

```lean
#cas [together] ((x^2-1)/(x-1) + 1/x)
```

---

[[simplify]] cancels a quotient as well:

```lean
#cas [simplify] ((x ^ 4 - 1) / (x ^ 2 - 1))
```

### Possible Issues

A function other than the field operations is refused:

```lean error
#cas [cancel] (sin x / x)
```

---

[[simplify]] cancels inside functions:

```lean
#cas [simplify] (exp ((x^2 - y^2)/(x - y)))
```

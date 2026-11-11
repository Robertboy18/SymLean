+++
id = "together"
kind = "mode"
title = "together"
summary = "Writes a rational expression as one fraction in lowest terms, with the conditions under which they agree."
forms = ["CAS.Command.casTogetherCommand"]
see_also = ["cancel", "numerator", "denominator", "apart", "simplify"]
guide = "algebra"
tutorials = ["first-hour"]
+++

::: usage
`#cas [together] ‹e›`
: writes the rational expression ‹e› as one fraction in lowest terms and gives the conditions under which the fraction equals ‹e›.
:::

`together` puts a sum of fractions over one denominator, the way you would by hand. The answer comes with a theorem, and the conditions of the theorem come from the divisors of the input.

On paper we rarely write those conditions down, but Lean needs them, because its division is total: $1/0 = 0$. At $x = 0$ the sum $1/x + 1/y$ is $1/y$ in Lean, while $(x + y)/(x y)$ is $y/0 = 0$. So the identity needs $x \ne 0$ and $y \ne 0$, and the theorem has them as hypotheses.

## Details and Options

- The theorem has the form $\forall x_1, \dots, x_n,\; d_1 \ne 0 \to \dots \to d_k \ne 0 \to e = N/D$ about Mathlib’s real division, where $d_1, \dots, d_k$ are the divisors of $e$ as written. It is proved by `field_simp` and `ring`.
- The input is built from real variables and rational numbers by `+`, `-`, `*`, `/` and natural powers, and every divisor is a polynomial.
- The denominator $D$ is a product of powers of pairwise coprime polynomials obtained from the divisors by gcds, so it stays factored as far as the input factors it. Each factor of $D$ divides one of the $d_i$, which `ring` shows. The numerator $N$ is expanded.
- A divisor that is a number gives no condition.
- [[numerator]] and [[denominator]] print $N$ and $D$, with the same theorem. [[cancel]] cancels inside each summand without a common denominator, and [[apart]] goes the other way.
- The tactic [[cas]] proves these identities, with the conditions as hypotheses.

## Examples

### Basic Examples

Two reciprocals:

```lean
#cas [together] (1/x + 1/y)
```

---

The denominator stays factored as the input factors it, and each divisor gives a condition:

```lean
#cas [together] (1/(x^2-1) + 1/(x-1))
```

### Scope

Numbers as divisors need no condition:

```lean
#cas [together] (x/2 + y/3)
```

---

The fraction is in lowest terms. Here the common factor $x - y$ cancels, and the condition is still the divisor of the input:

```lean
#cas [together] ((x^3 - y^3)/(x^2 - y^2))
```

### Applications

The first example as a theorem, with the conditions as hypotheses. Only the three standard axioms are used:

```lean
theorem reciprocals_together (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    1 / x + 1 / y = (x + y) / (x * y) := by
  cas

#print axioms reciprocals_together
```

---

Without the conditions the identity is false in Lean. At $x = 0$ and $y = 1$ the left side is $1$ and the right side is $1/0 = 0$:

```lean
example : ¬ ∀ x y : ℝ, 1 / x + 1 / y = (x + y) / (x * y) := by
  intro h
  have := h 0 1
  norm_num at this
```

### Properties and Relations

[[numerator]] gives the numerator $x + y$ of the first example:

```lean
#cas [numerator] (1/x + 1/y)
```

---

[[denominator]] gives the $6$ of $(3x + 2y)/6$:

```lean
#cas [denominator] (x/2 + y/3)
```

---

[[cancel]] cancels inside each summand and keeps the sum:

```lean
#cas [cancel] ((x^2-1)/(x-1) + 1/x)
```

---

[[apart]] splits one fraction into partial fractions:

```lean
#cas [apart] (1/((x - 1)*(x + 1)))
```

### Possible Issues

The conditions are the divisors as written. Here $(x y + x - x)^2$ is $x^2 y^2$, and the condition keeps the form of the input:

```lean
#cas [together] (1/((x*y + x - x)^2) + 1)
```

---

A divisor must be a polynomial. Multiply the inner fraction out first. For $x \ne 0$ the expression is $x/(x + 1)$:

```lean error
#cas [together] (1/(1 + 1/x))
```

---

Functions other than the field operations are refused. [[simplify]] and [[fullSimplify]] accept them:

```lean error
#cas [together] (sin x / x)
```

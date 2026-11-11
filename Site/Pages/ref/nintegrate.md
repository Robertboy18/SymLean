+++
id = "nintegrate"
kind = "mode"
title = "nintegrate"
summary = "A definite integral to a fixed number of decimal places, with a theorem that bounds the error."
forms = ["CAS.Command.casNIntegrateCommand"]
see_also = ["integrate", "N", "enclose", "cega", "ndsolve"]
guide = "numerics"
tutorials = ["trust"]
+++

::: usage
`#cas [nintegrate ‹x› in [‹a›, ‹b›]] ‹f›`
: gives the integral of ‹f› from ‹a› to ‹b› as a decimal $c$ with 6 places, and proves $\lvert \int_a^b f \, dx - c \rvert \le 10^{-6}$.
`#cas (digits := ‹d›) [nintegrate ‹x› in [‹a›, ‹b›]] ‹f›`
: the same with ‹d› decimal places, from 1 to 12.
:::

Some integrands have no elementary antiderivative, $e^{-x^2}$ among them, and even when there is one, I often find a decimal with an error bound more useful than the closed formula. That is what `nintegrate` gives you: a decimal, and a theorem about Mathlib’s interval integral that says how far the decimal can be from the true value.

## Details and Options

- For the printed $c \pm 10^{-d}$ the theorem is $\lvert (\int_a^b f\,dx) - c \rvert \le 1/10^d$, stated with `∫ x in a..b`.
- The proof is a composite Simpson rule. Its remainder comes from an enclosure of the fourth derivative of ‹f› on every panel, and the number of panels doubles from 4 to 1024 until the decimals are fixed.
- A domain checker proves that ‹f› and its first four derivatives are defined on $[a, b]$. A factor $\sqrt{x}$ or a fractional power of $x$ at 0 is first removed by a substitution, so $\int_0^1 \sqrt{x}\,dx$ works.
- The limits are closed rational expressions with $a < b$, such as `-1` or `3/2`. ‹f› is an expression in ‹x› alone, in the grammar of [[N]].
- `(digits := d)` sets the number of decimal places, from 1 to 12, by default 6.
- The tactic [[cega]] proves the printed statement in a proof, and also bounds such as $\int_a^b f \le c$ for integrands that are only continuous.

## Examples

### Basic Examples

The Gaussian integral over $[0, 1]$, which has no elementary antiderivative:

```lean
#cas [nintegrate x in [0, 1]] (exp (-x^2))
```

---

The integral of $1/(1+x^2)$ over $[0, 1]$ is $\pi/4 = 0.785398\ldots$:

```lean
#cas [nintegrate x in [0, 1]] (1 / (1 + x^2))
```

### Scope

Logarithms, products and longer intervals:

```lean
#cas (digits := 8) [nintegrate x in [1, 2]] (log x)
```

```lean
#cas (digits := 4) [nintegrate x in [0, 2]] (x * exp x)
```

---

A square root at the left end. A substitution removes it before the Simpson rule runs:

```lean
#cas [nintegrate x in [0, 1]] (sqrt x)
```

```lean
#cas [nintegrate x in [0, 1]] (sqrt x * exp x)
```

---

Fractional powers of $x$ work the same way:

```lean
#cas [nintegrate x in [0, 1]] (x ^ (1/3 : ℝ))
```

```lean
#cas [nintegrate x in [0, 1]] (x ^ (2/3 : ℝ) / (1 + x))
```

### Options

`(digits := 8)` asks for eight places:

```lean
#cas (digits := 8) [nintegrate x in [0, 1]] (sin x)
```

### Applications

The printed value in a proof. `cega` proves the same statement, and only the three standard axioms are used:

```lean
theorem nintegrate_gauss :
    |(∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) - 746824 / 10 ^ 6| ≤ 1 / 10 ^ 6 := by
  cega

#print axioms nintegrate_gauss
```

---

A one-sided bound is often all a proof needs:

```lean
example : (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 3 / 4 := by
  cega
```

### Properties and Relations

[[integrate]] gives exact values when it finds an antiderivative. Here both agree:

```lean
#cas [integrate x in [0, 1]] (x * exp x)
```

```lean
#cas [nintegrate x in [0, 1]] (x * exp x)
```

---

When there is no elementary antiderivative, `integrate` finds none and `nintegrate` still gives digits:

```lean error
#cas [integrate x in [0, 1]] (exp (x ^ 2))
```

```lean
#cas [nintegrate x in [0, 1]] (exp (x ^ 2))
```

### Possible Issues

A pole in the interval. $1/x$ has no finite integral on $[0, 1]$, and no certificate exists:

```lean error
#cas [nintegrate x in [0, 1]] (1 / x)
```

---

At most 12 places:

```lean error
#cas (digits := 16) [nintegrate x in [0, 1]] (x)
```

---

The smaller limit comes first:

```lean error
#cas [nintegrate x in [1, 0]] (x)
```

### Neat Examples

A square root and an oscillation together, over $[0, 4]$:

```lean
#cas [nintegrate x in [0, 4]] (sqrt x * cos x)
```

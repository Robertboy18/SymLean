+++
id = "apart"
kind = "mode"
title = "apart"
summary = "Writes a rational function of one variable as a polynomial plus partial fractions, with the conditions of the identity."
forms = ["CAS.Command.casApartCommand"]
see_also = ["together", "factor", "integrate", "denominator"]
guide = "algebra"
tutorials = ["first-hour"]
+++

::: usage
`#cas [apart] ‹e›`
: writes the rational function ‹e› of one variable as a polynomial plus a sum of partial fractions and gives the conditions under which they agree.
`#cas [apart ‹x›] ‹e›`
: does the same with ‹x› named as the variable.
:::

`apart` writes a rational function as a polynomial plus partial fractions. It undoes [[together]], and it plays the part of Mathematica’s `Apart`. Partial fractions are worth having for two reasons: they show the poles of a function at a glance, and they often make it easier to integrate.

The thing to watch is the poles themselves. The theorem holds where the divisors of the input are nonzero, and it has to say so, because Lean’s division is total. At a pole both sides are computed with $1/0 = 0$, and they differ. At $x = 1$, for instance, the fraction $1/((x - 1)(x + 1))$ is $0$ in Lean, while $\tfrac{1}{2(x - 1)} - \tfrac{1}{2(x + 1)}$ is $-\tfrac{1}{4}$.

## Details and Options

- The theorem has the form $\forall x,\; d_1 \ne 0 \to \dots \to d_k \ne 0 \to e = q + \sum c/p^k$, where $d_1, \dots, d_k$ are the divisors of $e$ as written, $q$ is a polynomial, each $p$ is a factor of the denominator with integer coefficients, $k$ runs up to its multiplicity and $\deg c < \deg p$. Each $p$ divides one of the $d_i$, which `ring` shows, and `field_simp` and `ring` prove the identity.
- The theorem does not state that the factors are irreducible.
- The input is a rational function of one variable with rational coefficients. `#cas [apart x] ‹e›` names the variable.
- Without Hex the factors are those written in the input, refined by gcds: `1/((x - 1)*(x + 1))` splits, and a factor written as `x^2 - 1` stays whole. When a factor of degree two or more remains, the label reads “partial fractions over the written factors, refined by gcds”.
- When the denominator is one nonlinear factor with exponent $1$, only the polynomial part is split off, and a proper fraction with such a denominator is refused.
- With `CASHex.Factor` imported (built by `lake -R -Khex=on build CASHex`), Hex factors the denominator completely over $\mathbb{Q}$. The [Hex guide](guide:hex) has the details.
- The tactic [[cas]] proves these identities, with the conditions as hypotheses.

## Examples

### Basic Examples

Two linear factors:

```lean
#cas [apart] (1/((x - 1)*(x + 1)))
```

---

A polynomial part, a quadratic factor and a triple pole:

```lean
#cas [apart] (x^5/((x^2+1)*(x-1)^3))
```

### Scope

Over one quadratic factor, the polynomial part is split off:

```lean
#cas [apart] (x^3/(x^2+1))
```

```lean
#cas [apart] ((x^4 + 1)/(x^2 + 1))
```

---

The written factors are refined by gcds. The common factor $x^2$ of $x^4 + x^2$ and $x^3 + x^2$ comes out as the base of a power:

```lean
#cas [apart] (1/((x^4 + x^2)*(x^3 + x^2)))
```

---

With Hex the denominator is factored completely over $\mathbb{Q}$. These lines are from the library’s Hex examples, with the output they pin:

```lean quote=CASHex/Examples.lean
#cas [apart] (1/(x^2-1))
```

```lean quote=CASHex/Examples.lean
#cas [apart] (1/(x^3 + 1))
```

```lean quote=CASHex/Examples.lean
#cas [apart] ((3*x + 5)/(2*x^2 + 3*x + 1))
```

### Options

A variable after the mode name says which variable the function is in. Large roots are no trouble:

```lean
#cas [apart x] (1 / ((x - 100000001) * (x - 2)))
```

### Applications

The first example as a theorem, with the printed condition as hypothesis. Only the three standard axioms are used:

```lean
theorem apart_two_linear (x : ℝ) (h : (x - 1) * (x + 1) ≠ 0) :
    1 / ((x - 1) * (x + 1)) = 1 / (2 * (x - 1)) - 1 / (2 * (x + 1)) := by
  cas

#print axioms apart_two_linear
```

---

Without its condition the decomposition is false in Lean. At $x = 1$ the left side is $1/0 = 0$ and the right side is $-\tfrac{1}{4}$:

```lean
example : ¬ ∀ x : ℝ, 1 / (x ^ 2 - 1) = 1 / (2 * (x - 1)) - 1 / (2 * (x + 1)) := by
  intro h
  have := h 1
  norm_num at this
```

---

Partial fractions are the first step in integrating a rational function. [[integrate]] splits $x$ off this denominator:

```lean
#cas [integrate x] (1/(x^3 + x))
```

---

With Hex, the integrand may have a denominator that has to be factored first:

```lean quote=CASHex/Examples.lean
#cas [integrate x] (1/(x^3 - 1))
```

### Properties and Relations

[[denominator]] goes back: it recovers the factored denominator of a sum of partial fractions:

```lean
#cas [denominator] (1/(x-1) - 1/(x+1))
```

---

[[factor]] finds the factors to write in a denominator. Without Hex it finds the rational roots:

```lean
#cas [factor] (x^4 - 5*x^2 + 4)
```

### Possible Issues

Without Hex, a proper fraction whose denominator is written as one nonlinear factor is refused. Write the denominator as `(x - 1)*(x + 1)`, as in the first example, or import `CASHex.Factor`:

```lean error
#cas [apart] (1/(x^2-1))
```

---

The mode works in one variable:

```lean error
#cas [apart] (1/(x*y))
```

---

The factors are those written, refined by gcds, and they need not be irreducible. Here the written factor $x^3 + x - x$ is $x^3$, and it stays the base of the power:

```lean
#cas [apart] (1 / ((x^3 + x - x)^2))
```

### Neat Examples

With Hex, Sophie Germain’s identity $x^4 + 4 = (x^2 - 2x + 2)(x^2 + 2x + 2)$ splits this fraction:

```lean quote=CASHex/Examples.lean
#cas [apart] (1/(x^4 + 4))
```

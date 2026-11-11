+++
id = "minimize"
kind = "mode"
title = "minimize"
summary = "The minimum of a polynomial on the real line or on an interval, exact or enclosed, with a theorem."
forms = ["CAS.Command.casMinimizeCommand", "CAS.Command.casMinimizeInCommand"]
see_also = ["maximize", "derive", "roots", "reduce", "enclose", "cega"]
guide = "calculus"
tutorials = ["proving"]
+++

::: usage
`#cas [minimize ‹x›] ‹p›`
: gives the global minimum of the polynomial ‹p›, exactly when a rational point attains it and otherwise as a certified enclosure, and proves that no value of ‹p› is smaller.
`#cas [minimize ‹x› in [‹a›, ‹b›]] ‹p›`
: gives the minimum of ‹p› on the closed interval $[a, b]$ with rational endpoints $a < b$, with a point of the interval that attains it or comes within the enclosure.
`#cas (digits := ‹d›) [minimize ‹x›] ‹p›`
: the same with an enclosure of width at most $2 \cdot 10^{-d}$, for ‹d› from 1 to 6. The interval form takes ‹d› too.
:::

`minimize` looks for the smallest value of a polynomial and proves that nothing goes below it. When a rational point attains the minimum, the answer is exact, and the theorem says $m \le p(x)$ for every real $x$, and $p(x_0) = m$.

Often the minimizer is irrational, as for $x^4 - x$, whose minimizer is $4^{-1/3}$. Then the answer is an enclosure $[lo, hi]$ of the minimum, and the theorem says $lo \le p(x)$ for every $x$, and $p(x_1) \le hi$ at a rational point $x_1$ near the minimizer. What it bounds is the value of the minimum, not the position of the minimizer.

## Details and Options

- ‹p› is a polynomial in ‹x› with rational coefficients and no other variable.
- The exact theorem is $(\forall x,\; m \le p) \wedge p(x_0) = m$, and the enclosure theorem is $(\forall x,\; lo \le p) \wedge p(x_1) \le hi$. Lean writes the value at the point as `(fun x ↦ p) x₀`.
- The candidates are the real roots of the derivative $p'$. The bound comes from the sign certificate that [[cas]] uses for $p - m \ge 0$, and the value at the point from `norm_num`.
- A polynomial of odd degree, or of even degree with a negative leading coefficient, is unbounded below and is refused. On a closed interval every polynomial has a minimum.
- On $[a, b]$ the theorem is $(\forall x \in [a, b],\; m \le p) \wedge x_0 \in [a, b] \wedge p(x_0) = m$, stated with `Set.Icc a b`, or its enclosure form with a witness $x_1$ in the interval.
- `(digits := d)` makes the enclosure at most $2 \cdot 10^{-d}$ wide, for $d$ from 1 to 6, by default 3. More digits make the sign certificate slower.
- [[maximize]] is `minimize` of $-p$. In a proof, [[cas]] proves the bound $\forall x,\; m \le p$, and [[cega]] proves bounds on an interval for functions other than polynomials.

## Examples

### Basic Examples

A quadratic, with an exact minimum at a rational point:

```lean
#cas [minimize x] (x^2 - 2*x + 4)
```

---

The minimizer of $x^4 - x$ is $4^{-1/3}$, so the minimum is enclosed:

```lean
#cas [minimize x] (x^4 - x)
```

---

The minimum on an interval:

```lean
#cas [minimize x in [0, 2]] (x^2 - 2*x)
```

### Scope

A quartic with a rational minimizer and a rational minimum:

```lean
#cas [minimize x] (x^4 - x^3)
```

---

A quartic with two local minima. The global one is at an irrational point:

```lean
#cas [minimize x] (x^4 - 3*x^2 + x)
```

---

On an interval, the candidates are the critical points inside and the two endpoints:

```lean
#cas [minimize x in [-1, 2]] (x^3 - 3*x)
```

```lean
#cas [minimize x in [1, 2]] (x)
```

---

A polynomial of odd degree has a minimum on a closed interval, here at $\sqrt{2/3}$:

```lean
#cas [minimize x in [0, 2]] (x^3 - 2*x)
```

---

Rational endpoints:

```lean
#cas [minimize x in [1/2, 3/2]] (x^5 - 5*x)
```

### Options

`(digits := 4)` makes the enclosure at most $2 \cdot 10^{-4}$ wide:

```lean
#cas (digits := 4) [minimize x] (x^4 - x)
```

### Applications

The bound in a proof. `cas` proves it, and only the three standard axioms are used:

```lean
theorem minimize_quadratic : ∀ x : ℝ, 3 ≤ x ^ 2 - 2 * x + 4 := by
  cas

#print axioms minimize_quadratic
```

---

The exact minimum of $x^4 - x^3$ is a sharp bound:

```lean
example : ∀ x : ℝ, (-27 : ℝ) / 256 ≤ x ^ 4 - x ^ 3 := by cas
```

### Properties and Relations

The minimizer $3/4$ is a root of the derivative:

```lean
#cas [derive x] (x^4 - x^3)
```

---

[[maximize]] of $-p$ gives the same point:

```lean
#cas [maximize x] (x^3 - x^4)
```

### Possible Issues

A polynomial of odd degree has no global minimum:

```lean error
#cas [minimize x] (x^3 - x)
```

On a closed interval it has one:

```lean
#cas [minimize x in [-1, 1]] (x^3 - x)
```

---

Only polynomials. For other functions on an interval, [[cega]] proves bounds:

```lean error
#cas [minimize x] (sin x)
```

---

The smaller endpoint comes first:

```lean error
#cas [minimize x in [1, 0]] (x)
```

---

At most 6 digits:

```lean error
#cas (digits := 7) [minimize x] (x^4 - x)
```

### Neat Examples

On $[-2, 2]$ the minimum of $x^4 - 3x^2 + x$ is the global one, with a witness in the interval:

```lean
#cas [minimize x in [-2, 2]] (x^4 - 3*x^2 + x)
```

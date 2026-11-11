+++
id = "maximize"
kind = "mode"
title = "maximize"
summary = "The maximum of a polynomial on the real line or on an interval, exact or enclosed, with a theorem."
forms = ["CAS.Command.casMaximizeCommand", "CAS.Command.casMaximizeInCommand"]
see_also = ["minimize", "derive", "roots", "reduce", "enclose", "cega"]
guide = "calculus"
tutorials = ["proving"]
+++

::: usage
`#cas [maximize ‹x›] ‹p›`
: gives the global maximum of the polynomial ‹p›, exactly when a rational point attains it and otherwise as a certified enclosure, and proves that no value of ‹p› is larger.
`#cas [maximize ‹x› in [‹a›, ‹b›]] ‹p›`
: gives the maximum of ‹p› on the closed interval $[a, b]$ with rational endpoints $a < b$, with a point of the interval that attains it or comes within the enclosure.
`#cas (digits := ‹d›) [maximize ‹x›] ‹p›`
: the same with an enclosure of width at most $2 \cdot 10^{-d}$, for ‹d› from 1 to 6. The interval form takes ‹d› too.
:::

`maximize` looks for the largest value of a polynomial and proves that nothing goes above it. It is [[minimize]] applied to $-p$, with the inequalities turned around, so everything on that page holds here too.

You get one of two answers. When a rational point attains the maximum, the answer is exact, and the theorem says $p(x) \le M$ for every real $x$, and $p(x_0) = M$. Otherwise the answer is an enclosure, and the theorem says $p(x) \le hi$ for every $x$, and $lo \le p(x_1)$ at a rational point $x_1$ near the maximizer.

## Details and Options

- ‹p› is a polynomial in ‹x› with rational coefficients and no other variable.
- The exact theorem is $(\forall x,\; p \le M) \wedge p(x_0) = M$, and the enclosure theorem is $(\forall x,\; p \le hi) \wedge lo \le p(x_1)$. Lean writes the value at the point as `(fun x ↦ p) x₀`.
- A polynomial of odd degree, or of even degree with a positive leading coefficient, is unbounded above and is refused. On a closed interval every polynomial has a maximum.
- On $[a, b]$ the bound is $\forall x \in [a, b],\; p \le M$, stated with `Set.Icc a b`, and the point is proved to lie in the interval.
- `(digits := d)` makes the enclosure at most $2 \cdot 10^{-d}$ wide, for $d$ from 1 to 6, by default 3.
- In a proof, [[cas]] proves the bound $\forall x,\; p \le M$, and [[cega]] proves bounds on an interval, also for functions other than polynomials.

## Examples

### Basic Examples

A downward parabola, with its maximum at a rational point:

```lean
#cas [maximize x] (3 + 2*x - x^2)
```

---

The maximum on an interval, at an endpoint:

```lean
#cas [maximize x in [-3, 3]] (x^3 - 3*x)
```

---

An enclosed maximum, with a witness in the interval:

```lean
#cas [maximize x in [0, 1]] (x * (1 - x) * (x + 1))
```

### Scope

A maximum inside the interval:

```lean
#cas [maximize x in [-1, 1]] (1 - x^2)
```

---

A convex function takes its maximum at an endpoint:

```lean
#cas [maximize x in [0, 2]] (x^2 - 2*x)
```

---

A quartic with a negative leading coefficient:

```lean
#cas [maximize x] (x^3 - x^4)
```

### Options

`(digits := 4)` makes the enclosure at most $2 \cdot 10^{-4}$ wide, on the real line and on an interval:

```lean
#cas (digits := 4) [maximize x] (1 - x^4 + x)
```

```lean
#cas (digits := 4) [maximize x in [0, 1]] (x - x^3)
```

### Applications

The bound in a proof. `cas` proves it, and only the three standard axioms are used:

```lean
theorem maximize_quadratic : ∀ x : ℝ, 3 + 2 * x - x ^ 2 ≤ 4 := by
  cas

#print axioms maximize_quadratic
```

---

A bound on an interval, from the maximum $1/4$ of $x(1 - x)$ on $[0, 1]$. The tactic [[cega]] proves it:

```lean
#cas [maximize x in [0, 1]] (x * (1 - x))
```

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega
```

### Properties and Relations

[[minimize]] of $-p = x^2 - 2x - 3$ gives the same point as the first example, and the opposite value:

```lean
#cas [minimize x] (x^2 - 2*x - 3)
```

### Possible Issues

A polynomial of even degree with a positive leading coefficient has no maximum:

```lean error
#cas [maximize x] (x^2)
```

On a closed interval it has one:

```lean
#cas [maximize x in [-1, 1]] (x^2 + 1)
```

---

The smaller endpoint comes first:

```lean error
#cas [maximize x in [1, 0]] (x)
```

### Neat Examples

The open box of largest volume from a unit square of card: cut squares of side $x$ from the corners and fold, for the volume $x(1 - 2x)^2$:

```lean
#cas [maximize x in [0, 1/2]] (x * (1 - 2*x)^2)
```

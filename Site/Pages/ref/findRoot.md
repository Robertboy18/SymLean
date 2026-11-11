+++
id = "findRoot"
kind = "mode"
title = "findRoot"
summary = "A certified simple root of a function in an interval, to a chosen number of decimals, with a uniqueness theorem."
forms = ["CAS.Command.casFindRootCommand"]
see_also = ["roots", "solve", "enclose", "N", "cas"]
guide = "equations"
tutorials = ["proving"]
+++

::: usage
`#cas [findRoot ‹x› in [‹a›, ‹b›]] ‹f›`
: finds a simple root of ‹f› in $[a, b]$, prints it with 10 decimal places, and proves that exactly one root lies within $10^{-10}$ of the printed value. ‹f› is an expression or an equation `‹g› = ‹h›`.
`#cas (digits := ‹d›) [findRoot ‹x› in [‹a›, ‹b›]] ‹f›`
: the same with ‹d› decimal places, from 1 to 30.
:::

For an equation such as $\cos x = x$ I don’t need a formula. I need a root I can trust, in an interval I chose, and that is what `findRoot` gives you.

The search is simple. SymLean samples ‹f› at 65 equally spaced points of the interval and narrows the first sign change from the left by bisection. The check is the part that matters. The kernel verifies opposite signs at the two ends of a small interval, and an enclosure of the derivative that has one sign on it, so the interval holds exactly one root. The sign change alone would only give existence, and the derivative is what gives uniqueness.

## Details and Options

- For the printed `x = m ± 10^-d`, the theorem is `∃! x, x ∈ Set.Icc lo hi ∧ f x = 0`, where $[lo, hi]$ is $[m - 10^{-d}, m + 10^{-d}]$ clipped to the bracket of the sign change. For an equation `g = h` the statement is `g x = h x`.
- The endpoints $a < b$ are closed rational expressions, such as `-1`, `3/2` or `10^200`. ‹f› is an expression or an equation in ‹x› alone, in the calculator grammar of [[N]].
- A root where the derivative vanishes, two roots closer than the sample spacing and a sign change across a pole are refused. `log` and `sqrt` are evaluated only at positive arguments, so an interval that reaches $x \le 0$ inside them is refused.
- `(digits := d)` is the number of decimal places, from 1 to 30, by default 10.
- In a proof, [[cas]] proves that a root lies between two rational bounds, such as `∃ x : ℝ, Real.cos x = x ∧ 0.739 < x ∧ x < 0.74`, and that it is unique in an interval where the derivative has one sign.

## Examples

### Basic Examples

The root of $\cos x = x$, with the theorem that it is the only one within $10^{-10}$ of the printed value:

```lean
#cas [findRoot x in [0, 1]] (cos x = x)
```

---

An expression stands for the equation $f = 0$:

```lean
#cas [findRoot x in [1, 2]] (x^2 - 2)
```

### Scope

A logarithm, on an interval of positive numbers:

```lean
#cas [findRoot x in [1, 3]] (log x + x - 2)
```

---

The root of $\sin x$ between 2 and 4 is $\pi$:

```lean
#cas [findRoot x in [2, 4]] (sin x)
```

---

The interval may be wide, with a large endpoint:

```lean
#cas [findRoot x in [0, 10^200]] (x - 1)
```

### Options

`(digits := 20)` gives 20 decimal places, here of $\log 3$:

```lean
#cas (digits := 20) [findRoot x in [0, 2]] (exp x - 3)
```

---

At most 30 places:

```lean
#cas (digits := 30) [findRoot x in [1, 2]] (x^2 - 2)
```

### Applications

Bounds on the root in a proof. `cas` proves them, and only the three standard axioms are used:

```lean
theorem findRoot_cos : ∃ x : ℝ, Real.cos x = x ∧ 0.739 < x ∧ x < 0.74 := by
  cas

#print axioms findRoot_cos
```

---

Uniqueness on the whole interval needs a derivative of one sign on it, and $-\sin x - 1 < 0$ on $[0, 1]$:

```lean
example : ∃! x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧ Real.cos x = x := by cas
```

### Properties and Relations

For a polynomial, [[roots]] finds every real root at once, here both square roots of 2:

```lean
#cas (digits := 40) [roots x] (x^2 = 2)
```

### Possible Issues

A double root does not change sign. Find the root of the derivative, or use [[roots]] for a polynomial:

```lean error
#cas [findRoot x in [-1, 1]] (x^2)
```

---

At a triple root the derivative vanishes too, and the sign near the root cannot be decided:

```lean error
#cas [findRoot x in [-1, 1]] (x^3)
```

---

$1/(x - 1)$ changes sign at its pole and has no root. Choose an interval without poles:

```lean error
#cas [findRoot x in [0, 2]] (1 / (x - 1))
```

### Neat Examples

The omega constant, the root of $x e^x = 1$:

```lean
#cas [findRoot x in [0, 1]] (x * exp x - 1)
```

---

The same root as a goal:

```lean
example : ∃ x ∈ Set.Icc (0 : ℝ) 1, x * Real.exp x = 1 := by cas
```

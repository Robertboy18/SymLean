+++
id = "reduce"
kind = "mode"
title = "reduce"
summary = "A polynomial equation or inequality reduced to an equivalent union of intervals, with a theorem."
forms = ["CAS.Command.casReduceCommand"]
see_also = ["solve", "roots", "minimize", "cas"]
tutorials = ["proving"]
+++

::: usage
`#cas [reduce ‹x›] (‹lhs› < ‹rhs›)`
: reduces an equation, disequation or comparison of polynomials in ‹x› to an equivalent condition on ‹x›, a union of intervals whose endpoints are the real roots of ‹lhs› - ‹rhs›, and proves the equivalence. The relation may be `=`, `≠`, `<`, `≤`, `>` or `≥`.
:::

`reduce` tells you exactly where a polynomial inequality holds. The answer is a union of intervals, and the theorem is an equivalence: the inequality holds on those intervals and nowhere else. The “nowhere else” is the half that a plot or a few test points can’t give you.

The endpoints are the real roots of $lhs - rhs$. The rational ones are written exactly. Each of the others is named `ρ0`, `ρ1`, … and located in a rational interval of width $10^{-20}$.

## Details and Options

- For an affine relation, and for an equation of degree at most 2, the theorem is `∀ x : ℝ, rel ↔ P x` for the printed condition `P x`. Otherwise it is `∃ ρ, (bounds on ρ 0, ρ 1, …) ∧ ∀ x : ℝ, rel ↔ P x`, and `∃ ρ` is dropped when every root is rational.
- The two sides are polynomials in ‹x› alone with rational coefficients, of any degree.
- A quotient `p / q` compared with 0 is reduced through the product `p * q`, which has the same sign as `p / q` under Lean’s convention `p / 0 = 0`.
- A relation that holds for every ‹x› gives `True`, and one that holds for none gives `False`.
- There are no options. In a proof, [[cas]] proves a sign condition that holds for every ‹x›, such as `∀ x : ℝ, 0 < x ^ 2 - x + 1`, but not the equivalence of the report.

## Examples

### Basic Examples

An affine inequality:

```lean
#cas [reduce x] (-2 * x + 3 ≤ 7)
```

---

A quadratic with rational roots, with the theorem:

```lean
#cas [reduce x] (x^2 - 3*x + 2 > 0)
```

---

Irrational endpoints are named `ρ0` and `ρ1`:

```lean
#cas [reduce x] (x^2 < 2)
```

### Scope

A cubic, with a union of two intervals:

```lean
#cas [reduce x] (x^3 - x ≥ 0)
```

---

A double root, where the sign does not change, gives an isolated point:

```lean
#cas [reduce x] ((x - 1)^2 * (x + 2) ≤ 0)
```

---

A quintic with one real root:

```lean
#cas [reduce x] (x^5 - x - 1 < 0)
```

---

A quotient, through the product of its numerator and denominator:

```lean
#cas [reduce x] ((x - 1) / (x + 2) > 0)
```

---

A relation that holds everywhere:

```lean
#cas [reduce x] (x^2 + 1 > 0)
```

### Applications

A sign condition in a proof. `cas` proves it, and only the three standard axioms are used:

```lean
theorem reduce_positive : ∀ x : ℝ, 0 < x ^ 2 - x + 1 := by
  cas

#print axioms reduce_positive
```

### Properties and Relations

The endpoint `ρ0` of $x^5 - x - 1 < 0$ is the real root that [[roots]] encloses:

```lean
#cas [roots x] (x ^ 5 - x - 1 = 0)
```

---

The endpoints of $x^2 < 2$ are the solutions of $x^2 = 2$, which [[solve]] writes with square roots:

```lean
#cas [solve x] (x ^ 2 = 2)
```

### Possible Issues

A polynomial alone is not a relation. Write one, such as `x^2 + 1 > 0`:

```lean error
#cas [reduce x] (x^2 + 1)
```

---

Only polynomial and rational relations are reduced:

```lean error
#cas [reduce x] (sin x > 0)
```

### Neat Examples

The sign of a product of four factors alternates from one root to the next:

```lean
#cas [reduce x] ((x - 1) * (x - 2) * (x - 3) * (x - 4) > 0)
```

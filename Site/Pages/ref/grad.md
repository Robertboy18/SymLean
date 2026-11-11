+++
id = "grad"
kind = "mode"
title = "grad"
summary = "The gradient of an expression in several variables, with a theorem about Mathlib’s `HasGradientAt`."
forms = ["CAS.Command.casGradientCommand"]
see_also = ["derive", "minimize", "solve", "integrate", "cas"]
tutorials = ["first-hour", "proving"]
+++

::: usage
`#cas [grad ‹x›, ‹y›, …] ‹e›`
: gives the gradient of ‹e› in the listed variables, in that order, with a theorem about Mathlib’s `HasGradientAt` and the conditions it needs.
:::

`grad` collects the partial derivatives of a function into one vector. The theorem is about Mathlib’s `HasGradientAt` at the point $(x_1, \dots, x_n)$ of `EuclideanSpace ℝ (Fin n)`, since that is where gradients live in Mathlib. Every component is also proved on its own, as with [[derive]], and I find that handy: when a proof needs one partial derivative, you don’t have to dig it out of the vector.

## Details and Options

- For the variables $x_1, \dots, x_n$, the printed components $g_1, \dots, g_n$ and the conditions $c_1, \dots, c_k$, the theorem is $\forall x_1 \dots x_n,\; c_1 \to \dots \to c_k \to \operatorname{HasGradientAt}\,(\lambda p.\, e)\; (g_1, \dots, g_n)\; (x_1, \dots, x_n)$. Lean writes the vectors as `!₂[g₁, …, gₙ]` and ‹e› in the coordinates `p.ofLp 0`, `p.ofLp 1`, … of the point `p`.
- The vector of the components is also Mathlib’s `gradient` at every point where ‹e› is defined: every divisor and every argument of `log` is nonzero, every argument of `sqrt` and every base of a real power is positive, and no argument of `asin` or `acos` is $1$ or $-1$.
- Every variable of ‹e› must be listed, and the order in brackets is the order of the components. For a partial derivative with the other variables as parameters, [[derive]] is the mode.
- The functions are those of [[derive]].
- `set_option cas.verbose true` shows the tree of differentiation rules of every component, and `set_option cas.suggest true` adds the theorem as an `example` to paste.

## Examples

### Basic Examples

The gradient of $xy$, with the theorem about `HasGradientAt`:

```lean
#cas [grad x, y] (x * y)
```

---

A polynomial in two variables:

```lean
#cas [grad x, y] (x ^ 2 * y + y ^ 3)
```

### Scope

Functions of a product:

```lean
#cas [grad x, y] (sin (x * y))
```

---

The order in brackets is the order of the components:

```lean
#cas [grad y, x] (x ^ 2 * y + y ^ 3)
```

---

Three variables:

```lean
#cas [grad x, y, z] (x * y * z)
```

---

A logarithm needs a nonzero argument, and the condition is a hypothesis of the theorem:

```lean
#cas [grad x, y] (log (x ^ 2 + y ^ 2))
```

### Options

With `cas.verbose`, the details show the differentiation rules of each component:

```lean
set_option cas.verbose true in
#cas [grad x, y] (x * y)
```

### Applications

A component in a proof. `cas` proves it as a `HasDerivAt` statement, and only the three standard axioms are used:

```lean
theorem grad_first_component (x y : ℝ) :
    HasDerivAt (fun x ↦ x ^ 2 * y + y ^ 3) (2 * x * y) x := by
  cas

#print axioms grad_first_component
```

---

A critical point: the gradient of $x^2 + xy + y^2 - 3x$ vanishes where a linear system holds, and [[solve]] solves it:

```lean
#cas [grad x, y] (x ^ 2 + x * y + y ^ 2 - 3 * x)
```

```lean
#cas [solve x, y] (2 * x + y - 3 = 0 ∧ x + 2 * y = 0)
```

### Properties and Relations

The components are the partial derivatives of [[derive]], where the other variables are parameters:

```lean
#cas [derive y] (x ^ 2 * y + y ^ 3)
```

### Possible Issues

Every variable must be listed. Here `y` is missing:

```lean error
#cas [grad x] (x * y)
```

---

A quotient is differentiated where its divisor is nonzero, so the theorem says nothing on the line $y = 0$:

```lean
#cas [grad x, y] (x / y)
```

### Neat Examples

The gradient of a Gaussian points to its peak:

```lean
#cas [grad x, y] (exp (-(x ^ 2 + y ^ 2)))
```

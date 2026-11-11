+++
id = "enclose"
kind = "mode"
title = "enclose"
summary = "An interval that holds every value of an expression on a box, with upper, absolute and center bounds, all proved."
forms = ["CAS.Command.CEGA.casEncloseCommand", "CAS.CEGA.cegaEnclose", "CAS.CEGA.Elaboration.«cegaIntervalBinding_In[_,_]»"]
see_also = ["N", "cega", "maximize", "minimize", "nintegrate", "options"]
guide = "numerics"
tutorials = ["proving", "trust"]
+++

::: usage
`#cas [enclose ‹x› in [‹a›, ‹b›]] ‹e›`
: gives an interval with rational endpoints that holds every value of ‹e› for ‹x› in $[a, b]$, and proves it.
`#cas [enclose ‹x› in [‹a›, ‹b›], ‹y› in [‹c›, ‹d›]] ‹e›`
: the same on a box, with one binding for each variable, up to 8.
`#cas [enclose] ‹e›`
: encloses a closed expression.
`cega [enclose ‹x› in [‹a›, ‹b›]] ‹e›`
: proves a goal from the same query: an enclosure, an upper bound, an absolute bound or an approximation.
:::

When I want to know what a function does on a box, `enclose` is where I start, before I think about plotting it. You get an interval the function can’t leave, and a theorem about Mathlib’s real functions that says so. The same certificate gives the report three more statements: an upper bound, a bound on the absolute value, and a center with a radius.

## Details and Options

- For the printed interval $[lo, hi]$ the first theorem is $\forall x \in [a, b],\; lo \le e \wedge e \le hi$, stated with `Set.Icc`, with one more `∀` for each further binding.
- The next steps prove $e \le u$ for the upper bound, $\lvert e \rvert \le m$ for the absolute bound and $\lvert e - c \rvert \le r$ for the center $c$ and the radius $r$.
- The enclosure is valid, and not always tight. `(depth := n)` first bisects the box, up to $n$ levels deep, which can make it tight.
- Each binding has rational literal endpoints with $a \le b$, such as `-1`, `3/2` or `0.1`. A box has at most 8 coordinates (`cega.maxDimension`).
- Every subexpression must be defined on the whole box: denominators stay away from zero and the arguments of `log` stay positive.
- An endpoint is printed exactly when its rational is short, and otherwise rounded outward to 6 decimal places. The details show the exact rationals.
- `(prec := n)` sets the number of Taylor terms for `exp`, series terms for `log` and binary digits for square roots together, and `(expOrder := n)`, `(logTerms := n)` and `(sqrtDigits := n)` set them one at a time. The defaults are 8, 10 and 12.
- `(digits := d)` first tries the digit evaluator of [[N]] and prints $d$ decimal places.
- `set_option cega.maxPrecision n` (256) and `set_option cega.maxRefinementWork n` (4096) cap the precision and the work of a subdivision.
- The tactics [[cega]] and [[cas]] take the box from hypotheses such as `0 ≤ x` and `x ≤ 1`, so the bounds go straight into proofs.

## Examples

### Basic Examples

A polynomial on $[0, 1]$, with its four bounds:

```lean
#cas [enclose x in [0, 1]] (x ^ 2 + x)
```

---

The sine on $[0, 1]$. Decimal endpoints are rounded outward:

```lean
#cas [enclose x in [0, 1]] (sin x)
```

---

A closed expression needs no binding:

```lean
#cas [enclose] (sqrt 2)
```

### Scope

Two variables, each with its own interval:

```lean
#cas [enclose x in [0, 1], y in [0, 1]] (x * y + sin y)
```

---

A rational function and an exponential:

```lean
#cas [enclose x in [0, 1]] (x / (1 + x))
```

```lean
#cas [enclose x in [9 / 10, 11 / 10]] (x * exp (-x))
```

---

A narrow interval gives a narrow enclosure:

```lean
#cas [enclose x in [10, 1001 / 100]] (sin x)
```

---

Absolute values, inverse and hyperbolic functions:

```lean
#cas [enclose x in [-2, 1]] (|x|)
```

```lean
#cas [enclose x in [-1 / 2, 1 / 2]] (arcsin x)
```

```lean
#cas [enclose x in [-5, 5]] (tanh x)
```

### Options

On $[-2, 2]$ the first enclosure of $x/(1+x^2)$ is loose:

```lean
#cas [enclose x in [-2, 2]] (x / (1 + x ^ 2))
```

---

With `(depth := 2)` the box is cut at 0 and at $\pm 1$, the function is monotone on each piece, and the enclosure is its exact range:

```lean
#cas (depth := 2) [enclose x in [-2, 2]] (x / (1 + x ^ 2))
```

---

`(prec := n)` raises the precision of the series and square roots:

```lean
#cas (prec := 16) [enclose] (sqrt 2)
```

```lean
#cas (prec := 40) [enclose x in [0, 1]] (exp x)
```

### Applications

A bound in a proof. `cas` takes the box from the hypotheses and proves the bound by an enclosure, and `cas?` shows the query it ran:

```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 3 := by
  cas?
```

---

`cega [enclose ...]` names the box and the expression itself. Here it proves $x(1-x) \le 1/4$ on $[0, 1]$:

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega [enclose x in [0, 1]] (x * (1 - x))
```

### Properties and Relations

An identity encloses to a point:

```lean
#cas [enclose x in [0, 1]] (sin x ^ 2 + cos x ^ 2)
```

---

[[maximize]] gives the largest value itself, and `enclose` only bounds it:

```lean
#cas [maximize x in [0, 1]] (x * (1 - x))
```

```lean
#cas [enclose x in [0, 1]] (x * (1 - x))
```

---

[[N]] gives digits of a closed expression, and `enclose` gives an interval:

```lean
#cas [N 10] (sqrt 2)
```

### Possible Issues

$1/x$ is unbounded near 0, so no interval holds its values on $[-1, 1]$. Enclose it on a box that leaves out 0, such as $[1/10, 1]$:

```lean error
#cas [enclose x in [-1, 1]] (1 / x)
```

```lean
#cas [enclose x in [1/10, 1]] (1 / x)
```

---

Endpoints are rational literals. For $[0, \pi]$, use a rational interval that contains it, such as $[0, 315/100]$:

```lean error
#cas [enclose x in [0, pi]] (sin x)
```

```lean
#cas [enclose x in [0, 315/100]] (sin x)
```

---

The smaller endpoint comes first:

```lean error
#cas [enclose x in [1, 0]] (x)
```

### Neat Examples

A tiny number is rounded outward to 6 places, and the radius covers the rounding of the center:

```lean
#cas [enclose] (1 / 1000000000000000000000000)
```

---

Three levels of bisection on $\sin x \cos x$:

```lean
#cas (depth := 3) [enclose x in [0, 2]] (sin x * cos x)
```

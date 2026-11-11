+++
id = "limit"
kind = "mode"
title = "limit"
summary = "A limit at a rational point, from one side, or at ±∞, with a theorem about Mathlib’s `Filter.Tendsto`."
forms = ["CAS.Command.casLimitCommand", "CAS.Command.casLimitSideCommand", "CAS.Command.casLimitAtTopCommand", "CAS.Command.casLimitAtBotCommand"]
see_also = ["series", "derive", "sum", "cas"]
tutorials = ["first-hour", "proving"]
+++

::: usage
`#cas [limit ‹x› → ‹a›] ‹e›`
: computes the limit of ‹e› as ‹x› tends to the rational number ‹a›, finite or infinite, and proves it with the filter `𝓝 a`, or `𝓝[≠] a` when ‹e› is a quotient whose denominator vanishes at ‹a›.
`#cas [limit ‹x› → ‹a› from above] ‹e›`
: gives the limit from the right, with the filter `𝓝[>] a`. With `from below` it gives the limit from the left, with `𝓝[<] a`.
`#cas [limit ‹x› → ∞] ‹e›`
: gives the limit as ‹x› tends to $\infty$, with the filter `atTop`.
`#cas [limit ‹x› → -∞] ‹e›`
: gives the limit as ‹x› tends to $-\infty$, with the filter `atBot`.
:::

`limit` computes a limit and proves it as a `Filter.Tendsto` statement, which is how Mathlib states limits. Where the expression is defined, the answer is simple: the limit is its value. The interesting case is a quotient whose denominator vanishes. There SymLean does what you would do by hand with l’Hôpital’s rule. It takes the first derivatives of the numerator and the denominator that don’t vanish, and their values have to be exact rational numbers.

At $\pm\infty$ the expression is rewritten in $t = 1/x$ and expanded at $t = 0$. Expressions with `exp`, `log`, `sqrt`, `atan`, `π` or `e` first go through a comparison of growth rates, and when that comparison proves the limit, the label of the answer says “limit from the dominant term”.

## Details and Options

- At a point where ‹e› is valid, the limit is the value $L$ and the theorem is `Tendsto (fun x ↦ e) (𝓝 a) (𝓝 L)`.
- For a quotient `g / h` with $h(a) = 0$, the theorem is `Tendsto (fun x ↦ g / h) (𝓝[≠] a) (𝓝 L)`. The derivatives of $g$ and $h$ at $a$ must have exact rational values, as those of `sin`, `cos`, `exp`, `atan` and `asin` at 0 and of `log` and `acos` at 1 do.
- At a pole the theorem has `atTop` or `atBot` in place of `𝓝 L`. At a pole of odd order the two sides differ, the answer is `Indeterminate`, and the theorem is the conjunction of the two one-sided limits.
- The point ‹a› is a closed expression with a rational value, built from integers, fractions and decimals by `+`, `-`, `*`, `/` and integer powers, such as `1/10000`, `-1/2` or `0.25`. A function value such as `sqrt 4` is refused, even when its value is rational, and so is `π`.
- ‹e› uses the functions of [[derive]]. The domain checker certifies that ‹e›, or the numerator and the denominator of a quotient, are defined at ‹a›, and the theorem extends this to a neighbourhood.
- There are no options. In a proof, [[cas]] proves these limits as goals, with all six filters.

## Examples

### Basic Examples

The classical one, with the theorem on the punctured neighbourhood of 0:

```lean
#cas [limit x → 0] (sin x / x)
```

---

A rational function at $\infty$. The terms of order 0 in $t = 1/x$ give the limit:

```lean
#cas [limit x → ∞] ((x^2 + 1) / (2*x^2 - 3))
```

---

A one-sided infinite limit:

```lean
#cas [limit x → 0 from above] (1 / x)
```

### Scope

A quotient whose denominator vanishes. The first derivatives give the limit:

```lean
#cas [limit x → 1] ((x^2 - 1) / (x - 1))
```

```lean
#cas [limit x → 0] ((1 - cos x) / x^2)
```

---

Where the expression is defined, the limit is its value. Here the point is close to the edge of the domain of the square root:

```lean
#cas [limit x → 1/10000] (sqrt x)
```

---

At $\infty$, $x \sin(1/x)$ is $\sin t / t$ in $t = 1/x$:

```lean
#cas [limit x → ∞] (x * sin (1 / x))
```

---

An infinite limit at $\infty$. In $t = 1/x$ the expression has a pole of order 2:

```lean
#cas [limit x → ∞] (x^3 / (x + 1))
```

---

Exponentials and arctangents at $\pm\infty$, by the dominant term:

```lean
#cas [limit x → ∞] (x^2 * exp (-x))
```

```lean
#cas [limit x → ∞] (atan x)
```

```lean
#cas [limit x → -∞] (x * exp x)
```

---

A difference of two terms that both grow:

```lean
#cas [limit x → ∞] (sqrt (x^2 + 1) - x)
```

---

At a pole of even order both sides agree. At a pole of odd order they differ, and the answer gives both:

```lean
#cas [limit x → 0] (1 / x^2)
```

```lean
#cas [limit x → 0] (1 / x)
```

### Applications

A limit in a proof. `cas` proves it, and only the three standard axioms are used:

```lean
open Filter Topology in
theorem limit_sinc : Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by
  cas

#print axioms limit_sinc
```

---

A one-sided infinite limit as a goal:

```lean
open Filter Topology in
example : Tendsto (fun x : ℝ ↦ 1 / x) (𝓝[>] 0) atTop := by
  cas
```

### Properties and Relations

The limit of $(e^x - 1 - x)/x^2$ at 0 is the coefficient of $x^2$ in the [[series]] of $e^x$:

```lean
#cas [series x 0 6] (exp x)
```

```lean
#cas [limit x → 0] ((exp x - 1 - x) / x^2)
```

### Possible Issues

The point must be a rational number, $\infty$ or $-\infty$:

```lean error
#cas [limit x → π] (sin x)
```

---

$\sin(1/x)$ is not defined at 0, and it has no limit there. For a quotient whose denominator vanishes, the message asks for a single quotient `g / h`:

```lean error
#cas [limit x → 0] (sin (1 / x))
```

---

Away from 0, $1/(x + x/x)$ is $1/(x + 1)$, but `x / x` is not valid at 0, so the domain checker refuses the denominator:

```lean error
#cas [limit x → 0] (1 / (x + x / x))
```

---

Some limits at $\infty$ are out of reach of both routes, and the message lists why each one stopped:

```lean error
#cas [limit x → ∞] (log (exp x + 1) - x)
```

### Neat Examples

Two terms that grow like $x$, and a difference of $3/2$:

```lean
#cas [limit x → ∞] (sqrt (x^2 + 3 * x) - x)
```

---

The exponential wins over $x^2$, in the numerator and in the denominator:

```lean
#cas [limit x → ∞] ((x^2 + exp x) / (exp x + 1))
```

---

A quotient of logarithms:

```lean
#cas [limit x → ∞] (log (x^2 + 1) / log x)
```

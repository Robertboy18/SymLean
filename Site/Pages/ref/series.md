+++
id = "series"
kind = "mode"
title = "series"
summary = "A Taylor or Laurent expansion at a rational point, with exact coefficients and a little-o remainder theorem."
forms = ["CAS.Command.casSeriesCommand"]
see_also = ["limit", "derive", "sum", "integrate"]
tutorials = ["first-hour"]
+++

::: usage
`#cas [series ‹x› ‹a› ‹n›] ‹e›`
: gives the Taylor polynomial of ‹e› of degree ‹n› at the rational point ‹a›, with exact coefficients, and proves that the remainder is $o((x - a)^n)$. When ‹e› is a quotient whose denominator vanishes at ‹a›, it gives the Laurent series instead.
:::

`series` computes the first terms of an expansion from the derivatives at the expansion point, with exact rational coefficients. The theorem is a little-o statement about Mathlib’s `Asymptotics.IsLittleO`. It is the precise form of what we usually write as “$e = c_0 + c_1 (x - a) + \dots + c_n (x - a)^n + o((x - a)^n)$”.

## Details and Options

- For the printed coefficients $c_k$ the theorem is `(fun x ↦ e - ∑ k ∈ Finset.range (n + 1), c k * (x - a) ^ k) =o[𝓝 a] fun x ↦ (x - a) ^ n`, with the sum written out.
- For a quotient $g/h$ whose denominator vanishes at $a$ to order $m$, the sum runs over the powers from $-m$ to $n$, and the remainder holds on the punctured neighbourhood `𝓝[≠] a`. When the singularity is removable, the answer is a Taylor series again.
- The order ‹n› is at most 12. ‹e› uses the functions of [[derive]] and no other variable.
- The centre ‹a› is a rational literal such as `1/2`, `-1/2` or `1/10000`, or a closed expression in parentheses with a rational value, such as `(1/2 - 1/3)`. A function value such as `(sqrt 4)` is refused, even when it is rational.
- The coefficients are exact, so every function must sit at a point where its value is rational: `sin`, `cos`, `exp`, `atan` and `asin` at 0, `log` and `acos` at 1, and square roots of rational squares.
- There are no options. The tactic [[cas]] does not prove the little-o statement, so a proof takes the printed theorem as a hypothesis.

## Examples

### Basic Examples

The exponential at 0, with the theorem about the remainder:

```lean
#cas [series x 0 6] (exp x)
```

---

A Laurent series. $1/\sin x$ has a pole of order 1 at 0:

```lean
#cas [series x 0 3] (1 / sin x)
```

### Scope

The sine, to order 7:

```lean
#cas [series x 0 7] (sin x)
```

---

The logarithm at 1, where its value is rational:

```lean
#cas [series x 1 4] (log x)
```

---

A composition:

```lean
#cas [series x 0 6] (exp (sin x))
```

---

A negative rational centre:

```lean
#cas [series x -1/2 2] (1 / (1 - x))
```

---

A centre close to the singularity of the square root. The theorem only needs the derivatives at the point:

```lean
#cas [series x 1/10000 2] (sqrt x)
```

---

A pole of order 2:

```lean
#cas [series x 0 2] (1 / sin x ^ 2)
```

---

A pole away from 0. The answer is in powers of $x - 1$:

```lean
#cas [series x 1 2] (1 / (x^2 - 1))
```

---

A removable singularity gives a Taylor series:

```lean
#cas [series x 0 4] (sin x / x)
```

### Applications

The little-o statement in a proof. From the printed theorem for $\sin x$ to order 3, the quotient by $x^3$ tends to 0:

```lean
open Filter Topology in
theorem series_sin_remainder
    (h : (fun x : ℝ ↦ Real.sin x - (x - 1 / 6 * x ^ 3)) =o[𝓝 0] fun x ↦ x ^ 3) :
    Tendsto (fun x : ℝ ↦ (Real.sin x - (x - 1 / 6 * x ^ 3)) / x ^ 3) (𝓝 0) (𝓝 0) :=
  h.tendsto_div_nhds_zero

#print axioms series_sin_remainder
```

### Properties and Relations

The coefficient of $x^2$ in the series of $e^x$ is the limit of $(e^x - 1 - x)/x^2$ at 0, which [[limit]] proves:

```lean
#cas [limit x → 0] ((exp x - 1 - x) / x^2)
```

---

The series of $1/(1 - x)$ at 0 is the geometric series:

```lean
#cas [series x 0 5] (1 / (1 - x))
```

### Possible Issues

The expression must be smooth at the centre. $|x|$ has no derivative at 0:

```lean error
#cas [series x 0 3] (abs x)
```

---

The coefficients must be exact, and the logarithm has a known value at 1, not at 0. The message lists the known values:

```lean error
#cas [series x 0 3] (log x)
```

---

The order is at most 12:

```lean error
#cas [series x 0 13] (sin x)
```

### Neat Examples

The coefficients of $1/(e^x - 1)$ are the Bernoulli numbers divided by factorials:

```lean
#cas [series x 0 3] (1 / (exp x - 1))
```

---

The cotangent:

```lean
#cas [series x 0 3] (cos x / sin x)
```

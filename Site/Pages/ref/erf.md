+++
id = "erf"
kind = "call"
title = "erf"
summary = "Proved decimal enclosures of the error function at a rational point, for SymLean’s `CAS.erf`, defined by the Gaussian integral."
calls = ["erf"]
see_also = ["N", "integrate", "derive", "BesselJ", "enclose"]
guide = "special-functions"
tutorials = ["proving"]
+++

::: usage
`#cas [N ‹d›] (erf ‹q›)`
: proves a decimal enclosure of width at most $10^{-d}$ of $\operatorname{erf} q$ at a rational ‹q›, and prints it.
:::

`erf` gives certified decimals for the error function. The Mathlib we build on doesn’t have an error function, so `erf` is our own `CAS.erf`, defined by the Gaussian integral

$$\operatorname{erf} x = \frac{2}{\sqrt{\pi}} \int_0^x e^{-t^2}\,dt.$$

What you get back is a decimal interval of width at most $10^{-d}$ and a theorem that $\operatorname{erf} q$ lies in it. The call only ever computes enclosures, and for the error function that’s usually what I want anyway: a number I can use in a proof, as accurate as I asked for.

## Details and Options

- ‹q› is a rational number with $|q| \le 10$ and a denominator of at most 1000, and $1 \le d \le 30$.
- The theorem is `a ≤ CAS.erf q ∧ CAS.erf q ≤ b ∧ b - a ≤ 1 / 10 ^ d` for the printed interval $[a, b]$, by `CAS.erfCheck_sound`.
- The kernel checks a partial sum of the Taylor series with a bound on its tail, and an interval for $\sqrt{\pi}$ from Machin’s formula. The Output line says how many terms of the series the check used.
- The call computes enclosures only, so `#cas (erf q)` is refused and points to `#cas [N d] (erf q)`. The library proves the exact value `CAS.erf_zero : CAS.erf 0 = 0`.
- There are no options.

## Examples

### Basic Examples

Ten proved digits of $\operatorname{erf} \tfrac{1}{2}$:

```lean
#cas [N 10] (erf (1/2))
```

### Scope

Thirty digits, the most the call gives:

```lean
#cas [N 30] (erf 1)
```

---

A negative point:

```lean
#cas [N 20] (erf (-3))
```

---

At $q = 10$, the end of the range, the check takes 294 terms of the series, and the enclosure contains 1:

```lean
#cas [N 10] (erf 10)
```

---

At 0 the enclosure is the single point 0, and the report prints it as the exact value:

```lean
#cas [N 5] (erf 0)
```

### Applications

A proof can take an enclosure as a hypothesis, here a coarser one than the printed interval:

```lean
theorem erf_one_pos (h : 21 / 25 ≤ CAS.erf 1 ∧ CAS.erf 1 ≤ 17 / 20) : 0 < CAS.erf 1 := by
  linarith [h.1]

#print axioms erf_one_pos
```

### Properties and Relations

[[integrate]] integrates Gaussians in terms of `erf`, with the theorem for every interval $[a, b]$:

```lean
#cas [integrate x] (exp (-x ^ 2))
```

---

[[derive]] differentiates `erf`, with $\operatorname{erf}'(x) = \tfrac{2}{\sqrt{\pi}}\, e^{-x^2}$:

```lean
#cas [derive x] (erf x)
```

### Possible Issues

`#cas` gives no exact value of `erf`, and the message points to `[N d]`:

```lean error
#cas (erf 1)
```

---

The point is a rational with $|q| \le 10$ and a denominator of at most 1000. The series converges slowly far from 0, and the bound keeps the kernel’s partial sum short:

```lean error
#cas [N 10] (erf 11)
```

---

The call gives at most 30 digits:

```lean error
#cas [N 31] (erf 1)
```

+++
id = "BesselJ"
kind = "call"
title = "BesselJ"
summary = "Proved decimal enclosures of Mathlib’s Bessel function `Complex.besselJ` at an integer order and a rational point."
calls = ["BesselJ"]
see_also = ["erf", "N", "enclose"]
guide = "special-functions"
tutorials = ["proving"]
+++

::: usage
`#cas [N ‹d›] (BesselJ ‹n› ‹q›)`
: proves a decimal enclosure of width at most $10^{-d}$ of the Bessel function $J_n(q)$ at an integer order ‹n› and a rational ‹q›, and prints it.
:::

`BesselJ` gives you digits of the Bessel function of the first kind, and a proof that they are right. The function is Mathlib’s `Complex.besselJ`. The answer is a decimal interval of width at most $10^{-d}$, with a theorem that $J_n(q)$ is a real number inside it. The call computes enclosures only, so you always say how many digits you want with `[N d]`.

## Details and Options

- ‹n› is an integer with $|n| \le 50$, ‹q› a rational with $|q| \le 50$ and a denominator of at most 1000, and $1 \le d \le 30$.
- The theorem is `∃ r : ℝ, Complex.besselJ n q = r ∧ a ≤ r ∧ r ≤ b ∧ b - a ≤ 1 / 10 ^ d` for the printed interval $[a, b]$, so the width is part of the theorem.
- The kernel checks a partial sum of the power series with a bound on its tail. The Output line says how many terms of the series the check used.
- At $q = 0$ the enclosure is a point and the output is the exact value: $J_0(0) = 1$, and $J_n(0) = 0$ otherwise. A negative order uses $J_{-n} = (-1)^n J_n$, Mathlib’s `Complex.besselJ_neg_int`.
- The call computes enclosures only, so `#cas (BesselJ n q)` is refused and points to `#cas [N d] (BesselJ n q)`. Mathlib’s `Complex.besselJ_zero` gives the exact value at 0.
- There are no options.

## Examples

### Basic Examples

Ten proved digits of $J_0(1)$:

```lean
#cas [N 10] (BesselJ 0 1)
```

### Scope

A higher order at a larger point:

```lean
#cas [N 10] (BesselJ 2 10)
```

---

A negative rational point:

```lean
#cas [N 20] (BesselJ 1 (-7/3))
```

---

At 0 the enclosure is a point, and the report prints the exact value $J_0(0) = 1$:

```lean
#cas [N 5] (BesselJ 0 0)
```

### Applications

A proof can take an enclosure as a hypothesis, here a coarser one than the printed interval, and show that $J_0(1) > 0$:

```lean
theorem besselJ_zero_one_pos
    (h : ∃ r : ℝ, Complex.besselJ (0 : ℂ) (1 : ℂ) = r ∧ 3 / 4 ≤ r ∧ r ≤ 4 / 5) :
    ∃ r : ℝ, Complex.besselJ (0 : ℂ) (1 : ℂ) = r ∧ 0 < r := by
  obtain ⟨r, hr, hlo, -⟩ := h
  exact ⟨r, hr, by linarith⟩

#print axioms besselJ_zero_one_pos
```

### Properties and Relations

A negative order uses $J_{-n} = (-1)^n J_n$, so $J_{-2}(\tfrac{1}{2}) = J_2(\tfrac{1}{2})$ is positive and $J_{-3}(\tfrac{1}{2}) = -J_3(\tfrac{1}{2})$ is negative:

```lean
#cas [N 5] (BesselJ (-2) (1/2))
```

```lean
#cas [N 5] (BesselJ (-3) (1/2))
```

### Possible Issues

`#cas` gives no exact value of `BesselJ`, and the message points to `[N d]`:

```lean error
#cas (BesselJ 0 1)
```

---

Mathlib defines `Complex.besselJ` at every complex order, but the series check is written for integer orders:

```lean error
#cas [N 5] (BesselJ (1/2) 1)
```

---

The point is a rational with $|q| \le 50$ and a denominator of at most 1000:

```lean error
#cas [N 5] (BesselJ 0 51)
```

### Neat Examples

Thirty decimals of $J_0(50)$, at the end of the range, from 97 terms of the series:

```lean
#cas [N 30] (BesselJ 0 50)
```

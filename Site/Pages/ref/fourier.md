+++
id = "fourier"
kind = "mode"
title = "fourier"
summary = "The Fourier coefficients of a function on [-π, π] as exact functions of n, with a theorem about the integrals."
forms = ["CAS.Command.casFourierCommand"]
see_also = ["fourierSin", "fourierCos", "fourierTransform", "integrate", "nintegrate"]
tutorials = ["proving"]
+++

::: usage
`#cas [fourier ‹x› ‹n›] ‹f›`
: gives the Fourier coefficients $a_0$, $a_n$ and $b_n$ of ‹f› on $[-\pi, \pi]$ as exact functions of ‹n› for $n \ge 1$, and proves the integrals.
:::

`fourier` computes the Fourier coefficients of a concrete function and proves their integral formulas. The theorem is about Mathlib’s interval integrals over $[-\pi, \pi]$, with one statement for $a_0$ and one each for $a_n$ and $b_n$ that holds at every $n \ge 1$. So you get the coefficients as functions of $n$, not a table of the first few.

The method is the one you would use by hand. The function is split into terms $c\,x^j e^{ax} \cos kx$ and $c\,x^j e^{ax} \sin kx$, and each one is integrated by parts. The case I always have to be careful with by hand is resonance. When a term has a frequency $k \ge 1$ and no exponential, the coefficients at $n = k$ differ from the general formula, and the report gives them by an `if` instead of leaving a formula that divides by zero there.

## Details and Options

- For the printed coefficients, the theorem is `1 / Real.pi * ∫ x in -Real.pi..Real.pi, f = a₀` and, for every `n : ℕ` with `0 < n`, `1 / Real.pi * ∫ x in -Real.pi..Real.pi, f * Real.cos (n * x) = aₙ` and the same with `Real.sin` and `bₙ`. They are the coefficients of the series $a_0/2 + \sum_{n \ge 1} (a_n \cos nx + b_n \sin nx)$.
- ‹f› is a sum of products of polynomials in ‹x›, exponentials `exp (a * x)` with rational `a`, and sines and cosines with integer frequencies, such as `x * sin x`, `x ^ 2 * exp x` or `sin x ^ 3 * cos (2 * x)`.
- When a term `c * x ^ j * cos (k * x)` or `c * x ^ j * sin (k * x)` has `k ≥ 1`, the coefficients at `n = k` are given by an `if`, unless the formula for general `n` covers them.
- When the proof of the coefficients fails, for instance at the heartbeat limit, the command is refused.
- There are no options. In a proof, [[cas]] proves a single coefficient, as under Applications.

## Examples

### Basic Examples

The Fourier coefficients of $x$, with the theorem for every $n \ge 1$:

```lean
#cas [fourier x n] (x)
```

---

An even function has only cosine terms:

```lean
#cas [fourier x n] (x^2)
```

### Scope

An exponential. The coefficients contain $\sinh \pi$:

```lean
#cas [fourier x n] (exp x)
```

---

A product with $\sin x$. The general formula for $a_n$ has a pole at $n = 1$, and $a_1$ comes out separately:

```lean
#cas [fourier x n] (x * sin x)
```

---

With $\cos 2x$, the special case is $n = 2$:

```lean
#cas [fourier x n] (x * cos (2 * x))
```

---

With an exponential factor, the general formula covers every $n$:

```lean
#cas [fourier x n] (exp x * sin (2 * x))
```

---

A polynomial and two trigonometric terms:

```lean
#cas [fourier x n] (x^3 - 2*x + 3*cos (2*x) + sin x)
```

---

Powers and products of sines and cosines are finite trigonometric sums. Here $\sin^3 x = \tfrac{3}{4} \sin x - \tfrac{1}{4} \sin 3x$:

```lean
#cas [fourier x n] (sin x ^ 3)
```

And $\cos^2 x = \tfrac{1}{2} + \tfrac{1}{2} \cos 2x$ and $\sin 2x \cos 3x = \tfrac{1}{2} (\sin 5x - \sin x)$:

```lean
#cas [fourier x n] (cos x ^ 2 + sin (2 * x) * cos (3 * x))
```

### Applications

The coefficient $b_1$ of $x$ in a proof. `cas` proves it, and only the three standard axioms are used:

```lean
theorem fourier_b_one : 1 / Real.pi * ∫ x in -Real.pi..Real.pi, x * Real.sin x = 2 := by
  cas

#print axioms fourier_b_one
```

### Properties and Relations

Parseval’s identity for $x$ says that $\frac{1}{\pi} \int_{-\pi}^{\pi} x^2\,dx$, which is $a_0 = 2\pi^2/3$ of $x^2$ above, equals $\sum_{n \ge 1} b_n^2 = 4 \sum_{n \ge 1} 1/n^2$. So $\sum_{n \ge 1} 1/n^2 = \pi^2/6$, the Basel sum that [[sum]] proves:

```lean
#cas [sum k 1 ∞] (1/k^2)
```

### Possible Issues

Other functions are refused. [[nintegrate]] encloses a single coefficient of them numerically:

```lean error
#cas [fourier x n] (exp (x ^ 2))
```

---

On $[-\pi, \pi]$ the frequencies are integers, as in `sin (k * x)`:

```lean error
#cas [fourier x n] (sin (x / 2))
```

### Neat Examples

The power $\sin^{10} x$ is a cosine polynomial with six coefficients:

```lean
#cas [fourier x n] (sin x ^ 10)
```

---

With a factor $x$, the even $n \le 10$ are special cases of the sine coefficients:

```lean
#cas [fourier x n] (x * sin x ^ 10)
```

+++
id = "fourierSin"
kind = "mode"
title = "fourierSin"
summary = "The coefficients of the sine series on [0, L] as exact functions of n, with a theorem about the integrals."
forms = ["CAS.Command.casFourierSinCommand"]
see_also = ["fourierCos", "fourier", "fourierTransform", "integrate"]
tutorials = ["proving"]
+++

::: usage
`#cas [fourierSin ‹x› ‹n› ‹L›] ‹f›`
: gives the coefficients $b_n$ of the sine series of ‹f› on the interval from 0 to ‹L›, as exact functions of ‹n› for $n \ge 1$, and proves the integrals.
:::

The sine series on $[0,L]$ is the one that comes up for a vibrating string with fixed ends, and `fourierSin` computes its coefficients. The series is $\sum_{n \ge 1} b_n \sin(n\pi x/L)$, and the theorem is about Mathlib’s interval integrals over $[0, L]$, one for every $n \ge 1$.

Each term $c\,x^j e^{ax}$ of ‹f› is integrated by parts, and $\cos n\pi = (-1)^n$ gives the factors $(-1)^n$ you see in the result. For the cosine series on the same interval, use [[fourierCos]], and for the full series on $[-\pi, \pi]$, use [[fourier]].

## Details and Options

- For the printed `bₙ`, the theorem is that for every `n : ℕ` with `0 < n`, `2 / L * ∫ x in 0..L, f * Real.sin (n * Real.pi * x / L) = bₙ`. It is printed in simplified form, such as `Real.sin (n * x)` for $L = \pi$.
- ‹f› is a sum of terms `c * x ^ j * exp (a * x)` with rational `a`, and `π` may appear in the coefficients `c`, as in `x * (pi - x)`. Sines, cosines and other functions are refused.
- ‹L› is a positive rational number or a positive rational multiple of `π`, such as `2 * pi / 3`.
- When the proof of the coefficients fails, the command is refused.
- There are no options. In a proof, [[cas]] proves the integral behind a single coefficient, as under Applications.

## Examples

### Basic Examples

The sine series of $x(\pi - x)$ on $[0, \pi]$, with the theorem for every $n \ge 1$. The coefficients for even $n$ are 0:

```lean
#cas [fourierSin x n pi] (x * (pi - x))
```

---

The sine series of $x$ on $[0, 1]$:

```lean
#cas [fourierSin x n 1] (x)
```

### Scope

An exponential. The coefficients contain $e^{\pi}$:

```lean
#cas [fourierSin x n pi] (exp x)
```

### Applications

The integral behind $b_1 = 8/\pi$ of $x(\pi - x)$, in a proof. `cas` proves it, and only the three standard axioms are used:

```lean
theorem fourierSin_b_one : ∫ x in (0 : ℝ)..Real.pi, x * (Real.pi - x) * Real.sin x = 4 := by
  cas

#print axioms fourierSin_b_one
```

### Properties and Relations

The sine series on $[0, \pi]$ is the Fourier series on $[-\pi, \pi]$ of the odd extension of ‹f›. For the odd function $x$, the sine series has the coefficients $b_n$ that [[fourier]] gives, $\pi$ times those on $[0, 1]$ above:

```lean
#cas [fourier x n] (x)
```

---

The cosine series of $x(\pi - x)$ decays more slowly than its sine series. The even extension to $[-\pi, \pi]$ has corners, and $a_n$ is of order $1/n^2$. The odd extension has a continuous derivative, and $b_n$ above is of order $1/n^3$:

```lean
#cas [fourierCos x n pi] (x * (pi - x))
```

### Possible Issues

The length must be positive:

```lean error
#cas [fourierSin x n 0] (x)
```

---

Other functions are refused on $[0, L]$, here $e^{x^2}$. [[fourier]] takes sines and cosines with integer frequencies on $[-\pi, \pi]$:

```lean error
#cas [fourierSin x n pi] (exp (x ^ 2))
```

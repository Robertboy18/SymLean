+++
id = "fourierCos"
kind = "mode"
title = "fourierCos"
summary = "The coefficients of the cosine series on [0, L] as exact functions of n, with a theorem about the integrals."
forms = ["CAS.Command.casFourierCosCommand"]
see_also = ["fourierSin", "fourier", "fourierTransform", "integrate"]
tutorials = ["proving"]
+++

::: usage
`#cas [fourierCos ‹x› ‹n› ‹L›] ‹f›`
: gives the coefficients $a_0$ and $a_n$ of the cosine series of ‹f› on the interval from 0 to ‹L›, as exact functions of ‹n› for $n \ge 1$, and proves the integrals.
:::

The cosine series on $[0,L]$ is the one that comes up for heat flow in a rod with insulated ends, and `fourierCos` computes its coefficients. The series is $a_0/2 + \sum_{n \ge 1} a_n \cos(n\pi x/L)$. The theorem is about Mathlib’s interval integrals over $[0, L]$, with one statement for $a_0$ and one for $a_n$ that holds at every $n \ge 1$.

Each term $c\,x^j e^{ax}$ of ‹f› is integrated by parts, and then $\sin n\pi = 0$ and $\cos n\pi = (-1)^n$ turn the result into a closed form. For the sine series on the same interval, use [[fourierSin]], and for the full series on $[-\pi, \pi]$, use [[fourier]].

## Details and Options

- For the printed coefficients, the theorem is `2 / L * ∫ x in 0..L, f = a₀` and, for every `n : ℕ` with `0 < n`, `2 / L * ∫ x in 0..L, f * Real.cos (n * Real.pi * x / L) = aₙ`. It is printed in simplified form, such as `2 * ∫ x in 0..1, f` for $L = 1$.
- ‹f› is a sum of terms `c * x ^ j * exp (a * x)` with rational `a`, and `π` may appear in the coefficients `c`, as in `x * (pi - x)`. Sines, cosines and other functions are refused.
- ‹L› is a positive rational number or a positive rational multiple of `π`, such as `2 * pi / 3`.
- When the proof of the coefficients fails, the command is refused.
- There are no options. In a proof, [[cas]] proves the integral behind a single coefficient, as under Applications.

## Examples

### Basic Examples

The cosine series of $x$ on $[0, 1]$, with the theorem for every $n \ge 1$:

```lean
#cas [fourierCos x n 1] (x)
```

---

On $[0, \pi]$, with $\pi$ in the function:

```lean
#cas [fourierCos x n pi] (x * (pi - x))
```

### Scope

Any positive rational length. On $[0, 2]$ the frequencies are $n\pi/2$:

```lean
#cas [fourierCos x n 2] (x ^ 2)
```

### Applications

The integral behind $a_1 = -4/\pi^2$ of $x$ on $[0, 1]$, in a proof. `cas` proves it, and only the three standard axioms are used:

```lean
theorem fourierCos_a_one :
    ∫ x in (0 : ℝ)..1, x * Real.cos (Real.pi * x) = -(2 / Real.pi ^ 2) := by
  cas

#print axioms fourierCos_a_one
```

### Properties and Relations

The cosine series on $[0, \pi]$ is the Fourier series on $[-\pi, \pi]$ of the even extension of ‹f›. For the even function $x^2$, the cosine series has the coefficients that [[fourier]] gives, $\pi^2/4$ times those on $[0, 2]$ above:

```lean
#cas [fourier x n] (x^2)
```

---

The sine series of $x(\pi - x)$ decays faster than its cosine series. The odd extension to $[-\pi, \pi]$ has a continuous derivative, and $b_n$ is of order $1/n^3$. The even extension has corners, and $a_n$ above is of order $1/n^2$:

```lean
#cas [fourierSin x n pi] (x * (pi - x))
```

### Possible Issues

Sines and cosines are refused on $[0, L]$. [[fourier]] takes them on $[-\pi, \pi]$:

```lean error
#cas [fourierCos x n pi] (sin x)
```

---

The length is a positive rational number or a rational multiple of $\pi$, such as `2 * pi / 3`:

```lean error
#cas [fourierCos x n (sqrt 2)] (x)
```

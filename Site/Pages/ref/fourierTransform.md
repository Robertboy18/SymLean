+++
id = "fourierTransform"
kind = "mode"
title = "fourierTransform"
summary = "The Fourier transform of a Gaussian in Mathlib’s convention, with a theorem for every frequency."
forms = ["CAS.Command.casFourierTransformCommand"]
see_also = ["laplace", "fourier", "integrate", "erf"]
tutorials = ["proving"]
+++

::: usage
`#cas [fourierTransform ‹x› ‹ξ›] ‹f›`
: gives the Fourier transform of the Gaussian ‹f› as a function of ‹ξ›, in Mathlib’s convention, and proves it for every real ‹ξ›.
:::

`fourierTransform` computes the transform of a Gaussian $c\,e^{-\alpha x^2 + \beta x + \gamma}$. It covers those and nothing else. Conventions for the Fourier transform differ by factors of $2\pi$ from one book to the next, and the first thing to know is which one you are getting. Here it is Mathlib’s, $\mathcal{F} f(\xi) = \int_{\mathbb{R}} e^{-2\pi i x \xi} f(x)\,dx$, the one Mathematica uses with `FourierParameters -> {0, -2 Pi}`. The theorem is about `FourierTransform.fourier` of ‹f› as a complex function, for every real $\xi$.

The computation is the one from a first course, completing the square, which gives $c \sqrt{\pi/\alpha}\, e^{\beta^2/(4\alpha) + \gamma - \pi^2\xi^2/\alpha}$, times the phase $e^{-i\pi\beta\xi/\alpha}$ when $\beta \ne 0$.

## Details and Options

- For the printed `F`, the theorem is `∀ ξ : ℝ, FourierTransform.fourier (fun x : ℝ ↦ (f : ℂ)) ξ = F`, with ‹f› as written. In Mathlib, `𝓕 f ξ = ∫ x, exp (-2 * π * I * x * ξ) * f x`.
- ‹f› is `c * exp (-α * x ^ 2 + β * x + γ)` with rational `c ≠ 0`, `α > 0`, `β` and `γ`. The exponent may be written in any form, such as `-(x - 1) ^ 2`, as long as it is a polynomial of degree 2 in ‹x›.
- The transform is `c * √(π / α) * exp (β ^ 2 / (4 * α) + γ - π ^ 2 * ξ ^ 2 / α)` times the phase `exp (-(π * β * ξ / α) * I)`, which is left out when `β = 0`. With `α = a / b` in lowest terms, the root is printed `sqrt(b*pi/a)`.
- Parameters, `π` among them, are refused, and so are products with other functions. The command is also refused inside a section with `variable`s.
- There are no options. A proof can take the printed theorem as a hypothesis and evaluate it, as under Applications.

## Examples

### Basic Examples

The transform of $e^{-x^2}$, with the theorem for every real $\xi$:

```lean
#cas [fourierTransform x ξ] (exp (-x ^ 2))
```

---

A linear term in the exponent gives a phase, and completing the square gives the factor $e^1$:

```lean
#cas [fourierTransform x ξ] (3 * exp (-(x ^ 2) + 2 * x))
```

### Scope

Rational $\alpha$, $\beta$ and $\gamma$, and a negative coefficient. For $\alpha = 3/2$ the root is printed `sqrt(2*pi/3)`:

```lean
#cas [fourierTransform x ξ] (-2 * exp (-(3 / 2) * x ^ 2 - x / 3 + 1))
```

---

For $\alpha = 5/7$ the root is `sqrt(7*pi/5)`, and the coefficient `-1 *` comes out as a sign:

```lean
#cas [fourierTransform x ξ] (-1 * exp (-(5 / 7) * x ^ 2 + 2 * x - 1))
```

### Applications

The printed theorem as a hypothesis in a proof, evaluated at $\xi = 0$. Only the three standard axioms are used:

```lean
theorem fourierTransform_at_zero
    (h : ∀ ξ : ℝ, FourierTransform.fourier (fun x : ℝ ↦ ((Real.exp (-x ^ 2) : ℝ) : ℂ)) ξ =
      ((√Real.pi * Real.exp (-(Real.pi ^ 2 * ξ ^ 2)) : ℝ) : ℂ)) :
    FourierTransform.fourier (fun x : ℝ ↦ ((Real.exp (-x ^ 2) : ℝ) : ℂ)) 0 = (√Real.pi : ℂ) := by
  rw [h 0]
  simp

#print axioms fourierTransform_at_zero
```

### Properties and Relations

Shifting $f$ by 1 multiplies the transform by the phase $e^{-2\pi i\xi}$. Compare the transform of $e^{-x^2}$ under Basic Examples:

```lean
#cas [fourierTransform x ξ] (exp (-(x - 1) ^ 2))
```

---

Reflecting $f$ in $x = 0$ reflects the transform. These two Gaussians are mirror images, and their phases are conjugate:

```lean
#cas [fourierTransform x ξ] (exp (-(x ^ 2) / 2 + x / 2))
```

```lean
#cas [fourierTransform x ξ] (exp (-(x ^ 2) / 2 - x / 2))
```

---

A narrower Gaussian has a wider transform. For $\alpha = 3$ it is $\sqrt{\pi/3}\, e^{-\pi^2\xi^2/3}$, here with a sign:

```lean
#cas [fourierTransform x ξ] (-exp (-3 * x ^ 2))
```

---

At $\xi = 0$ the transform is the integral of $f$ over $\mathbb{R}$. An antiderivative of $e^{-x^2}$ is $\frac{\sqrt\pi}{2} \operatorname{erf} x$, with [[erf]], and $\operatorname{erf} x \to \pm 1$ as $x \to \pm\infty$, so the integral is $\sqrt{\pi}$:

```lean
#cas [integrate x] (exp (-x ^ 2))
```

### Possible Issues

The coefficients are rational, so `π` in the exponent is refused. Mathlib’s theorem `fourier_gaussian_pi` gives the transform of `exp (-π * b * x ^ 2)`:

```lean error
#cas [fourierTransform x ξ] (exp (-pi * x ^ 2))
```

---

The Gaussian must decay. $e^{x^2}$ is not integrable, and the input is refused:

```lean error
#cas [fourierTransform x ξ] (exp (x ^ 2))
```

---

A product with another function is refused, here with $\cos x$:

```lean error
#cas [fourierTransform x ξ] (exp (-x ^ 2) * cos x)
```

---

The two variables must be different:

```lean error
#cas [fourierTransform x x] (exp (-x ^ 2))
```

### Neat Examples

The function $e^{-x^2/2}/2$ is $\sqrt{2\pi}/2$ times the density of the standard normal distribution. Without that factor, the transform is $e^{-2\pi^2\xi^2}$, the characteristic function $e^{-t^2/2}$ of the distribution at $t = 2\pi\xi$:

```lean
#cas [fourierTransform x ξ] (exp (-(x ^ 2) / 2) / 2)
```

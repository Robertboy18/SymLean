+++
id = "laplace"
kind = "mode"
title = "laplace"
summary = "The Laplace transform of a sum of exponential, trigonometric and hyperbolic terms, with a theorem about the integral."
forms = ["CAS.Command.casLaplaceCommand"]
see_also = ["inverseLaplace", "dsolve", "integrate", "fourierTransform", "gamma"]
tutorials = ["proving"]
+++

::: usage
`#cas [laplace ‹t› ‹s›] ‹f›`
: gives the Laplace transform of ‹f›, a sum of polynomial, exponential, trigonometric and hyperbolic terms in ‹t›, as a rational function of ‹s›, and proves it for every ‹s› above a bound.
:::

`laplace` gives the transform of a concrete function, together with a proof that the integral converges and has that value. The theorem is about Mathlib’s integral over `Set.Ioi 0`, with the integrand exactly as you wrote it.

Each term $c\,t^n e^{at} g(bt)$ has a transform in closed form, and the transform of a sum is the sum of the transforms. The bound on $s$ is printed as the domain. It is enough for convergence, though not always the smallest such bound. To go back from a rational function of $s$, use [[inverseLaplace]].

## Details and Options

- For the printed transform `F` and the bound σ of the domain, the theorem is `∀ s : ℝ, σ < s → IntegrableOn (fun t ↦ Real.exp (-(s * t)) * f) (Set.Ioi 0) ∧ ∫ t in Set.Ioi 0, Real.exp (-(s * t)) * f = F`.
- σ is the largest bound of the terms: $a$ for a term with `exp (a * t)`, `cos` or `sin`, and $a + |b|$ for a term with `cosh (b * t)` or `sinh (b * t)`. It is enough for convergence, and not always the smallest such bound.
- ‹f› is a sum of at most 8 terms `c * t ^ n * exp (a * t) * g (b * t)` with `g` one of `cos`, `sin`, `cosh` and `sinh`, or without `g`, with rational `a`, `c` and `b ≠ 0`, and $n \le 8$.
- Parameters, `tanh` and other functions are refused, and so is a product of two of the functions `g`. The command is also refused inside a section with `variable`s.
- There are no options. In a proof, [[cas]] proves an improper integral such as the transform of 1, as under Applications.

## Examples

### Basic Examples

The transform of $t \sin 2t$, with the theorem for every $s > 0$:

```lean
#cas [laplace t s] (t * sin (2 * t))
```

---

A sum is transformed term by term, and the bound on $s$ is the largest bound of its terms:

```lean
#cas [laplace t s] (3 * t ^ 2 * exp (2 * t) + cos (5 * t))
```

### Scope

A constant:

```lean
#cas [laplace t s] 1
```

---

A decaying exponential and a power of $t$:

```lean
#cas [laplace t s] (exp (-t) - 2 * t ^ 3)
```

---

A power, an exponential and a cosine in one term. The factor $e^{t/2}$ shifts the transform to $s - 1/2$:

```lean
#cas [laplace t s] (t ^ 2 * exp (t / 2) * cos (3 * t))
```

---

A negative rate and a negative frequency. The bound on $s$ is $-3/2$:

```lean
#cas [laplace t s] (exp (-(3 / 2) * t) * sin (-2 * t))
```

---

The hyperbolic functions. For `cosh (b * t)` and `sinh (b * t)` the bound is $a + |b|$:

```lean
#cas [laplace t s] (cosh (3 * t))
```

```lean
#cas [laplace t s] (exp (2 * t) * sinh t)
```

### Applications

The transform of 1 in a proof. `cas` proves the integral for $s > 0$, and only the three standard axioms are used:

```lean
theorem laplace_one (s : ℝ) (hs : 0 < s) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s * t)) * 1 = 1 / s := by
  cas

#print axioms laplace_one
```

### Properties and Relations

The transform is linear. Written with exponentials, $\sinh 3t = (e^{3t} - e^{-3t})/2$ has the transform $\left(\frac{1}{s - 3} - \frac{1}{s + 3}\right)/2 = 3/(s^2 - 9)$:

```lean
#cas [laplace t s] ((exp (3 * t) - exp (-(3 * t))) / 2)
```

---

[[inverseLaplace]] goes back. The transform of $t^2 e^t/2$ is $1/(s - 1)^3$:

```lean
#cas [inverseLaplace s t] (1 / (s - 1) ^ 3)
```

### Possible Issues

A product of two of the functions `cos`, `sin`, `cosh` and `sinh` is not one term. Write it as a sum first, here `(exp t * cos t + exp (-t) * cos t) / 2`:

```lean error
#cas [laplace t s] (cosh t * cos t)
```

---

The integral of $e^{-st} e^{t^2}$ diverges for every $s$, and the input is refused:

```lean error
#cas [laplace t s] (exp (t ^ 2))
```

---

Parameters are refused. The rates, frequencies and coefficients are rational numbers:

```lean error
#cas [laplace t s] (exp (a * t))
```

---

`tanh` is not one of the functions:

```lean error
#cas [laplace t s] (tanh t)
```

---

Powers of $t$ go up to 8. The transform of $t^n$ is $n!/s^{n+1}$:

```lean error
#cas [laplace t s] (t ^ 9)
```

---

At most 8 terms:

```lean error
#cas [laplace t s] (1 + t + t ^ 2 + t ^ 3 + t ^ 4 + t ^ 5 + t ^ 6 + t ^ 7 + t ^ 8)
```

---

The two variables must be different:

```lean error
#cas [laplace t t] (exp t)
```

### Neat Examples

Other names for the variables. The bound is $p > -1$, and at $p = 0$ the integral is $\Gamma(9) = 8! = 40320$:

```lean
#cas [laplace x p] (x ^ 8 * exp (-x))
```

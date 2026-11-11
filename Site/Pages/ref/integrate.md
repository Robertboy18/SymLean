+++
id = "integrate"
kind = "mode"
title = "integrate"
summary = "An antiderivative or a definite integral, checked by differentiation, with a theorem about Mathlib’s interval integral."
forms = ["CAS.Command.casIntegralCommand", "CAS.Command.casUnivariateIntegralCommand", "CAS.Command.casDefiniteIntegralCommand"]
see_also = ["derive", "nintegrate", "cas-integrate-primitive", "apart", "laplace", "cas"]
tutorials = ["first-hour", "proving"]
+++

::: usage
`#cas [integrate ‹x›] ‹e›`
: finds an antiderivative $F$ of ‹e› in ‹x›, checks it by differentiation, and proves $\int_a^b e \, dx = F(b) - F(a)$ on every interval where the printed conditions hold. Every other variable is a parameter.
`#cas [integrate] ‹e›`
: integrates ‹e› in its only variable, or a function `fun ‹x› ↦ ‹e›` in its parameter.
`#cas [integrate ‹x› in [‹a›, ‹b›]] ‹e›`
: gives the integral of ‹e› from ‹a› to ‹b›, where an endpoint may be `∞` or `-∞`, with a theorem that states its value.
:::

`integrate` searches for an antiderivative and proves the integral formula that goes with it. Finding an antiderivative is a search, and searches go wrong, so SymLean differentiates every candidate and prints it only after its derivative matches the integrand. Differentiation is the easy direction, and that asymmetry is what makes the answer checkable.

The theorem is the fundamental theorem of calculus for Mathlib’s interval integral `∫ x in a..b`, with the printed conditions as a hypothesis on the whole interval. I would read those conditions before the formula. Conditions such as $x > 0$ or $\log x \ne 0$ are part of the answer, because they say on which intervals the formula holds.

## Details and Options

- For the printed antiderivative $F$ and conditions $c_1, \dots, c_k$ the theorem is $\forall a\, b,\; (\forall x \in [a, b],\; c_1 \wedge \dots \wedge c_k) \to \int_a^b e \, dx = F(b) - F(a)$, stated with `Set.uIcc a b`, so the endpoints may come in either order. It holds for every value of the parameters, and the endpoints get other names when a variable is called `a` or `b`.
- ‹e› uses the functions of [[derive]]. The search covers polynomials and a table of elementary antiderivatives, substitution, rational functions, integration by parts, polynomials times exponentials, sines and cosines, and rational functions of $\sin x$ and $\cos x$. Gaussians $c\, e^{-\alpha x^2 + \beta x + \gamma}$ are tried first and give the error function [[erf]].
- The search is bounded. When no candidate passes the derivative check, the command stops with an error and proves nothing.
- Without the optional Hex library, a rational function is refused when its denominator keeps a factor of degree three or more after the powers of $x$ are split off. With `import CASHex.Factor` the denominator is factored over $\mathbb{Q}$.
- The definite form gives $F(b) - F(a)$ for the antiderivative that the search finds, without the Gaussian step. At an endpoint `∞` or `-∞` it uses the limit of $F$, and the theorem says that the integrand is integrable over `Set.Ioi a`, `Set.Iic b` or the whole line and that its integral there is the value.
- `set_option cas.suggest true` adds the theorem as an `example` you can paste in place of the command. `set_option cas.verbose true` adds the tree of differentiation rules that checked the antiderivative.
- The tactic [[cas]] proves `HasDerivAt` goals, definite integrals `∫ x in a..b, e = v`, improper integrals, and improper integrals with their integrability, `IntegrableOn (fun x ↦ e) D ∧ ∫ x in D, e = v`. When you already have a primitive, [[cas-integrate-primitive]] checks it.

## Examples

### Basic Examples

A rational function, by partial fractions:

```lean
#cas [integrate x] (1/(x^3 + x))
```

---

A polynomial times an exponential:

```lean
#cas [integrate x] (x * exp x)
```

---

A definite integral, $\int_0^1 x e^x \, dx$:

```lean
#cas [integrate x in [0, 1]] (x * exp x)
```

### Scope

A substitution. The logarithm in the answer needs $\log x \ne 0$, and the theorem has it as a hypothesis:

```lean
#cas [integrate x] (1 / (x * log x))
```

---

An inverse sine, with the conditions of the square root:

```lean
#cas [integrate x] (1 / sqrt (1 - x ^ 2))
```

---

Powers of sines and cosines:

```lean
#cas [integrate x] (sin x ^ 3 * cos x ^ 2)
```

---

A rational function of $\cos x$:

```lean
#cas [integrate x] (1 / (5 + 3 * cos x))
```

---

Parameters are allowed, and their conditions become hypotheses, here $a^2 + n^2 \ne 0$:

```lean
#cas [integrate x] (exp (a * x) * sin (n * x))
```

---

A Gaussian gives the error function. Without a name in brackets, the only variable is used:

```lean
#cas [integrate] (exp (-(t - 1) ^ 2))
```

---

A function is integrated in its parameter:

```lean
#cas [integrate] (fun x : ℝ ↦ 2)
```

---

A definite integral over $[0, \pi]$, and one over $[0, \infty)$, where the theorem states integrability on `Set.Ioi 0` with the value:

```lean
#cas [integrate x in [0, π]] (sin x ^ 2)
```

```lean
#cas [integrate x in [0, ∞]] (exp (-x))
```

### Options

With `cas.suggest`, the report ends with the theorem as an `example`, ready to paste:

```lean
set_option cas.suggest true in
#cas [integrate x] (x * exp x)
```

---

Here it is pasted, and `cas` proves it:

```lean
example (a b : ℝ) :
    ∫ (x : ℝ) in a..b, x * Real.exp x = Real.exp b * (b - 1) - Real.exp a * (a - 1) := by
  cas
```

### Applications

A definite integral in a proof. The tactic `cas` proves it, and only the three standard axioms are used:

```lean
theorem integrate_x_exp : ∫ x in (0 : ℝ)..1, x * Real.exp x = 1 := by
  cas

#print axioms integrate_x_exp
```

---

A primitive I found by hand, checked by [[cas-integrate-primitive]] on an interval that avoids $0$:

```lean
example (a b : ℝ) (h : ∀ t ∈ Set.uIcc a b, t ≠ 0) :
    (∫ t in a..b, Real.log t / t) = Real.log b ^ 2 / 2 - Real.log a ^ 2 / 2 := by
  cas [integrate primitive := fun t ↦ Real.log t ^ 2 / 2 using h]
```

### Properties and Relations

Differentiating the antiderivative of $x e^x$ gives back the integrand:

```lean
#cas [derive x] (exp x * (x - 1))
```

### Possible Issues

$e^{x^2}$ has no elementary antiderivative, so the search finds none. The message points to [[nintegrate]] for a value:

```lean error
#cas [integrate x in [0, 1]] (exp (x ^ 2))
```

---

On $[0, 4]$ the primitive of $\frac{1}{2 + \cos x}$ jumps at $\pi$, where its condition $\cos x + 1 \ne 0$ fails, so the command refuses its difference at the endpoints:

```lean error
#cas [integrate x in [0, 4]] (1 / (2 + cos x))
```

---

On $[0, 1]$ the conditions hold, but the proof needs more heartbeats than an attempt gets: the kernel checks of an attempt have a quarter of `maxHeartbeats`, and the check of this primitive’s certificate needs more. The command refuses when an attempt runs out:

```lean error
#cas [integrate x in [0, 1]] (1 / (2 + cos x))
```

---

Without Hex, the cubic $x^3 - 1$ in a denominator is not factored:

```lean error
#cas [integrate x] (1/(x^3 - 1))
```

With `import CASHex.Factor` the same command integrates it:

```lean quote=CASHex/Examples.lean
#cas [integrate x] (1/(x^3 - 1))
```

---

A divergent integral is refused. The primitive $\log x$ has no limit at $\infty$:

```lean error
#cas [integrate x in [1, ∞]] (1 / x)
```

---

The conditions are those of the antiderivative as it is written. Here $\cos 2x \ne 0$ comes from the tangent in the answer, so the theorem says nothing about an interval through $\pi/4$, although the integrand is defined there:

```lean
#cas [integrate x] (1 / sin (2 * x) ^ 2)
```

### Neat Examples

A polynomial times an exponential and a sine:

```lean
#cas [integrate x] (x * exp x * sin x)
```

---

A Gaussian with a linear term in the exponent:

```lean
#cas [integrate x] (3 * exp (-2 * x ^ 2 + x + 1))
```

---

The whole line, $\int_{-\infty}^{\infty} \frac{dx}{1 + x^2} = \pi$:

```lean
#cas [integrate x in [-∞, ∞]] (1 / (1 + x ^ 2))
```

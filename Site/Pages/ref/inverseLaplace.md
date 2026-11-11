+++
id = "inverseLaplace"
kind = "mode"
title = "inverseLaplace"
summary = "A function whose Laplace transform is a given proper rational function, with a theorem about the integral."
forms = ["CAS.Command.casInverseLaplaceCommand"]
see_also = ["laplace", "apart", "dsolve", "factor"]
tutorials = ["proving"]
+++

::: usage
`#cas [inverseLaplace ‹s› ‹t›] ‹F›`
: finds a function of ‹t› whose Laplace transform is the proper rational function ‹F› of ‹s›, and proves the transform for every ‹s› above a bound.
:::

When you solve a differential equation with Laplace transforms, you often end up holding a rational function of $s$, and `inverseLaplace` takes you back to the function of $t$. The theorem is the one that [[laplace]] proves: the integral of $e^{-st} f(t)$ over `Set.Ioi 0` converges and equals ‹F› as written.

The function comes from the partial fractions of ‹F›, with one group of terms for each factor of the denominator. Those terms are exact when the roots of the factor are rational or roots of a quadratic, and otherwise they are built over enclosures that the kernel checks. There is one limit. Mathlib has no uniqueness theorem for the Laplace transform, so the report gives an inverse transform, and the theorem does not say it is the only one.

## Details and Options

- For the printed `f` and the bound σ of the domain, the theorem is `∀ s : ℝ, σ < s → IntegrableOn (fun t ↦ Real.exp (-(s * t)) * f) (Set.Ioi 0) ∧ ∫ t in Set.Ioi 0, Real.exp (-(s * t)) * f = F`, with `F` as written.
- σ is at least every real zero of a written divisor of ‹F›, cancelled ones included, and every growth rate of a term of `f`.
- ‹F› is a proper rational function of ‹s› with rational coefficients and no parameters. Every written divisor has degree at most 8, and `f` has at most 16 terms.
- The terms of `f` are `c * t ^ n * exp (a * t) * g t` with `g` one of `1`, `cos (b * t)`, `sin (b * t)`, `cosh (b * t)` and `sinh (b * t)`, where `b` may be a square root, and terms over the roots of factors without a closed form.
- The denominator is factored as [[apart]] factors it, and completely over $\mathbb{Q}$ with `import CASHex.Factor`. A repeated factor whose roots are known only by enclosures is refused, and so is an input inside a section with `variable`s.
- There are no options. A proof can take the printed theorem as a hypothesis and specialize it, as under Applications.

## Examples

### Basic Examples

A sine, with the theorem for every $s > 0$:

```lean
#cas [inverseLaplace s t] (1 / (s ^ 2 + 4))
```

---

Two simple poles give two exponentials:

```lean
#cas [inverseLaplace s t] (1 / ((s - 1) * (s + 2)))
```

### Scope

A simple pole, and a pole of order 3:

```lean
#cas [inverseLaplace s t] (1 / (s - 2))
```

```lean
#cas [inverseLaplace s t] (1 / (s - 1) ^ 3)
```

---

Irrational real poles give a hyperbolic sine, with the bound $\sqrt 2$, and irrational frequencies give a sine:

```lean
#cas [inverseLaplace s t] (1 / (s ^ 2 - 2))
```

```lean
#cas [inverseLaplace s t] (1 / (s ^ 2 + 2))
```

---

A real pole and a pair of complex poles:

```lean
#cas [inverseLaplace s t] ((2 * s + 3) / ((s + 1) * (s ^ 2 + 2 * s + 5)))
```

---

A repeated pair of complex poles gives a term $t \cos t$:

```lean
#cas [inverseLaplace s t] (1 / (s ^ 2 + 1) ^ 2)
```

---

Decimal coefficients are read as exact rationals:

```lean
#cas [inverseLaplace s t] (0.5 / (s - 0.25))
```

---

A cubic with the rational root $-1$. The quadratic that remains gives the other roots, so every term is exact:

```lean
#cas [inverseLaplace s t] (1 / (s ^ 3 + 1))
```

---

A cubic without rational roots. Its roots are known by enclosures that the kernel checks, and the bound is the upper end of the enclosure of the real root $\sqrt[3]{2}$:

```lean
#cas [inverseLaplace s t] (1 / (s ^ 3 - 2))
```

---

Without Hex, $s^4 + 4$ stays whole, and its two pairs of complex roots are enclosed:

```lean
#cas [inverseLaplace s t] (1 / (s ^ 4 + 4))
```

With Hex it factors as $(s^2 - 2s + 2)(s^2 + 2s + 2)$, the answer is exact, and the bound is $s > 1$. This line is from the library’s Hex examples, with the output it pins:

```lean quote=CASHex/Examples.lean
#cas [inverseLaplace s t] (1 / (s ^ 4 + 4))
```

### Applications

Solving an initial-value problem by transforms. For `y'' + 4 * y = 0` with `y 0 = 1` and `y' 0 = 0`, the transform $Y$ satisfies $s^2 Y - s + 4Y = 0$, so $Y = s/(s^2 + 4)$, and the solution is $\cos 2t$:

```lean
#cas [inverseLaplace s t] (s / (s ^ 2 + 4))
```

---

The printed theorem as a hypothesis in a proof, specialized at $s = 1$. Only the three standard axioms are used:

```lean
theorem inverseLaplace_at_one
    (h : ∀ s : ℝ, 0 < s → ∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(s * t)) * (1 / 2 * Real.sin (2 * t)) = 1 / (s ^ 2 + 4)) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(1 * t)) * (1 / 2 * Real.sin (2 * t)) = 1 / 5 := by
  rw [h 1 one_pos]
  norm_num

#print axioms inverseLaplace_at_one
```

### Properties and Relations

Dividing by $s$ integrates: $F(s)/s$ is the transform of $\int_0^t f$. Here $\int_0^t \sin u\,du = 1 - \cos t$:

```lean
#cas [inverseLaplace s t] (1 / (s * (s ^ 2 + 1)))
```

---

Replacing $s$ by $s + 1$ multiplies the function by $e^{-t}$. The terms of a divisor may come in any order:

```lean
#cas [inverseLaplace s t] ((s + 3) / (s ^ 2 + 5 + 2 * s))
```

### Possible Issues

The theorem is about ‹F› as written, and Lean’s division by zero gives 0. So the bound covers $s = 2$, a zero of a written divisor, although the transform of $e^{-t}$ exists for $s > -1$:

```lean
#cas [inverseLaplace s t] ((s - 2) / ((s - 2) * (s + 1)))
```

---

An improper ‹F› has a polynomial part, the transform of Dirac deltas, and is refused. Subtract the polynomial part, here $s - 1$, and invert the proper rest $1/(s + 1)$:

```lean error
#cas [inverseLaplace s t] (s ^ 2 / (s + 1))
```

---

A factor $e^{-as}$ shifts the inverse transform by $a$, and is refused. Invert $1/s$ and shift the result by hand:

```lean error
#cas [inverseLaplace s t] (exp (-s) / s)
```

---

Parameters are refused:

```lean error
#cas [inverseLaplace s t] (1 / (s - a))
```

---

A repeated factor whose roots are known only by enclosures is refused:

```lean error
#cas [inverseLaplace s t] (1 / (s ^ 3 - 2) ^ 2)
```

---

The divisors must be polynomials. Write this one as `(s - 1) / (s ^ 2 - 1)`:

```lean error
#cas [inverseLaplace s t] (1 / ((s ^ 2 - 1) / (s - 1)))
```

+++
id = "ndsolve"
kind = "mode"
title = "ndsolve"
summary = "Certified enclosures of the solution of a polynomial initial-value problem, with a theorem of existence and uniqueness."
forms = ["CAS.Command.casNDSolveCommand"]
see_also = ["dsolve", "nintegrate", "findRoot", "enclose", "N"]
guide = "differential-equations"
tutorials = ["trust"]
+++

::: usage
`#cas [ndsolve ‹y› ‹t› in [‹t₀›, ‹T›], ‹y› ‹t₀› = ‹y₀›] (‹y›' = ‹f›)`
: solves the initial-value problem on $[t_0, T]$ for a polynomial ‹f› in ‹t› and ‹y›, prints a certified enclosure of the solution at ‹T›, and proves that the solution exists and is unique.
`#cas [ndsolve ‹y› ‹t› in [‹t₀›, ‹T›], ‹y› ‹t₀› = ‹y₀›, at [‹τ₁›, …]] (‹y›' = ‹f›)`
: prints enclosures at the output times ‹τ₁›, … instead.
`#cas (digits := ‹d›) [ndsolve ‹y› ‹t› in [‹t₀›, ‹T›], ‹y› ‹t₀› = ‹y₀›] (‹y›' = ‹f›)`
: makes every enclosure of width at most $10^{-d}$, for ‹d› from 1 to 15.
:::

An initial-value problem is often easier to study through bounds on its solution than through a closed formula. `ndsolve` gives you those bounds as a theorem with three parts: a solution exists on the whole interval, it is the only one, and at each output time it lies in the printed interval.

We get the enclosures from a piecewise Taylor approximation, and the kernel checks it piece by piece. If your equation is linear and has an exact solution, [[dsolve]] gives you the formula instead.

## Details and Options

- With the field `F = fun t y ↦ f`, the theorem has three parts: a solution exists, `∃ y, y t₀ = y₀ ∧ IsIntegralCurveOn y F (Set.Icc t₀ T)`; two solutions agree on `Set.Icc t₀ T`; and every solution satisfies `lo ≤ y τ ∧ y τ ≤ hi ∧ hi - lo ≤ 1 / 10 ^ d` at each output time `τ` with the printed `[lo, hi]`.
- The kernel checks the residual of each Taylor piece, one-sided Lipschitz bounds of `f` in tubes around the pieces, and the Grönwall bounds that keep every solution in the tubes. At most 200 pieces are used, and the report says how many.
- `f` is a polynomial in `t` and `y` with rational coefficients, of degree at most 4 in each variable and with at most 20 monomials.
- The endpoints are rational with $t_0 < T$, $|t_0|, |T| \le 100$ and $T - t_0 \le 20$. The initial value is a rational $y_0$ at $t_0$ with $|y_0| \le 100$.
- `, at [τ₁, …]` lists at most 8 output times in $[t_0, T]$, by default $T$ alone.
- `(digits := d)` makes every enclosure of width at most $10^{-d}$, for $d$ from 1 to 15, by default 6.
- Where no certified step exists, as near a blow-up of the solution, the command is refused. It is also refused inside a section with `variable`s.
- The tactic [[cas]] does not prove the statement of `ndsolve`. The solution of `y' = y` with `y 0 = 1` is `Real.exp`, and `cas` bounds its value directly, as under Applications.

## Examples

### Basic Examples

The solution of `y' = y` with `y 0 = 1` is $e^t$, and its enclosure at 1 holds $e$:

```lean
#cas [ndsolve y t in [0, 1], y 0 = 1] (y' = y)
```

---

A Riccati equation, at the output times $1/2$ and $1$:

```lean
#cas [ndsolve y t in [0, 1], y 0 = 1/2, at [1/2, 1]] (y' = y ^ 2 + t)
```

### Scope

Other names for the function and the variable, an interval that starts at $-1$, and an output time at the start:

```lean
#cas [ndsolve x s in [-1, 1], x (-1) = 2, at [-1, 0, 1]] (x' = s * x - x ^ 2)
```

---

Rational endpoints and a rational initial value:

```lean
#cas (digits := 8) [ndsolve y t in [-1/2, 3/4], y (-1/2) = -3/7, at [0, 3/4]] (y' = t ^ 2 - y / 3)
```

---

The logistic equation on $[0, 10]$, where the solution $1/(1 + 9e^{-t})$ comes close to 1:

```lean
#cas (digits := 8) [ndsolve y t in [0, 10], y 0 = 1/10] (y' = y * (1 - y))
```

### Options

`(digits := 10)` gives enclosures of width at most $10^{-10}$. The solution here is $\tanh t$:

```lean
#cas (digits := 10) [ndsolve y t in [0, 3], y 0 = 0, at [1, 2, 3]] (y' = 1 - y ^ 2)
```

---

A decaying solution keeps its accuracy, because the Lipschitz bound in the check is one-sided, so the negative slope of `-10 * y` costs only a small positive constant. Here $y(1) = e^{-10}$, within $10^{-12}$:

```lean
#cas (digits := 12) [ndsolve y t in [0, 1], y 0 = 1] (y' = -10 * y)
```

### Applications

The enclosure of $e$ in a proof. `cas` bounds `Real.exp 1` directly, and only the three standard axioms are used:

```lean
theorem ndsolve_exp_bounds : 2.7182818 ≤ Real.exp 1 ∧ Real.exp 1 ≤ 2.7182819 := by
  cas

#print axioms ndsolve_exp_bounds
```

### Properties and Relations

The solution of `y' = y` with `y 0 = 1` is $e^t$, so the enclosures at $1/2$ and $1$ hold $\sqrt{e}$ and $e$:

```lean
#cas (digits := 10) [ndsolve y t in [0, 1], y 0 = 1, at [1/2, 1]] (y' = y)
```

---

When `f` does not involve `y`, the solution is a primitive of `f`. Here $y(1) = \int_0^1 t\,dt = 1/2$, and the enclosure is the single point $1/2$:

```lean
#cas [ndsolve y t in [0, 1], y 0 = 0] (y' = t)
```

### Possible Issues

The solution $1/(1 - t)$ of `y' = y ^ 2` with `y 0 = 1` blows up at $t = 1$, and no certified step gets past it. Solve on an interval that ends before 1:

```lean error
#cas [ndsolve y t in [0, 2], y 0 = 1] (y' = y ^ 2)
```

---

`f` must be a polynomial in `t` and `y`. For a linear equation, [[dsolve]] takes sines, cosines and exponentials of the variable:

```lean error
#cas [ndsolve y t in [0, 1], y 0 = 1] (y' = sin y)
```

---

The degree in `y` is at most 4, and so is the degree in `t`:

```lean error
#cas [ndsolve y t in [0, 1], y 0 = 1] (y' = y ^ 5)
```

---

The initial condition is at the left end of the interval. To start at 1, write `[ndsolve y t in [1, 2], y 1 = 1]`:

```lean error
#cas [ndsolve y t in [0, 1], y 1 = 1] (y' = y)
```

---

The output times lie in the interval:

```lean error
#cas [ndsolve y t in [0, 1], y 0 = 1, at [2]] (y' = y)
```

---

The interval has length at most 20:

```lean error
#cas [ndsolve y t in [0, 30], y 0 = 1] (y' = -y)
```

---

At most 15 digits:

```lean error
#cas (digits := 16) [ndsolve y t in [0, 1], y 0 = 1] (y' = y)
```

---

The equation is about the function named in the brackets:

```lean error
#cas [ndsolve y t in [0, 1], y 0 = 1] (z' = y)
```

### Neat Examples

The solution of `y' = 1 + y ^ 2` with `y 0 = 0` is $\tan t$, and the enclosure holds $\tan 1$:

```lean
#cas [ndsolve y t in [0, 1], y 0 = 0] (y' = 1 + y ^ 2)
```

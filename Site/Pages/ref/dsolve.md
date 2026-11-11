+++
id = "dsolve"
kind = "mode"
title = "dsolve"
summary = "The general solution of a linear differential equation, or the solution of an initial-value problem, with a theorem."
forms = ["CAS.Command.casDSolveCommand"]
see_also = ["ndsolve", "laplace", "rsolve", "integrate", "oracle"]
tutorials = ["proving"]
+++

::: usage
`#cas [dsolve ‹y› ‹x›] ‹eq›`
: gives the general solution of the linear differential equation ‹eq› for the function ‹y› of ‹x›, and proves that every solution is in the family.
`#cas [dsolve ‹y› ‹x›, ‹y› ‹x₀› = ‹v₀›, ‹y›' ‹x₀› = ‹v₁›, …] ‹eq›`
: gives the solution with these initial values, and proves that it is the only one.
:::

`dsolve` finds the general solution of a supported linear differential equation, and what I wanted from it is the complete statement, not only that the printed family solves the equation. The theorem is an equivalence about every function `y : ℝ → ℝ` with enough derivatives: `y` solves the equation exactly when it is a member of the printed family. So there are no other solutions, and with initial values the printed solution is the only one.

With rational constant coefficients the equation may have any order, and the family comes from the roots of the characteristic polynomial, exact or enclosed. A right side of polynomials, exponentials, sines and cosines gets a particular solution. A first-order equation `y' + p * y = q` whose coefficients depend on $x$ is solved by an integrating factor, when the checked integrator finds the primitives it needs. Coefficients that depend on $x$ are taken in first order only.

## Details and Options

- For an equation of order $n$ and the printed family `F`, the theorem is: for every `y : ℝ → ℝ` with `∀ k < n, Differentiable ℝ (iteratedDeriv k y)`, `(∀ x, eq) ↔ ∃ c₁ … cₙ, ∀ x, y x = F`. In the theorem `y'` is `deriv y x` and `y''` is `iteratedDeriv 2 y x`.
- With initial values the theorem is `(∀ x, eq) ∧ y x₀ = v₀ ∧ deriv y x₀ = v₁ ∧ … ↔ ∀ x, y x = Y` for the printed solution `Y`. The values of `y` and its derivatives below the order are given at one rational point.
- The equation is linear in `y` and its derivatives `y'`, `y''` and so on. With rational constant coefficients, the right side is a sum of terms `x ^ k * exp (a * x) * cos (b * x)` and `x ^ k * exp (a * x) * sin (b * x)`.
- The characteristic roots are rational, roots of quadratic factors, or certified enclosures, named `r₁`, … for real roots and `z₁ = α ± iβ`, … for pairs of complex roots. With enclosed roots only the general solution is given. With `import CASHex.Factor`, Hex splits the characteristic polynomial over $\mathbb{Q}$ first.
- A first-order equation `y' + p * y = q` with coefficients that depend on $x$ is solved when the checked integrator finds a primitive $P$ of $p$ and a primitive of $e^P q$. First-order equations may have parameters.
- There are no options of its own. `oracle := sympy` or `oracle := sage` gives a family that an external system proposes, and Lean checks that it solves the equation (see [[oracle]]).
- The tactic [[cas]] does not prove the equivalence. It proves that a member of the family satisfies the equation, as under Applications.

## Examples

### Basic Examples

A second-order equation with two real characteristic roots, and the theorem that every solution is in the family:

```lean
#cas [dsolve y x] (y'' + 3*y' + 2*y = 0)
```

---

With initial values, the only solution:

```lean
#cas [dsolve y x, y 0 = 1, y' 0 = 0] (y'' + y = 0)
```

### Scope

A double root, and a pair of complex roots:

```lean
#cas [dsolve y x] (y'' - 2*y' + y = 0)
```

```lean
#cas [dsolve y x] (y'' + 2*y' + 5*y = 0)
```

---

Irrational roots from a quadratic factor:

```lean
#cas [dsolve y x] (y'' - 2*y = 0)
```

---

A right side gets a particular solution. At resonance it has a factor $x$:

```lean
#cas [dsolve y x] (y'' + y = sin x)
```

```lean
#cas [dsolve y x] (2*y'' + y = cos x * exp x)
```

---

A first-order equation with a polynomial right side:

```lean
#cas [dsolve y x] (y' + 2*y = x)
```

---

Third order, with three rational roots:

```lean
#cas [dsolve y x] (y''' - 6*y'' + 11*y' - 6*y = 0)
```

---

Initial values for an equation of order 3:

```lean
#cas [dsolve y x, y 0 = 0, y' 0 = 1, y'' 0 = 0] (y''' + y' = 0)
```

---

The roots of $r^4 + 1$ are enclosed, and the theorem states their enclosures first:

```lean
#cas [dsolve y x] (y'''' + y = 0)
```

---

A coefficient that depends on $x$, by an integrating factor, without and with an initial value:

```lean
#cas [dsolve y x] (y' + 2*x*y = x)
```

```lean
#cas [dsolve y x, y 0 = 1] (y' - 2*x*y = 0)
```

---

A first-order equation with a parameter:

```lean
#cas [dsolve y x] (y' + k * y = exp (2 * x))
```

### Options

An external system can propose a family, here for an equation whose leading coefficient is $x$. Lean checks that the family solves the equation, and the report says that its completeness is not checked:

```lean quote=tests/oracle/Oracles.lean
#cas [dsolve y x, oracle := sympy] (x * y' + y = 0)
```

### Applications

A member of the family of `y' + 2*y = x` in a proof. `cas` proves that it satisfies `y' = x - 2*y`, and only the three standard axioms are used:

```lean
theorem dsolve_solution (c₁ x : ℝ) :
    HasDerivAt (fun x ↦ -(1 / 4) + 1 / 2 * x + c₁ * Real.exp (-(2 * x)))
      (x - 2 * (-(1 / 4) + 1 / 2 * x + c₁ * Real.exp (-(2 * x)))) x := by
  cas

#print axioms dsolve_solution
```

### Properties and Relations

The [[laplace]] transform turns `y'' + y = sin x` with `y 0 = 0` and `y' 0 = 0` into $Y(s) = 1/(s^2 + 1)^2$, and [[inverseLaplace]] gives back the solution, the member of the family under Scope with $c_1 = 0$ and $c_2 = 1/2$:

```lean
#cas [inverseLaplace s t] (1 / (s ^ 2 + 1) ^ 2)
```

### Possible Issues

Coefficients that depend on $x$ are taken in first order only:

```lean error
#cas [dsolve y x] (y'' + x*y = 0)
```

---

The integrating factor of `y' + x*y = 1` is $e^{x^2/2}$, which has no elementary primitive:

```lean error
#cas [dsolve y x] (y' + x*y = 1)
```

---

The equation must be linear in `y` and its derivatives:

```lean error
#cas [dsolve y x] (y' * y = 1)
```

---

The equation must be about the function named in the brackets. Here it is `z`, so write `#cas [dsolve z x]`:

```lean error
#cas [dsolve y x] (z'' + z = 0)
```

---

The initial values must be given at one point. For a boundary-value problem, fit the constants of the general solution:

```lean error
#cas [dsolve y x, y 0 = 1, y 1 = 2] (y'' + y = 0)
```

---

With enclosed characteristic roots, only the general solution is given:

```lean error
#cas [dsolve y x, y 0 = 1, y' 0 = 0, y'' 0 = 0] (y''' - 2 * y = 0)
```

### Neat Examples

The fifth roots of unity: $r^5 - 1 = (r - 1)(r^4 + r^3 + r^2 + r + 1)$, and the four complex roots are enclosed:

```lean
#cas [dsolve y x] (y''''' - y = 0)
```

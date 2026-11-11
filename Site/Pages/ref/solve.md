+++
id = "solve"
kind = "mode"
title = "solve"
summary = "Every real solution of a polynomial equation or system, with a theorem that the list is complete."
forms = ["CAS.Command.casSolveCommand", "CAS.Command.casSolveSystemCommand"]
see_also = ["reduce", "roots", "findRoot", "linearSolve", "groebner", "cas"]
tutorials = ["first-hour", "proving"]
+++

::: usage
`#cas [solve ‹x›] (‹lhs› = ‹rhs›)`
: describes every real solution of a polynomial equation in ‹x› and proves that the description is complete.
`#cas [solve ‹x›, ‹y›, …] (‹e₁› ∧ … ∧ ‹eₘ›)`
: lists every real solution of a system of equations in several unknowns, linear or polynomial, and proves that the list is complete.
:::

`solve` finds all real solutions of a supported equation and proves that the list is complete. Checking that a value solves the equation is easy, since you can plug it back in. Knowing that you haven’t missed one is the harder half, and that is the half I wanted proved. So the theorem is an equivalence: the equation holds exactly when ‹x› is one of the printed values. `False` means that there is no real solution, and `True` that every real number is one.

Up to degree 2 the roots are written with square roots. From degree 3 on, a rational root is written exactly, and an irrational one as a named algebraic number `ρ0`, `ρ1`, … with an interval of width $10^{-8}$ that contains no other root.

## Details and Options

- For one unknown the theorem is `∀ x : ℝ, lhs = rhs ↔ P x`, where `P x` is `x = r₁ ∨ … ∨ x = rₖ`, `True` or `False`. A multiple root is listed once.
- ‹lhs› and ‹rhs› are polynomials in ‹x› alone with rational coefficients, of any degree. An irrational root of degree 3 or more is `AlgRoot.real a lo hi`, the only root of the polynomial with coefficient list `a` in $(lo, hi)$, and the theorem also states `lo < AlgRoot.real a lo hi < hi`.
- A system is a conjunction of equations, with two or more unknowns in brackets, and the theorem is `∀ x y … : ℝ, e₁ ∧ … ∧ eₘ ↔ S` for the printed solutions `S`.
- A linear system with rational coefficients is solved by exact elimination, with free parameters when it has infinitely many solutions. A square linear system whose coefficients are polynomials in one parameter is solved by the cases of the parameter.
- A polynomial system with finitely many complex solutions goes through a lexicographic Gröbner basis and the certified real roots of its eliminant. The theorem names those roots with intervals of width $10^{-20}$. In the output, `…` marks a coordinate truncated from its enclosure, and `≈` a decimal value of the exact formula in the theorem.
- There are no options. In a proof, [[cas]] proves the equivalence for one unknown. For inequalities, [[reduce]] is the mode, and for equations with other functions, [[findRoot]] certifies a root in an interval.

## Examples

### Basic Examples

A quadratic equation:

```lean
#cas [solve x] (x ^ 2 = 1)
```

---

A cubic with one irrational root, named `ρ0` with its interval:

```lean
#cas [solve x] (x ^ 3 - 2 = 0)
```

---

A linear system, with the theorem about all pairs $(x, y)$:

```lean
#cas [solve x, y] (2*x + y = 1 ∧ x - y = 2)
```

### Scope

Square roots from the quadratic formula:

```lean
#cas [solve x] (x ^ 2 = 2)
```

---

No real solution gives `False`, and every real number gives `True`:

```lean
#cas [solve x] (x ^ 2 + 1 = 0)
```

```lean
#cas [solve x] (x = x)
```

---

Three unknowns:

```lean
#cas [solve x, y, z] (x + y + z = 6 ∧ x - y = 0 ∧ x + 2*z = 7)
```

---

A system with a free parameter, and one with no solution:

```lean
#cas [solve x, y, z] (x + y + z = 1 ∧ x - z = 2)
```

```lean
#cas [solve x, y, z] (x + y + z = 6 ∧ x - y = 0 ∧ 2*x + z = 5)
```

---

A parameter in the coefficients. The answer splits into the cases $a \ne \pm 1$, $a = 1$ and $a = -1$:

```lean
#cas [solve x, y] (a*x + y = 1 ∧ x + a*y = 1)
```

---

A polynomial system with four rational solutions:

```lean
#cas [solve x, y] (x^2 + y^2 = 5 ∧ x * y = 2)
```

---

The circle and the parabola $y = x^2$ meet at two irrational points:

```lean
#cas [solve x, y] (x^2 + y^2 = 1 ∧ y = x^2)
```

---

Three unknowns, two of them fixed by the third:

```lean
#cas [solve x, y, z] (x^2 + y^2 + z^2 = 3 ∧ x = y ∧ y = z)
```

### Applications

The equivalence for one unknown in a proof. `cas` proves it, and only the three standard axioms are used:

```lean
theorem solve_square : ∀ x : ℝ, x ^ 2 = 1 ↔ x = 1 ∨ x = -1 := by
  cas

#print axioms solve_square
```

### Properties and Relations

For an inequality, [[reduce]] gives the equivalent condition, here between the two roots of $x^2 = 2$:

```lean
#cas [reduce x] (x^2 < 2)
```

### Possible Issues

Only polynomial equations. For other equations, the message points to [[findRoot]]:

```lean error
#cas [solve x] (sin x = 0)
```

---

An inequality is not an equation:

```lean error
#cas [solve x] (x < 1)
```

---

A circle alone has infinitely many points, and the nonlinear solver needs finitely many complex solutions:

```lean error
#cas [solve x, y] (x^2 + y^2 = 1)
```

### Neat Examples

The real and imaginary parts of $(x + iy)^3 = 1$. The three solutions are the cube roots of unity:

```lean
#cas [solve x, y] (x^3 - 3*x*y^2 = 1 ∧ 3*x^2*y - y^3 = 0)
```

---

The four points $(\pm 1/\sqrt{2}, \pm 1/\sqrt{2})$ share their coordinates in pairs:

```lean
#cas [solve x, y] (x^2 + y^2 = 1 ∧ x^2 - y^2 = 0)
```

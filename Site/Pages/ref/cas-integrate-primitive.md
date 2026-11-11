+++
id = "cas-integrate-primitive"
kind = "tactic"
title = "cas [integrate primitive := F]"
summary = "Proves a definite integral from a primitive that you supply: the derivative is checked, then the fundamental theorem of calculus applies."
forms = ["CAS.ExactTactic.casIntegratePrimitive"]
see_also = ["cas", "cas-using", "integrate", "cas-query", "nintegrate", "oracle"]
tutorials = ["proving"]
+++

::: usage
`cas [integrate primitive := ‹F›]`
: proves $\int_a^b f = v$ from the primitive ‹F›: it checks that $F' = f$ on the interval, and applies the fundamental theorem of calculus.
`cas [integrate primitive := ‹F› using ‹h›]`
: the same, with ‹h› as evidence for the conditions that $F$ and $f$ need on the whole interval.
:::

Sometimes I already know the antiderivative and only want Lean to accept it. Maybe it came from a book, from SymPy, or from a page of my own algebra. This form takes that $F$, checks its derivative against the integrand, and turns the check into the value of the integral by the fundamental theorem of calculus. If $F$ is wrong, the check fails and nothing is proved.

## Details and Options

- The goal is an equality with one bounded interval integral on one side, `(∫ x in a..b, f x) = v` or `v = ∫ x in a..b, f x`.
- ‹F› is a term of type `ℝ → ℝ`, such as `fun t ↦ Real.log t ^ 2 / 2`, or a local definition made with `let`.
- The derivative of ‹F› minus the integrand must reduce to zero. That check is decided by the kernel, and then Mathlib’s `intervalIntegral.integral_eq_sub_of_hasDerivAt` gives $\int_a^b f = F(b) - F(a)$.
- With `using h`, the conditions hold on the whole interval, stated as `∀ t ∈ Set.uIcc a b, …`, so the endpoints may come in either order.
- Improper integrals, inequalities and goals with several integrals are refused with a message. Bare [[cas]] proves many of them.
- There are no other options.

## Examples

### Basic Examples

A primitive for $2x$:

```lean
example : (∫ x in (0 : ℝ)..1, 2 * x) = 1 := by
  cas [integrate primitive := fun x ↦ x ^ 2]
```

---

A primitive that needs $t \ne 0$ on the interval, given by `using`:

```lean
example (a b : ℝ) (h : ∀ t ∈ Set.uIcc a b, t ≠ 0) :
    (∫ t in a..b, Real.log t / t) = Real.log b ^ 2 / 2 - Real.log a ^ 2 / 2 := by
  cas [integrate primitive := fun t ↦ Real.log t ^ 2 / 2 using h]
```

### Scope

Parameters in the integrand and in the primitive:

```lean
example (a b c d : ℝ) (h : ∀ t ∈ Set.uIcc a b, t ≠ 0) :
    (∫ t in a..b, c * Real.log t / t + d) =
      (d * b + c * Real.log b ^ 2 / 2) - (d * a + c * Real.log a ^ 2 / 2) := by
  cas [integrate primitive := (fun t : ℝ ↦ d * t + c * Real.log t ^ 2 / 2) using h]
```

---

A primitive named with `let`:

```lean
example (a b : ℝ) (h : ∀ t ∈ Set.uIcc a b, t ≠ 0) :
    (∫ t in a..b, Real.log t / t) = Real.log b ^ 2 / 2 - Real.log a ^ 2 / 2 := by
  let F : ℝ → ℝ := fun t ↦ Real.log t ^ 2 / 2
  cas [integrate primitive := F using h]
```

### Applications

The integral of $x e^x$ from a primitive found by integrating by parts on paper. Only the three standard axioms are used:

```lean
theorem integral_x_exp : (∫ x in (0 : ℝ)..1, x * Real.exp x) = 1 := by
  cas [integrate primitive := fun x ↦ (x - 1) * Real.exp x]

#print axioms integral_x_exp
```

### Properties and Relations

[[integrate]] finds the primitive itself when it can, and prints it with its theorem:

```lean
#cas [integrate x] (x * exp x)
```

---

With the optional [[oracle|oracles]], `cas [oracle := sympy]` asks SymPy for a primitive, checks it, and suggests this form. The suggestion needs no oracle:

```lean quote=tests/oracle/Oracles.lean
theorem integral_by_oracle : ∫ x in (0 : ℝ)..1, x * Real.exp x = 1 := by
  cas [oracle := sympy]
```

### Possible Issues

A wrong primitive is refused. The derivative of $x^3$ is not $2x$:

```lean error
example : (∫ x in (0 : ℝ)..1, 2 * x) = 1 := by
  cas [integrate primitive := fun x ↦ x ^ 3]
```

---

A primitive that is right only where it is defined. Without `using h`, nothing says that $t \ne 0$ on the interval:

```lean error
example (a b : ℝ) :
    (∫ t in a..b, Real.log t / t) = Real.log b ^ 2 / 2 - Real.log a ^ 2 / 2 := by
  cas [integrate primitive := fun t ↦ Real.log t ^ 2 / 2]
```

---

Only equalities. For a bound on an integral, [[cega]] is the tactic:

```lean error
example : (∫ x in (0 : ℝ)..1, x) ≤ 1 := by
  cas [integrate primitive := fun x ↦ x ^ 2 / 2]
```

---

Only bounded intervals:

```lean error
example : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x)) = 1 := by
  cas [integrate primitive := fun x ↦ -Real.exp (-x)]
```

### Neat Examples

The arctangent as a primitive, on any interval:

```lean
example (a b : ℝ) : (∫ t in a..b, 1 / (1 + t ^ 2)) = Real.arctan b - Real.arctan a := by
  cas [integrate primitive := fun t ↦ Real.arctan t]
```

+++
id = "rsolve"
kind = "mode"
title = "rsolve"
summary = "The general solution of a linear recurrence with constant coefficients, or the sequence with given initial values, with a theorem."
forms = ["CAS.Command.casRSolveCommand"]
see_also = ["dsolve", "sum", "product", "fibonacci", "roots"]
tutorials = ["proving"]
+++

::: usage
`#cas [rsolve ‹a› ‹n›] ‹eq›`
: gives the general solution of the linear recurrence ‹eq› for the sequence ‹a›, and proves that every solution has this form.
`#cas [rsolve ‹a› ‹n›, ‹a› 0 = ‹v₀›, …] ‹eq›`
: gives the sequence with these initial values, and proves that it is the only one.
:::

`rsolve` finds a closed form for a linear recurrence, such as Binet’s formula for the Fibonacci numbers. I wanted more than a formula that matches the first few terms, so the theorem is an equivalence about every sequence `a : ℕ → ℝ`: it satisfies the recurrence, and the initial values when they are given, exactly when it has the printed form.

The closed form comes from the roots of the characteristic polynomial. Rational roots and the roots of quadratic factors are written exactly, and the other roots are certified enclosures. When the right side has terms $c\,n^j r^n$, we find a particular solution by undetermined coefficients.

## Details and Options

- Without initial values, for a recurrence of order $d$ and the printed general solution `y`, the theorem is `∀ a : ℕ → ℝ, (∀ n, eq) ↔ ∃ c₁ … c_d, ∀ n, a n = y n`. With initial values it is `∀ a : ℕ → ℝ, (∀ n, eq) ∧ initial values ↔ ∀ n, a n = Y n` for the printed sequence `Y`.
- The recurrence is linear in ‹a› with constant rational coefficients, and the coefficient of `a n` is not zero. The right side may contain terms `c * n ^ j * r ^ n`.
- An enclosed real root is named `r₁`, `r₂`, …, and a pair of complex roots `z₁`, `conj z₁` gives the real terms `re(z₁^n)` and `im(z₁^n)`. The theorem states their enclosures first. With `import CASHex.Factor`, Hex splits the characteristic polynomial over $\mathbb{Q}$ before anything is enclosed.
- A recurrence of order $d$ takes $d$ initial values at consecutive indices, such as `a 0 = 0, a 1 = 1` or `a 1 = 1, a 2 = 1`.
- There are no options. The tactic [[cas]] does not prove the statements of `rsolve`, and the closed form follows from the recurrence by induction, as in the example under Applications.

## Examples

### Basic Examples

The Fibonacci numbers. Binet’s formula is the only sequence with the recurrence and these initial values:

```lean
#cas [rsolve a n, a 0 = 0, a 1 = 1] (a (n + 2) = a (n + 1) + a n)
```

---

Without initial values, the general solution has a constant for each order:

```lean
#cas [rsolve a n] (a (n + 2) = a (n + 1) + a n)
```

### Scope

A first-order recurrence with a constant term:

```lean
#cas [rsolve a n, a 0 = 1] (a (n + 1) = 2 * a n + 1)
```

---

Two rational characteristic roots, in the general solution and with initial values:

```lean
#cas [rsolve a n] (a (n + 2) = 5 * a (n + 1) - 6 * a n)
```

```lean
#cas [rsolve a n, a 0 = 2, a 1 = 3] (a (n + 2) = 3 * a (n + 1) - 2 * a n)
```

---

A double root gives the terms $1$ and $n$:

```lean
#cas [rsolve a n] (a (n + 2) = 2 * a (n + 1) - a n)
```

---

A polynomial right side, by undetermined coefficients:

```lean
#cas [rsolve a n, a 0 = 0, a 1 = 0] (a (n + 2) - 2 * a (n + 1) + a n = 1)
```

```lean
#cas [rsolve a n, a 0 = 1] (a (n + 1) = a n + n)
```

---

The initial values may sit at any two consecutive indices:

```lean
#cas [rsolve a n, a 1 = 1, a 2 = 1] (a (n + 2) = a (n + 1) + a n)
```

---

The complex characteristic roots $\pm i$, in real form:

```lean
#cas [rsolve a n, a 0 = 1, a 1 = 0] (a (n + 2) = - a n)
```

---

A cubic with one real root and a pair of complex roots, known by enclosures and named `r₁` and `z₁`:

```lean
#cas [rsolve a n] (a (n + 3) = a (n + 1) + a n)
```

---

Without Hex, the quartic $r^4 - 5r^2 + 6$ is not split, and its four real roots are enclosed:

```lean
#cas [rsolve a n] (a (n + 4) = 5 * a (n + 2) - 6 * a n)
```

With Hex it factors as $(r^2 - 3)(r^2 - 2)$, and the roots are exact. This line is from the library’s Hex examples, with the output it pins:

```lean quote=CASHex/Examples.lean
#cas [rsolve a n] (a (n + 4) = 5 * a (n + 2) - 6 * a n)
```

### Applications

The closed form in a proof, by induction from the recurrence. Only the three standard axioms are used:

```lean
theorem rsolve_closed_form (a : ℕ → ℝ) (h : ∀ n, a (n + 1) = 2 * a n + 1) (h₀ : a 0 = 1) :
    ∀ n, a n = -1 + 2 * 2 ^ n := by
  intro n
  induction n with
  | zero =>
    rw [h₀]
    norm_num
  | succ n ih =>
    rw [h, ih]
    ring

#print axioms rsolve_closed_form
```

### Properties and Relations

Binet’s formula at $n = 20$ is 6765, the value of the call [[fibonacci]]:

```lean
#cas (fibonacci 20)
```

### Possible Issues

The coefficients must be constants. Here the coefficient of `a n` is $n$:

```lean error
#cas [rsolve a n] (a (n + 1) = n * a n)
```

---

When the coefficient of `a n` is zero, the recurrence is one of lower order for `a (n + 1)`:

```lean error
#cas [rsolve a n] (a (n + 2) = a (n + 1))
```

---

The recurrence must be linear in the sequence:

```lean error
#cas [rsolve a n] (a (n + 1) = a n * a n)
```

---

A recurrence of order 2 takes two initial values:

```lean error
#cas [rsolve a n, a 0 = 1] (a (n + 2) = a (n + 1) + a n)
```

---

The right side may contain polynomial and exponential terms in $n$ only:

```lean error
#cas [rsolve a n] (a (n + 1) = a n + sin n)
```

---

The first name in the brackets is the sequence, and the message says how to fix a mismatch:

```lean error
#cas [rsolve a n] (b (n + 1) = 2 * b n)
```

### Neat Examples

The Padovan numbers. Their characteristic polynomial $r^3 - r - 1$ has the plastic number as its real root, here `r₁`:

```lean
#cas [rsolve a n, a 0 = 1, a 1 = 1, a 2 = 1] (a (n + 3) = a (n + 1) + a n)
```

+++
id = "trigExpand"
kind = "mode"
title = "trigExpand"
summary = "Expands sines and cosines of sums, differences and double angles, with a theorem about Mathlib’s sine and cosine."
forms = ["CAS.Command.casTrigExpandCommand"]
see_also = ["expand", "fullSimplify", "simplify", "cas"]
guide = "algebra"
tutorials = ["first-hour"]
+++

::: usage
`#cas [trigExpand] ‹e›`
: expands the sines and cosines of sums, differences and double angles in ‹e› and proves that the expansion equals ‹e›.
:::

`trigExpand` applies the angle-addition formulas to sines and cosines, so that their products can be expanded and simplified. The theorem is an identity about `Real.sin` and `Real.cos` for all real values of the variables, so it needs no conditions.

It applies six formulas and nothing else, which keeps it predictable: you can tell from the input what the output will be. For identities that need more, such as $\sin^2 x + \cos^2 x = 1$ or a triple angle, I use [[fullSimplify]] or the tactic [[cas]].

## Details and Options

- The theorem is $\forall x_1, \dots, x_n,\; e = e'$ about `Real.sin` and `Real.cos`, where $e'$ is the printed expansion, proved by the addition and double-angle formulas.
- The formulas are those for `sin (a + b)`, `cos (a + b)`, `sin (a - b)`, `cos (a - b)`, `sin (2 * a)` and `cos (2 * a)`. The double angle of the cosine is written $\cos^2 a - \sin^2 a$.
- Other expressions, such as `sin (3 * x)` or `x ^ 2`, are printed unchanged, and the theorem is then the trivial identity.
- It plays the part of Mathematica’s `TrigExpand` and SymPy’s `expand_trig` for these formulas.
- [[expand]] does not look inside functions. [[fullSimplify]] counts the trigonometric expansion among its candidates and keeps the smallest form.

## Examples

### Basic Examples

The sine of a sum:

```lean
#cas [trigExpand] (sin (x + y))
```

---

The cosine of a double angle:

```lean
#cas [trigExpand] (cos (2*x))
```

### Scope

A difference and a double angle in one product. Each factor is expanded:

```lean
#cas [trigExpand] (cos (x - y) * sin (2 * y))
```

### Applications

The addition formula as a theorem, for all real `x` and `y`. Only the three standard axioms are used:

```lean
theorem sin_add_expanded (x y : ℝ) :
    Real.sin (x + y) = Real.sin x * Real.cos y + Real.cos x * Real.sin y := by
  cas

#print axioms sin_add_expanded
```

---

The tactic `cas` proves the other forms of the double-angle formula, which also need $\sin^2 x + \cos^2 x = 1$:

```lean
example (x : ℝ) : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
  cas
```

---

A product of a sum and a difference:

```lean
example (x y : ℝ) :
    Real.sin (x + y) * Real.sin (x - y) = Real.sin x ^ 2 - Real.sin y ^ 2 := by
  cas
```

### Properties and Relations

[[expand]] leaves the argument of a function alone:

```lean
#cas [expand] (sin (x + y))
```

---

[[fullSimplify]] tries the trigonometric expansion with the other candidates, so it finds identities that reduce to $0$:

```lean
#cas [fullSimplify] (sin (2*x) - 2*sin x*cos x)
```

```lean
#cas [fullSimplify] (cos x ^ 2 - sin x ^ 2 - cos (2*x))
```

### Possible Issues

A multiple angle other than a double angle is not expanded, and the report proves the trivial identity $\sin 3x = \sin 3x$:

```lean
#cas [trigExpand] (sin (3*x))
```

---

The tactic `cas` proves the triple-angle formula:

```lean
example (x : ℝ) : Real.cos (3 * x) = 4 * Real.cos x ^ 3 - 3 * Real.cos x := by
  cas
```

---

A false identity is refused. Here $\sin 2x = 2 \sin x$ fails at $x = \pi/2$, where the left side is $0$ and the right side is $2$:

```lean error
example (x : ℝ) : Real.sin (2 * x) = 2 * Real.sin x := by
  cas
```

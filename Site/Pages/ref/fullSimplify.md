+++
id = "fullSimplify"
kind = "mode"
title = "fullSimplify"
summary = "Tries many checked forms of a real expression and gives the simplest one, with the conditions it needs."
forms = ["CAS.Command.casFullSimplifyCommand"]
see_also = ["simplify", "expand", "factor", "trigExpand", "cas"]
guide = "algebra"
tutorials = ["first-hour", "proving"]
+++

::: usage
`#cas [fullSimplify] ‹e›`
: gives the simplest form of the real expression ‹e› by `leafCount` that it proves equal to ‹e›, with the conditions under which it holds.
`#cas [fullSimplify ‹c›] ‹e›`
: does the same with the complexity function ‹c›, one of `leafCount`, `depth` and `length`.
:::

An expression usually has many equivalent forms, and `fullSimplify` looks for the simplest one. It gathers candidate forms, ranks them by size, and reports the simplest one whose identity with the input the kernel accepts. It plays the part of Mathematica’s `FullSimplify` with `LeafCount`, except that the answer is a theorem.

It works the way the rest of SymLean does: the search only proposes. A candidate that can’t be proved costs some time and nothing else, and the next one in the ranking is tried. So a bad guess can make the command slower, but it can’t make the answer wrong.

## Details and Options

- The theorem has the form $\forall x_1, \dots, x_n,\; c_1 \to \dots \to c_k \to e = e'$ about Mathlib’s real functions, where $e'$ is the printed form and $c_1, \dots, c_k$ are the printed conditions. Its proof is the rewrite that produced the form (the trigonometric or logarithm lemmas, or `Real.sqrt_sq_eq_abs`), `ring`, the tactic `cas`, or `field_simp` followed by `ring`.
- The candidates are the input, the results of the checked simplification routes, the expanded and the factored polynomial, the trigonometric expansion of sums and double angles, the expansion of logarithms of products, quotients and powers, and $|t|$ for the square root of a perfect square $t^2$.
- `leafCount`, the default, counts atoms and operations, after Mathematica’s `LeafCount` with weights of its own. A variable, an integer, $\pi$ and $e$ count 1, and a fraction such as `3/2` counts 3. A sum, difference, product, quotient, real power or function counts 1 plus its operands, and a negation or a natural power $a^k$ counts 2 plus $a$. So $(x + 1)^5$ counts 5 and its expansion counts 27.
- `depth` is the depth of the expression tree, and `length` is the length of the printed form.
- Ties go to the candidate with fewer conditions, then to the shorter printed form. The candidates are tried in the order of their rank, and the first one proved is reported. “The computation” lists the ranked candidates with their sizes, and these are proposals, not proof.
- The variables and functions are those of [[simplify]]. [[expand]], [[factor]] and [[trigExpand]] run the same search with fewer candidates.
- The tactic [[cas]] proves most of these identities as goals, with the conditions as hypotheses. An identity with a square root needs sign hypotheses there (see Possible Issues).

## Examples

### Basic Examples

A polynomial that is a fifth power. The factored form counts 5, the input 27:

```lean
#cas [fullSimplify] (x^5 + 5*x^4 + 10*x^3 + 10*x^2 + 5*x + 1)
```

---

Mathlib’s logarithm is $\log |x|$, with $\log 0 = 0$, so the product rule needs only $x \ne 0$ and $y \ne 0$, not positivity:

```lean
#cas [fullSimplify] (log (x*y) - log x - log y)
```

---

The square root of a perfect square is an absolute value, for every $x$:

```lean
#cas [fullSimplify] (sqrt (x^2 + 2*x + 1))
```

### Scope

Trigonometric identities that reduce to $0$:

```lean
#cas [fullSimplify] (sin (2*x) - 2*sin x*cos x)
```

```lean
#cas [fullSimplify] (cos x ^ 2 - sin x ^ 2 - cos (2*x))
```

---

A quotient that cancels, with its condition:

```lean
#cas [fullSimplify] ((x^4 - 1)/(x^2 - 1))
```

---

Several variables:

```lean
#cas [fullSimplify] (x^3 + 3*x^2*y + 3*x*y^2 + y^3)
```

---

In Mathlib $\exp(\log x) = |x|$ for $x \ne 0$, and $\exp(\log 0) = 1$, so getting $x$ back needs $x > 0$:

```lean
#cas [fullSimplify] (exp (log x))
```

### Options

With `depth`, the depth of the expression tree decides:

```lean
#cas [fullSimplify depth] (x^2 + 2*x + 1)
```

```lean
#cas [fullSimplify depth] (sin (2*x) - 2*sin x*cos x)
```

### Applications

The logarithm identity as a theorem, with the printed conditions as hypotheses. Only the three standard axioms are used:

```lean
theorem log_mul_sub_logs (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log (x * y) - Real.log x - Real.log y = 0 := by
  cas

#print axioms log_mul_sub_logs
```

---

Away from $0$ the logarithm sees $|x|$, and `cas` proves the identity with the absolute value:

```lean
example (x : ℝ) (hx : x ≠ 0) : Real.exp (3 * Real.log x) = |x| ^ 3 := by
  cas
```

### Properties and Relations

`fullSimplify` keeps $x^3 - x$, which counts 5, over $x (x - 1)(x + 1)$, which counts 9. [[factor]] gives the factored form whatever its size:

```lean
#cas [fullSimplify] (x^3 - x)
```

```lean
#cas [factor] (x ^ 3 - x)
```

### Possible Issues

The complexity function must be one of the three:

```lean error
#cas [fullSimplify size] (x + 1)
```

---

The tactic `cas` does not prove an identity with a square root without sign hypotheses, even one that `fullSimplify` proves for every $x$. Its message lists the candidate conditions:

```lean error
example (x : ℝ) : Real.sqrt (x ^ 2 + 2 * x + 1) = |x + 1| := by
  cas
```

---

In a proof, Mathlib’s `Real.sqrt_sq_eq_abs` does it, the lemma behind the `fullSimplify` answer:

```lean
example (x : ℝ) : Real.sqrt (x ^ 2 + 2 * x + 1) = |x + 1| := by
  rw [show x ^ 2 + 2 * x + 1 = (x + 1) ^ 2 by ring]
  exact Real.sqrt_sq_eq_abs (x + 1)
```

### Neat Examples

A quartic that is the square of a quadratic. The answer $(x^2 - 1)^2$ counts 7, while the full factorization $(x - 1)^2 (x + 1)^2$ would count 11:

```lean
#cas [fullSimplify] (x^4 - 2*x^2 + 1)
```

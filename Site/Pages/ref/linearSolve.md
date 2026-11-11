+++
id = "linearSolve"
kind = "mode"
title = "linearSolve"
summary = "All solutions of a linear system $A x = b$ with rational entries, with a theorem that there are no others."
forms = ["CAS.Command.casLinearSolveCommand"]
see_also = ["nullSpace", "rowReduce", "inverse", "solve", "dot"]
tutorials = ["proving"]
+++

::: usage
`#cas [linearSolve] (‹A›, ‹b›)`
: finds all solutions $x$ of $A x = b$ for the matrix ‹A› and the vector ‹b› with rational entries, and proves that there are no others.
:::

A lot of the linear systems I meet arrive as a matrix, and `linearSolve` takes them in that form. What matters to me is that the report gives every solution, not just one. The answer is a single vector, one solution plus the span of a basis of the null space, or the fact that there is none. Each answer is a theorem about Mathlib’s `Matrix.mulVec` over $\mathbb{Q}$ that rules out any other solution, so it tells you what all the solutions are, not only that some vector works.

## Details and Options

- ‹A› is a matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]` of any shape. ‹b› is a vector `![a, b]` or `[a, b]` with one entry for each row of ‹A›. The entries are closed rational expressions such as `-3/2`, `0.25` or `1/10^15`.
- The theorem is one of three statements over $\mathbb{Q}$:
  - one solution $x_0$: `∀ x, A.mulVec x = b ↔ x = x₀`;
  - one solution $x_0$ plus the span of independent vectors $V_i$: `A.mulVec x₀ = b ∧ LinearIndependent ℚ V ∧ ∀ x, A.mulVec x = b ↔ ∃ c, x = x₀ + ∑ i, c i • V i`;
  - no solution: `¬∃ x, A.mulVec x = b`.
- The kernel decides the equations between literals, and `linarith` proves the statements about every $x$ from the coordinates of `A.mulVec x`.
- For equations in named variables, such as `2*x + y = 1 ∧ x - y = 2`, the mode [[solve]] takes the system as you write it.
- The tactic [[cas]] proves goals `A.mulVec v = b` for literals over $\mathbb{Q}$.

## Examples

### Basic Examples

The system $x + 2 y = 5$, $3 x + 4 y = 6$ has one solution:

```lean
#cas [linearSolve] (!![1, 2; 3, 4], ![5, 6])
```

---

Here the second equation is twice the first, and the solutions form a plane: one solution plus the span of two vectors:

```lean
#cas [linearSolve] (!![1, 2, 3; 2, 4, 6], ![1, 2])
```

### Scope

With another right side the two equations contradict each other, and the theorem says that no $x$ solves them:

```lean
#cas [linearSolve] (!![1, 2, 3; 2, 4, 6], ![1, 3])
```

---

A square system with a line of solutions. The third equation is the sum of the first two:

```lean
#cas [linearSolve] (!![1, 1, 1; 1, -1, 2; 2, 0, 3], ![6, 5, 11])
```

---

Fractions in the matrix, and the right side as a list:

```lean
#cas [linearSolve] (!![1/2, 1/3; 1/4, 1/5], [1, 1])
```

### Applications

A solution as a theorem, with the axioms its proof uses:

```lean
theorem linearSolve_check : !![(1 : ℚ), 2; 3, 4].mulVec ![-4, 9 / 2] = ![5, 6] := by
  cas

#print axioms linearSolve_check
```

---

The numbers $a$, $b$ in $\frac{1}{(x - 1)(x + 1)} = \frac{a}{x - 1} + \frac{b}{x + 1}$ solve $a + b = 0$ and $a - b = 1$, the coefficients of $a (x + 1) + b (x - 1) = 1$. [[apart]] finds the same decomposition:

```lean
#cas [linearSolve] (!![1, 1; 1, -1], ![0, 1])
```

```lean
#cas [apart] (1/((x - 1)*(x + 1)))
```

### Properties and Relations

The span in the second example is the null space of the matrix:

```lean
#cas [nullSpace] !![1, 2, 3; 2, 4, 6]
```

---

[[solve]] takes a system in named variables, and proves its answer for every real assignment:

```lean
#cas [solve x, y] (2*x + y = 1 ∧ x - y = 2)
```

```lean
#cas [linearSolve] (!![2, 1; 1, -1], ![1, 2])
```

### Possible Issues

The right side needs one entry for each row of the matrix:

```lean error
#cas [linearSolve] (!![1, 2; 3, 4], ![5, 6, 7])
```

---

The mode takes the pair `(A, b)`. For $A x = 0$, [[nullSpace]] takes the matrix alone:

```lean error
#cas [linearSolve] !![1, 2; 3, 4]
```

### Neat Examples

The sum $1^2 + 2^2 + \dots + n^2$ is a cubic $a n + b n^2 + c n^3$. Its values $1$, $5$, $14$ at $n = 1, 2, 3$ give the coefficients of $\tfrac{n}{6} + \tfrac{n^2}{2} + \tfrac{n^3}{3}$:

```lean
#cas [linearSolve] (!![1, 1, 1; 2, 4, 8; 3, 9, 27], ![1, 5, 14])
```

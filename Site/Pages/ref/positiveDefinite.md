+++
id = "positiveDefinite"
kind = "mode"
title = "positiveDefinite"
summary = "Whether a square matrix with rational entries is positive definite, with a theorem about Mathlib’s `Matrix.PosDef` either way."
forms = ["CAS.Command.casPositiveDefiniteCommand"]
see_also = ["eigenvalueBounds", "eigenvalues", "transpose", "det"]
tutorials = ["proving"]
+++

::: usage
`#cas [positiveDefinite] ‹A›`
: decides whether the square matrix ‹A› with rational entries is positive definite over $\mathbb{R}$, and proves the answer.
:::

For a symmetric matrix, positive definiteness means $x^T A x>0$ for every nonzero $x$. It is the condition behind the second-derivative test and many quadratic-form estimates. `positiveDefinite` proves its answer either way, and the two proofs are of quite different kinds. `True` comes with an exact factorization $A = L D L^T$ over $\mathbb{Q}$ with positive pivots. `False` comes with a rational vector $x \ne 0$ such that $x^T A x \le 0$, which you can check by hand, or with an entry that breaks the symmetry.

## Details and Options

- ‹A› is a square matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`. The entries are closed rational expressions such as `-3/2`, `0.25` or `1/10^15`.
- The theorem is `M.PosDef` or `¬M.PosDef` for the matrix `M : Matrix (Fin n) (Fin n) ℝ` with the entries of ‹A›. Mathlib’s `Matrix.PosDef` asks that $M$ be Hermitian, which over $\mathbb{R}$ means symmetric, and that $x^T M x > 0$ for every $x \ne 0$.
- `True` comes from the symmetric elimination $A = L D L^T$ over $\mathbb{Q}$, with all pivots in $D$ positive. The report prints the pivots, and the kernel checks the factorization entry by entry and the signs of the pivots (`CAS.Analysis.Matrix.posDef_of_ldlCheck`).
- `False` names a rational vector $x \ne 0$ with $x^T A x \le 0$, and the kernel checks its quadratic form (`CAS.Analysis.Matrix.not_posDef_of_quadFormCheck`). For a matrix that is not symmetric, the theorem comes from one entry with $A_{i j} \ne A_{j i}$.
- The elimination is exact, so there is no tolerance: a pivot of $10^{-15}$ counts as positive.

## Examples

### Basic Examples

A symmetric matrix with the pivots 2 and $\tfrac{3}{2}$:

```lean
#cas [positiveDefinite] !![2, 1; 1, 2]
```

---

For this one the vector $x = (-2, 1)$ gives $x^T A x = -3$:

```lean
#cas [positiveDefinite] !![1, 2; 2, 1]
```

### Scope

Mathlib’s `PosDef` includes symmetry, so a matrix that is not symmetric is never positive definite:

```lean
#cas [positiveDefinite] !![1, 2; 3, 4]
```

---

The matrix $\begin{pmatrix} 1 & 1 \\ 1 & 1 + 10^{-12} \end{pmatrix}$ has the pivots 1 and $10^{-12}$:

```lean
#cas [positiveDefinite] !![1, 1; 1, 1000000000001/1000000000000]
```

---

Tiny entries are fine:

```lean
#cas [positiveDefinite] !![1/10^15, 0; 0, 1/10^15]
```

---

A list of rows with fractions:

```lean
#cas [positiveDefinite] [[1, 1/2], [1/2, 1/3]]
```

### Applications

A proof can take the printed theorem as a hypothesis and use Mathlib’s consequences of positive definiteness, here `Matrix.PosDef.det_pos`:

```lean
theorem posDef_det_pos (h : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef) :
    0 < (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).det :=
  h.det_pos

#print axioms posDef_det_pos
```

---

The quadratic form $f(x, y, z) = 2 x^2 + \tfrac{3}{2} y^2 + z^2 + x y + y z$ has this Hessian. It is positive definite, so $f$ is positive away from 0 and has a strict minimum there:

```lean
#cas [positiveDefinite] !![4, 1, 0; 1, 3, 1; 0, 1, 2]
```

### Properties and Relations

A symmetric matrix is positive definite exactly when its smallest eigenvalue is positive. For the Hessian above, [[eigenvalueBounds]] puts it at $3 - \sqrt{3} \approx 1.27$:

```lean
#cas [eigenvalueBounds] !![4, 1, 0; 1, 3, 1; 0, 1, 2]
```

---

The pivots are the ratios of the leading principal minors, so they are all positive exactly when the minors are (Sylvester’s criterion). For the Hessian the pivots are $4$, $\tfrac{11}{4}$ and $\tfrac{18}{11}$, and the minors are 4, 11 and the determinant 18:

```lean
#cas [det] !![4, 1, 0; 1, 3, 1; 0, 1, 2]
```

### Possible Issues

A positive semidefinite matrix that is singular is not positive definite. The vector $x = (-1, 1)$ has $A x = 0$:

```lean
#cas [positiveDefinite] !![1, 1; 1, 1]
```

---

The quadratic form of the first matrix is $x_1^2 + x_2^2$, positive for every $x \ne 0$, but the matrix is not symmetric, so it is not `PosDef`. Its symmetric part $\tfrac{1}{2}(A + A^T)$ has the same quadratic form, and here it is the identity:

```lean
#cas [positiveDefinite] !![1, 1; -1, 1]
```

```lean
#cas [positiveDefinite] !![1, 0; 0, 1]
```

---

The matrix has to be square:

```lean error
#cas [positiveDefinite] !![1, 2, 3; 4, 5, 6]
```

### Neat Examples

The $10 \times 10$ Hilbert matrix is the Gram matrix of $1, x, \dots, x^9$ on $[0, 1]$, so it is positive definite, and it is close to singular. Its last pivot is about $2.2 \cdot 10^{-11}$, and the exact elimination proves it positive all the same:

```lean
#cas [positiveDefinite] !![1, 1/2, 1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10;
  1/2, 1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11;
  1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12;
  1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13;
  1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14;
  1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15;
  1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16;
  1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17;
  1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17, 1/18;
  1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17, 1/18, 1/19]
```

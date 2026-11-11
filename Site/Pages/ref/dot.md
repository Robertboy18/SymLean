+++
id = "dot"
kind = "mode"
title = "dot"
summary = "The product of two matrices, or of a matrix and a vector, with rational entries and a theorem that it is right."
forms = ["CAS.Command.casDotCommand"]
see_also = ["matrixPower", "transpose", "linearSolve", "inverse", "eigenvectors"]
tutorials = ["proving"]
+++

::: usage
`#cas [dot] (‹A›, ‹B›)`
: gives the product of the matrices ‹A› and ‹B›, and proves `‹A› * ‹B› = C`.
`#cas [dot] (‹A›, ‹v›)`
: gives the product of the matrix ‹A› and the vector ‹v›, and proves `‹A›.mulVec ‹v› = w`.
:::

`dot` is the matrix product, like Mathematica’s `Dot`. I use it to check things: that a vector is an eigenvector, that a proposed inverse is one, that a solution solves the system. The theorem is an equation between Mathlib matrices or vectors over $\mathbb{Q}$, which the kernel decides by evaluating both sides.

## Details and Options

- ‹A› is a matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`. The second factor is a matrix in the same forms, or a vector `![a, b]` or `[a, b]`.
- The second factor has as many rows, or entries, as ‹A› has columns. The entries are closed rational expressions such as `-3/2`, `0.25` or `1/10^15`.
- For a matrix the theorem is `A * B = C`, and for a vector it is `A.mulVec v = w`, Mathlib’s product of a matrix and a vector. The kernel decides it with `decide +kernel`.
- The tactic [[cas]] proves the same equations in a proof.

## Examples

### Basic Examples

The product of two matrices. The swap matrix on the right swaps the columns:

```lean
#cas [dot] (!![1, 2; 3, 4], !![0, 1; 1, 0])
```

---

A matrix times a vector. With all ones, the product is the vector of row sums:

```lean
#cas [dot] (!![1, 2, 3; 4, 5, 6], ![1, 1, 1])
```

### Scope

Shapes $2 \times 3$ and $3 \times 2$ give a $2 \times 2$ product:

```lean
#cas [dot] (!![1, 2, 3; 4, 5, 6], !![1, 0; 0, 1; 1, 1])
```

---

For the dot product of two vectors, write the first one as a row:

```lean
#cas [dot] (!![1, 2], ![3, 4])
```

---

A vector can also be a list:

```lean
#cas [dot] (!![1, 2; 3, 4], [1, 1])
```

### Applications

The product as a theorem, with the axioms its proof uses:

```lean
theorem dot_swap : !![(1 : ℚ), 2; 3, 4] * !![0, 1; 1, 0] = !![2, 1; 4, 3] := by
  cas

#print axioms dot_swap
```

---

A check that $v = (1, 1)$ is an eigenvector with eigenvalue $5$, as [[eigenvectors]] says:

```lean
#cas [dot] (!![4, 1; 2, 3], ![1, 1])
```

---

A check of the inverse that [[inverse]] prints: the product is the identity:

```lean
#cas [dot] (!![1, 2; 3, 4], !![-2, 1; 3/2, -1/2])
```

### Properties and Relations

The product depends on the order. On the left, the swap matrix swaps the rows:

```lean
#cas [dot] (!![0, 1; 1, 0], !![1, 2; 3, 4])
```

---

A matrix times itself is its square, which [[matrixPower]] computes too:

```lean
#cas [dot] (!![1, 1; 1, 0], !![1, 1; 1, 0])
```

```lean
#cas [matrixPower 2] !![1, 1; 1, 0]
```

### Possible Issues

The sizes have to match:

```lean error
#cas [dot] (!![1, 2; 3, 4], ![1, 2, 3])
```

---

The first factor is a matrix. For two vectors, write the first one as a row, as in the Scope example:

```lean error
#cas [dot] (![1, 2], ![3, 4])
```

---

`dot` takes a pair:

```lean error
#cas [dot] !![1, 2; 3, 4]
```

### Neat Examples

The rows of a Hadamard matrix are orthogonal, so $H H^T = 4 I$. This $H$ is symmetric, so $H^T = H$:

```lean
#cas [dot] (!![1, 1, 1, 1; 1, -1, 1, -1; 1, 1, -1, -1; 1, -1, -1, 1], !![1, 1, 1, 1; 1, -1, 1, -1; 1, 1, -1, -1; 1, -1, -1, 1])
```

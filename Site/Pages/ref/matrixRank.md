+++
id = "matrixRank"
kind = "mode"
title = "matrixRank"
summary = "The rank of a matrix of any shape with rational entries, with a theorem about Mathlib’s `Matrix.rank`."
forms = ["CAS.Command.casMatrixRankCommand"]
see_also = ["rowReduce", "nullSpace", "det", "linearSolve"]
tutorials = ["proving"]
+++

::: usage
`#cas [matrixRank] ‹A›`
: gives the rank of the matrix ‹A› with rational entries, and proves `‹A›.rank = r`.
:::

The rank of a matrix is the number of its independent rows, which is also the number of its independent columns. You can use `matrixRank` to check that some vectors are independent, or to count how many conditions in a linear system are really independent. The theorem is about Mathlib’s `Matrix.rank` over $\mathbb{Q}$, and the interesting part is how it is proved. A rank is an equality, so it needs a bound from each side, and the kernel checks one certificate for each. A factorization $A = C F$ through $r$ columns bounds the rank from above, and an $r \times r$ submatrix with nonzero determinant bounds it from below.

## Details and Options

- ‹A› is a matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]` of any shape. The entries are closed rational expressions such as `-3/2`, `0.25` or `1/10^15`.
- The theorem is `A.rank = r` for Mathlib’s `Matrix.rank` over $\mathbb{Q}$. The columns of $C$ are the pivot columns of $A$, and the kernel checks $A = C F$ by evaluation (`Matrix.rank_mul_le_right`). The rows of the minor come from a second elimination, and its nonzero determinant gives the lower bound (`Matrix.rank_of_det_ne_zero`).
- The tactic [[cas]] proves goals `Matrix.rank A = r` for matrix literals over $\mathbb{Q}$, and refuses a wrong $r$.

## Examples

### Basic Examples

The third row of this matrix is twice the second minus the first, so the rank is 2:

```lean
#cas [matrixRank] !![1, 2, 3; 4, 5, 6; 7, 8, 9]
```

---

The second row is twice the first:

```lean
#cas [matrixRank] !![1, 2, 3, 4; 2, 4, 6, 8]
```

### Scope

The zero matrix has rank 0:

```lean
#cas [matrixRank] !![0, 0; 0, 0]
```

---

Entries can be fractions. Here the second row is 6 times the first:

```lean
#cas [matrixRank] !![1/2, 1/3; 3, 2]
```

---

A column, written as a list of rows:

```lean
#cas [matrixRank] [[1], [2], [3]]
```

### Applications

The rank as a theorem, with the axioms its proof uses:

```lean
theorem rank_three : Matrix.rank !![(1 : ℚ), 2, 3; 4, 5, 6; 7, 8, 9] = 2 := by
  cas

#print axioms rank_three
```

---

Three vectors in $\mathbb{Q}^4$ are independent when the matrix with these rows has rank 3:

```lean
#cas [matrixRank] !![1, 0, 1, 0; 0, 1, 0, 1; 1, 1, 0, 0]
```

### Properties and Relations

The rank and the dimension of the null space add up to the number of columns, here $1 + 2 = 3$:

```lean
#cas [matrixRank] !![1, 2, 3; 2, 4, 6]
```

```lean
#cas [nullSpace] !![1, 2, 3; 2, 4, 6]
```

---

A system $A x = b$ has a solution exactly when adding $b$ as a column keeps the rank. Here the rank goes up from 1 to 2, and [[linearSolve]] finds no solution:

```lean
#cas [matrixRank] !![1, 2, 3, 1; 2, 4, 6, 3]
```

```lean
#cas [linearSolve] (!![1, 2, 3; 2, 4, 6], ![1, 3])
```

---

A square matrix below full rank has determinant 0:

```lean
#cas [det] !![1, 2, 3; 4, 5, 6; 7, 8, 9]
```

### Possible Issues

A vector is not a matrix. Write it as a row `!![1, 2, 3]` or a column `!![1; 2; 3]`:

```lean error
#cas [matrixRank] ![1, 2, 3]
```

---

`cas` refuses a wrong rank:

```lean error
example : Matrix.rank !![(1 : ℚ), 2; 2, 4] = 2 := by
  cas
```

### Neat Examples

The $5 \times 5$ matrix with entries $(i + j)^2$ has rank 3, because $(i + j)^2 = i^2 \cdot 1 + 2\, i \cdot j + 1 \cdot j^2$ is a sum of three matrices of rank 1:

```lean
#cas [matrixRank] !![4, 9, 16, 25, 36; 9, 16, 25, 36, 49; 16, 25, 36, 49, 64; 25, 36, 49, 64, 81; 36, 49, 64, 81, 100]
```

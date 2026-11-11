+++
id = "transpose"
kind = "mode"
title = "transpose"
summary = "The transpose of a matrix of any shape with rational entries, with a theorem about Mathlib’s `Matrix.transpose`."
forms = ["CAS.Command.casTransposeCommand"]
see_also = ["dot", "trace", "positiveDefinite", "inverse", "det"]
tutorials = ["proving"]
+++

::: usage
`#cas [transpose] ‹A›`
: gives the transpose of the matrix ‹A› with rational entries, and proves `‹A›.transpose = B`.
:::

`transpose` swaps rows and columns. You need it to form $A^T A$, to test symmetry, or to turn a row vector into a column vector and back. The theorem is `A.transpose = B` for Mathlib’s `Matrix.transpose`, which Mathlib writes `Aᵀ`.

## Details and Options

- ‹A› is a matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]` of any shape. The entries are closed rational expressions such as `-3/2`, `0.25` or `1/10^15`.
- The theorem is `A.transpose = B` for the matrices over $\mathbb{Q}$. The kernel decides it by evaluation (`decide +kernel`).
- The tactic [[cas]] proves the same equations in a proof.

## Examples

### Basic Examples

The transpose of a $2 \times 3$ matrix is $3 \times 2$:

```lean
#cas [transpose] !![1, 2, 3; 4, 5, 6]
```

---

A row becomes a column:

```lean
#cas [transpose] !![1, 2, 3]
```

### Scope

A column becomes a row:

```lean
#cas [transpose] !![1; 2; 3]
```

---

A list of rows works as well as a matrix literal:

```lean
#cas [transpose] [[1, 2], [3, 4]]
```

---

A symmetric matrix is its own transpose:

```lean
#cas [transpose] !![2, 1; 1, 2]
```

### Applications

The transpose as a theorem, with the axioms its proof uses:

```lean
theorem transpose_two : !![(1 : ℚ), 2; 3, 4].transpose = !![1, 3; 2, 4] := by
  cas

#print axioms transpose_two
```

---

The Gram matrix $A^T A$ holds the dot products of the columns of $A$. With the transpose from the first example:

```lean
#cas [dot] (!![1, 4; 2, 5; 3, 6], !![1, 2, 3; 4, 5, 6])
```

---

The rows of $A$ are independent, so $A A^T$ is positive definite:

```lean
#cas [dot] (!![1, 2, 3; 4, 5, 6], !![1, 4; 2, 5; 3, 6])
```

```lean
#cas [positiveDefinite] !![14, 32; 32, 77]
```

### Properties and Relations

Transposing twice gives back the matrix:

```lean
#cas [transpose] !![1, 4; 2, 5; 3, 6]
```

---

A matrix and its transpose have the same determinant. This is the transpose of the matrix with determinant $-3$ on the [[det]] page:

```lean
#cas [det] !![1, 4, 7; 2, 5, 8; 3, 6, 10]
```

### Possible Issues

Every row needs the same number of entries:

```lean error
#cas [transpose] !![1, 2; 3]
```

---

A vector `![1, 2, 3]` is not a matrix. Write a row as `!![1, 2, 3]`, as above:

```lean error
#cas [transpose] ![1, 2, 3]
```

### Neat Examples

The Pythagorean triple $3, 4, 5$ gives a rotation with rational entries. Its transpose is its inverse:

```lean
#cas [transpose] !![3/5, -4/5; 4/5, 3/5]
```

```lean
#cas [inverse] !![3/5, -4/5; 4/5, 3/5]
```

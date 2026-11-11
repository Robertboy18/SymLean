+++
id = "rowReduce"
kind = "mode"
title = "rowReduce"
summary = "The reduced row echelon form of a matrix with rational entries, with the row operations that prove it."
forms = ["CAS.Command.casRowReduceCommand"]
see_also = ["matrixRank", "nullSpace", "linearSolve", "inverse", "det"]
tutorials = ["proving"]
+++

::: usage
`#cas [rowReduce] ‹A›`
: gives the reduced row echelon form `R` of the matrix ‹A› with rational entries and its pivot columns, and proves `E * ‹A› = R ∧ E.det ≠ 0 ∧ R.IsReducedRowEchelon`.
:::

I like row reduction because the reduced form shows so much at once: the pivots, the free columns and the relations between the columns. `rowReduce` gives you that form, with a theorem about Mathlib’s `Matrix.IsReducedRowEchelon`. The theorem gives an invertible matrix $E$ of row operations with $E A = R$, and since the reduced form of a matrix is unique, that pins $R$ down.

## Details and Options

- ‹A› is a matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]` of any shape. The entries are closed rational expressions such as `-3/2`, `0.25` or `1/10^15`.
- The theorem is `E * A = R ∧ E.det ≠ 0 ∧ R.IsReducedRowEchelon` over $\mathbb{Q}$, where $E$ records the row operations of an exact Gauss-Jordan elimination. The kernel evaluates the product and the conditions of the echelon form, and `norm_det` proves `E.det ≠ 0`.
- The report also prints the pivot columns, numbered from 0. Their number is the rank.
- The mode takes one matrix. For a system $A x = b$, reduce the augmented matrix, or solve it with [[linearSolve]].

## Examples

### Basic Examples

The reduced form of a singular $3 \times 3$ matrix. The pivots are in the first two columns, and the last row is zero:

```lean
#cas [rowReduce] !![1, 2, 3; 4, 5, 6; 7, 8, 9]
```

---

The first entry is 0, so the elimination swaps two rows, and $E$ records the swap:

```lean
#cas [rowReduce] !![0, 2, 4, 1; 1, 1, 1, 1; 2, 4, 6, 3]
```

### Scope

A row whose first entry is 1 is already reduced:

```lean
#cas [rowReduce] !![1, 2, 3]
```

---

An invertible matrix reduces to the identity. A list of rows works as well as a matrix literal:

```lean
#cas [rowReduce] [[2, 4], [1, 3]]
```

### Applications

The theorem of the first report contains its matrix $E$. Kernel evaluation, the proof behind the report, checks the product again:

```lean
theorem rowReduce_certificate :
    !![(-(5 / 3) : ℚ), 2 / 3, 0; 4 / 3, -(1 / 3), 0; 1, -2, 1] * !![1, 2, 3; 4, 5, 6; 7, 8, 9] =
      !![1, 0, -1; 0, 1, 2; 0, 0, 0] := by
  decide +kernel

#print axioms rowReduce_certificate
```

---

The system $x + 2 y = 5$, $3 x + 4 y = 6$ as an augmented matrix. The last column of the reduced form is the solution $x = -4$, $y = \tfrac{9}{2}$, which [[linearSolve]] finds too:

```lean
#cas [rowReduce] !![1, 2, 5; 3, 4, 6]
```

```lean
#cas [linearSolve] (!![1, 2; 3, 4], ![5, 6])
```

---

Reducing $[A \mid I]$ gives $[I \mid A^{-1}]$. The right half is the inverse that [[inverse]] prints:

```lean
#cas [rowReduce] !![1, 2, 1, 0; 3, 4, 0, 1]
```

```lean
#cas [inverse] !![1, 2; 3, 4]
```

### Properties and Relations

The number of pivot columns is the rank. The second example has two:

```lean
#cas [matrixRank] !![0, 2, 4, 1; 1, 1, 1, 1; 2, 4, 6, 3]
```

---

Each column without a pivot gives a vector of the null space. For the first example the reduced form says $x_1 = x_3$ and $x_2 = -2 x_3$:

```lean
#cas [nullSpace] !![1, 2, 3; 4, 5, 6; 7, 8, 9]
```

### Possible Issues

The mode takes one matrix, not a system. Reduce the augmented matrix as above, or use [[linearSolve]]:

```lean error
#cas [rowReduce] (!![1, 2; 3, 4], ![5, 6])
```

### Neat Examples

Dürer’s magic square from *Melencolia I* is singular. The reduced form says that its last column is $c_1 - 3 c_2 + 3 c_3$:

```lean
#cas [rowReduce] !![16, 3, 2, 13; 5, 10, 11, 8; 9, 6, 7, 12; 4, 15, 14, 1]
```

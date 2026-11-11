+++
id = "nullSpace"
kind = "mode"
title = "nullSpace"
summary = "A basis of the null space of a matrix with rational entries, with a theorem that it spans every solution."
forms = ["CAS.Command.casNullSpaceCommand"]
see_also = ["linearSolve", "matrixRank", "rowReduce", "eigenvectors"]
tutorials = ["proving"]
+++

::: usage
`#cas [nullSpace] ‹A›`
: gives a basis of the null space of the matrix ‹A› with rational entries, the vectors $x$ with $A x = 0$, and proves that it is a basis.
:::

`nullSpace` gives a basis for the solutions of $Ax=0$, and applied to $A-\lambda I$ it gives an eigenspace. The theorem says three things about the printed vectors $V_i$, over $\mathbb{Q}$: each one solves $A x = 0$, they are linearly independent, and every solution is a combination of them. You could check the first by multiplying. The other two are what make the list a basis and not only a list of solutions, and they are the ones I want a proof of.

## Details and Options

- ‹A› is a matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]` of any shape. The entries are closed rational expressions such as `-3/2`, `0.25` or `1/10^15`.
- The theorem is `A.mulVec (V i) = 0` for each $i$, `LinearIndependent ℚ V`, and `∀ x, A.mulVec x = 0 → ∃ c, x = ∑ i, c i • V i`. When only the zero vector solves the equation, the output is `[] (only the zero vector)` and the theorem is `∀ x, A.mulVec x = 0 → x = 0`.
- The vectors come from the free columns of the reduced row echelon form: each has a 1 at its own free column and 0 at the other free ones. The printed dimension is the number of columns minus the rank.
- `linarith` proves the statement about every $x$ from the coordinates of `A.mulVec x`, and the kernel evaluates the rest.
- The tactic [[cas]] proves goals `A.mulVec v = 0` for literals over $\mathbb{Q}$.

## Examples

### Basic Examples

The two rows say the same thing, $x + 2 y + 3 z = 0$, so the solutions form a plane:

```lean
#cas [nullSpace] !![1, 2, 3; 2, 4, 6]
```

---

Only the zero vector solves $A x = 0$ for an invertible $A$:

```lean
#cas [nullSpace] !![1, 2; 3, 4]
```

### Scope

A single nonzero column:

```lean
#cas [nullSpace] !![1; 2; 3]
```

---

A singular square matrix has a null space of dimension at least 1:

```lean
#cas [nullSpace] !![1, 2, 3; 4, 5, 6; 7, 8, 9]
```

---

A row with fractions, written as a list of rows:

```lean
#cas [nullSpace] [[1/2, 1/3, 1/6]]
```

### Applications

A vector of the null space as a theorem, with the axioms its proof uses:

```lean
theorem nullSpace_vector : !![(1 : ℚ), 2, 3; 2, 4, 6].mulVec ![-2, 1, 0] = 0 := by
  cas

#print axioms nullSpace_vector
```

---

The eigenvectors of $\begin{pmatrix} 4 & 1 \\ 2 & 3 \end{pmatrix}$ for the eigenvalue 2 form the null space of $A - 2 I$. [[eigenvectors]] gives the same vector:

```lean
#cas [nullSpace] !![2, 1; 2, 1]
```

```lean
#cas [eigenvectors] !![4, 1; 2, 3]
```

---

To balance $a\,\mathrm{CH_4} + b\,\mathrm{O_2} \to c\,\mathrm{CO_2} + d\,\mathrm{H_2O}$, I count each element on both sides: carbon gives $a = c$, hydrogen $4 a = 2 d$ and oxygen $2 b = 2 c + d$. Twice the null vector is the balanced equation $\mathrm{CH_4} + 2\,\mathrm{O_2} \to \mathrm{CO_2} + 2\,\mathrm{H_2O}$:

```lean
#cas [nullSpace] !![1, 0, -1, 0; 4, 0, 0, -2; 0, 2, -2, -1]
```

### Properties and Relations

The dimension is the number of columns minus the rank. For the singular matrix in Scope it is $3 - 2 = 1$:

```lean
#cas [matrixRank] !![1, 2, 3; 4, 5, 6; 7, 8, 9]
```

---

Every solution of $A x = b$ is one solution plus a vector of the null space. [[linearSolve]] prints the same basis:

```lean
#cas [linearSolve] (!![1, 2, 3; 2, 4, 6], ![1, 2])
```

### Possible Issues

The mode takes the matrix alone. For a right side, use [[linearSolve]]:

```lean error
#cas [nullSpace] (!![1, 2; 3, 4], ![0, 0])
```

### Neat Examples

The rows hold the values of $1$, $n$ and $n^2$ at $n = 1, 2, 3, 4$. The null space is spanned by the third difference $(-1, 3, -3, 1)$, so $-p(1) + 3 p(2) - 3 p(3) + p(4) = 0$ for every polynomial $p$ of degree at most 2:

```lean
#cas [nullSpace] !![1, 1, 1, 1; 1, 2, 3, 4; 1, 4, 9, 16]
```

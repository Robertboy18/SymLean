+++
id = "inverse"
kind = "mode"
title = "inverse"
summary = "The inverse of a square matrix with rational entries, or a proof that its determinant is 0."
forms = ["CAS.Command.casInverseCommand"]
see_also = ["det", "linearSolve", "dot", "matrixPower", "rowReduce"]
tutorials = ["proving"]
+++

::: usage
`#cas [inverse] ‹A›`
: gives the inverse of the square matrix ‹A› with rational entries and proves `‹A›⁻¹ = B`, or proves `‹A›.det = 0` when ‹A› has no inverse.
:::

`inverse` computes the entries of $A^{-1}$ over $\mathbb{Q}$. The theorem is about Mathlib’s `A⁻¹`, and here a Mathlib convention matters. That inverse is total, and for a singular matrix it is the zero matrix. A statement `A⁻¹ = 0` would then be true and still tell you nothing about an inverse, which is the kind of statement I don’t want a tool to print. So for a singular matrix the report proves `A.det = 0` instead.

## Details and Options

- ‹A› is a square matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`. The entries are closed rational expressions such as `-3/2`, `0.25` or `1/10^15`.
- For an invertible ‹A› the theorem is `A⁻¹ = B` for Mathlib’s inverse over $\mathbb{Q}$. The kernel evaluates the product $B A$ and checks that it is the identity, and `Matrix.inv_eq_left_inv` turns that into the inverse.
- For a singular ‹A› the output is “no inverse” and the theorem is `A.det = 0`, proved with Mathlib’s `norm_det`.
- The tactic [[cas]] proves goals `A⁻¹ = B` for matrix literals over $\mathbb{Q}$, and refuses a wrong $B$.

## Examples

### Basic Examples

The inverse of a $2 \times 2$ matrix:

```lean
#cas [inverse] !![1, 2; 3, 4]
```

---

This $3 \times 3$ matrix has determinant 1, so its inverse has integer entries:

```lean
#cas [inverse] !![1, 2, 3; 0, 1, 4; 5, 6, 0]
```

### Scope

A $1 \times 1$ matrix:

```lean
#cas [inverse] !![5]
```

---

Entries can be fractions:

```lean
#cas [inverse] !![1/2, 1; 3, 4]
```

---

A singular matrix has no inverse. The report proves that its determinant is 0:

```lean
#cas [inverse] !![1, 2; 2, 4]
```

### Applications

The inverse as a theorem, with the axioms its proof uses:

```lean
theorem inverse_two : (!![(1 : ℚ), 2; 3, 4])⁻¹ = !![-2, 1; 3 / 2, -1 / 2] := by
  cas

#print axioms inverse_two
```

---

The inverse solves $A x = b$ as $x = A^{-1} b$. Multiplying by the inverse gives the same solution that [[linearSolve]] finds:

```lean
#cas [dot] (!![-2, 1; 3/2, -1/2], ![5, 6])
```

```lean
#cas [linearSolve] (!![1, 2; 3, 4], ![5, 6])
```

### Properties and Relations

The product of the inverse and the matrix is the identity:

```lean
#cas [dot] (!![-2, 1; 3/2, -1/2], !![1, 2; 3, 4])
```

---

The determinant of $A^{-1}$ is $1/\det A$. Here $\det A = -2$:

```lean
#cas [det] !![-2, 1; 3/2, -1/2]
```

---

Mathlib’s inverse of a singular matrix is the zero matrix, a fact any proof can use:

```lean
example : (!![(1 : ℚ), 2; 2, 4])⁻¹ = 0 :=
  Matrix.nonsing_inv_apply_not_isUnit _ (by simp only [norm_det]; norm_num)
```

### Possible Issues

The matrix has to be square:

```lean error
#cas [inverse] !![1, 2, 3; 4, 5, 6]
```

---

Every row needs the same number of entries:

```lean error
#cas [inverse] !![1, 2; 3]
```

---

`cas` refuses a wrong inverse. Here one sign is wrong:

```lean error
example : (!![(1 : ℚ), 2; 3, 4])⁻¹ = !![-2, 1; 3 / 2, 1 / 2] := by
  cas
```

### Neat Examples

The Hilbert matrix has fractions as entries, and its inverse has integers:

```lean
#cas [inverse] !![1, 1/2, 1/3; 1/2, 1/3, 1/4; 1/3, 1/4, 1/5]
```

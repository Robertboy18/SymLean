+++
id = "det"
kind = "mode"
title = "det"
summary = "The determinant of a square matrix with rational entries, with a theorem about Mathlib’s `Matrix.det`."
forms = ["CAS.Command.casDetCommand"]
see_also = ["inverse", "characteristicPolynomial", "matrixRank", "cas", "hex"]
tutorials = ["first-hour", "proving"]
+++

::: usage
`#cas [det] ‹A›`
: gives the determinant of the square matrix ‹A› with rational entries, and proves `‹A›.det = d` for Mathlib’s `Matrix.det`.
:::

`det` evaluates the determinant of a matrix over $\mathbb{Q}$. You write the matrix as a Mathlib literal, the report prints the number, and the theorem under it is `A.det = d` for Mathlib’s `Matrix.det` over $\mathbb{Q}$. Because it is a statement about the same matrix you would write in a proof, it can go straight into one.

## Details and Options

- ‹A› is a square matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`. The entries are closed rational expressions such as `-3/2`, `0.25` or `1/10^15`.
- The theorem is `A.det = d` for ‹A› as a matrix over $\mathbb{Q}$. Mathlib’s `norm_det` simproc computes the determinant of the literal together with a proof, and Lean’s kernel checks that proof.
- With Hex, the value comes from Hex’s fraction-free (Bareiss) elimination, and the kernel checks its certificate by evaluation instead of replaying the elimination. The theorem is the same, and the output line says “determinant (Hex’s Bareiss certificate)”. To turn it on, build with `lake -R -Khex=on build CASHex` and add `import CASHex.LinearAlgebra`. The [Hex guide](guide:hex) has the details.
- The tactic [[cas]] proves goals `Matrix.det A = d` for matrix literals, also over $\mathbb{Z}$ and $\mathbb{R}$, and proves a determinant with variables as a polynomial identity. A wrong value is refused, and the message shows the value it found.

## Examples

### Basic Examples

The determinant of a $3 \times 3$ matrix:

```lean
#cas [det] !![1, 2, 3; 4, 5, 6; 7, 8, 10]
```

---

The entries can be fractions:

```lean
#cas [det] !![1/2, 1; 3, 4]
```

### Scope

A $5 \times 5$ matrix, tridiagonal except for its two corners:

```lean
#cas [det] !![2, -1, 0, 0, 1; -1, 2, -1, 0, 0; 0, -1, 2, -1, 0; 0, 0, -1, 2, -1; 1, 0, 0, -1, 2]
```

---

A list of rows works as well as a matrix literal:

```lean
#cas [det] [[1, 2], [3, 4]]
```

---

The smallest case, a $1 \times 1$ matrix:

```lean
#cas [det] !![0]
```

### Applications

The determinant as a theorem, with the axioms its proof uses:

```lean
theorem det_three : Matrix.det !![(1 : ℚ), 2, 3; 4, 5, 6; 7, 8, 10] = -3 := by
  cas

#print axioms det_three
```

---

In a proof, `cas` also evaluates a determinant with variables. The Vandermonde determinant becomes a polynomial identity:

```lean
example (a b c : ℝ) :
    Matrix.det !![1, a, a ^ 2; 1, b, b ^ 2; 1, c, c ^ 2] = (b - a) * (c - a) * (c - b) := by
  cas
```

---

A $5 \times 5$ determinant over the integers:

```lean
example : Matrix.det !![(-1 : ℤ), -1, -2, 3, 0; -2, 4, 0, -5, 1; -4, 1, -2, -1, 0;
    -1, 4, -1, 4, 0; -5, 4, 1, -5, -3] = 228 := by
  cas
```

### Properties and Relations

The constant term of the characteristic polynomial $\det(x I - A)$ is $(-1)^n \det A$. For the first matrix on this page that is $(-1)^3 \cdot (-3) = 3$:

```lean
#cas [characteristicPolynomial] !![1, 2, 3; 4, 5, 6; 7, 8, 10]
```

---

A matrix with determinant 0 has no inverse, and [[inverse]] proves that its determinant is 0:

```lean
#cas [inverse] !![1, 2; 2, 4]
```

---

With Hex the same determinant comes from Hex’s Bareiss elimination. The site is built without Hex, so this is the report pinned in the Hex examples:

```lean quote=CASHex/Examples.lean
#cas [det] !![1, 2, 3; 4, 5, 6; 7, 8, 10]
```

### Possible Issues

The matrix has to be square:

```lean error
#cas [det] !![1, 2, 3; 4, 5, 6]
```

---

The entries have to be rational numbers. For a determinant with variables, state it as a goal for [[cas]], as in the Vandermonde example:

```lean error
#cas [det] !![x, 1; 1, 1]
```

---

`cas` refuses a wrong value. The message shows the goal after the determinant was evaluated:

```lean error
example : Matrix.det !![(2 : ℤ), 1, 1; 1, 2, 1; 1, 1, 2] = 5 := by
  cas
```

### Neat Examples

The $3 \times 3$ Hilbert matrix, with entries $1/(i + j - 1)$, has determinant $1/2160$:

```lean
#cas [det] !![1, 1/2, 1/3; 1/2, 1/3, 1/4; 1/3, 1/4, 1/5]
```

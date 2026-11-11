+++
id = "characteristicPolynomial"
kind = "mode"
title = "characteristicPolynomial"
summary = "The characteristic polynomial $\\det(x I - A)$ of a square matrix with rational entries, with a theorem about Mathlib’s `Matrix.charpoly`."
forms = ["CAS.Command.casCharacteristicPolynomialCommand"]
see_also = ["eigenvalues", "eigenvectors", "det", "trace", "matrixPower"]
tutorials = ["proving"]
+++

::: usage
`#cas [characteristicPolynomial] ‹A›`
: gives the characteristic polynomial $\det(x I - A)$ of the square matrix ‹A› with rational entries, and proves `‹A›.charpoly = p` in `ℚ[X]`.
:::

The characteristic polynomial holds a lot of a matrix at once: its roots are the eigenvalues, and the trace and the determinant can be read off its coefficients. It also appears in the Cayley-Hamilton theorem and in formulas for linear recurrences. `characteristicPolynomial` computes it, with a theorem about Mathlib’s `Matrix.charpoly`, the monic polynomial $\det(X I - A)$. If you are coming from Mathematica, watch the sign. Mathematica’s `CharacteristicPolynomial` is $\det(A - x I)$, which is $(-1)^n$ times this one.

## Details and Options

- ‹A› is a square matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`. The entries are closed rational expressions such as `-3/2`, `0.25` or `1/10^15`.
- The theorem is `A.charpoly = p` in `ℚ[X]`, with `p` written in `Polynomial.X`. The proof compares both sides at every point $t$ (`Polynomial.funext`): `Matrix.eval_charpoly` turns the value of `A.charpoly` at $t$ into the determinant of $t I - A$, which `norm_det` evaluates.
- For an $n \times n$ matrix the polynomial is monic of degree $n$. The coefficient of $x^{n-1}$ is $-\operatorname{tr} A$ and the constant term is $(-1)^n \det A$.
- The tactic [[cas]] proves goals `Matrix.charpoly A = p` for matrix literals over $\mathbb{Q}$.

## Examples

### Basic Examples

For a $2 \times 2$ matrix the polynomial is $x^2 - (\operatorname{tr} A)\, x + \det A$:

```lean
#cas [characteristicPolynomial] !![1, 2; 3, 4]
```

---

A $3 \times 3$ matrix:

```lean
#cas [characteristicPolynomial] !![1, 2, 3; 4, 5, 6; 7, 8, 10]
```

### Scope

The matrix of second differences of size 4:

```lean
#cas [characteristicPolynomial] !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2]
```

---

Fractions give rational coefficients:

```lean
#cas [characteristicPolynomial] !![1/2, 1/3; 1/4, 1/5]
```

---

A rotation by a right angle, written as a list of rows. Its polynomial $x^2 + 1$ has no real roots:

```lean
#cas [characteristicPolynomial] [[0, -1], [1, 0]]
```

### Applications

The polynomial as a theorem, with the axioms its proof uses:

```lean
theorem charpoly_two :
    Matrix.charpoly !![(1 : ℚ), 2; 3, 4] = Polynomial.X ^ 2 - 5 * Polynomial.X - 2 := by
  cas

#print axioms charpoly_two
```

---

With the theorem above, Mathlib’s Cayley-Hamilton theorem `Matrix.aeval_self_charpoly` says that the matrix is a root of the printed polynomial, $A^2 - 5 A - 2 I = 0$:

```lean
example : Polynomial.aeval !![(1 : ℚ), 2; 3, 4]
    (Polynomial.X ^ 2 - 5 * Polynomial.X - 2 : Polynomial ℚ) = 0 := by
  rw [← charpoly_two]
  exact Matrix.aeval_self_charpoly _
```

---

Every monic polynomial is the characteristic polynomial of its companion matrix. This one belongs to $x^3 - 2$:

```lean
#cas [characteristicPolynomial] !![0, 0, 2; 1, 0, 0; 0, 1, 0]
```

### Properties and Relations

The roots of the polynomial are the eigenvalues. For the first example they are $\frac{5 \pm \sqrt{33}}{2}$:

```lean
#cas [eigenvalues] !![1, 2; 3, 4]
```

---

The trace and the determinant are coefficients. For the second example the trace is 16 and the determinant is $-3$, so the polynomial is $x^3 - 16 x^2 + \dots + 3$:

```lean
#cas [trace] !![1, 2, 3; 4, 5, 6; 7, 8, 10]
```

```lean
#cas [det] !![1, 2, 3; 4, 5, 6; 7, 8, 10]
```

---

A matrix and its transpose have the same characteristic polynomial:

```lean
#cas [characteristicPolynomial] !![1, 3; 2, 4]
```

### Possible Issues

The matrix has to be square:

```lean error
#cas [characteristicPolynomial] !![1, 2, 3; 4, 5, 6]
```

### Neat Examples

The companion matrix of $x^4 - 10 x^2 + 1$, whose roots are the four numbers $\pm\sqrt{2} \pm \sqrt{3}$. Their eigenvalue report is on the [[eigenvalues]] page:

```lean
#cas [characteristicPolynomial] !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 10; 0, 0, 1, 0]
```

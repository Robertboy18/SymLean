+++
id = "matrixPower"
kind = "mode"
title = "matrixPower"
summary = "The power $A^k$ of a square matrix with rational entries, for $k$ up to 1000, with a theorem that it is right."
forms = ["CAS.Command.casMatrixPowerCommand"]
see_also = ["dot", "inverse", "eigenvalues", "characteristicPolynomial", "fibonacci"]
tutorials = ["proving"]
+++

::: usage
`#cas [matrixPower ‹k›] ‹A›`
: gives the power $A^k$ of the square matrix ‹A› with rational entries, for a natural number ‹k› up to 1000, and proves `‹A› ^ ‹k› = B`.
:::

A linear recurrence or a Markov chain takes the same linear step over and over, so $k$ steps of it are the $k$-th power of a matrix, and `matrixPower` computes that power for the $k$ you choose. A good first example is $\begin{pmatrix} 1 & 1 \\ 1 & 0 \end{pmatrix}$, whose powers hold the Fibonacci numbers. The theorem `A ^ k = B` is about Mathlib’s power in the ring of matrices over $\mathbb{Q}$, and the kernel decides it by evaluating the product.

## Details and Options

- ‹k› is a natural number literal with $k \le 1000$. ‹A› is a square matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`, with closed rational entries such as `-3/2`, `0.25` or `1/10^15`.
- The theorem is `A ^ k = B` for the matrices over $\mathbb{Q}$, decided by kernel evaluation (`decide +kernel`).
- In a proof, `decide +kernel` proves the printed equation. A larger exponent splits with `pow_add` and `pow_mul` into powers that the mode computes.
- The exponent is a natural number. For a negative power, take a power of the matrix that [[inverse]] prints.

## Examples

### Basic Examples

The tenth power of the Fibonacci matrix:

```lean
#cas [matrixPower 10] !![1, 1; 1, 0]
```

---

A Jordan block with fractions. The corner entry of $\begin{pmatrix} \lambda & 1 \\ 0 & \lambda \end{pmatrix}^k$ is $k \lambda^{k-1}$, here $3 \cdot \tfrac{1}{4} = \tfrac{3}{4}$:

```lean
#cas [matrixPower 3] !![1/2, 1; 0, 1/2]
```

### Scope

A rotation by a right angle has order 4:

```lean
#cas [matrixPower 4] !![0, -1; 1, 0]
```

---

A nilpotent matrix:

```lean
#cas [matrixPower 2] !![0, 1; 0, 0]
```

---

The zeroth power is the identity:

```lean
#cas [matrixPower 0] !![1, 2; 3, 4]
```

### Applications

The power as a theorem. Kernel evaluation, the proof behind the report, proves it directly:

```lean
theorem fibonacci_matrix : !![(1 : ℚ), 1; 1, 0] ^ 10 = !![89, 55; 55, 34] := by
  decide +kernel

#print axioms fibonacci_matrix
```

---

Twenty steps of the Fibonacci recurrence. The corner entry is $F_{20}$, which [[fibonacci]] gives too:

```lean
#cas [matrixPower 20] !![1, 1; 1, 0]
```

```lean
#cas (fibonacci 20)
```

---

A Markov chain with two states. Row $i$ of $P^3$ is the distribution after three steps from state $i$:

```lean
#cas [matrixPower 3] !![1/2, 1/2; 1/4, 3/4]
```

### Properties and Relations

The characteristic polynomial of this matrix is $x^3 - 2$, so by the Cayley-Hamilton theorem $A^3 = 2 I$:

```lean
#cas [characteristicPolynomial] !![0, 0, 2; 1, 0, 0; 0, 1, 0]
```

```lean
#cas [matrixPower 3] !![0, 0, 2; 1, 0, 0; 0, 1, 0]
```

---

The eigenvalues of $A^2$ are the squares of the eigenvalues of $A$. Those of $A$ are $1$, $2$ and $11$ (see [[eigenvalues]]):

```lean
#cas [matrixPower 2] !![2, 0, 0; 0, 3, 4; 0, 4, 9]
```

```lean
#cas [eigenvalues] !![4, 0, 0; 0, 25, 48; 0, 48, 97]
```

### Possible Issues

The kernel evaluates the power, and the exponent is at most 1000:

```lean error
#cas [matrixPower 1001] !![1, 1; 1, 0]
```

---

The matrix has to be square:

```lean error
#cas [matrixPower 2] !![1, 2, 3; 4, 5, 6]
```

### Neat Examples

The powers of $\begin{pmatrix} 3 & 4 \\ 2 & 3 \end{pmatrix}$ solve Pell’s equation $x^2 - 2 y^2 = 1$: the first column of each power is a solution. Here it is $(3363, 2378)$:

```lean
#cas [matrixPower 5] !![3, 4; 2, 3]
```

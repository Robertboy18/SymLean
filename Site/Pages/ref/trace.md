+++
id = "trace"
kind = "mode"
title = "trace"
summary = "The trace of a square matrix with rational entries, with a theorem about Mathlib’s `Matrix.trace`."
forms = ["CAS.Command.casTraceCommand"]
see_also = ["det", "characteristicPolynomial", "eigenvalues", "transpose", "matrixPower"]
tutorials = ["proving"]
+++

::: usage
`#cas [trace] ‹A›`
: gives the trace of the square matrix ‹A› with rational entries, the sum of its diagonal entries, and proves `‹A›.trace = t`.
:::

The trace is the sum of the diagonal entries. It is also the sum of the eigenvalues, and minus the second coefficient of the characteristic polynomial, so it makes a quick check on both. `trace` prints it with a theorem about Mathlib’s `Matrix.trace`.

## Details and Options

- ‹A› is a square matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`. The entries are closed rational expressions such as `-3/2`, `0.25` or `1/10^15`.
- The theorem is `A.trace = t` for ‹A› as a matrix over $\mathbb{Q}$. The kernel decides it by evaluation (`decide +kernel`).
- The tactic [[cas]] proves the same equations in a proof.

## Examples

### Basic Examples

The trace of a $2 \times 2$ matrix:

```lean
#cas [trace] !![1, 2; 3, 4]
```

---

Fractions on the diagonal:

```lean
#cas [trace] !![1/2, 7; 0, 1/3]
```

### Scope

A list of rows works as well as a matrix literal:

```lean
#cas [trace] [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
```

---

The trace of the identity is its size:

```lean
#cas [trace] !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
```

### Applications

The trace as a theorem, with the axioms its proof uses:

```lean
theorem trace_two : Matrix.trace !![(1 : ℚ), 2; 3, 4] = 5 := by
  cas

#print axioms trace_two
```

### Properties and Relations

The trace is the sum of the eigenvalues. Here they are $1$, $2$ and $11$, and the trace is $14$:

```lean
#cas [eigenvalues] !![2, 0, 0; 0, 3, 4; 0, 4, 9]
```

```lean
#cas [trace] !![2, 0, 0; 0, 3, 4; 0, 4, 9]
```

---

The coefficient of $x^{n-1}$ in the characteristic polynomial is minus the trace:

```lean
#cas [characteristicPolynomial] !![1, 2; 3, 4]
```

---

The eigenvalues of the same matrix are irrational, and they add up to $5$:

```lean
#cas [eigenvalues] !![1, 2; 3, 4]
```

### Possible Issues

The matrix has to be square:

```lean error
#cas [trace] !![1, 2, 3; 4, 5, 6]
```

---

The entries have to be rational numbers:

```lean error
#cas [trace] !![a, b; c, d]
```

For a $2 \times 2$ literal with variables, Mathlib has the formula:

```lean
example (a b c d : ℝ) : Matrix.trace !![a, b; c, d] = a + d :=
  Matrix.trace_fin_two_of a b c d
```

### Neat Examples

The powers of $\begin{pmatrix} 1 & 1 \\ 1 & 0 \end{pmatrix}$ hold the Fibonacci numbers, and their traces are the Lucas numbers. The trace of the tenth power is $L_{10} = 123$:

```lean
#cas [matrixPower 10] !![1, 1; 1, 0]
```

```lean
#cas [trace] !![89, 55; 55, 34]
```

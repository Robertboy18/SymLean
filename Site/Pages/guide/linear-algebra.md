+++
id = "linear-algebra"
kind = "guide"
title = "Linear algebra"
summary = "Determinants, inverses, ranks, linear systems and eigenvalues of matrices with rational entries, each with a theorem about Mathlib’s `Matrix`."
related_guides = ["numerics", "polynomials", "equations", "hex", "tactics"]
tutorials = ["first-hour", "proving"]
+++

You write matrices with rational entries in Mathlib’s own notation, such as `!![1, 2; 3, 4]` and `![5, 6]`. The arithmetic is exact, and every answer is a theorem about Mathlib’s definitions: `Matrix.det`, the inverse `A⁻¹`, `Matrix.rank` and `Matrix.charpoly`. For me that’s the point of this part, because the statement is about the same matrix I would write in a proof. A linear system, a null space or an eigenspace comes with the theorem that there are no other solutions, and an irrational eigenvalue is an algebraic number, in closed form or named by an interval.

::: commands
### Products and powers
- dot
- matrixPower
- transpose
- trace
### Determinants and inverses
- det
- inverse
### Rank, null spaces and linear systems
- matrixRank
- rowReduce
- nullSpace
- linearSolve
### Eigenvalues
- characteristicPolynomial
- eigenvalues
- eigenvectors
### Symmetric matrices
- positiveDefinite
- eigenvalueBounds
:::

The matrix of the Fibonacci recurrence has the golden ratio and its conjugate as eigenvalues. The theorem is about Mathlib’s `spectrum ℝ`, and it also gives the roots of the characteristic polynomial with their multiplicities, so the two numbers are the whole spectrum:

```lean
#cas [eigenvalues] !![0, 1; 1, 1]
```

In a proof, the tactic [[cas]] proves statements about matrices written in Mathlib’s notation, also with variables among the entries. Here it is the Vandermonde determinant:

```lean
example (a b c : ℝ) :
    Matrix.det !![1, a, a ^ 2; 1, b, b ^ 2; 1, c, c ^ 2] = (b - a) * (c - a) * (c - b) := by
  cas
```

One thing to watch is that Mathlib’s inverse is total. For a singular matrix `A⁻¹` is the zero matrix, so a theorem `A⁻¹ = 0` would be true and tell you nothing about an inverse. That’s why `inverse` proves `A.det = 0` for a singular matrix instead.

The `#cas` modes take rational entries, so a determinant with variables, like the one above, goes in as a goal for `cas`. `eigenvalueBounds` takes symmetric matrices only, and `matrixPower` takes exponents up to 1000. `eigenvalues` and `eigenvectors` put no limit on the size of the matrix, but their proofs run with `maxHeartbeats` raised to at least one million, so a large matrix can take a long time. Without Hex, a factor of the characteristic polynomial of degree three or more comes from a squarefree decomposition and need not be irreducible. With the optional [Hex library](guide:hex), the theorem adds irreducibility for every factor that Hex certifies.

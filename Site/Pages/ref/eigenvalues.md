+++
id = "eigenvalues"
kind = "mode"
title = "eigenvalues"
summary = "The exact eigenvalues of a square matrix with rational entries, with their multiplicities and a theorem that there are no others."
forms = ["CAS.Command.casEigenvaluesCommand"]
see_also = ["characteristicPolynomial", "eigenvectors", "eigenvalueBounds", "roots", "hex"]
tutorials = ["proving"]
+++

::: usage
`#cas [eigenvalues] ‹A›`
: gives the eigenvalues of the square matrix ‹A› with rational entries, each as often as its algebraic multiplicity, and proves that there are no others.
:::

`eigenvalues` gives you the eigenvalues exactly. They come back as rational numbers, quadratic surds such as $\tfrac{1}{2} + \tfrac{\sqrt{5}}{2}$, complex numbers, or roots of a factor of higher degree, and a root of that last kind is named by an interval that contains it. I reach for this mode when the eigenvalues have to go into a proof, because the theorem doesn’t stop at saying that each number is an eigenvalue. It says the list is the whole spectrum. When every eigenvalue is rational, that theorem is a factorization of the characteristic polynomial over $\mathbb{Q}$. Otherwise it is a statement about Mathlib’s `spectrum` over $\mathbb{R}$ or $\mathbb{C}$, together with the roots of `A.charpoly` and their multiplicities.

## Details and Options

- ‹A› is a square matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`. The entries are closed rational expressions such as `-3/2`, `0.25` or `1/10^15`.
- When every eigenvalue is rational, the theorem is `A.charpoly = (X - λ₁) ^ m₁ * ⋯ * (X - λₖ) ^ mₖ` in `ℚ[X]`.
- Otherwise let $M$ be the matrix with the entries of ‹A› over $K = \mathbb{R}$ when every eigenvalue is real, and over $K = \mathbb{C}$ when one is not. The theorem is `spectrum K M = {μ₁, …, μₛ}`, each eigenvalue once, and `M.charpoly.roots = {μ₁, …}`, the multiset with the multiplicities.
- A root of a factor $R$ of degree 3 or more is named in the theorem by `let r₁ := CAS.AlgRoot.real R lo hi`, with `r₁ ∈ Set.Ioo lo hi` and $R(r_1) = 0$, or by `CAS.AlgRoot.complex R u v ρ`, with intervals for its real and imaginary parts. The report prints the intervals.
- The kernel checks that the factors multiply to the characteristic polynomial (`CAS.Analysis.Matrix.eigenCheck`).
- Without Hex, a factor of higher degree comes from the squarefree decomposition of the characteristic polynomial and need not be irreducible, and each of its roots gets its own interval. With the optional [Hex library](guide:hex) (`import CASHex.Factor`), the factors are irreducible: the theorem adds `Irreducible R` for each factor $R$ whose irreducibility Hex certifies, and the report lists the others.
- There is no limit on the size of ‹A›. The search for the eigenvalues runs before the proof, and the proof runs with `maxHeartbeats` raised to at least one million, so a large matrix can take long.

## Examples

### Basic Examples

Rational eigenvalues. The theorem factors the characteristic polynomial over $\mathbb{Q}$:

```lean
#cas [eigenvalues] !![2, 0, 0; 0, 3, 4; 0, 4, 9]
```

---

The golden ratio and its conjugate. The theorem is about `spectrum ℝ`:

```lean
#cas [eigenvalues] !![0, 1; 1, 1]
```

### Scope

A rotation by a right angle has the eigenvalues $\pm i$, and the theorem is about `spectrum ℂ`:

```lean
#cas [eigenvalues] !![0, -1; 1, 0]
```

---

Complex eigenvalues with a real part:

```lean
#cas [eigenvalues] !![1, 2; -2, 1]
```

---

A real and two complex eigenvalues together:

```lean
#cas [eigenvalues] !![2, 0, 0; 0, 0, -1; 0, 1, 0]
```

---

Each eigenvalue appears as often as its multiplicity:

```lean
#cas [eigenvalues] !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]
```

---

The roots of $x^3 - 2$ are named by intervals: the real root $\sqrt[3]{2}$ and two complex roots $\alpha \pm i \beta$:

```lean
#cas [eigenvalues] !![0, 0, 2; 1, 0, 0; 0, 1, 0]
```

---

With Hex, the theorem for the same matrix also says that $x^3 - 2$ is irreducible over $\mathbb{Q}$. This part of the theorem is the one pinned in the quoted file:

```lean quote=CASHex/Examples.lean
#cas [eigenvalues] !![0, 0, 2; 1, 0, 0; 0, 1, 0]
```

### Applications

A proof can take the printed theorem as a hypothesis and read an eigenvalue off it, here the golden ratio:

```lean
theorem golden_ratio_mem_spectrum
    (h : spectrum ℝ !![(0 : ℝ), 1; 1, 1] = {1 / 2 - 1 / 2 * √5, 1 / 2 + 1 / 2 * √5}) :
    1 / 2 + 1 / 2 * √5 ∈ spectrum ℝ !![(0 : ℝ), 1; 1, 1] := by
  rw [h]
  exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
```

---

A transition matrix of a Markov chain has the eigenvalue 1. The other eigenvalue, $\tfrac{1}{4}$, says how fast the chain forgets where it started:

```lean
#cas [eigenvalues] !![1/2, 1/2; 1/4, 3/4]
```

### Properties and Relations

The eigenvalues are the roots of the characteristic polynomial. Here their sum is the trace 5 and their product is the determinant $-2$:

```lean
#cas [eigenvalues] !![1, 2; 3, 4]
```

```lean
#cas [characteristicPolynomial] !![1, 2; 3, 4]
```

---

For a symmetric matrix, [[eigenvalueBounds]] bounds the smallest and the largest eigenvalue in decimals. Here they are $3 \mp \sqrt{3}$:

```lean
#cas [eigenvalues] !![4, 1, 0; 1, 3, 1; 0, 1, 2]
```

```lean
#cas [eigenvalueBounds] !![4, 1, 0; 1, 3, 1; 0, 1, 2]
```

### Possible Issues

The matrix has to be square. [[matrixRank]] and [[nullSpace]] describe a matrix of any shape:

```lean error
#cas [eigenvalues] !![1, 2, 3; 4, 5, 6]
```

### Neat Examples

The companion matrix of $x^4 - 10 x^2 + 1$ has the eigenvalues $\pm\sqrt{2} \pm \sqrt{3}$, named here by intervals. The polynomial is irreducible over $\mathbb{Q}$, but it is outside the languages of Hex’s certificates, so the report lists it as a factor without a Hex irreducibility certificate:

```lean quote=CASHex/Examples.lean
#cas [eigenvalues] !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 10; 0, 0, 1, 0]
```

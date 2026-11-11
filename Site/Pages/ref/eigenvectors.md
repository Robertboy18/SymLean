+++
id = "eigenvectors"
kind = "mode"
title = "eigenvectors"
summary = "A basis of each eigenspace of a square matrix with rational entries, with a theorem for every eigenvalue, irrational ones included."
forms = ["CAS.Command.casEigenvectorsCommand"]
see_also = ["eigenvalues", "nullSpace", "characteristicPolynomial", "dot", "hex"]
tutorials = ["proving"]
+++

::: usage
`#cas [eigenvectors] ‹A›`
: gives a basis of the eigenspace of each eigenvalue of the square matrix ‹A› with rational entries, and proves it for every eigenvalue, the irrational ones included.
:::

For a rational eigenvalue $\lambda$ there isn’t much to say: `eigenvectors` computes the null space of $A - \lambda I$ and proves it with the theorem of [[nullSpace]]. The irrational eigenvalues are where it gets interesting. Take a factor $q$ of the characteristic polynomial. You get one basis that serves all the roots $\alpha$ of $q$ at once, with entries that are polynomials in $\alpha$, and one theorem that holds for every root of $q$ in $\mathbb{R}$ or $\mathbb{C}$. That’s how I would write these eigenvectors by hand, and it means nobody has to read nested radicals.

## Details and Options

- ‹A› is a square matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`. The entries are closed rational expressions such as `-3/2`, `0.25` or `1/10^15`.
- For a rational eigenvalue $\lambda$ with printed vectors $V_i$, the theorem is the statement of [[nullSpace]] for `A - λ • 1` over $\mathbb{Q}$: `(A - λ • 1).mulVec (V i) = 0` for each $i$, `LinearIndependent ℚ V`, and `∀ x, (A - λ • 1).mulVec x = 0 → ∃ c, x = ∑ i, c i • V i`.
- The other eigenvalues are the roots of the monic factors $q$ of `A.charpoly` left after the rational roots. For each $q$, the field $K$ is $\mathbb{R}$ when a certificate shows that every root of $q$ is real, and $\mathbb{C}$ otherwise, and $M$ is ‹A› over $K$. The theorem is `∀ α : K, Polynomial.aeval α q = 0 → (∀ i, (M - α • 1).mulVec (V i) = 0) ∧ LinearIndependent K V ∧ ∀ x, (M - α • 1).mulVec x = 0 → ∃ c, x = ∑ i, c i • V i`.
- For $K = \mathbb{R}$ the theorem also says `(q.map (algebraMap ℚ ℝ)).Splits`, so that the real roots are all the roots of $q$. The certificate is the discriminant of a quadratic, or intervals around the roots that do not overlap, and the kernel checks it (`CAS.Analysis.Matrix.EigFactor.splits_of_realCheck`).
- The theorem ends with the factorization of `A.charpoly` in `ℚ[X]` into the factors $X - \lambda$ and $q$, with their multiplicities.
- Without Hex, a factor $q$ of degree 3 or more comes from the squarefree decomposition and need not be irreducible. The elimination over $\mathbb{Q}[X]/(q)$ may then split $q$, and each part gets its own statement. With the optional [Hex library](guide:hex) (`import CASHex.Factor`), the theorem adds `Irreducible q` for each $q$ whose irreducibility Hex certifies, and the report lists the others.
- There is no limit on the size of ‹A›. The search runs before the proof, and the proof runs with `maxHeartbeats` raised to at least one million, so a large matrix can take long.

## Examples

### Basic Examples

Two rational eigenvalues, each with its eigenvector:

```lean
#cas [eigenvectors] !![4, 1; 2, 3]
```

---

The eigenvalues of the Fibonacci matrix are the two roots of $\alpha^2 - \alpha - 1$, and one vector $(\alpha, 1)$ serves both. The theorem says that $x^2 - x - 1$ splits over $\mathbb{R}$:

```lean
#cas [eigenvectors] !![1, 1; 1, 0]
```

### Scope

A Jordan block has the eigenvalue 1 twice, and only one eigenvector:

```lean
#cas [eigenvectors] !![1, 1; 0, 1]
```

---

The roots of $\alpha^2 + 1$ are not real, so the theorem is over $\mathbb{C}$:

```lean
#cas [eigenvectors] !![0, -1; 1, 0]
```

---

A rational eigenvalue and two irrational ones in one report:

```lean
#cas [eigenvectors] !![2, 0, 0; 0, 1, 1; 0, 1, 0]
```

---

The cubic $\alpha^3 - 3 \alpha + 1$ has three real roots. Intervals around them that do not overlap show it, so the theorem is over $\mathbb{R}$:

```lean
#cas [eigenvectors] !![0, 0, -1; 1, 0, 3; 0, 1, 0]
```

---

An irrational eigenvalue with an eigenspace of dimension 2:

```lean
#cas [eigenvectors] !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0]
```

---

Two quadratic factors, each with its own roots $\alpha_1$ and $\alpha_2$:

```lean
#cas [eigenvectors] !![0, 2, 0, 0; 1, 0, 0, 0; 0, 0, 0, 3; 0, 0, 1, 0]
```

---

With Hex, the theorem also says that $x^2 - x - 1$ is irreducible over $\mathbb{Q}$. Here is the whole report, with its theorem:

```lean quote=CASHex/Examples.lean
#cas [eigenvectors] !![1, 1; 1, 0]
```

---

Hex certifies a factor with fractions, $x^2 - \tfrac{1}{2} x - 1$, through its multiple $2 x^2 - x - 2$ with integer coefficients:

```lean quote=CASHex/Examples.lean
#cas [eigenvectors] !![1/2, 1; 1, 0]
```

### Applications

An eigenvector as a theorem, with the axioms its proof uses:

```lean
theorem eigenvector_five : !![(4 : ℚ), 1; 2, 3].mulVec ![1, 1] = (5 : ℚ) • ![1, 1] := by
  cas

#print axioms eigenvector_five
```

---

The eigenvectors of the first example, as the columns of $P$, diagonalize $A$: $A P = P D$ with $D$ the diagonal matrix of the eigenvalues 2 and 5:

```lean
#cas [dot] (!![4, 1; 2, 3], !![-1/2, 1; 1, 1])
```

```lean
#cas [dot] (!![-1/2, 1; 1, 1], !![2, 0; 0, 5])
```

### Properties and Relations

The eigenspace of a rational eigenvalue $\lambda$ is the null space of $A - \lambda I$. For $\lambda = 2$ in the first example:

```lean
#cas [nullSpace] !![2, 1; 2, 1]
```

---

[[eigenvalues]] gives the roots of $\alpha^2 - \alpha - 1$ as surds. Put into $(\alpha, 1)$, each one gives an eigenvector of the Fibonacci matrix:

```lean
#cas [eigenvalues] !![1, 1; 1, 0]
```

### Possible Issues

The matrix has to be square:

```lean error
#cas [eigenvectors] !![1, 2, 3; 4, 5, 6]
```

### Neat Examples

One vector $(\alpha^3 - 10 \alpha, \alpha^2 - 10, \alpha, 1)$ for the four eigenvalues $\pm\sqrt{2} \pm \sqrt{3}$ of this companion matrix at once. Hex has no certificate for the irreducibility of $x^4 - 10 x^2 + 1$, and the report says so:

```lean quote=CASHex/Examples.lean
#cas [eigenvectors] !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 10; 0, 0, 1, 0]
```

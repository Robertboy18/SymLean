+++
id = "eigenvalueBounds"
kind = "mode"
title = "eigenvalueBounds"
summary = "Decimal bounds on the smallest and the largest eigenvalue of a symmetric matrix, with a theorem that they hold and are sharp."
forms = ["CAS.Command.casEigenvalueBoundsCommand"]
see_also = ["eigenvalues", "positiveDefinite", "N", "enclose", "options"]
guide = "linear-algebra"
tutorials = ["proving"]
+++

::: usage
`#cas [eigenvalueBounds] ‹A›`
: gives the smallest and the largest eigenvalue of the symmetric matrix ‹A› with rational entries, rounded outward to 6 decimal places, and proves the bounds and that they are sharp.
`#cas (digits := ‹d›) [eigenvalueBounds] ‹A›`
: gives the same bounds to ‹d› decimal places.
:::

For a symmetric matrix, the extreme eigenvalues are the extreme values of $x^T A x$ on the unit sphere, and in a proof that is usually the form you need: $c\,|x|^2 \le x^T A x \le \mu\,|x|^2$ for every $x$. `eigenvalueBounds` proves exactly this, with decimals $c$ and $\mu$. It also proves that neither bound improves by $10^{-d}$, so the bounds are as tight as the digits allow. I find this most useful when the exact eigenvalues are roots of a high-degree polynomial and the argument only needs a bound on the quadratic form.

## Details and Options

- ‹A› is a symmetric square matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`. The entries are closed rational expressions such as `-3/2`, `0.25` or `1/10^15`.
- With $Q(x) = \sum_i \sum_j A_{ij} x_i x_j$ for the real matrix ‹A› and the printed decimals $c$ and $\mu$, the theorem says three things over $\mathbb{R}$:
  - `c * ∑ i, x i ^ 2 ≤ Q x ∧ Q x ≤ μ * ∑ i, x i ^ 2` for every `x : Fin n → ℝ`;
  - `Q x < (c + 10 ^ (-d)) * ∑ i, x i ^ 2` for some $x$;
  - `(μ - 10 ^ (-d)) * ∑ i, x i ^ 2 < Q x` for some $x$.
- The theorem writes $Q(x)$ out as `∑ i, ∑ j, A i j * x i * x j`, and the numbers as decimals. So $c$ is the smallest eigenvalue rounded down to $d$ places, and $\mu$ the largest one rounded up.
- Both bounds come from bisection on the grid $10^{-d} \mathbb{Z}$. The kernel checks exact factorizations $L D L^T$ over $\mathbb{Q}$ with nonnegative pivots of $A - c I$ and $\mu I - A$, and the two rational vectors that show the bounds are sharp.
- `(digits := d)` sets the number $d$ of decimal places: 6 by default, between 1 and `cas.maxDigits`, which is 2000 by default (see [[options]]).

## Examples

### Basic Examples

The eigenvalues of this matrix are 1 and 3, and the bounds are exact:

```lean
#cas [eigenvalueBounds] !![2, 1; 1, 2]
```

---

Here the extreme eigenvalues are $3 \mp \sqrt{3}$, rounded outward:

```lean
#cas [eigenvalueBounds] !![4, 1, 0; 1, 3, 1; 0, 1, 2]
```

### Scope

Eigenvalues of very different sizes:

```lean
#cas [eigenvalueBounds] !![1000000, 0; 0, 1]
```

---

A negative eigenvalue:

```lean
#cas [eigenvalueBounds] !![1, 2; 2, 1]
```

---

Fractions, written as a list of rows:

```lean
#cas [eigenvalueBounds] [[1/2, 1/4], [1/4, 1/2]]
```

### Options

Three decimal places:

```lean
#cas (digits := 3) [eigenvalueBounds] !![4, 1, 0; 1, 3, 1; 0, 1, 2]
```

---

Twenty places for the eigenvalues $\tfrac{5 \pm \sqrt{5}}{2}$ of this matrix:

```lean
#cas (digits := 20) [eigenvalueBounds] !![2, 1; 1, 3]
```

### Applications

A proof can take the first part of the printed theorem as a hypothesis and use its lower bound:

```lean
theorem rayleigh_lower
    (h : ∀ x : Fin 2 → ℝ,
      1.000000 * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, !![(2 : ℝ), 1; 1, 2] i j * x i * x j ∧
        ∑ i, ∑ j, !![(2 : ℝ), 1; 1, 2] i j * x i * x j ≤ 3.000000 * ∑ i, x i ^ 2)
    (x : Fin 2 → ℝ) :
    ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, !![(2 : ℝ), 1; 1, 2] i j * x i * x j := by
  have e : (1.000000 : ℝ) = 1 := by norm_num
  have h₁ := (h x).1
  rw [e, one_mul] at h₁
  exact h₁

#print axioms rayleigh_lower
```

### Properties and Relations

[[eigenvalues]] gives the exact eigenvalues, here 1 and 3:

```lean
#cas [eigenvalues] !![2, 1; 1, 2]
```

---

A lower bound above 0 says that the matrix is positive definite, which [[positiveDefinite]] decides exactly:

```lean
#cas [positiveDefinite] !![2, 1; 1, 2]
```

### Possible Issues

The matrix has to be symmetric. [[eigenvalues]] takes every square matrix:

```lean error
#cas [eigenvalueBounds] !![1, 2; 3, 4]
```

---

The number of places is between 1 and `cas.maxDigits`:

```lean error
#cas (digits := 0) [eigenvalueBounds] !![2, 1; 1, 2]
```

### Neat Examples

The $10 \times 10$ Hilbert matrix, with entries $\frac{1}{i + j - 1}$, is the classic example of an ill-conditioned matrix. Its smallest eigenvalue is about $1.09 \cdot 10^{-13}$, and fourteen places bound it away from 0:

```lean
#cas (digits := 14) [eigenvalueBounds] !![1, 1/2, 1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10;
  1/2, 1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11;
  1/3, 1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12;
  1/4, 1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13;
  1/5, 1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14;
  1/6, 1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15;
  1/7, 1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16;
  1/8, 1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17;
  1/9, 1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17, 1/18;
  1/10, 1/11, 1/12, 1/13, 1/14, 1/15, 1/16, 1/17, 1/18, 1/19]
```

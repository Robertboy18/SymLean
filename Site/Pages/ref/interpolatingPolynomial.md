+++
id = "interpolatingPolynomial"
kind = "mode"
title = "interpolatingPolynomial"
summary = "Gives the polynomial of least degree through given points, with a theorem about its values and degree in `ℚ[X]`."
forms = ["CAS.Command.casInterpolatingPolynomialCommand"]
see_also = ["coefficientList", "sum", "polynomialRemainder", "solve"]
guide = "polynomials"
tutorials = ["first-hour"]
+++

::: usage
`#cas [interpolatingPolynomial ‹x›] [(‹a₀›, ‹b₀›), …]`
: gives the polynomial $P$ in ‹x› of degree at most $n - 1$ through the $n$ points $(a_i, b_i)$, and proves its values and its degree bound in Mathlib’s `ℚ[X]`.
`#cas [interpolatingPolynomial ‹x›] [‹b₁›, ‹b₂›, …]`
: gives the polynomial through the points $(1, b_1), (2, b_2), \dots$ in the same way.
:::

Give `interpolatingPolynomial` some exact data points and it finds the polynomial that passes through them. The polynomial comes from Lagrange’s formula, and the theorem is the conjunction of `P.eval aᵢ = bᵢ` for every point and `P.natDegree ≤ n - 1`.

You might expect the theorem to say that $P$ is the one and only interpolating polynomial, but it doesn’t need to. The values and the degree bound already determine $P$, because two polynomials of degree at most $n - 1$ that agree at $n$ points are equal.

## Details and Options

- The theorem is `P.eval a₀ = b₀ ∧ … ∧ P.natDegree ≤ n - 1` in `ℚ[X]`, with the variable read as `Polynomial.X`. The values are checked by `norm_num` and the degree by `compute_degree`.
- The points are pairs of exact rational literals, such as `2`, `-1/3` or `0.5`, with distinct abscissae. A list of values `[b₁, b₂, …]` stands for the points $(1, b_1), (2, b_2), \dots$.
- The degree can be smaller than $n - 1$, as for four values of $x^2$.
- The polynomial is printed expanded.
- The tactic [[cas]] proves single values `P.eval a = b` in `ℚ[X]`.

## Examples

### Basic Examples

The parabola through three points:

```lean
#cas [interpolatingPolynomial x] [(0, 1), (1, 3), (2, 7)]
```

---

A list of values stands for the abscissae $1, 2, 3, \dots$. Four values of $x^2$ give $x^2$ back, of degree $2$:

```lean
#cas [interpolatingPolynomial x] [1, 4, 9, 16]
```

### Scope

The abscissae and the values can be fractions:

```lean
#cas [interpolatingPolynomial x] [(1/2, 1), (2, 0), (3, 5)]
```

### Applications

One value of the first example as a theorem about `Polynomial.eval`. Only the three standard axioms are used:

```lean
open Polynomial in
theorem interpolant_at_two : (X ^ 2 + X + 1 : ℚ[X]).eval 2 = 7 := by
  cas

#print axioms interpolant_at_two
```

---

The first five sums of squares, $1, 5, 14, 30, 55$, determine a polynomial of degree at most $4$:

```lean
#cas [interpolatingPolynomial n] [1, 5, 14, 30, 55]
```

It is $n(n + 1)(2n + 1)/6$, and [[sum]] proves that this is the sum of the first $n$ squares for every $n$:

```lean
#cas [sum k 1 n] (k^2)
```

### Properties and Relations

The value at a point is the remainder of the division by $x - a$, here at $a = 2$ ([[polynomialRemainder]]):

```lean
#cas [polynomialRemainder] (x^2 + x + 1, x - 2)
```

### Possible Issues

Two values at the same abscissa have no interpolating polynomial:

```lean error
#cas [interpolatingPolynomial x] [(0, 1), (0, 2)]
```

---

The points go in square brackets:

```lean error
#cas [interpolatingPolynomial x] (1, 2)
```

---

The points must be exact rational literals:

```lean error
#cas [interpolatingPolynomial x] [(0, sqrt 2), (1, 1)]
```

### Neat Examples

The chords between $n = 1, \dots, 5$ points on a circle cut the disc into at most $1, 2, 4, 8, 16$ regions, and the interpolating polynomial of these values, $\binom{n}{4} + \binom{n}{2} + 1$, gives $31$ and not $32$ at $n = 6$:

```lean
#cas [interpolatingPolynomial n] [1, 2, 4, 8, 16]
```

```lean
example : (6 : ℚ) ^ 4 / 24 - 6 ^ 3 / 4 + 23 * 6 ^ 2 / 24 - 3 * 6 / 4 + 1 = 31 := by
  norm_num
```

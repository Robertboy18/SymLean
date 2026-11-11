+++
id = "groebner"
kind = "mode"
title = "groebner"
summary = "Gives the reduced lexicographic Gröbner basis of a polynomial ideal, with theorems about `Ideal.span` in `MvPolynomial`."
forms = ["CAS.Command.casGroebnerCommand"]
see_also = ["member", "solve", "cas", "oracle", "polynomialRemainder"]
guide = "polynomials"
tutorials = ["proving"]
+++

::: usage
`#cas [groebner ‹x›, ‹y›, …] [‹f₁›, …, ‹fₘ›]`
: gives the reduced Gröbner basis of the polynomials ‹f₁›, …, ‹fₘ› for the lexicographic order ‹x› > ‹y› > …, and proves that it spans the same ideal and is a Gröbner basis in Mathlib’s `MvPolynomial`.
:::

A Gröbner basis reorganizes a system of polynomial equations into a form that is easier to solve, and `groebner` computes one for the input ideal. The lexicographic basis eliminates variables. Its last elements involve only the last variables, so you can read off the common zeros one variable at a time, much as you would back-substitute in a triangular linear system.

The report proves two theorems about Mathlib’s `Ideal.span` in `MvPolynomial (Fin n) ℚ`. The first says that the basis spans the same ideal as the input. The second says that it is a Gröbner basis for `MonomialOrder.lex`: the leading term of every nonzero element of the ideal is divisible by the leading term of a basis element. I want both. The first alone is also true of the input itself, and it’s the second that makes the basis worth having.

## Details and Options

- The theorems are `Ideal.span {f₁, …, fₘ} = Ideal.span {g₁, …, gₖ}` and `∀ p ∈ Ideal.span {g₁, …, gₖ}, p ≠ 0 → ∃ g ∈ {g₁, …, gₖ}, MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm p`, in `MvPolynomial (Fin n) ℚ` with the $i$-th listed variable read as `X i`, so the first one is the largest.
- The equality of the ideals comes with explicit cofactors both ways, checked by `ring`. The Gröbner property follows from Buchberger’s criterion ([Buchberger 1970](https://doi.org/10.1007/BF01844169)) and a division of the S-polynomial of every pair of the basis, which the kernel checks (`CAS.Polynomial.Sparse.groebnerCertified`). That the basis is the reduced one is not part of the theorem.
- The inputs are polynomials with rational coefficients in the listed variables. Division is allowed by nonzero constants only.
- Each element of the basis is scaled to coprime integer coefficients with a positive leading coefficient. An ideal that contains a nonzero constant has the basis $1$. The zero ideal has the empty basis, printed $0$ and written `{0}` in the theorems.
- The search stops after 400 polynomials or 4000 pairs, with a message that suggests an oracle.
- With `CASOracle.Ideal` imported, `#cas [groebner x, y, oracle := sage] [f₁, …]` asks SageMath for the basis, and `oracle := sympy` asks SymPy. Lean checks the basis in the same way, and that it is reduced is printed as a hint. See [[oracle]].
- The tactic [[cas]] proves equalities of spans in any commutative ring, and the Gröbner property for `MonomialOrder.lex` of a set literal in `MvPolynomial (Fin n) ℚ`. Other monomial orders are not among its goals.

## Examples

### Basic Examples

The circle $x^2 + y^2 = 5$ and the hyperbola $xy = 2$. The last element of the basis is a polynomial in $y$ alone:

```lean
#cas [groebner x, y] [x^2 + y^2 - 5, x*y - 2]
```

---

The unit sphere, the paraboloid $y = x^2 + z^2$ and the plane $x = z$. The basis is triangular and ends with a polynomial in $z$:

```lean
#cas [groebner x, y, z] [x^2 + y^2 + z^2 - 1, x^2 + z^2 - y, x - z]
```

### Scope

Rational coefficients are allowed, and each element of the basis is scaled to coprime integer coefficients:

```lean
#cas [groebner x, y] [x/2 + y - 1, x^2 - y]
```

---

The polynomials $xy - 1$ and $x$ have no common zero. The basis is $1$: the ideal is the whole ring.

```lean
#cas [groebner x, y] [x*y - 1, x]
```

---

The zero ideal has the empty basis, printed $0$:

```lean
#cas [groebner x, y] [x - x]
```

### Options

SageMath can propose the basis, with `CASOracle.Ideal` imported. Lean checks it in the same way and proves the same two theorems:

```lean quote=tests/oracle/Oracles.lean
#cas [groebner x, y, oracle := sage] [x ^ 2 + y ^ 2 - 5, x * y - 2]
```

### Applications

The first example as a theorem about Mathlib’s `Ideal.span`. Only the three standard axioms are used:

```lean
open MvPolynomial in
theorem span_circle_hyperbola :
    Ideal.span {(X 0 ^ 2 + X 1 ^ 2 - 5 : MvPolynomial (Fin 2) ℚ), X 0 * X 1 - 2} =
      Ideal.span {2 * X 0 + X 1 ^ 3 - 5 * X 1, X 1 ^ 4 - 5 * X 1 ^ 2 + 4} := by
  cas

#print axioms span_circle_hyperbola
```

---

The Gröbner property of its basis, which the tactic [[cas]] proves from Buchberger’s criterion:

```lean
open MvPolynomial in
theorem groebner_circle_hyperbola :
    ∀ p ∈ Ideal.span ({2 * X 0 + X 1 ^ 3 - 5 * X 1, X 1 ^ 4 - 5 * X 1 ^ 2 + 4} :
        Set (MvPolynomial (Fin 2) ℚ)), p ≠ 0 →
      ∃ g ∈ ({2 * X 0 + X 1 ^ 3 - 5 * X 1, X 1 ^ 4 - 5 * X 1 ^ 2 + 4} :
        Set (MvPolynomial (Fin 2) ℚ)),
        MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm p := by
  cas
```

---

In the first example $y$ is a root of $y^4 - 5y^2 + 4 = (y^2 - 1)(y^2 - 4)$, and then $x = (5y - y^3)/2$. [[solve]] uses such a basis to prove the complete list of real solutions:

```lean
#cas [solve x, y] (x^2 + y^2 = 5 ∧ x * y = 2)
```

### Properties and Relations

[[member]] writes an element of the ideal as a combination of the inputs. Here it is the last element of the first basis:

```lean
#cas [member x, y] (y^4 - 5*y^2 + 4) [x^2 + y^2 - 5, x*y - 2]
```

---

The order of the variables is the order of elimination. With $y > x$, the basis of the line and the parabola of Scope ends with a polynomial in $x$:

```lean
#cas [groebner y, x] [x/2 + y - 1, x^2 - y]
```

### Possible Issues

Every variable of the inputs is listed after the mode name:

```lean error
#cas [groebner x, y] [x^2 + z, y]
```

---

The inputs are polynomials:

```lean error
#cas [groebner x, y] [x^2 + sin y, y]
```

---

The tactic [[cas]] refuses the Gröbner property of a set that does not have it, and names a pair whose S-polynomial leaves a nonzero remainder. The parabolas $x^2 - y$ and $y^2 - x$ are such a set:

```lean error
open MvPolynomial in
example :
    ∀ p ∈ Ideal.span ({X 0 ^ 2 - X 1, X 1 ^ 2 - X 0} : Set (MvPolynomial (Fin 2) ℚ)), p ≠ 0 →
      ∃ g ∈ ({X 0 ^ 2 - X 1, X 1 ^ 2 - X 0} : Set (MvPolynomial (Fin 2) ℚ)),
        MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm p := by
  cas
```

The reduced basis $x - y^2, y^4 - y$ of the same ideal has the property:

```lean
open MvPolynomial in
theorem groebner_two_parabolas :
    ∀ p ∈ Ideal.span ({X 0 - X 1 ^ 2, X 1 ^ 4 - X 1} : Set (MvPolynomial (Fin 2) ℚ)), p ≠ 0 →
      ∃ g ∈ ({X 0 - X 1 ^ 2, X 1 ^ 4 - X 1} : Set (MvPolynomial (Fin 2) ℚ)),
        MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm p := by
  cas
```

---

The two sets in the statement are compared as written, so the same set listed in another order after `∃ g ∈` is refused:

```lean error
open MvPolynomial in
example :
    ∀ p ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 2) ℚ)), p ≠ 0 →
      ∃ g ∈ ({X 1, X 0} : Set (MvPolynomial (Fin 2) ℚ)),
        MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm p := by
  cas
```

### Neat Examples

The elementary symmetric polynomials of $x, y, z$, the last one shifted by $1$. At a common zero, $x$, $y$ and $z$ are the three roots of $t^3 - 1$ in some order, and the basis ends with $z^3 - 1$:

```lean
#cas [groebner x, y, z] [x + y + z, x*y + y*z + z*x, x*y*z - 1]
```

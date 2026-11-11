+++
id = "ChebyshevU"
kind = "call"
title = "ChebyshevU"
summary = "The Chebyshev polynomial $U_n$ in monomials, proved in every commutative ring, and its exact values at rational points."
calls = ["ChebyshevU"]
see_also = ["ChebyshevT", "LegendreP", "HermiteHe", "expand", "N"]
guide = "special-functions"
tutorials = ["proving"]
+++

::: usage
`#cas (ChebyshevU ‹n› ‹x›)`
: gives the Chebyshev polynomial of the second kind $U_n$ in the variable ‹x›, in monomials with integer coefficients, and proves the expansion in every commutative ring.
`#cas (ChebyshevU ‹n› ‹q›)`
: gives the exact value of $U_n$ at the rational number ‹q› and proves it.
`#cas [N ‹d›] (ChebyshevU ‹n› ‹q›)`
: gives the exact value of $U_n$ at ‹q› with its first ‹d› significant digits, truncated toward zero, and proves their decimal bounds.
:::

`ChebyshevU` does the same for the Chebyshev polynomial of the second kind: monomials in a variable, or an exact value at a rational point. As with `ChebyshevT`, the theorem for the polynomial is about Mathlib’s `Polynomial.Chebyshev.U R n`, and it holds in every commutative ring `R : Type` at once, so one statement serves whichever ring your proof works in.

## Details and Options

- ‹n› is a natural number with $n \le 80$, a literal or a closed integer expression.
- The second argument is a variable, which the polynomial is written in and which may have any name other than `pi`, `π`, `Pi`, `e` and `E`, or a rational number.
- For the polynomial the theorem is `∀ (R : Type) [CommRing R], Polynomial.Chebyshev.U R n = p` for the printed $p$, written in `Polynomial.X`. The kernel evaluates the coefficient list of degree $n$, and `CAS.Analysis.SpecialFunctions.chebyshevU_eq_intPoly`, proved from Mathlib’s recurrence `Polynomial.Chebyshev.U_add_two`, identifies it with Mathlib’s polynomial.
- At a rational $q$ the theorem is `Polynomial.eval q (Polynomial.Chebyshev.U ℝ n) = v`. With `[N d]` it adds the first $d$ significant digits of $v$, truncated toward zero, and their decimal bounds. The report prints `v = digits` when the digits are exact and `v ≈ digits` otherwise.
- With `[N d]`, $1 \le d \le 2000$, as for [[N]].
- `#cas [expand] (ChebyshevU n x)` prints the same polynomial as `#cas (ChebyshevU n x)`.
- There are no options.

## Examples

### Basic Examples

$U_4$ in monomials, with the theorem in every commutative ring:

```lean
#cas (ChebyshevU 4 x)
```

### Scope

[[expand]] prints the same polynomial:

```lean
#cas [expand] (ChebyshevU 2 x)
```

---

At a rational point the call gives the exact value, and `[N d]` adds its first digits. With $U_n(\cos\theta) = \sin((n + 1)\theta) / \sin\theta$ at $\cos\tfrac{2\pi}{3} = -\tfrac{1}{2}$, the value is $U_3(-\tfrac{1}{2}) = \sin\tfrac{8\pi}{3} / \sin\tfrac{2\pi}{3} = 1$, and the digits are exact:

```lean
#cas [N 10] (ChebyshevU 3 (-1/2))
```

### Applications

A proof can take the printed theorem as a hypothesis and specialize it, here to $R = \mathbb{R}$ at $x = 1$, where $U_n(1) = n + 1$:

```lean
theorem chebyshevU_four_at_one
    (h : ∀ (R : Type) [CommRing R], Polynomial.Chebyshev.U R 4 =
      16 * Polynomial.X ^ 4 - 12 * Polynomial.X ^ 2 + 1) :
    (Polynomial.Chebyshev.U ℝ 4).eval 1 = 5 := by
  rw [h ℝ]
  norm_num

#print axioms chebyshevU_four_at_one
```

### Properties and Relations

The derivative of the first kind is $T_n' = n\,U_{n-1}$. The [[ChebyshevT]] polynomial $T_5$ has $T_5' = 80x^4 - 60x^2 + 5 = 5\,U_4$:

```lean
#cas (ChebyshevT 5 x)
```

### Possible Issues

The degree is at most 80. Mathlib’s recurrence `Polynomial.Chebyshev.U_add_two` gives higher degrees from two lower ones:

```lean error
#cas (ChebyshevU 81 x)
```

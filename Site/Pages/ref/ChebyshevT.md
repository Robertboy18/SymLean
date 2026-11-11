+++
id = "ChebyshevT"
kind = "call"
title = "ChebyshevT"
summary = "The Chebyshev polynomial $T_n$ in monomials, proved in every commutative ring, and its exact values at rational points."
calls = ["ChebyshevT"]
see_also = ["ChebyshevU", "LegendreP", "HermiteHe", "expand", "N"]
guide = "special-functions"
tutorials = ["proving"]
+++

::: usage
`#cas (ChebyshevT ‹n› ‹x›)`
: gives the Chebyshev polynomial of the first kind $T_n$ in the variable ‹x›, in monomials with integer coefficients, and proves the expansion in every commutative ring.
`#cas (ChebyshevT ‹n› ‹q›)`
: gives the exact value of $T_n$ at the rational number ‹q› and proves it.
`#cas [N ‹d›] (ChebyshevT ‹n› ‹q›)`
: gives the exact value of $T_n$ at ‹q› with its first ‹d› significant digits, truncated toward zero, and proves their decimal bounds.
:::

`ChebyshevT` writes the Chebyshev polynomial of the first kind in monomials, or gives its exact value at a rational point. The theorem is unusually general. For the polynomial it is about Mathlib’s `Polynomial.Chebyshev.T R n`, and it holds in every commutative ring `R : Type` at once, so a proof can specialize it to the ring it works in, whether that is $\mathbb{R}$, $\mathbb{Z}$ or a finite field.

## Details and Options

- ‹n› is a natural number with $n \le 80$, a literal or a closed integer expression such as `2 * 3`.
- The second argument is a variable, which the polynomial is written in and which may have any name other than `pi`, `π`, `Pi`, `e` and `E`, or a rational number.
- For the polynomial the theorem is `∀ (R : Type) [CommRing R], Polynomial.Chebyshev.T R n = p` for the printed $p$, written in `Polynomial.X`. The kernel evaluates the coefficient list of degree $n$, and `CAS.Analysis.SpecialFunctions.chebyshevT_eq_intPoly`, proved from Mathlib’s recurrence `Polynomial.Chebyshev.T_add_two`, identifies it with Mathlib’s polynomial.
- At a rational $q$ the theorem is `Polynomial.eval q (Polynomial.Chebyshev.T ℝ n) = v`. With `[N d]` it adds the first $d$ significant digits of $v$, truncated toward zero, and their decimal bounds. The report prints `v = digits` when the digits are exact and `v ≈ digits` otherwise.
- With `[N d]`, $1 \le d \le 2000$, as for [[N]].
- `#cas [expand] (ChebyshevT n x)` prints the same polynomial as `#cas (ChebyshevT n x)`.
- There are no options.

## Examples

### Basic Examples

$T_5$ in monomials, with the theorem in every commutative ring:

```lean
#cas (ChebyshevT 5 x)
```

---

The exact value at a rational point:

```lean
#cas (ChebyshevT 5 (1/2))
```

### Scope

The degree may be a closed integer expression:

```lean
#cas (ChebyshevT (2 + 1) x)
```

---

The variable need not be `x`, and [[expand]] prints the same polynomial:

```lean
#cas [expand] (ChebyshevT 1 t)
```

---

`[N d]` adds the first digits of the exact value:

```lean
#cas [N 10] (ChebyshevT 5 (1/3))
```

### Applications

A proof can take the printed theorem as a hypothesis and specialize it, here to $R = \mathbb{R}$ at $x = \tfrac{1}{2}$:

```lean
theorem chebyshevT_five_at_half
    (h : ∀ (R : Type) [CommRing R], Polynomial.Chebyshev.T R 5 =
      16 * Polynomial.X ^ 5 - 20 * Polynomial.X ^ 3 + 5 * Polynomial.X) :
    (Polynomial.Chebyshev.T ℝ 5).eval (1 / 2) = 1 / 2 := by
  rw [h ℝ]
  norm_num

#print axioms chebyshevT_five_at_half
```

### Properties and Relations

$T_n(\cos\theta) = \cos n\theta$. At $\cos\tfrac{\pi}{3} = \tfrac{1}{2}$ this gives $T_3(\tfrac{1}{2}) = \cos\pi = -1$, and the digits are exact:

```lean
#cas [N 5] (ChebyshevT 3 (1/2))
```

---

The derivative of $T_n$ is $n\,U_{n-1}$. For $n = 5$ it is $T_5' = 80x^4 - 60x^2 + 5 = 5\,U_4$, with $U_4$ from [[ChebyshevU]]:

```lean
#cas (ChebyshevU 4 x)
```

### Possible Issues

The degree is at most 80. Mathlib’s recurrence `Polynomial.Chebyshev.T_add_two` gives higher degrees from two lower ones:

```lean error
#cas (ChebyshevT 81 x)
```

---

`[N d]` evaluates at a number, not at a variable:

```lean error
#cas [N 10] (ChebyshevT 3 x)
```

---

The second argument is a variable or a rational number, not an expression in a variable:

```lean error
#cas (ChebyshevT 2 (x + 1))
```

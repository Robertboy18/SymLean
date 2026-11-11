+++
id = "HermiteHe"
kind = "call"
title = "HermiteHe"
summary = "The probabilists’ Hermite polynomial $\\mathrm{He}_n$, Mathlib’s `Polynomial.hermite n`, in monomials, with its exact values at rational points."
calls = ["HermiteHe"]
see_also = ["HermiteH", "ChebyshevT", "LegendreP", "expand", "N"]
guide = "special-functions"
tutorials = ["proving"]
+++

::: usage
`#cas (HermiteHe ‹n› ‹x›)`
: gives the probabilists’ Hermite polynomial $\mathrm{He}_n$ in the variable ‹x›, in monomials with integer coefficients, and proves the expansion in `ℤ[X]`.
`#cas (HermiteHe ‹n› ‹q›)`
: gives the exact value of $\mathrm{He}_n$ at the rational number ‹q› and proves it.
`#cas [N ‹d›] (HermiteHe ‹n› ‹q›)`
: gives the exact value of $\mathrm{He}_n$ at ‹q› with its first ‹d› significant digits, truncated toward zero, and proves their decimal bounds.
:::

`HermiteHe` gives the probabilists’ Hermite polynomials $\mathrm{He}_n$, the ones SymPy calls `hermite_prob`. They are Mathlib’s own `Polynomial.hermite n`, so the theorem is as plain as it can be: an equation of polynomials in `ℤ[X]`, with nothing rescaled on the way. [[HermiteH]] gives the physicists’ polynomials $H_n$.

## Details and Options

- ‹n› is a natural number with $n \le 80$, a literal or a closed integer expression.
- The second argument is a variable, which the polynomial is written in and which may have any name other than `pi`, `π`, `Pi`, `e` and `E`, or a rational number.
- For the printed polynomial $p$ the theorem is `Polynomial.hermite n = p` in `ℤ[X]`, with $p$ written in `Polynomial.X`, by `CAS.Analysis.SpecialFunctions.hermite_eq_intPoly`, proved from Mathlib’s recurrence `Polynomial.hermite_succ`.
- At a rational $q$ the theorem is `Polynomial.aeval q (Polynomial.hermite n) = v`. With `[N d]` it adds the first $d$ significant digits of $v$, truncated toward zero, and their decimal bounds. The report prints `v = digits` when the digits are exact and `v ≈ digits` otherwise.
- With `[N d]`, $1 \le d \le 2000$, as for [[N]].
- `#cas [expand] (HermiteHe n x)` prints the same polynomial as `#cas (HermiteHe n x)`.
- There are no options.

## Examples

### Basic Examples

$\mathrm{He}_4$ in monomials, with the theorem in `ℤ[X]`:

```lean
#cas (HermiteHe 4 x)
```

### Scope

The variable need not be `x`:

```lean
#cas (HermiteHe 3 t)
```

---

[[expand]] prints the same polynomial:

```lean
#cas [expand] (HermiteHe 3 x)
```

---

At a rational point the call gives the exact value, and `[N d]` adds its first digits. Here they are exact:

```lean
#cas [N 10] (HermiteHe 3 2)
```

---

$\mathrm{He}_3 = x^3 - 3x$ is odd, so $\mathrm{He}_3(0) = 0$, and the report prints the exact value alone:

```lean
#cas [N 10] (HermiteHe 3 0)
```

### Applications

A proof can take the printed theorem as a hypothesis and evaluate it, here at $x = 1$:

```lean
theorem hermiteHe_four_at_one
    (h : Polynomial.hermite 4 = Polynomial.X ^ 4 - 6 * Polynomial.X ^ 2 + 3) :
    (Polynomial.hermite 4).eval 1 = -2 := by
  rw [h]
  norm_num

#print axioms hermiteHe_four_at_one
```

### Properties and Relations

The physicists’ polynomials of [[HermiteH]] are $H_n(x) = \sqrt{2}^{\,n}\,\mathrm{He}_n(\sqrt{2}\,x)$. For $n = 4$ this is $4\,\mathrm{He}_4(\sqrt{2}\,x) = 4\,(4x^4 - 12x^2 + 3)$:

```lean
#cas (HermiteH 4 x)
```

### Possible Issues

The degree is at most 80. Mathlib’s recurrence `Polynomial.hermite_succ` gives higher degrees from lower ones:

```lean error
#cas (HermiteHe 81 x)
```

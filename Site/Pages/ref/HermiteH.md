+++
id = "HermiteH"
kind = "call"
title = "HermiteH"
summary = "The physicists’ Hermite polynomial $H_n$ in monomials, proved at every real $x$, and its exact values at rational points."
calls = ["HermiteH"]
see_also = ["HermiteHe", "ChebyshevT", "LegendreP", "expand", "N"]
guide = "special-functions"
tutorials = ["proving"]
+++

::: usage
`#cas (HermiteH ‹n› ‹x›)`
: gives the physicists’ Hermite polynomial $H_n$ in the variable ‹x›, in monomials with integer coefficients, and proves the expansion at every real ‹x›.
`#cas (HermiteH ‹n› ‹q›)`
: gives the exact value of $H_n$ at the rational number ‹q› and proves it.
`#cas [N ‹d›] (HermiteH ‹n› ‹q›)`
: gives the exact value of $H_n$ at ‹q› with its first ‹d› significant digits, truncated toward zero, and proves their decimal bounds.
:::

There are two families of Hermite polynomials in common use, and `HermiteH` gives the physicists’ ones, $H_n$, with the convention of Mathematica’s `HermiteH`. Mathlib defines only the probabilists’ polynomials $\mathrm{He}_n$, as `Polynomial.hermite n`, so the theorem cannot name $H_n$ directly. It states $H_n$ through them, as $\sqrt{2}^{\,n}\,\mathrm{He}_n(\sqrt{2}\,x)$, and you will see those factors of $\sqrt{2}$ in every statement. [[HermiteHe]] gives $\mathrm{He}_n$ itself.

## Details and Options

- ‹n› is a natural number with $n \le 60$, a literal or a closed integer expression.
- The second argument is a variable, which the polynomial is written in and which may have any name other than `pi`, `π`, `Pi`, `e` and `E`, or a rational number.
- $H_n(x) = \sqrt{2}^{\,n}\,\mathrm{He}_n(\sqrt{2}\,x)$. For the printed polynomial $p$ the theorem is `∀ x : ℝ, √2 ^ n * Polynomial.aeval (√2 * x) (Polynomial.hermite n) = p`, by `CAS.Analysis.SpecialFunctions.sqrt_two_pow_mul_aeval_hermite`.
- At a rational $q$ the theorem is `√2 ^ n * Polynomial.aeval (√2 * q) (Polynomial.hermite n) = v`. With `[N d]` it adds the first $d$ significant digits of $v$, truncated toward zero, and their decimal bounds. The report prints `v = digits` when the digits are exact and `v ≈ digits` otherwise.
- With `[N d]`, $1 \le d \le 2000$, as for [[N]].
- `#cas [expand] (HermiteH n x)` prints the same polynomial as `#cas (HermiteH n x)`.
- There are no options.

## Examples

### Basic Examples

$H_4$ in monomials, with the theorem at every real $x$:

```lean
#cas (HermiteH 4 x)
```

### Scope

Degree 1 gives $H_1 = 2x$:

```lean
#cas (HermiteH 1 x)
```

---

[[expand]] prints the same polynomial:

```lean
#cas [expand] (HermiteH 5 x)
```

---

At a rational point the call gives the exact value, and `[N d]` adds its first digits. Here they are exact:

```lean
#cas [N 10] (HermiteH 3 (1/2))
```

---

With fewer digits than the value has, the report prints `≈`, and the theorem bounds the value between $-830$ and $-820$:

```lean
#cas [N 2] (HermiteH 6 2)
```

### Applications

A proof can take the printed theorem as a hypothesis and specialize it, here at $x = 0$:

```lean
theorem hermiteH_four_at_zero
    (h : ∀ x : ℝ, √2 ^ 4 * Polynomial.aeval (√2 * x) (Polynomial.hermite 4) =
      16 * x ^ 4 - 48 * x ^ 2 + 12) :
    √2 ^ 4 * Polynomial.aeval (√2 * 0) (Polynomial.hermite 4) = 12 := by
  rw [h 0]
  norm_num

#print axioms hermiteH_four_at_zero
```

### Properties and Relations

[[HermiteHe]] gives $\mathrm{He}_4 = x^4 - 6x^2 + 3$. With $H_4(x) = 4\,\mathrm{He}_4(\sqrt{2}\,x) = 4\,(4x^4 - 12x^2 + 3)$ it gives $H_4$ above:

```lean
#cas (HermiteHe 4 x)
```

### Possible Issues

The degree is at most 60. `#cas (HermiteHe n x)` accepts degrees up to 80, and $H_n(x) = \sqrt{2}^{\,n}\,\mathrm{He}_n(\sqrt{2}\,x)$ relates the two:

```lean error
#cas (HermiteH 61 x)
```

---

The call takes two arguments, the degree and then the variable or the point:

```lean error
#cas (HermiteH 3)
```

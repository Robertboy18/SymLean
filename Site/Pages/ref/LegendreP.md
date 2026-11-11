+++
id = "LegendreP"
kind = "call"
title = "LegendreP"
summary = "The Legendre polynomial $P_n$ in monomials, proved at every real $x$, and its exact values at rational points."
calls = ["LegendreP"]
see_also = ["ChebyshevT", "HermiteHe", "BernoulliB", "expand", "N"]
guide = "special-functions"
tutorials = ["proving"]
+++

::: usage
`#cas (LegendreP ‹n› ‹x›)`
: gives the Legendre polynomial $P_n$ in the variable ‹x›, in monomials with exact rational coefficients, and proves the expansion at every real ‹x›.
`#cas (LegendreP ‹n› ‹q›)`
: gives the exact value of $P_n$ at the rational number ‹q› and proves it.
`#cas [N ‹d›] (LegendreP ‹n› ‹q›)`
: gives the exact value of $P_n$ at ‹q› with its first ‹d› significant digits, truncated toward zero, and proves their decimal bounds.
:::

`LegendreP` writes a Legendre polynomial in powers of its argument, or gives its exact value at a rational point. Its coefficients are rational, and they come out as exact fractions. The theorem holds at every real $x$ for SymLean’s `CAS.Analysis.SpecialFunctions.legendre n`, which we define as Mathlib’s shifted Legendre polynomial at $(1 - x)/2$, so it is the classical $P_n$, with $P_n(1) = 1$.

## Details and Options

- ‹n› is a natural number with $n \le 30$, a literal or a closed integer expression.
- The second argument is a variable, which the polynomial is written in and which may have any name other than `pi`, `π`, `Pi`, `e` and `E`, or a rational number.
- For the printed polynomial $p$ the theorem is `∀ x : ℝ, (CAS.Analysis.SpecialFunctions.legendre n).eval x = p`, from the coefficient formula `CAS.Analysis.SpecialFunctions.legendre_eval_eq_sum_coeff`. The kernel checks each coefficient, a closed rational computation.
- `legendre n` is Mathlib’s shifted Legendre polynomial `Polynomial.shiftedLegendre n` at $(1 - x)/2$, so $P_n(1) = 1$.
- At a rational $q$ the theorem is `(CAS.Analysis.SpecialFunctions.legendre n).eval q = v`, by `CAS.Analysis.SpecialFunctions.legendre_eval_ratCast`. With `[N d]` it adds the first $d$ significant digits of $v$, truncated toward zero, and their decimal bounds. The report prints `v = digits` when the digits are exact and `v ≈ digits` otherwise.
- With `[N d]`, $1 \le d \le 2000$, as for [[N]].
- `#cas [expand] (LegendreP n x)` prints the same polynomial as `#cas (LegendreP n x)`.
- There are no options.

## Examples

### Basic Examples

$P_3$ in monomials, with the theorem at every real $x$:

```lean
#cas (LegendreP 3 x)
```

---

The exact value at a rational point:

```lean
#cas (LegendreP 2 (1/2))
```

### Scope

A higher degree, with every coefficient in lowest terms:

```lean
#cas (LegendreP 10 x)
```

---

[[expand]] prints the same polynomial:

```lean
#cas [expand] (LegendreP 5 x)
```

---

`[N d]` adds the first digits of the exact value, here exact:

```lean
#cas [N 10] (LegendreP 2 (1/2))
```

### Applications

A proof can take the printed theorem as a hypothesis and specialize it, here at $x = \tfrac{1}{2}$:

```lean
theorem legendre_three_at_half
    (h : ∀ x : ℝ,
      (CAS.Analysis.SpecialFunctions.legendre 3).eval x = 5 / 2 * x ^ 3 - 3 / 2 * x) :
    (CAS.Analysis.SpecialFunctions.legendre 3).eval (1 / 2) = -7 / 16 := by
  rw [h]
  norm_num

#print axioms legendre_three_at_half
```

### Properties and Relations

The polynomial $P_3 = \tfrac{5}{2}x^3 - \tfrac{3}{2}x$ at $\tfrac{1}{2}$ is $\tfrac{5}{16} - \tfrac{3}{4} = -\tfrac{7}{16}$, the value of the theorem above, and the call at the point agrees:

```lean
#cas [N 5] (LegendreP 3 (1/2))
```

### Possible Issues

The degree is at most 30. The bound keeps the rational coefficients short, and `legendre n` is defined at every degree:

```lean error
#cas (LegendreP 31 x)
```

---

A call computes with numbers of at most 10000 digits, and $P_2(10^{5000}) = \tfrac{3 \cdot 10^{10000} - 1}{2}$ is larger:

```lean error
#cas (LegendreP 2 (10 ^ 5000))
```

---

`LegendreP` is a call, not a mode, and the message lists its three forms:

```lean error
#cas [LegendreP 5]
```

### Neat Examples

$P_5$ takes the value $\tfrac{1}{3}$ at $\tfrac{1}{3}$, a repeating decimal, so the report prints `≈`:

```lean
#cas [N 20] (LegendreP 5 (1 / 3))
```

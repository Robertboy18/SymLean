+++
id = "BernoulliB"
kind = "call"
title = "BernoulliB"
summary = "Bernoulli numbers $B_n$ and Bernoulli polynomials $B_n(x)$ for $n \\le 60$, with theorems about Mathlib’s `bernoulli` and `Polynomial.bernoulli`."
calls = ["BernoulliB"]
see_also = ["zeta", "sum", "LegendreP", "expand", "N"]
guide = "special-functions"
tutorials = ["proving"]
+++

::: usage
`#cas (BernoulliB ‹n›)`
: gives the Bernoulli number $B_n$ of ‹n› ≤ 60, with $B_1 = -\tfrac{1}{2}$, and proves `bernoulli ‹n› = ‹q›` in ℚ.
`#cas (BernoulliB ‹n› ‹x›)`
: gives the Bernoulli polynomial $B_n$ in the variable ‹x›, in monomials with exact rational coefficients, and proves the expansion at every real ‹x›.
`#cas (BernoulliB ‹n› ‹q›)`
: gives the exact value of $B_n$ at the rational number ‹q› and proves it.
`#cas [N ‹d›] (BernoulliB ‹n› ‹q›)`
: gives the exact value of $B_n$ at ‹q› with its first ‹d› significant digits, truncated toward zero, and proves their decimal bounds.
:::

`BernoulliB` gives you the Bernoulli numbers and the Bernoulli polynomials. Call it with one argument and you get the number $B_n$. Call it with two and you get the polynomial $B_n(x)$, whose constant term is the number $B_n$. The sign of $B_1$ is a convention, and here it is Mathlib’s, $B_1 = -\tfrac{1}{2}$, because the theorems are about Mathlib’s `bernoulli` and `Polynomial.bernoulli`. I want the printed number to agree with the definition your proof will use.

## Details and Options

- ‹n› is a natural number with $n \le 60$, a literal or a closed integer expression.
- For the number the theorem is `bernoulli n = q` in ℚ. Mathlib’s `bernoulli'` has $B'_1 = \tfrac{1}{2}$ instead. The proof rewrites with `CAS.Analysis.SpecialFunctions.bernoulli_eq_numerators`, which holds at every $n$ and writes $B_n$ as entry $n$ of the integer recurrence `bernoulliNumerators n` over $(n + 1)!$, and the kernel evaluates the recurrence and decides the equation (`decide +kernel`).
- $B_0 = 1$, and $B_n = 0$ for odd $n \ge 3$.
- For the polynomial the theorem is `∀ x : ℝ, Polynomial.aeval x (Polynomial.bernoulli n) = p` for the printed $p$, from `Polynomial.coeff_bernoulli` and integer Bernoulli numerators that the kernel evaluates (`CAS.Analysis.SpecialFunctions.bernoulli_eq_intPoly`).
- The second argument is a variable, which the polynomial is written in, or a rational number. At a rational $q$ the call proves the exact value of $B_n(q)$, and `[N d]` adds its first $d$ significant digits, truncated toward zero, with their decimal bounds in the theorem. The report prints `v = digits` when the digits are exact and `v ≈ digits` otherwise.
- `#cas [expand] (BernoulliB n x)` prints the same polynomial as `#cas (BernoulliB n x)`.
- The tactic [[cas]] does not evaluate `bernoulli`. A proof repeats the two steps of the command, as in the Applications below.
- There are no options.

## Examples

### Basic Examples

A Bernoulli number, in lowest terms:

```lean
#cas (BernoulliB 10)
```

---

A Bernoulli polynomial, with the theorem at every real $x$:

```lean
#cas (BernoulliB 4 x)
```

### Scope

$B_1$ follows Mathlib’s convention $B_1 = -\tfrac{1}{2}$:

```lean
#cas (BernoulliB 1)
```

---

The variable need not be `x`, and [[expand]] prints the same polynomial:

```lean
#cas [expand] (BernoulliB 2 y)
```

---

At a rational point, `[N d]` gives the exact value with its first digits:

```lean
#cas [N 10] (BernoulliB 2 (1/2))
```

### Applications

A proof can take the printed theorem as a hypothesis and specialize it, here at $x = \tfrac{1}{2}$:

```lean
theorem bernoulliB_four_at_half
    (h : ∀ x : ℝ, Polynomial.aeval x (Polynomial.bernoulli 4) =
      x ^ 4 - 2 * x ^ 3 + x ^ 2 - 1 / 30) :
    Polynomial.aeval (1 / 2 : ℝ) (Polynomial.bernoulli 4) = 7 / 240 := by
  rw [h]
  norm_num

#print axioms bernoulliB_four_at_half
```

---

The tactic [[cas]] does not evaluate `bernoulli`, so a proof repeats the two steps of the command, the rewrite and the kernel’s evaluation:

```lean
theorem bernoulli_ten : bernoulli 10 = 5 / 66 := by
  rw [CAS.Analysis.SpecialFunctions.bernoulli_eq_numerators]
  decide +kernel

#print axioms bernoulli_ten
```

### Properties and Relations

The constant term of $B_4(x) = x^4 - 2x^3 + x^2 - \tfrac{1}{30}$ is the Bernoulli number $B_4$:

```lean
#cas (BernoulliB 4)
```

---

The values of [[zeta]] at the nonpositive integers come from Bernoulli numbers, such as $\zeta(-1) = -B_2/2 = -\tfrac{1}{12}$:

```lean
#cas (zeta (-1))
```

### Possible Issues

Both forms stop at $n = 60$, the cutoff of the command, although `bernoulli_eq_numerators` holds at every $n$ and `Polynomial.bernoulli_def` gives the coefficients at every degree in a proof:

```lean error
#cas (BernoulliB 61)
```

```lean error
#cas (BernoulliB 61 x)
```

---

The index is an integer:

```lean error
#cas (BernoulliB (1/2))
```

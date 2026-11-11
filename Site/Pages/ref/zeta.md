+++
id = "zeta"
kind = "call"
title = "zeta"
summary = "Exact values of the Riemann zeta function at even positive and nonpositive integers, with a theorem about Mathlib’s `riemannZeta`."
calls = ["zeta"]
see_also = ["BernoulliB", "sum", "gamma"]
guide = "special-functions"
tutorials = ["proving"]
+++

::: usage
`#cas (zeta ‹s›)`
: gives the exact value of $\zeta(s)$ at an even positive or a nonpositive integer ‹s› and proves it as an equation about `riemannZeta ‹s›` in ℂ.
:::

`zeta` gives exact values of the Riemann zeta function at the even positive integers and at the nonpositive integers. At an even positive integer the value is a rational multiple of $\pi^s$, as in Euler’s $\zeta(2) = \pi^2/6$, and at a nonpositive integer it is rational. Both come from Bernoulli numbers that the kernel evaluates. The call has no formula for the odd integers from 3 on, and refuses them.

## Details and Options

- ‹s› is a closed rational expression whose value is an integer, such as `2` or `(-1)`, with $-59 \le s \le 60$.
- At an even $s = 2k > 0$ the theorem is `riemannZeta s = a * (Real.pi : ℂ) ^ s / b` with $a/b$ in lowest terms, and without `a *` when $a = 1$, by Mathlib’s `riemannZeta_two_mul_nat`, such as `riemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6`.
- At an integer $s \le 0$ the theorem is `riemannZeta s = q` with a rational $q$, by `riemannZeta_neg_nat_eq_bernoulli`.
- The equations hold in ℂ, for Mathlib’s `riemannZeta`, and their rational number comes from a Bernoulli number that the kernel evaluates.
- The odd integers $s \ge 3$ and the pole $s = 1$ are refused, and so are rationals that are not integers.
- The call is evaluated when it is the whole input of `#cas`.
- There are no options.

## Examples

### Basic Examples

Euler’s value of $\zeta(2)$, the sum of the reciprocal squares:

```lean
#cas (zeta 2)
```

---

At a negative integer the value is rational:

```lean
#cas (zeta (-1))
```

### Scope

Larger even values bring in Bernoulli numbers of higher index. The 691 in $\zeta(12)$ is the numerator of $B_{12} = -\tfrac{691}{2730}$:

```lean
#cas (zeta 12)
```

---

The value at 0:

```lean
#cas (zeta 0)
```

---

The negative even integers are the trivial zeros of $\zeta$:

```lean
#cas (zeta (-2))
```

### Applications

A proof can take the printed theorem as a hypothesis and use it:

```lean
theorem six_mul_zeta_two (h : riemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6) :
    6 * riemannZeta 2 = (Real.pi : ℂ) ^ 2 := by
  rw [h]
  ring

#print axioms six_mul_zeta_two
```

### Properties and Relations

$\zeta(2)$ is the sum of the series $\sum_{k \ge 1} 1/k^2$, and [[sum]] proves the sum as a `HasSum`:

```lean
#cas [sum k 1 ∞] (1/k^2)
```

---

Euler’s formula $\zeta(2k) = (-1)^{k+1} B_{2k} (2\pi)^{2k} / (2\,(2k)!)$ ties the even values to the Bernoulli numbers. With $B_4 = -\tfrac{1}{30}$ it gives $\zeta(4) = \tfrac{1}{30} \cdot \tfrac{16\pi^4}{48} = \tfrac{\pi^4}{90}$:

```lean
#cas (zeta 4)
```

```lean
#cas (BernoulliB 4)
```

### Possible Issues

At the odd integers $s \ge 3$ the call has no formula and refuses:

```lean error
#cas (zeta 3)
```

---

$s = 1$ is the pole. Mathlib’s `riemannZeta 1` is a convention, not a value of the series, and the call does not report it:

```lean error
#cas (zeta 1)
```

---

The argument is an integer:

```lean error
#cas (zeta (1/2))
```

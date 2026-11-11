+++
id = "special-functions"
kind = "guide"
title = "Special functions"
summary = "Gamma and zeta values, Bernoulli numbers, the error function, Bessel functions and the classical orthogonal polynomials, each with its theorem."
related_guides = ["number-theory", "numerics", "polynomials", "series-limits"]
tutorials = ["first-hour"]
+++

With special functions the conventions matter as much as the values. Mathlib’s `bernoulli` has $B_1 = -\tfrac{1}{2}$, and there are two families of Hermite polynomials, the physicists’ and the probabilists’. So I want every value to say which function it is about, and here it does. A special function is a call inside `#cas`, as in `#cas (gamma (5/2))` or `#cas (ChebyshevT 5 x)`. The exact values come with a theorem about Mathlib’s own function, such as `Real.Gamma` or `riemannZeta`. Two of the functions, `erf` and `BesselJ`, give digits only: you request them with `[N d]`, and the theorem is an enclosure of width at most $10^{-d}$.

::: commands
### Exact values
- gamma
- zeta
- BernoulliB
### Digits
- erf
- BesselJ
### Orthogonal polynomials
- LegendreP
- ChebyshevT
- ChebyshevU
- HermiteH
- HermiteHe
:::

The Gamma function at a half-integer is a rational multiple of $\sqrt{\pi}$, and the theorem is about Mathlib’s `Real.Gamma`, so a proof can use it as it is:

```lean
#cas (gamma (5/2))
```

A Chebyshev polynomial comes in monomials, and the theorem holds in every commutative ring at once, so a proof can specialize it to the ring it works in:

```lean
#cas (ChebyshevT 5 x)
```

Here are thirty proved digits of $\operatorname{erf} 1$. The Mathlib that SymLean builds on has no error function, so `erf` is SymLean’s own `CAS.erf`, defined by the Gaussian integral $\operatorname{erf} x = \frac{2}{\sqrt{\pi}} \int_0^x e^{-t^2}\,dt$. When it appears in a statement of yours, that definition is part of what a reader has to check:

```lean
#cas [N 30] (erf 1)
```

The exact values cover a fixed set of points. `gamma` takes integers and half-integers with $|q| \le \tfrac{1001}{2}$, and `zeta` takes even positive integers and nonpositive integers. At the odd integers $s \ge 3$ there is no formula, and `zeta` refuses. At a pole of $\Gamma$ the theorem is Mathlib’s value there, `Real.Gamma q = 0`, and the report says so. `erf` and `BesselJ` stop at 30 digits. The orthogonal polynomials have caps on the degree, from 30 for `LegendreP` to 80 for the Chebyshev polynomials and `HermiteHe`, and `BernoulliB` stops at $n = 60$. `gamma` and `zeta` are evaluated only when the call is the whole input of `#cas`, not inside a larger expression.

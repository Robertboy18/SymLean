+++
id = "sums"
kind = "guide"
title = "Sums and recurrences"
summary = "Finite sums and products in closed form, sums of series, and linear recurrences, each with a theorem."
related_guides = ["number-theory", "series-limits", "special-functions", "algebra"]
tutorials = ["first-hour", "proving"]
+++

What I usually want from a sum is a formula, not a number. With a symbolic upper bound $n$ you get a closed form, and SymLean proves it for every $n$ by induction. With a fixed upper bound the sum is evaluated exactly. A finite product in closed form also comes with a theorem for every upper bound. The sum of a series comes with a `HasSum` theorem, which also says that the series converges, and a linear recurrence with constant coefficients gets its general solution, or the only sequence with the given initial values.

::: commands
### Sums and products
- sum
- product
### Recurrences
- rsolve
:::

The Basel problem, with Mathlib’s `HasSum`. The theorem says that the series converges and that its sum is $\pi^2/6$. The sum starts at $k = 1$, so the theorem writes the shift out as $k + 1$:

```lean
#cas [sum k 1 ∞] (1/k^2)
```

Binet’s formula for the Fibonacci numbers. The theorem is an equivalence about every sequence `a : ℕ → ℝ`: it has the recurrence and these initial values exactly when it is the closed form, so no other sequence has them:

```lean
#cas [rsolve a n, a 0 = 0, a 1 = 1] (a (n + 2) = a (n + 1) + a n)
```

The closed forms of sums cover terms $c\,k^j r^k$, which include polynomials, geometric terms and their products, and hypergeometric terms through Gosper’s algorithm. The harmonic numbers have no closed form in hypergeometric terms, so $\sum 1/k$ is refused, and so is a summand with a parameter. A fixed upper bound sums at most 200 terms. A series takes terms $c\,k^j r^k$ with $|r| < 1$, or $c/k^{2m}$ through the values of the zeta function, so odd zeta values such as $\zeta(3)$ are refused. A product takes a constant times powers of linear factors $k + s$ with integer shifts, and without Hex those factors have to be written out. In a proof, `cas` proves the closed forms of finite sums and products. It doesn’t prove the statements about series or those of `rsolve`, but the closed form of a recurrence follows from the recurrence by induction.

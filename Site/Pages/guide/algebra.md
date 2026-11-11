+++
id = "algebra"
kind = "guide"
title = "Algebra"
summary = "Simplifying, expanding, factoring and combining fractions, each with a theorem about real numbers and its conditions."
related_guides = ["polynomials", "equations", "calculus", "hex", "tactics"]
tutorials = ["first-hour", "proving"]
+++

Most of the algebra I do on paper is moving an expression from one form to another: simplifying it, multiplying it out, factoring it, collecting the powers of one variable, or putting fractions over one denominator and splitting them apart again. These modes make those moves. Each answer comes with a theorem that the new form equals the input for all real values of the variables, under the conditions the rewriting needs.

The conditions come from division. Lean’s division is total ($1/0 = 0$), so $(x^2 - 1)/(x - 1) = x + 1$ is false at $x = 1$, where the left side is $0$. On paper I cancel that factor without a second thought. Here the modes that cancel or combine fractions print the denominators that must be nonzero, and the theorem has them as hypotheses.

::: commands
### Simplifying
- simplify
- fullSimplify
### Expanding and factoring
- expand
- factor
- collect
- trigExpand
### Rational functions
- together
- cancel
- apart
- numerator
- denominator
:::

A factorization needs no conditions at all. This one is an identity for all real $x$ and $y$, proved by `ring`, so the product is right whatever the factors turn out to be:

```lean
#cas [factor] (x^3*y - x*y^3)
```

Adding fractions is where the conditions show up. Here the sum goes over one denominator, and the theorem holds where the divisors of the input are nonzero. They are taken as you wrote them, so the report lists $x^2 - 1 \ne 0$ and $x - 1 \ne 0$:

```lean
#cas [together] (1/(x^2-1) + 1/(x-1))
```

Each mode has its limits, and I’d rather you meet them here than in the middle of a proof. `factor` on its own finds rational roots, perfect powers and homogeneous forms in two variables. A factor of degree two or more that’s left over is printed whole, and the report doesn’t claim it’s irreducible, so $x^4 + 4$ stays in one piece although it factors over $\mathbb{Q}$. With the optional [Hex library](guide:hex), the factors are proved irreducible over $\mathbb{Q}$ whenever Hex certifies every one of them. `together`, `cancel` and `apart` take the field operations and natural powers with polynomial divisors, and `apart` works in one variable. When there’s a square root, a logarithm or a sine in the expression, `simplify` and `fullSimplify` are the modes to use. `trigExpand` applies the addition and double-angle formulas and nothing else.

The same identities, written in Mathlib’s notation, are goals that the tactic [[cas]] proves, with the conditions as hypotheses.

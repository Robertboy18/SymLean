+++
id = "calculus"
kind = "guide"
title = "Calculus"
summary = "Derivatives, gradients, antiderivatives, definite integrals and extrema, each with a theorem about Mathlib’s definitions."
related_guides = ["series-limits", "numerics", "differential-equations", "tactics"]
tutorials = ["first-hour", "proving"]
+++

When a proof needs a derivative or an integral, I don’t want to work it out on paper and then convince Lean of it line by line. Here you can compute derivatives, gradients, antiderivatives, definite integrals and the extrema of polynomials, and use them on their own or as steps in a proof. A derivative comes with a theorem about Mathlib’s `HasDerivAt`, an antiderivative with a theorem about the interval integral, and both carry the conditions they need, such as $x \ne 0$ under a logarithm.

::: commands
### Derivatives
- derive
- grad
### Integrals
- integrate
- nintegrate
- cas-integrate-primitive
### Extrema
- maximize
- minimize
:::

Integration shows the idea best. Finding an antiderivative is a search, and a search can go wrong. Checking one is easy: differentiate it and compare with the integrand. So SymLean prints a candidate only after its derivative matches, and the fundamental theorem of calculus turns that into the theorem. It holds on every interval where the conditions hold, which here means every interval that avoids $x = 0$:

```lean
#cas [integrate x] (1 / (x ^ 3 + x))
```

The search is bounded. It covers polynomials and a table of elementary antiderivatives, substitution, rational functions, integration by parts, polynomials times exponentials, sines and cosines, and rational functions of $\sin x$ and $\cos x$. When no candidate passes the derivative check, the command stops with an error and proves nothing. $e^{x^2}$ is the classic case, since it has no elementary antiderivative, and `nintegrate` gives a definite integral of it as a decimal with a proved error bound instead. When I already have a primitive, from a book or from SymPy, `cas [integrate primitive := F]` checks mine. The extrema modes take a polynomial in one variable, and for other functions on an interval `cega` proves the bounds.

The same statements, written in Mathlib’s notation, are goals that the tactic [[cas]] proves.

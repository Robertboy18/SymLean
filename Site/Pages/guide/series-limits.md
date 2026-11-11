+++
id = "series-limits"
kind = "guide"
title = "Series and limits"
summary = "Taylor and Laurent expansions with a little-o remainder, and limits at a point, from one side or at ±∞."
related_guides = ["calculus", "sums", "special-functions", "tactics"]
tutorials = ["first-hour", "proving"]
+++

On paper a Taylor expansion ends with $+ \dots$, and I rarely stop to say what the dots mean. Here they become a theorem. Use a series to describe the local expansion of a function, and a limit to prove its limiting value. A series has exact coefficients and a theorem that the remainder is little-o of the last power, in Mathlib’s `=o[𝓝 a]`. A limit comes with a theorem about `Filter.Tendsto` on the filter that fits: the neighbourhood of the point or the punctured one, one side of it, or `atTop` and `atBot`.

::: commands
### Series
- series
### Limits
- limit
:::

The exponential at 0. The theorem is the precise form of the dots: $e^x$ minus the printed polynomial is little-o of $x^6$ as $x \to 0$:

```lean
#cas [series x 0 6] (exp x)
```

The classical limit. In Lean $\sin x / x$ is $0/0 = 0$ at $x = 0$, so the value there is beside the point, and the theorem is on the punctured neighbourhood of 0. In a proof, the tactic [[cas]] proves the same `Tendsto` statement:

```lean
#cas [limit x → 0] (sin x / x)
```

A series needs exact coefficients, so every function in it has to sit at a point where its value is rational: `sin`, `cos`, `exp`, `atan` and `asin` at 0, `log` and `acos` at 1, and square roots of rational squares. The same goes for the derivatives that a limit of a quotient uses when its denominator vanishes. The centre of a series is a rational number, and so is the point of a limit, unless it is $\pm\infty$. A series goes up to order 12. Some limits at infinity are out of reach of both routes, and then the message says why each one stopped. The tactic `cas` doesn’t prove the little-o statement, so in a proof I take the printed theorem as a hypothesis.

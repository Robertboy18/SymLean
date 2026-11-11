+++
id = "numerics"
kind = "guide"
title = "Numerics"
summary = "Digits, ranges, integrals, roots and eigenvalue bounds, each a proved enclosure, and the tactic `cega` that proves numerical bounds."
related_guides = ["certificates", "calculus", "equations", "linear-algebra", "tactics"]
tutorials = ["first-hour", "trust"]
+++

Sooner or later a proof needs an actual number: some digits of a constant, the range of a function on a box, a definite integral, a root, or a bound on an eigenvalue. Every number here comes with a theorem. The printed digits are digits of the real value, and an enclosure holds at every point of its box, not at sample points. The arithmetic is exact rational interval arithmetic from [FloatLib](https://github.com/lean-dojo/FloatLib), so the error of finite precision is part of the bound, and there is no rounding left over for me to argue about.

::: commands
### Digits
- N
### Ranges and extrema
- enclose
- maximize
- minimize
### Integrals, roots and differential equations
- nintegrate
- findRoot
- ndsolve
### Matrices
- eigenvalueBounds
### Bounds in proofs
- cega
- cega-using
- cega-query
### Settings
- options
:::

Fifty digits of $\pi$, each one proved. The theorem puts $\pi$ between the printed decimal and the next one up:

```lean
#cas [N 50] (pi)
```

The same arithmetic proves bounds inside a proof. A bound like the one below is obvious from a plot and tedious to prove by hand. Here `cega` reads the box $[0, 1]$ from the hypothesis and proves $e^x \le 2.72$ on it, which is tight, since $e \approx 2.71828$:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : Real.exp x ≤ 2.72 := by
  cega
```

An enclosure is always valid, but it isn’t always tight, and `(depth := n)` bisects the box first when you need it closer. A box has at most 8 coordinates and rational endpoints, and every subexpression has to be defined on all of it: denominators stay away from zero and the arguments of `log` stay positive. `cega` needs rational bounds on every variable among the hypotheses. When a bound is false, or true but out of reach of the enclosures, it refuses, and the message proposes the next call to try. Every check stays in the kernel unless you turn on `cega.nativeCertificates`, which also trusts Lean’s compiler. The [trust tutorial](tutorial:trust) goes through what that adds to the trusted base.

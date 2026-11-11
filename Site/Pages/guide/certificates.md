+++
id = "certificates"
kind = "guide"
title = "Certificates"
summary = "The statements behind the numerics: enclosures, bounds and approximations on a box, the carriers that hold them, and the tactics that prove and reuse them."
related_guides = ["numerics", "tactics"]
tutorials = ["trust", "proving"]
+++

CEGA stands for Certified Enclosures, Guarantees, and Approximations. I wanted a numerical result to be a statement you can read and use like any other, so its statements are ordinary propositions about real functions on a set, and each one has a fixed meaning:

::: table
Statement | Meaning
`EnclosedOn f s lo hi` | $\mathrm{lo} \le f(x) \le \mathrm{hi}$ for every $x \in s$
`BoundOn f s hi` | $f(x) \le \mathrm{hi}$ for every $x \in s$
`ApproxOn f g s ε` | $\lVert f(x) - g(x) \rVert \le \varepsilon$ for every $x \in s$
`ResidualBound r s ε` | $\lVert r(x) \rVert \le \varepsilon$ for every $x \in s$
:::

A carrier, such as `EnclosureCert`, `BoundCert`, `ApproxCert`, `ResidualCert`, `ModelApproxCert` or `QuadratureCert`, keeps the function, the domain, the bounds and a proof of its statement. Anything else it holds, such as the order of a model, is data and proves nothing. Only the proved statement counts.

::: commands
### Proving the statements
- cega
- enclose
### Reusing a carrier
- cega-using
### Asking for the call to keep
- cega-query
### Settings
- options
:::

The examples on this page run after `open CAS.Certificate`. `ℝ^n` is our notation for Mathlib’s `EuclideanSpace ℝ (Fin n)`, and `p 0` is the first coordinate of a point `p`.

```lean hidden
open CAS.Certificate
```

The explicit form of `cega` names the box and the expression. The bounds you state may be weaker than the ones it computes, and exact arithmetic covers the difference:

```lean
example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0))
      {p : ℝ^1 | 0 ≤ p 0 ∧ p 0 ≤ 1} 0 (1 / 2) := by
  cega [enclose x in [0, 1]] (x / (1 + x))
```

When the domain is a box with rational bounds, bare `cega` reads the function and the box off the goal, so you don’t have to repeat them:

```lean
example :
    BoundOn (fun p : ℝ^2 ↦ p 0 * p 1)
      {p : ℝ^2 | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 2 ≤ p 1 ∧ p 1 ≤ 3} 4 := by
  cega
```

In practice, most uses need no certificate statement at all. On an inequality whose variables have rational bounds in the context, `cega` builds the certificate itself and carries it to the goal, as in [[numerics|Numerics]].

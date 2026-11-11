+++
id = "tactics"
kind = "guide"
title = "Tactics"
summary = "The tactics: `cas` for identities, calculus and limits, `cega` for numerical bounds, `cas_nf` for normal forms, and the options that tune them."
related_guides = ["certificates", "calculus", "numerics"]
tutorials = ["proving", "trust"]
+++

The calculator is only half of SymLean. The same calculations that `#cas` prints also close goals: you state the goal in Mathlib’s terms, and the tactic finds a proof that the kernel checks. If no route works, the goal stays as it was, and the message says what was tried.

::: commands
### Closing goals
- cas
- cas-using
- cega
- cega-using
### Asking for the call to keep
- cas-query
- cega-query
### Rewriting
- cas_nf
### Settings
- options
:::

Here is one of each. `cas` proves a derivative, and `cega` proves a numerical bound:

```lean
example (x : ℝ) : deriv (fun x ↦ x ^ 2 * Real.sin x) x = 2 * x * Real.sin x + x ^ 2 * Real.cos x := by
  cas

example : Real.sqrt 2 ≤ 1.415 := by
  cega
```

+++
id = "options"
kind = "option"
title = "Options"
summary = "The settings of `cas`, `cega` and `#cas`: the budget of a call, what a report shows, and the trace classes."
see_also = ["cas", "cega", "cas-query", "cega-query", "cas-command"]
tutorials = ["trust"]
+++

::: usage
`set_option ‹name› ‹value› in ‹command›`
: sets an option for one command, declaration or tactic.
`set_option ‹name› ‹value›`
: sets it to the end of the section or file.
`set_option trace.‹class› true in ‹command›`
: prints the messages of a trace class under the call.
:::

SymLean works within budgets, because I’d rather have an expensive call stop and say so than hang. When a call would need more work than its budget allows, it stops, and the message names the budget. A box query that is too big is refused before the kernel starts, so it fails at once instead of stalling a build. Two more options choose what a report shows, and the trace classes print the steps of a route.

## Details and Options

- An option is an ordinary Lean option. With `in` it holds for the next command, and without it to the end of the section or file.
- A trace class is an option whose name starts with `trace.`. Set to `true`, it prints its messages under the call, in the InfoView and in the output of `lake build`.

### Options of `cas` and `#cas`

::: table
Option | Default | What it sets
`cas.verbose` | `false` | Shows the full report under a suggestion of `cas?` and `cega?`, and the derivation trees of `#cas` reports.
`cas.suggest` | `false` | Offers the first checked statement of a `#cas` report as an `example` to paste in place of the command.
`cas.maxDigits` | `2000` | The most decimal digits that a `#cas` command or a CEGA query may ask for.
`cas.maxDerivativeSteps` | `512` | The most recursive steps of the search for derivative rules.
`cas.grindHeartbeats` | `20000` | The heartbeats, in thousands, of the `grind` and `norm_num` fallbacks of bare `cas`. `0` turns them off.
`cas.maxReadBackWork` | `100000` | The most read-back steps for checked data over variable types other than `Fin`.
:::

### Options of `cega`

::: table
Option | Default | What it sets
`cega.maxRefinementWork` | `4096` | The most planner calls of a subdivided query, estimated before any kernel work. Raising it permits a larger search and never changes the depth.
`cega.maxPrecision` | `256` | The largest Taylor order, number of logarithm terms or number of square-root digits in a query.
`cega.maxDimension` | `8` | The most coordinates of a box query.
`cega.maxFaceReductions` | `5` | The most nested reductions by monotonicity. Each one roughly doubles the kernel work.
`cega.maxIntegrationPanels` | `256` | The most panels of the doubling search of bare `cega` on an integral. `(panels := n)` is not capped.
`cega.nativeCertificates` | `false` | Lets `cega [fast]` and `cega [fast, batch := n]` check finite certificates with compiled code, which also trusts Lean’s compiler. `lake build -R -Kcertificates=fast` builds SymLean with it on.
:::

### Options of the optional libraries

::: table
Option | Default | What it sets
`cas.hexHeartbeats` | `20000` | With `CASHex`: the heartbeats, in thousands, of the Hex route of `cas`. `0` turns the route off.
`cas.oracle.timeout` | `120000` | With `CASOracle`: the deadline of one oracle run, in milliseconds.
:::

### Trace classes

::: table
Trace class | What it prints
`trace.cega.stated` | Each kernel check of a stated bound, and its outcome.
`trace.cega.integration` | For bare `cega` on an integral: the panel count, the method and the precision of the quadrature, and the enclosure.
`trace.cega.native` | The stages of a finite native certificate.
`trace.cas.fallback` | The complete diagnostics of the `grind` and `norm_num` fallbacks in a failure report of `cas`.
`trace.cas.derivativeRules` | The rules tried on each `HasDerivAt` goal, and the error of each rule that fails.
`trace.cas.validation` | The validation of a proof before it closes a goal, and the replay of a `cas?` or `cega?` suggestion.
`trace.cas.profile` | Kernel evaluations, proof validations and axiom checks, each as a profile node of its own. `trace.profiler` shows them too.
:::

## Examples

### Basic Examples

`cas.suggest` turns a report into an `example` to paste in place of the command:

```lean
set_option cas.suggest true in
#cas [derive x] (tan x)
```

---

The suggestion, pasted:

```lean
example (x : ℝ) (h : Real.cos x ≠ 0) :
    HasDerivAt (fun x ↦ Real.tan x) (1 / Real.cos x ^ 2) x := by
  cas
```

---

`trace.cega.stated` shows the bound that the kernel checked:

```lean
set_option trace.cega.stated true in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega
```

### Scope

`trace.cega.integration` shows the quadrature behind a bound on an integral:

```lean
set_option trace.cega.integration true in
example : |(∫ x in (0 : ℝ)..1, x ^ 2) - 1 / 3| ≤ 1 / 100 := by
  cega
```

---

`cas.verbose` shows the full report under a suggestion:

```lean
set_option cas.verbose true in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega?
```

### Options

Without `in`, an option holds to the end of the section:

```lean
section
set_option cas.suggest true

#cas [simplify] (x + x)

end
```

### Applications

Five bounds in one conjunction, each proved by `cega`. The trace shows the kind of query and the bound that each check proved:

```lean
set_option trace.cega.stated true in
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    x * (1 - x) < 1 / 3 ∧ 0 ≤ x * (1 - x) ∧ x * (1 - x) > -1 / 2 ∧ |x - 1 / 2| < 1 ∧
      3 / 10 ≥ x * (1 - x) :=
  ⟨by cega, by cega, by cega, by cega, by cega⟩
```

### Properties and Relations

The options in parentheses belong to one call, where `set_option` holds for a whole command. Here the digits of [[findRoot]]:

```lean
#cas (digits := 30) [findRoot x in [1, 2]] (x^2 - 2)
```

### Possible Issues

A fallback that runs out of its budget says so. Here `grind` gets a thousand heartbeats:

```lean error
set_option cas.grindHeartbeats 1 in
example (x : ℝ) (h₁ : x - 1 ≠ 0) (h₂ : x + 1 ≠ 0) :
    (x ^ 3 - 1) / (x ^ 2 - 1) = (x ^ 2 + x + 1) / (x + 1) := by
  cas
```

---

A box with nine coordinates is over `cega.maxDimension`:

```lean error
example (x0 x1 x2 x3 x4 x5 x6 x7 x8 : ℝ) (h0 : x0 ∈ Set.Icc (0 : ℝ) 1)
    (h1 : x1 ∈ Set.Icc (0 : ℝ) 1) (h2 : x2 ∈ Set.Icc (0 : ℝ) 1) (h3 : x3 ∈ Set.Icc (0 : ℝ) 1)
    (h4 : x4 ∈ Set.Icc (0 : ℝ) 1) (h5 : x5 ∈ Set.Icc (0 : ℝ) 1) (h6 : x6 ∈ Set.Icc (0 : ℝ) 1)
    (h7 : x7 ∈ Set.Icc (0 : ℝ) 1) (h8 : x8 ∈ Set.Icc (0 : ℝ) 1) :
    x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 ≤ 9 := by
  cega
```

---

Twenty thousand digits of $\pi$ are over `cas.maxDigits`:

```lean error
example : (3 : ℝ) ≤ Real.pi ∧ Real.pi ≤ 4 := by
  cega (digits := 20000) [enclose] Real.pi
```

### Neat Examples

A sum of six squares on $[1, 2]^6$. Every coordinate could be reduced by monotonicity, and that search would take about 385 seconds and 42 GB. `cega.maxFaceReductions` refuses it at once:

```lean error
example (x0 x1 x2 x3 x4 x5 : ℝ) (h0 : x0 ∈ Set.Icc (1 : ℝ) 2) (h1 : x1 ∈ Set.Icc (1 : ℝ) 2)
    (h2 : x2 ∈ Set.Icc (1 : ℝ) 2) (h3 : x3 ∈ Set.Icc (1 : ℝ) 2) (h4 : x4 ∈ Set.Icc (1 : ℝ) 2)
    (h5 : x5 ∈ Set.Icc (1 : ℝ) 2) :
    x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3 + x4 * x4 + x5 * x5 ≤ 24 := by
  cega
```

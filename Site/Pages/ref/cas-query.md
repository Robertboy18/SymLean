+++
id = "cas-query"
kind = "tactic"
title = "cas?"
summary = "Proves the goal as `cas` does, and suggests the call to keep in the proof."
forms = ["CAS.tacticCas?"]
see_also = ["cas", "cega-query", "cas-using", "cas-integrate-primitive", "cega", "options"]
tutorials = ["proving", "trust"]
+++

::: usage
`cas?`
: proves the goal as [[cas]] does, and suggests the call to keep in the proof.
`cas? using ‹h›`, `cas? using [‹h₁›, ‹h₂›]`, `cas? [‹l₁›, ‹l₂›]`
: the same for the other forms of `cas`, with the same arguments.
`cas? [integrate primitive := ‹F›]`
: the same for a supplied primitive, also with `using ‹h›` inside the brackets.
:::

I write `cas?` while a proof is still taking shape. It closes the goal as `cas` would, then tells me which route did it and what to write instead. When the box route proved a bound, the suggestion names the box and the expression, so the finished proof says what it checks.

## Details and Options

- After the box route, the suggestion is `cega [enclose x in [a, b]] e`, with the box and the expression that the route used.
- After the integration route, when it checked a primitive $F$ written as an ordinary function, the suggestion is `cas [integrate primitive := F]`.
- Either one is suggested only when it closes the original goal with no error. Otherwise the suggestion is the call as written.
- Lean runs the suggested call on the original goal before it shows it. The line under the suggestion names the route that closed the goal, and the InfoView shows that route with its checked evidence.
- `set_option cas.verbose true` replaces that line by the full report, with the planner steps and the checked evidence. It is `false` by default.
- `cas?` fails where `cas` fails, with the message of `cas`, and then suggests nothing.
- The other options are those of [[cas]].

## Examples

### Basic Examples

A polynomial identity. The suggestion is plain `cas`, and the line under it names the route:

```lean
example (x : ℝ) : (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by
  cas?
```

---

A bound on a box. The route was the box route of [[cega]], and the suggestion is the explicit query:

```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 3 := by
  cas?
```

---

A definite integral, by a search for an antiderivative:

```lean
example : (∫ x in (0 : ℝ)..1, x * Real.exp x) = 1 := by
  cas?
```

### Scope

Evidence for a domain condition, as in [[cas-using|`cas using`]]:

```lean
example (x : ℝ) (hx : 0 < x) :
    deriv (fun t : ℝ ↦ t ^ (3 / 2 : ℝ)) x = (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
  cas? using hx
```

---

Equation hypotheses as facts:

```lean
example (x y : ℝ) (h₁ : x + y = 3) (h₂ : x - y = 1) : x = 2 := by
  cas? using [h₁, h₂]
```

---

A definition to unfold:

```lean
def square (x : ℝ) : ℝ := x * x

example (x : ℝ) : square (x + 1) = x ^ 2 + 2 * x + 1 := by
  cas? [square]
```

---

A supplied primitive, with and without domain evidence:

```lean
example : (∫ x in (0 : ℝ)..1, 2 * x) = 1 := by
  cas? [integrate primitive := fun x ↦ x ^ 2]
```

```lean
example (a b : ℝ) (h : ∀ t ∈ Set.uIcc a b, t ≠ 0) :
    (∫ t in a..b, Real.log t / t) = Real.log b ^ 2 / 2 - Real.log a ^ 2 / 2 := by
  cas? [integrate primitive := fun t ↦ Real.log t ^ 2 / 2 using h]
```

### Options

`set_option cas.verbose true` shows the full report under the suggestion:

```lean
set_option cas.verbose true in
example (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
  cas?
```

### Applications

The suggested call replaces `cas?`, and the theorem keeps it. Only the three standard axioms are used:

```lean
theorem exp_le_three (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 3 := by
  cega [enclose x in [0, 1]] (Real.exp x)

#print axioms exp_le_three
```

### Properties and Relations

[[cega-query|`cega?`]] does the same for [[cega]]:

```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cega?
```

---

A limit, written with Mathlib’s filters. The statement is one that [[limit]] prints:

```lean
open Filter Topology in
example : Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by
  cas?
```

### Possible Issues

`cas?` fails where `cas` fails, with the message of `cas`:

```lean error
example (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 2 := by
  cas?
```

---

A resource limit is not a refutation. The message names a larger setting to try:

```lean error
example (x : ℝ) : x + 1 = 1 + x := by
  set_option maxRecDepth 12 in cas?
```

### Neat Examples

An integral whose right side is $F(b) - F(a)$ for $F(t) = \tfrac{1}{2} \log^2 t$, with the condition $t \ne 0$ on the interval:

```lean
theorem log_div_integral_of_goal (a b : ℝ) (h : ∀ t ∈ Set.uIcc a b, t ≠ 0) :
    (∫ t in a..b, Real.log t / t) =
      Real.log b ^ 2 / 2 - Real.log a ^ 2 / 2 := by
  cas? using h
```

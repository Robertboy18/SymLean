+++
id = "cas_nf"
kind = "tactic"
title = "cas_nf"
summary = "Rewrites the real terms of a goal or a hypothesis to a normal form, with a checked proof of each rewrite."
forms = ["CAS.ExactTactic.tacticCas_nf_", "CAS.ExactTactic.tacticCas_nfUsing__", "CAS.ExactTactic.convCasNF", "CAS.ExactTactic.convCasNFUsing"]
see_also = ["cas", "simplify", "expand", "together", "cancel"]
guide = "tactics"
tutorials = ["proving"]
+++

::: usage
`cas_nf`
: rewrites the real terms of the goal to their normal form, and closes the goal when it becomes a reflexive equality.
`cas_nf at ‹h›`
: rewrites the hypothesis ‹h›. `at ‹h› ⊢` and `at *` choose locations as for `simp`.
`cas_nf using ‹h›`
: the same, with ‹h› as evidence for the conditions a rewrite needs, such as a nonzero denominator.
`conv => cas_nf`
: rewrites the focused term only, also as `cas_nf using ‹h›`.
:::

[[cas]] closes a goal or leaves it alone. Sometimes I want something in between: the goal is not finished, but one quotient in it should cancel, or a hypothesis should look like the goal. `cas_nf` rewrites to a normal form and leaves the rest of the proof to me.

## Details and Options

- `cas_nf` turns the goal `P e` into `P e'`, with a proof of $e = e'$. A polynomial gets the normal form of Mathlib’s `ring_nf`. An expression with quotients, roots, logarithms or trigonometric functions gets the normal form of the checked symbolic routes.
- A rewrite that needs a condition, such as $x - y \ne 0$ to cancel $(x^2 - y^2)/(x - y)$, takes it from the local context or from `using h`. For two conditions, pass `And.intro h₁ h₂`.
- Without the condition the rewrite is refused, never assumed. Lean’s division is total, and the normal form keeps that meaning: $x/0$ becomes $0$.
- `cas_nf` normalizes, and is not an equality solver: two equal analytic expressions can keep different normal forms.
- It fails when it changes nothing.
- There are no options.

## Examples

### Basic Examples

A polynomial identity becomes reflexive, and the goal closes:

```lean
example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  cas_nf
```

---

A hypothesis and the goal brought to the same form:

```lean
example (x y c : ℝ) (h : (x + y) ^ 2 ≤ c) : x ^ 2 + 2 * x * y + y ^ 2 ≤ c := by
  cas_nf at h ⊢
  exact h
```

---

A quotient that cancels, under a function you know nothing about, with the denominator condition passed by `using`:

```lean
example (F : ℝ → ℝ) (x y z : ℝ) (hden : x - y ≠ 0) (h : F (x + y) = z) :
    F ((x ^ 2 - y ^ 2) / (x - y)) = z := by
  cas_nf using hden
  exact h
```

### Scope

The Pythagorean identity inside a hypothesis:

```lean
example (P : ℝ → Prop) (x : ℝ) (h : P (Real.sin x ^ 2 + Real.cos x ^ 2)) : P 1 := by
  cas_nf at h
  exact h
```

---

The normal form of $e^{\log x}$ depends on what you know about $x$:

```lean
example (P : ℝ → Prop) (x : ℝ) (hx : 0 < x) (h : P (Real.exp (Real.log x))) : P x := by
  cas_nf using hx at h
  exact h
```

```lean
example (P : ℝ → Prop) (x : ℝ) (hx : x ≠ 0) (h : P (Real.exp (Real.log x))) : P |x| := by
  cas_nf using hx at h
  exact h
```

```lean
example (P : ℝ → Prop) (x : ℝ) (hx : x < 0) (h : P (Real.exp (Real.log x))) : P (-x) := by
  cas_nf using hx at h
  exact h
```

---

Square roots, with and without a sign condition:

```lean
example (P : ℝ → Prop) (x : ℝ) (hx : 0 ≤ x) (h : P (√x ^ 2)) : P x := by
  cas_nf using hx at h
  exact h
```

```lean
example (P : ℝ → Prop) (x : ℝ) (h : P (√(x ^ 2))) : P |x| := by
  cas_nf at h
  exact h
```

---

Two conditions at once:

```lean
example (P : ℝ → Prop) (F : ℝ → ℝ → ℝ) (x y z : ℝ) (hz : 0 < z) (hden : x - y ≠ 0)
    (h : P (F (Real.exp (Real.log z)) ((x ^ 2 - y ^ 2) / (x - y)))) :
    P (F z (x + y)) := by
  cas_nf using And.intro hz hden at h
  exact h
```

### Options

In `conv` mode only the focused term changes. Here the first argument is rewritten and the second, the same term, is not:

```lean
example (P : ℝ → ℝ → Prop) (x y : ℝ) (h : P (x * y * 2 + x ^ 2 + y ^ 2) ((x + y) ^ 2)) :
    P ((x + y) ^ 2) ((x + y) ^ 2) := by
  conv =>
    arg 1
    cas_nf
  exact h
```

---

`cas_nf using h` works under a binder too:

```lean
example (F : ℝ → ℝ) (hden : ∀ t, F t ≠ 0) :
    (fun t ↦ F t / F t) = (fun _ ↦ (1 : ℝ)) := by
  conv =>
    lhs
    intro t
    cas_nf using hden t
```

### Applications

A theorem whose proof is one normalization and one `exact`. Only the three standard axioms are used:

```lean
theorem square_le (x y c : ℝ) (h : (x + y) ^ 2 ≤ c) : x ^ 2 + 2 * x * y + y ^ 2 ≤ c := by
  cas_nf at h ⊢
  exact h

#print axioms square_le
```

### Properties and Relations

[[cancel]] shows the same cancellation as a `#cas` report, with its condition:

```lean
#cas [cancel] ((x ^ 2 - y ^ 2) / (x - y))
```

---

Lean’s division is total. `cas_nf` keeps that meaning, so $x/0$ is $0$:

```lean
example (P : ℝ → Prop) (x : ℝ) (h : P (x / 0)) : P 0 := by
  cas_nf at h
  exact h
```

### Possible Issues

`cas_nf` fails when it changes nothing. This goal is in normal form already, and `exact h` closes it:

```lean error
example (P : ℝ → Prop) (x : ℝ) (h : P x) : P x := by
  cas_nf
```

---

A cancellation needs its condition. Here $x - 1 \ne 0$ is missing, and the message says what kind of condition to supply:

```lean error
example (P : ℝ → Prop) (x : ℝ) (h : P ((x ^ 2 - 1) / (x - 1))) : P (x + 1) := by
  cas_nf at h
  exact h
```

### Neat Examples

Arguments are normalized before equal atoms are collected, so $F(x + 0) + F(x)$ becomes $2F(x)$:

```lean
example (P : ℝ → Prop) (F : ℝ → ℝ) (x : ℝ) (h : P (F (x + 0) + F x)) : P (2 * F x) := by
  cas_nf at h
  exact h
```

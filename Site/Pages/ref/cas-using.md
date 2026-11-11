+++
id = "cas-using"
kind = "tactic"
title = "cas using"
summary = "Proves the goal as `cas` does, with your hypotheses as evidence for the conditions that the routes need."
forms = ["CAS.ExactTactic.casUsing", "CAS.ExactTactic.casUsingFacts"]
see_also = ["cas", "cas-query", "cas_nf", "derive", "integrate"]
tutorials = ["proving"]
+++

::: usage
`cas using ‹h›`
: proves the goal as [[cas]] does, with ‹h› as evidence for the conditions that the routes need, such as $x \ne 0$ for $\log x$.
`cas using [‹h₁›, ‹h₂›]`
: the same with a list of complete proofs, added as local facts.
:::

Many statements about real functions are true only where the functions are defined. The derivative of $x \log x$ is $\log x + 1$ for $x \ne 0$, but at $x = 0$ Lean’s `deriv` is $0$, while the right side is $\log 0 + 1 = 1$, since Mathlib sets $\log 0 = 0$. `cas` never assumes a condition like that. You give it one with `using`, and the proof uses exactly what you gave.

## Details and Options

- On a derivative or an integral, ‹h› is the domain evidence: a nonzero, positivity or branch hypothesis, such as `hx : x ≠ 0` or `hx : 0 < 1 - x ^ 2`.
- For an integral from $a$ to $b$, the condition holds on the whole interval and is stated as `∀ t ∈ Set.uIcc a b, …`.
- ‹h› is any proof term: an applied hypothesis such as `h 0`, a fact proved in place with `show … from …`, or `And.intro h₁ h₂` for two conditions.
- On an ordinary equation, ‹h› rewrites the goal when its left side occurs in it. Otherwise the denominators of ‹h› are cleared and it enters a linear combination.
- `cas using [h₁, h₂]` adds each proof as a local fact. Inequalities and other propositions help with arithmetic and domain conditions, and equalities also go to the search for polynomial consequences.
- The list holds proofs, not simp lemmas. For lemmas and definitions to unfold, [[cas]] has `cas [l₁, l₂]`.
- A missing condition is reported, never added.
- The options are those of [[cas]].

## Examples

### Basic Examples

A derivative that needs $x \ne 0$:

```lean
example (x : ℝ) (hx : x ≠ 0) :
    deriv (fun t : ℝ ↦ t * Real.log t) x = Real.log x + 1 := by
  cas using hx
```

---

An integral that needs the integrand to be defined on the whole interval:

```lean
example (a b : ℝ) (hpositive : ∀ t ∈ Set.uIcc a b, 0 < t) :
    (∫ t in a..b, 1 / t) = Real.log b - Real.log a := by
  cas using hpositive
```

---

Two equations as facts, over any commutative ring:

```lean
theorem mul_minor_eq_zero {R : Type*} [CommRing R] (a b c d e f : R)
    (h₁ : a * d = b * c) (h₂ : c * f = e * d) :
    c * (a * f - b * e) = 0 := by
  cas using [h₁, h₂]
```

### Scope

One-sided evidence settles the sign inside an absolute value:

```lean
example (x : ℝ) (hpositive : 0 < 2 * x + 1) :
    deriv (fun t : ℝ ↦ |2 * t + 1|) x = 2 := by
  cas using hpositive
```

---

An inverse function, inside its domain:

```lean
example (x : ℝ) (hinside : 0 < 1 - x ^ 2) :
    HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x := by
  cas using hinside
```

---

Negative powers, and a nested derivative:

```lean
example (x : ℝ) (hx : x ≠ 0) :
    deriv (fun t : ℝ ↦ t ^ (-2 : ℤ)) x = -2 / x ^ 3 := by
  cas using hx
```

```lean
example (x : ℝ) (hx : x ≠ 0) :
    deriv (deriv (fun t : ℝ ↦ Real.log (2 * t))) x = -(x ^ 2)⁻¹ := by
  cas using hx
```

---

Positivity evidence covers a nonzero condition, here $4 \pi s \ne 0$:

```lean
example (s : ℝ) (h : 0 < 4 * Real.pi * s) :
    deriv (fun t : ℝ ↦ Real.log (4 * Real.pi * t)) s = 1 / s := by
  cas using h
```

---

A real power with a symbolic exponent. The interval may contain $0$, since $r > -1$:

```lean
example (r a b : ℝ) (hr : -1 < r) :
    (∫ t : ℝ in a..b, t ^ r) = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) := by
  cas using hr
```

---

An equation with a quotient as the hypothesis. Its denominators are cleared, with $q \ne 0$ from the context:

```lean
example (p q : ℝ) (hq : q ≠ 0) (h : p / q = p - 1) : p = q * (p - 1) := by
  cas using h
```

### Options

Evidence proved in place. Here $r + 1 > 0$ is what I know, and the route wants $-1 < r$:

```lean
example (r a b : ℝ) (hr : 0 < r + 1) :
    (∫ t : ℝ in a..b, t ^ r) = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) := by
  cas using (show -1 < r from by linarith)
```

---

Two conditions at once, with `And.intro`:

```lean
example (r a b : ℝ) (hr : r ≠ -1) (hab : (0 : ℝ) ∉ Set.uIcc a b) :
    (∫ t : ℝ in a..b, t ^ r) = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) := by
  cas using And.intro hr hab
```

---

Applied hypotheses, in a list and alone:

```lean
example (x : ℝ) (hlower : ∀ t : ℝ, t = x → 1 ≤ t) (hupper : ∀ t : ℝ, t = x → t ≤ 2) :
    x ^ 2 ≤ 4 := by
  cas using [hlower x rfl, hupper x rfl]
```

```lean
example (f : ℝ → ℝ) (h : ∀ t, (1 : ℝ) ≤ f t) : 0 ≤ f 0 := by
  cas using (h 0)
```

### Applications

An integral with two parameters. The only condition is that $a$ and $b$ are not both zero:

```lean
theorem exp_mul_sin_over_unit (a b : ℝ) (h : a ^ 2 + b ^ 2 ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.exp (a * x) * Real.sin (b * x) =
      (Real.exp a * (a * Real.sin b - b * Real.cos b) + b) / (a ^ 2 + b ^ 2) := by
  cas using h

#print axioms exp_mul_sin_over_unit
```

### Properties and Relations

[[derive]] prints the same derivative together with the condition it needs:

```lean
#cas [derive x] (x * log x)
```

---

[[cas-query|`cas?`]] accepts the same evidence and suggests the call to keep:

```lean
example (x : ℝ) (hx : 0 < x) :
    deriv (fun t : ℝ ↦ t ^ (3 / 2 : ℝ)) x = (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
  cas? using hx
```

### Possible Issues

Without the condition, `cas` refuses. At $x = 0$ this statement is false in Lean:

```lean error
example (x : ℝ) : deriv (fun t : ℝ ↦ t * Real.log t) x = Real.log x + 1 := by
  cas
```

---

Evidence that is too weak is refused in the same way. $0 \le x$ still allows $x = 0$:

```lean error
example (x : ℝ) (hx : 0 ≤ x) :
    deriv (fun t : ℝ ↦ t * Real.log t) x = Real.log x + 1 := by
  cas using hx
```

### Neat Examples

The second derivative of $\lvert t \rvert$ is $0$ at every point except $0$:

```lean
theorem deriv_deriv_abs (x : ℝ) (hx : x ≠ 0) : deriv (deriv (fun t : ℝ ↦ |t|)) x = 0 := by
  cas using hx
```

---

Conjugate exponents. From $p/q = p - 1$ it follows that $1/q = 1 - 1/p$:

```lean
example (p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) (h : p / q = p - 1) : 1 / q = 1 - 1 / p := by
  cas using h
```

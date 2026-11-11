+++
id = "cas"
kind = "tactic"
title = "cas"
summary = "Proves the goal by computer algebra whose steps Lean’s kernel checks: identities, derivatives, integrals, limits and bounds."
forms = ["CAS.ExactTactic.tacticCas", "CAS.ExactTactic.casLemmas"]
see_also = ["cas-using", "cas-query", "cas_nf", "cega", "derive", "integrate", "limit"]
tutorials = ["proving", "first-hour"]
+++

::: usage
`cas`
: proves the goal, or leaves it unchanged and says what each route tried.
`cas [‹l₁›, ‹l₂›]`
: the same, with ‹l₁› and ‹l₂› as local simp lemmas for the routes, such as a definition to unfold or an applied hypothesis.
:::

Inside a proof, `cas` is the main entry point. I wanted one tactic to try on a calculation without first deciding what kind of calculation it is. You state what you want, in Mathlib’s own terms, and write `cas`. It tries a fixed list of routes, from determinants and ideals to derivatives, integrals and bounds on a box, and every route ends in a proof that Lean checks against your goal. If no route works, the goal stays as it was and the message tells you what was tried. That is all a refusal means: it is not a proof that the goal is false.

`cas using h` passes a hypothesis such as `x ≠ 0` as evidence for the routes, and it has [[cas-using|its own page]].

## Details and Options

- `cas` closes the goal and proves no other statement. It does not change a goal it cannot close.
- Identities and relations: what Mathlib’s `field_simp`, `ring`, `norm_num`, `positivity`, `linarith` and `nlinarith` prove, and real identities that the checked symbolic normalizer proves, such as $\sin^2 x + \cos^2 x = 1$.
- Calculus: `deriv f x = e`, `HasDerivAt f e x`, `HasDerivWithinAt`, `DifferentiableAt`, `iteratedDeriv n f x = e` for a literal `n`, nested derivatives, and `Continuous`, `ContinuousOn`, `Differentiable`, `ContDiff`, `AnalyticAt` and their relatives over `ℝ`.
- Integrals: `(∫ x in a..b, f x) = v` and improper integrals such as `(∫ t in Set.Ioi 0, f t) = v`, also with their integrability, `IntegrableOn f (Set.Ioi 0) ∧ ∫ t in Set.Ioi 0, f t = v`, by an analytic theorem, one integration by parts or a checked primitive.
- The theorems that the `#cas` modes print: algebra, matrices and number theory, limits at a point and at `atTop` and `atBot`, the sign of a polynomial and counts of real roots.
- Ideals: `f ∈ Ideal.span {g₁, …, gₘ}` and equalities of spans, with cofactors from a Gröbner basis, and goals with determinants of matrix literals.
- Inequalities on real variables that hypotheses bound by rational numbers, such as `0 ≤ x` and `x ≤ 1`, by the box route of [[cega]].
- The routes run in a fixed order: determinants, ideals, the `#cas` theorems, derivatives, integrals, the checked evaluator, arithmetic, equation hypotheses, the checked identity route, the box route, elementary rewrites, `norm_num`, and `grind` last.
- A derivative or an integral whose function needs a condition, such as $x \ne 0$ for $\log x$, takes it from `cas using h`.
- `set_option cas.grindHeartbeats n` sets the budget of the `grind` and `norm_num` fallbacks in thousands of heartbeats, by default `20000`, and `0` turns them off.
- `set_option cas.maxDerivativeSteps n` caps the steps of the derivative rules, by default `512`.
- `set_option trace.cas.fallback true` shows what the `grind` fallback did.

## Examples

### Basic Examples

The Pythagorean identity:

```lean
example (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
  cas
```

---

A derivative, stated with Mathlib’s `deriv`:

```lean
example (x : ℝ) : deriv Real.sin x = Real.cos x := by
  cas
```

---

A definite integral, by parts:

```lean
example : (∫ x in (0 : ℝ)..1, x * Real.exp x) = 1 := by
  cas
```

### Scope

An identity that needs a hypothesis. Without `hx`, the statement is false in Lean at $x = \pm 1$:

```lean
example (x : ℝ) (hx : x ^ 2 - 1 ≠ 0) :
    (x ^ 4 - 1) / (x ^ 2 - 1) = x ^ 2 + 1 := by
  cas
```

---

Derivatives of every order, nested ones included:

```lean
example (x : ℝ) :
    iteratedDeriv 3 (fun x ↦ Real.sin (2 * x)) x = -8 * Real.cos (2 * x) := by
  cas
```

```lean
example (x : ℝ) (hx : 0 < x) :
    deriv (fun x ↦ deriv Real.sqrt x) x = -1 / (4 * x * Real.sqrt x) := by
  cas
```

---

Smoothness and analyticity:

```lean
example : AnalyticAt ℝ (fun x ↦ Real.exp (Real.sin x) / (1 + x ^ 2)) 0 := by
  cas
```

```lean
example : ContinuousOn (fun x ↦ Real.log x / x) (Set.Ioi 0) := by
  cas
```

---

Integrals with symbolic limits, and over the whole line:

```lean
example (a b : ℝ) : (∫ t in a..b, Real.sin t) = Real.cos a - Real.cos b := by
  cas
```

```lean
example : ∫ x : ℝ, 1 / (1 + x ^ 2) = Real.pi := by
  cas
```

---

Limits, written with Mathlib’s filters:

```lean
open Filter Topology in
example : Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by
  cas
```

```lean
open Filter Topology in
example : Tendsto (fun x : ℝ ↦ x * Real.exp (-x)) atTop (𝓝 0) := by
  cas
```

---

The sign of a polynomial, and how many real roots it has:

```lean
example : ∀ x : ℝ, x ^ 4 - 4 * x + 3 ≥ 0 := by
  cas
```

```lean
open Polynomial in
example : Fintype.card ((X ^ 5 - 4 * X + 2 : ℚ[X]).rootSet ℝ) = 3 := by
  cas
```

---

A bound on a box, from the hypotheses on `x` and `y`:

```lean
example (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 2 ≤ y) (hy' : y ≤ 3) :
    Real.exp (x * y) ≤ 21 := by
  cas
```

---

Matrices and polynomials over $\mathbb{Q}$:

```lean
example : (!![(1 : ℚ), 2; 3, 4])⁻¹ = !![-2, 1; 3 / 2, -1 / 2] := by
  cas
```

```lean
open Polynomial in
example : gcd (X ^ 2 - 1 : ℚ[X]) (X ^ 2 - 2 * X + 1) = X - 1 := by
  cas
```

### Options

`cas [l₁, l₂]` hands lemmas to the routes. Here an applied hypothesis rewrites `f (x + 1)` first:

```lean
example (f : ℝ → ℝ) (x : ℝ) (hf : ∀ t, f t = t ^ 2) : f (x + 1) = x ^ 2 + 2 * x + 1 := by
  cas [hf (x + 1)]
```

---

A definition to unfold works the same way:

```lean
def shifted (t : ℝ) : ℝ := t ^ 2 + 2 * t

example (x : ℝ) : shifted (x - 1) = x ^ 2 - 1 := by
  cas [shifted]
```

### Applications

`cas` proves a bound that `linarith` then uses:

```lean
theorem exp_lt_four (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x < 4 := by
  have h : Real.exp x ≤ 3 := by cas
  linarith

#print axioms exp_lt_four
```

---

Nicomachus’s theorem, the sum of the first $n$ cubes:

```lean
example (n : ℕ) : ∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 3 = (n * (n + 1) / 2) ^ 2 := by
  cas
```

### Properties and Relations

`#cas` prints a theorem, and `cas` proves the same statement in a proof:

```lean
#cas [derive x] (tan x)
```

```lean
example (x : ℝ) (h : Real.cos x ≠ 0) :
    HasDerivAt (fun x ↦ Real.tan x) (1 / Real.cos x ^ 2) x := by
  cas
```

---

[[cas-query|`cas?`]] runs the same routes and tells you the call to keep in your proof:

```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x ≤ 3 := by
  cas?
```

### Possible Issues

A false statement is refused. The message lists what each route tried, and it does not prove that the goal is false:

```lean error
example (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 2 := by
  cas
```

---

A wrong derivative. `#cas [derive x] (x ^ 2)` prints the one that is right:

```lean error
example (x : ℝ) : deriv (fun x ↦ x ^ 2) x = 3 * x := by
  cas
```

---

`cas` has no modes. The words of `#cas`, such as `derive` and `integrate`, are not lemmas:

```lean error
example (x : ℝ) : deriv Real.sin x = Real.cos x := by
  cas [derive]
```

---

The box route needs rational bounds on every variable. For all real $x$, this one is Mathlib’s `Real.add_one_le_exp`:

```lean error
example (x : ℝ) : Real.exp x ≥ x + 1 := by
  cas
```

### Neat Examples

A power of 2 with a 27 digit exponent, modulo a prime:

```lean
example : (2 : ℕ) ^ 123456789123456789123456789 % 1000000007 = 612059118 := by
  cas
```

---

You can teach `cas` a derivative. Here is a function it cannot read, the integral of a Gaussian from 0 to $x$, with the fundamental theorem of calculus registered as a rule:

```lean
noncomputable def gaussInt (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)

theorem hasDerivAt_gaussInt (x : ℝ) : HasDerivAt gaussInt (Real.exp (-x ^ 2)) x :=
  (Continuous.integral_hasStrictDerivAt (by fun_prop) 0 x).hasDerivAt

attribute [cas_deriv] hasDerivAt_gaussInt
```

Now `cas` applies the rule together with the chain rule:

```lean
example (x : ℝ) : deriv (fun x ↦ gaussInt (x ^ 2)) x = 2 * x * Real.exp (-x ^ 4) := by
  cas
```

---

A product that telescopes:

```lean
example : ∀ n : ℕ, ∏ k ∈ Finset.Icc 1 n, ((k : ℝ) + 1) / k = n + 1 := by
  cas
```

+++
id = "proving"
kind = "tutorial"
title = "Proving with `cas`"
summary = "How to state a goal so that `cas` and `cega` close it, and what to do when they refuse."
+++

The tactics work on the goal you wrote. You state the result with Mathlib’s functions and the hypotheses your argument needs, and a tactic proves exactly that statement, or fails and leaves the goal as it was. For me that’s the property that matters most.

Mathlib’s `Real.log` is defined everywhere, with $\log x = \log \lvert x \rvert$ and $\log 0 = 0$. So $\exp(\log x)$ is $x$, $\lvert x \rvert$ or $-x$, depending on what you know about $x$, and `cas` proves whichever one your hypotheses support:

```lean
example (x : ℝ) (hx : 0 < x) : Real.exp (Real.log x) = x := by
  cas

example (x : ℝ) (hx : x ≠ 0) : Real.exp (Real.log x) = |x| := by
  cas

example (x : ℝ) (hx : x < 0) : Real.exp (Real.log x) = -x := by
  cas
```

Nothing is assumed along the way. If a condition is missing, it’s reported, never added.

## Choosing a tactic {#choosing}

::: table
Goal | Tactic
exact algebra, identities, derivatives, regularity, integral formulas | [[cas]]
a side condition that a hypothesis supplies | [[cas-using|`cas using h`]]
numerical bounds on a box, on an integral or on a constant | [[cega]]
a rewrite inside a hypothesis or a goal | [[cas_nf]]
not sure | [[cas-query|`cas?`]] or [[cega-query|`cega?`]], which suggest the call to keep
:::

The one place to be careful is an integral. There `cas` looks for an exact formula and `cega` proves a numerical bound, and neither switches to the other, so pick the one that matches what your goal states.

## Compute first, then state {#compute}

The habit I’d recommend is to compute with `#cas` until you know what’s true, and only then write the statement. Say I want to show that $x^3 - 3x^2 + 4x$ is increasing on all of $\mathbb{R}$. By Mathlib’s `strictMono_of_deriv_pos`, it is if its derivative is positive everywhere. `#cas` computes the derivative and shows that it has no real zero, so the derivative keeps the sign of its leading coefficient:

```lean
#cas [derive x] (x ^ 3 - 3 * x ^ 2 + 4 * x)
```

```lean
#cas [roots x] (3 * x ^ 2 - 6 * x + 4 = 0)
```

In the proof I state the derivative and let `cas` prove it, then show that it is positive by writing it as $3(x - 1)^2 + 1$, an identity that `cas` proves too. And since a strictly monotone function is injective, the cubic takes no value twice:

```lean
theorem cubic_strictMono : StrictMono (fun x : ℝ ↦ x ^ 3 - 3 * x ^ 2 + 4 * x) := by
  apply strictMono_of_deriv_pos
  intro x
  have h : deriv (fun x : ℝ ↦ x ^ 3 - 3 * x ^ 2 + 4 * x) x = 3 * x ^ 2 - 6 * x + 4 := by cas
  rw [h]
  calc (0 : ℝ) < 3 * (x - 1) ^ 2 + 1 := by positivity
    _ = 3 * x ^ 2 - 6 * x + 4 := by cas

theorem cubic_injective (a b : ℝ)
    (h : a ^ 3 - 3 * a ^ 2 + 4 * a = b ^ 3 - 3 * b ^ 2 + 4 * b) : a = b :=
  cubic_strictMono.injective h

#print axioms cubic_injective
```

## Conditions from hypotheses {#conditions}

When a rule needs a condition, you hand over the hypothesis that proves it with `using`. A logarithm of $-t$ needs $-t \ne 0$, which $x < 0$ gives, and $\int_a^b dt/t$ needs $t \ne 0$ on the whole interval:

```lean
example (x : ℝ) (hx : x < 0) : deriv (fun t : ℝ ↦ Real.log (-t)) x = 1 / x := by
  cas using hx

example (a b : ℝ) (hnonzero : ∀ t ∈ Set.uIcc a b, t ≠ 0) :
    (∫ t in a..b, 1 / t) = Real.log b - Real.log a := by
  cas using hnonzero
```

Without the condition the call fails, and the message names what it needed. Here $x / x = 1$ is false at $x = 0$, where Lean’s division gives $0$, and the message lists $x \ne 0$ as the condition to supply:

```lean error
example (x : ℝ) : x / x = 1 := by
  cas
```

## Numbers inside a proof {#numbers}

Suppose I want to know how large $\int_0^1 \frac{dt}{1 + t^2} + \int_0^1 e^{-t^2}\,dt$ is. The first integral is $\pi/4$, which `#cas` evaluates exactly. The second has no elementary closed form, so for an estimate I need its digits:

```lean
#cas [integrate x in [0, 1]] (1 / (1 + x ^ 2))
```

```lean
#cas [nintegrate x in [0, 1]] (exp (-x^2))
```

So the sum is $1.5322\ldots$, and $1.54$ is a safe bound to prove. In the proof, `cas` proves the exact value of the first integral, `cega` proves a bound on the second and one on $\pi$, and `linarith` adds them up:

```lean
theorem integral_estimate :
    (∫ t in (0 : ℝ)..1, 1 / (1 + t ^ 2)) + (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) < 1.54 := by
  have h₁ : (∫ t in (0 : ℝ)..1, 1 / (1 + t ^ 2)) = Real.pi / 4 := by cas
  have h₂ : (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 3 / 4 := by cega
  have hπ : Real.pi < 3.1416 := by cega
  rw [h₁]
  linarith

#print axioms integral_estimate
```

Behind the second `have`, `cega` encloses the Gaussian integral by Simpson’s rule, with the error on each panel bounded by the remainder (3.5.6) of [DLMF §3.5](https://dlmf.nist.gov/3.5), and it doubles the number of panels until the enclosure proves $3/4$.

## A primitive of my own {#primitive}

When I already know a primitive, I hand it over, and `cas` checks it by differentiating. Here it is $F(t) = (\log t)^2/2$:

```lean
example (a b : ℝ) (h : ∀ t ∈ Set.uIcc a b, t ≠ 0) :
    (∫ t in a..b, Real.log t / t) = Real.log b ^ 2 / 2 - Real.log a ^ 2 / 2 := by
  let F : ℝ → ℝ := fun t ↦ Real.log t ^ 2 / 2
  cas [integrate primitive := F using h]
```

## Keeping the call that worked {#keep}

Once a call works, keep the simplest one. `cas?` proves the goal as `cas` does and suggests the quieter call to keep in the source:

```lean
example (x : ℝ) : Real.cos (3 * x) = 4 * Real.cos x ^ 3 - 3 * Real.cos x := by
  cas?
```

## When a call refuses {#refusals}

A refusal leaves the goal as it was. For a numerical bound that is false or too tight, `cega` says which values its queries certified. This one is false, since $x(1 - x)$ is $1/4$ at $x = 1/2$, so no setting will prove it. The message reports the certified upper bound $1/4$, which is exactly the maximum:

```lean error
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 5 := by
  cega
```

When a call fails, read the message first. It names what was missing and, where there is one, the call or setting to try. After that, these are the things I reach for:

- `#cas` answers the question itself: `#cas [derive x]` prints the derivative with its conditions, `#cas [integrate x]` a primitive and `#cas [N 20]` the digits of a constant, so that the goal can state what SymLean computes.
- `cas?` and `cega?` show the route that closed a goal and suggest the call to keep.
- When a message names an option, [[options]] lists it with its default, and `set_option ‹name› ‹value› in` sets it for one call.
- `set_option trace.cas.fallback true in` shows the full diagnostics of the `grind` and `norm_num` fallbacks of `cas`.

Every theorem on this page depends only on `propext`, `Classical.choice` and `Quot.sound`, as `#print axioms` shows, and [[trust|What you trust]] explains why.

+++
id = "simplify"
kind = "mode"
title = "simplify"
summary = "Simplifies a real expression by checked rewrites, with the conditions under which the result equals it."
forms = ["CAS.Command.casSimplifyCommand"]
see_also = ["fullSimplify", "together", "cancel", "factor", "cas-command", "cas"]
guide = "algebra"
tutorials = ["first-hour", "proving"]
+++

::: usage
`#cas [simplify] ‹e›`
: simplifies the real expression ‹e› by exact rewrites and gives the conditions under which the result equals ‹e›.
:::

`simplify` reduces an expression and tells you when the result equals it. Every rewrite is checked, and the theorem under the answer proves the equality wherever the printed conditions hold. The conditions are sufficient, not necessary, so the result can also equal the input where they fail. $\sqrt{x}^2$ simplifies to $x$ under $x > 0$, for example, and the two agree at $x = 0$ as well.

The conditions are there because Lean’s division is total: $1/0 = 0$. At $x = 1$ the quotient $(x^4 - 1)/(x^2 - 1)$ is $0/0 = 0$ in Lean, while $x^2 + 1$ is $2$. So the identity holds where $x^2 - 1 \ne 0$, and that is the condition the theorem carries. Without that condition the identity is false in Lean, and that is easy to miss when you copy an answer from a computer algebra system into a proof.

## Details and Options

- The theorem has the form $\forall x_1, \dots, x_n,\; c_1 \to \dots \to c_k \to e = e'$ about Mathlib’s real functions, where $e'$ is the printed result and $c_1, \dots, c_k$ are the printed conditions. For `x + x` it is `∀ (x : ℝ), x + x = 2 * x`.
- “The certificate” shows two steps: that theorem, and the same statement for SymLean’s internal expressions, from which it is transported. When the proof of the first takes more than its own budget of `maxHeartbeats` heartbeats, the report keeps only the internal statement.
- The variables are real. The functions are `abs`, `sin`, `cos`, `tan`, `sinh`, `cosh`, `tanh`, `atan`, `asin`, `acos`, `exp`, `log` and `sqrt`, with `+`, `-`, `*`, `/` and powers. A power with a variable exponent is a real power.
- Cancelling a divisor $d$ adds the condition $d \ne 0$, and combining real powers of $a$ adds the condition $a > 0$.
- A condition is printed as a polynomial only when it equals that polynomial for every value of its variables. Otherwise it keeps the form it has in the input.
- `set_option cas.suggest true` adds the theorem as an `example` to paste in place of the command, when that example elaborates in your file to the same statement.
- A bare `#cas ‹e›` with no mode also simplifies (see [[cas-command]]). [[fullSimplify]] tries many more forms and keeps the simplest.
- The tactic [[cas]] proves the same identities, with the conditions as hypotheses.

## Examples

### Basic Examples

A quotient that cancels, with the condition that makes the cancellation valid:

```lean
#cas [simplify] ((x ^ 4 - 1) / (x ^ 2 - 1))
```

---

Like terms are collected. No condition is needed:

```lean
#cas [simplify] (x + x)
```

---

In Mathlib $\tan x$ is $\sin x / \cos x$, so where $\cos x = 0$ the product $\tan x \cos x$ is $0$, not $\sin x$. The condition says so:

```lean
#cas [simplify] (tan x * cos x)
```

### Scope

The rewrites reach inside functions:

```lean
#cas [simplify] (exp ((x^2 - y^2)/(x - y)))
```

---

Real powers of one base are combined, for a positive base:

```lean
#cas [simplify] (a ^ p * a * sqrt a / a ^ q)
```

---

A division does not always need a condition. Where $\cos x = 0$ both sides are $0$, so this identity holds for every $x$:

```lean
#cas [simplify] (tan x + sin x / cos x)
```

### Options

With `cas.suggest`, the report ends with the theorem as an `example`, ready to paste:

```lean
set_option cas.suggest true in
#cas [simplify] (x + x)
```

---

Here it is pasted, and `cas` proves it:

```lean
example (x : ℝ) : x + x = 2 * x := by cas
```

### Applications

The first example as a theorem in a proof. The hypothesis is the printed condition, and only the three standard axioms are used:

```lean
theorem quartic_over_quadratic (x : ℝ) (h : x ^ 2 - 1 ≠ 0) :
    (x ^ 4 - 1) / (x ^ 2 - 1) = x ^ 2 + 1 := by
  cas

#print axioms quartic_over_quadratic
```

---

A quotient under a square root. One hypothesis is enough for the cancellation:

```lean
example (x y : ℝ) (h : x ^ 2 - y ^ 2 ≠ 0) :
    Real.sqrt ((x ^ 4 - y ^ 4) / (x ^ 2 - y ^ 2)) = Real.sqrt (x ^ 2 + y ^ 2) := by
  cas
```

---

The tangent example, with its condition as a hypothesis:

```lean
example (x : ℝ) (h : Real.cos x ≠ 0) : Real.tan x * Real.cos x = Real.sin x := by
  cas
```

### Properties and Relations

A bare `#cas` with no mode simplifies too, with the same report:

```lean
#cas ((x ^ 4 - 1) / (x ^ 2 - 1))
```

---

[[fullSimplify]] tries many forms, the logarithm rules among them, and keeps the simplest. Here it finds that the expression is $0$:

```lean
#cas [fullSimplify] (log (x*y) - log x - log y)
```

### Possible Issues

An identifier applied to an argument is read as a function. Write a product as `x * y`:

```lean error
#cas [simplify] (x y)
```

---

The divisor here equals $-(x^2 - x + 1)$ only where $x \ne 0$ and $x \ne 1$ (at $x = 0$ it is $0$, since $1/0 = 0$), so the condition keeps the form of the input:

```lean
#cas [simplify] ((1 / (1/x + 1/(1-x)) - 1) / (1 / (1/x + 1/(1-x)) - 1))
```

---

$\sqrt{x^2}$ is $|x|$, not $x$, and `simplify` leaves it as it is. [[fullSimplify]] finds the absolute value of a square under a root:

```lean
#cas [simplify] (sqrt (x ^ 2))
```

```lean
#cas [fullSimplify] (sqrt (x^2 + 2*x + 1))
```

---

Without its condition the first identity is false in Lean. At $x = 1$ the left side is $0/0 = 0$ and the right side is $2$:

```lean
example : ¬ ∀ x : ℝ, (x ^ 4 - 1) / (x ^ 2 - 1) = x ^ 2 + 1 := by
  intro h
  have := h 1
  norm_num at this
```

### Neat Examples

An exponent that is itself a real power. Since $4^{1/2} = 2$, the result is $x^2$ for every real $x$, negative ones included:

```lean
#cas [simplify] (x ^ ((4 : ℝ) ^ (1 / 2 : ℝ)))
```

```lean
example (x : ℝ) : x ^ ((4 : ℝ) ^ (1 / 2 : ℝ) : ℝ) = x ^ 2 := by cas
```

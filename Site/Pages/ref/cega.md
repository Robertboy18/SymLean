+++
id = "cega"
kind = "tactic"
title = "cega"
summary = "Proves numerical bounds: inequalities on a box of real variables, closed constants and interval integrals."
forms = ["CAS.CEGA.tacticCega", "CAS.CEGA.cegaConfigured", "CAS.CEGA.cegaFast", "CAS.Numerics.cegaBatch", "CAS.Numerics.cegaFastBatch"]
see_also = ["cega-query", "cega-using", "enclose", "nintegrate", "N", "cas", "options"]
guide = "tactics"
tutorials = ["proving", "trust"]
imports = ["CAS.Numerics.Tactic"]
+++

::: usage
`cega`
: proves a numerical bound: an inequality on real variables that the hypotheses bound by rationals, a bound on a closed constant, or a bound on an interval integral.
`cega (prec := ‹n›) (depth := ‹n›) (panels := ‹n›)`
: the same with the precision, the depth of subdivision and the number of integration panels set by hand.
`cega [fast]`
: tries finite certificates first, checked by compiled code when `cega.nativeCertificates` is on, and is bare `cega` otherwise.
`cega [batch := ‹n›]`
: proves a goal `∀ i : Fin m, p i` by checking ‹n› indices at a time in the kernel.
`cega [fast, batch := ‹n›]`
: the same, with the batches checked by compiled code when `cega.nativeCertificates` is on.
:::

`cega` is the tactic I use for numbers. A bound like $\sin x \le 0.85$ for $x \in [0, 1]$ is true, obvious from a plot and tedious to prove by hand. `cega` encloses the expression on the box that your hypotheses describe, compares the enclosure with the bound by exact rational arithmetic, and hands the kernel a certificate for the whole argument.

The name is short for *certified enclosures, guarantees and approximations*.

## Details and Options

- The goal is a bound: $f \le c$, $f < c$, $c \le f$, $\lvert f \rvert \le c$, a two-sided bound, `f ∈ Set.Icc a b` (also `Ioo`, `Ico`, `Ioc`), $f \le g$, or a conjunction of these.
- Every real variable needs rational bounds among the hypotheses: `a ≤ x` and `x ≤ b`, `x ∈ Set.Icc a b`, or `|x| ≤ r`. A goal without variables needs none.
- When the first enclosure is too weak, the box is cut in halves, by default to depth 2. `(depth := n)` sets that depth.
- A bound on one interval integral, such as $\int_a^b f \le c$ or $\lvert \int_a^b f - c \rvert \le \varepsilon$, uses Simpson panels when the first four derivatives of $f$ are certified on $[a, b]$, and range panels, which need only continuity, otherwise. The number of panels doubles up to `cega.maxIntegrationPanels`, by default 256, and `(panels := n)` fixes it.
- A closed goal that these routes refuse is tried with `dyadic_interval` at 32 bits, or at the bits of `(prec := n)`.
- The certificate propositions `EnclosedOn`, `BoundOn` and `ApproxOn` of SymLean are goals too.
- The functions are those of [[N]], written as Mathlib terms such as `Real.sin x` and `Real.sqrt x`. A box has at most 8 variables (`cega.maxDimension`).
- `set_option cega.nativeCertificates true` lets the `fast` forms check finite certificates with compiled code. That also trusts Lean’s compiler, so it is off by default and every check stays in the kernel.
- `cega [batch := n]` and `cega [fast, batch := n]` need `import CAS.Numerics.Tactic`.
- A false bound, or a true one that the enclosures do not reach, is refused, and the message proposes the next call to try.

## Examples

### Basic Examples

A bound on a box, from the hypotheses on `x`:

```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cega
```

---

A bound on a constant:

```lean
example : Real.exp 1 ≤ 2.72 := by
  cega
```

---

A bound on an integral with no elementary antiderivative:

```lean
example : (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 3 / 4 := by
  cega
```

### Scope

A strict two-sided bound, and membership in an open interval:

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 < x * (1 - x) + 1 ∧ x * (1 - x) + 1 < 2 := by
  cega
```

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ∈ Set.Ioo (-1 : ℝ) 1 := by
  cega
```

---

Several bounds at once, each checked once:

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ x / (1 + x) ∧ Real.exp x ≤ 3 ∧ |Real.sin x| < 1 := by
  cega
```

---

A hypothesis `|x| ≤ r` gives the box $[-r, r]$. Here it also keeps the denominator away from zero:

```lean
example (x : ℝ) (hx : |x| ≤ 1 / 2) : 1 / (1 - x) ≤ 2 := by
  cega
```

---

Integrals with the limits reversed, and with an integrand that has a corner:

```lean
example : (∫ x in (1 : ℝ)..0, Real.exp x) < -1 := by
  cega
```

```lean
example : 1 / 2 < ∫ x in (-1 : ℝ)..1, |x| := by
  cega
```

### Options

`(panels := 2)` fixes the number of Simpson panels instead of doubling them:

```lean
example : |(∫ x in (0 : ℝ)..1, Real.exp x) - 17182818 / 10000000| ≤ 1 / 10000 := by
  cega (panels := 2)
```

---

`(depth := 3)` cuts the box three times before giving up:

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega (depth := 3)
```

---

`cega [fast]` with the default settings is bare `cega`, checked in the kernel:

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * x ≤ 1 := by
  cega [fast]
```

---

A finite statement, checked three indices at a time:

```lean
example : ∀ i : Fin 10, i.val * i.val < 100 := by
  cega [batch := 3]
```

```lean
example : ∀ i : Fin 10, i.val * i.val < 100 := by
  cega [fast, batch := 4]
```

### Applications

`cega` proves the numerical fact and `linarith` finishes. Only the three standard axioms are used:

```lean
theorem cega_sin_lt_one (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x < 1 := by
  have h : Real.sin x ≤ 17 / 20 := by cega
  linarith

#print axioms cega_sin_lt_one
```

---

The digits that [[N]] prints, as a bound:

```lean
example : Real.sqrt 2 ≤ 1.415 := by
  cega
```

### Properties and Relations

[[cega-query|`cega?`]] proves the goal and tells you the explicit query that did it:

```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cega?
```

---

That query is the one [[enclose]] runs, and it prints the interval behind the proof:

```lean
#cas [enclose x in [0, 1]] (sin x)
```

---

[[cas]] tries the same box route on ordinary inequalities:

```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cas
```

### Possible Issues

A false bound is refused. Here $\sin 1 > 0.84$:

```lean error
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.8 := by
  cega
```

---

Every variable needs rational bounds. For all real $x$, this bound follows from Mathlib’s `Real.sin_le_one`:

```lean error
example (x : ℝ) : Real.sin x ≤ 1.5 := by
  cega
```

---

Too few panels. The message gives the interval that the search proposes and the call to try next:

```lean error
example : |(∫ x in (0 : ℝ)..1, Real.exp x) - 17182818 / 10000000| ≤ 1 / 10000 := by
  cega (panels := 1)
```

---

A batch that fails names its indices. A failed batch is not a counterexample, only a check that did not reduce to `true`:

```lean error
example : ∀ i : Fin 2, i.val = 0 := by
  cega [batch := 1]
```

### Neat Examples

The exact range of $x/(1+x^2)$ on $[-2, 2]$, stated as a certificate proposition on a box in $\mathbb{R}^1$. Bare `cega` finds the subdivision at the turning points $\pm 1$ on its own:

The next examples run after `open CAS.Certificate`.

```lean hidden
open CAS.Certificate
```

```lean
example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0 ^ 2)) {p | -2 ≤ p 0 ∧ p 0 ≤ 2}
      (-1 / 2 : ℝ) (1 / 2 : ℝ) := by
  cega
```

---

The cosine on a short interval near 100:

```lean
example (x : ℝ) (h0 : 100 ≤ x) (h1 : x ≤ 100001 / 1000) : 0.86 ≤ Real.cos x := by
  cega
```

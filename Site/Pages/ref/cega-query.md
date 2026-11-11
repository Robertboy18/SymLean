+++
id = "cega-query"
kind = "tactic"
title = "cega?"
summary = "Proves the goal as `cega` does, and suggests the explicit query to keep in the proof."
forms = ["CAS.tacticCega?"]
see_also = ["cega", "cas-query", "cega-using", "enclose", "options"]
tutorials = ["proving"]
imports = ["CAS.Numerics.Tactic"]
+++

::: usage
`cega?`
: proves the goal as [[cega]] does, and suggests the explicit call to keep in the proof.
`cega? (‹options›)`, `cega? [fast]`, `cega? [batch := ‹n›]`
: the same for the other forms of `cega`, with the same arguments.
`cega? [enclose ‹x› in [‹a›, ‹b›]] ‹e›`
: runs the explicit query, and names the bound that it proved.
`cega? using ‹c›`
: the same for [[cega-using|`cega using`]].
:::

When bare `cega` proves a bound on a box, I like to keep the box in the proof. `cega?` proves the goal and suggests the explicit query `cega [enclose x in [a, b]] e`, with the box and the expression that the route used. Whoever reads the proof later sees what was enclosed, and where.

## Details and Options

- When the box route closed the goal, the suggestion is the query `cega [enclose x in [a, b]] e` with the box and the expression that the route used, provided that this query closes the original goal. Otherwise the suggestion is the call as written.
- Bare `cega?` runs the routes of bare `cega`, except the kernel certificate of a closed decidable proposition.
- The line under the suggestion names the route: a box enclosure, a box query with the kind of bound it proved, quadrature of an integral, or a checked certificate. After `cega? (‹options›)`, `cega? [fast]` and `cega? [batch := ‹n›]` it only says that Lean checked the suggestion.
- `set_option cas.verbose true` replaces that line by the full report, as for [[cas-query|`cas?`]].
- `cega?` refuses the goals that `cega` refuses, with the same message.
- `cega? [batch := n]` needs `import CAS.Numerics.Tactic`, like `cega [batch := n]`.

## Examples

### Basic Examples

A bound on a box. The suggestion names the box and the expression:

```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cega?
```

---

A closed constant needs no binding:

```lean
example : Real.sqrt 2 ≤ 1.415 := by
  cega?
```

---

The maximum of $x(1 - x)$ on $[0, 1]$:

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega?
```

### Scope

A lower bound on a constant. Here the suggestion is plain `cega`:

```lean
example : (3 / 11 : ℝ) ≤ Real.exp (-1) := by
  cega?
```

---

A bound on an integral, by quadrature:

```lean
example : |(∫ x in (0 : ℝ)..1, x ^ 2) - 1 / 3| ≤ 1 / 100 := by
  cega?
```

---

The explicit query itself. The line under the suggestion says which bound it proved:

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega? [enclose x in [0, 1]] (x * (1 - x))
```

---

A certificate proposition, with options inside the query:

The next examples run after `open CAS.Certificate`.

```lean hidden
open CAS.Certificate
```

```lean
example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0 / (1 + p 0))
      {p : ℝ^1 | 0 ≤ p 0 ∧ p 0 ≤ 1} 0 (1 / 2) := by
  cega? (depth := 2) [enclose x in [0, 1]] (x / (1 + x))
```

### Options

With options or a flag, the suggestion is the call as written:

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  cega? (depth := 3)
```

```lean
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * x ≤ 1 := by
  cega? [fast]
```

---

The batch forms:

```lean
example : ∀ i : Fin 10, i.val * i.val < 100 := by
  cega? [batch := 3]
```

```lean
example : ∀ i : Fin 10, i.val * i.val < 100 := by
  cega? [fast, batch := 4]
```

### Applications

The suggestion replaces `cega?` in the theorem. Only the three standard axioms are used:

```lean
theorem cega_sin_bound (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cega [enclose x in [0, 1]] (Real.sin x)

#print axioms cega_sin_bound
```

### Properties and Relations

[[enclose]] prints the interval behind that query:

```lean
#cas [enclose x in [0, 1]] (sin x)
```

---

[[cega-using|`cega using`]] projects a certificate that you built yourself, and `cega?` names it:

```lean
noncomputable def cosineEnclosure : EnclosureCert ℝ (Set.Icc 0 1) where
  fn := Real.cos
  lo := 1 / 2
  hi := 1
  sound := by
    intro x hx
    obtain ⟨h0, h1⟩ := hx
    constructor <;> cega

example : EnclosedOn Real.cos (Set.Icc 0 1) (1 / 2 : ℝ) 1 := by
  cega? using cosineEnclosure
```

### Possible Issues

`cega?` refuses what `cega` refuses. Every variable needs rational bounds:

```lean error
example (x : ℝ) : Real.sin x ≤ 1.5 := by
  cega?
```

---

A false bound. Here $\sin 1 > 0.84$:

```lean error
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.8 := by
  cega?
```

### Neat Examples

A bound on a box in two variables:

```lean
example (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 2 ≤ y) (hy' : y ≤ 3) :
    Real.exp (x * y) ≤ 21 := by
  cega?
```

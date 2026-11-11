+++
id = "cega-using"
kind = "tactic"
title = "cega using"
summary = "Proves a goal from a certificate that you built once, by the certificate’s own soundness theorem."
forms = ["CAS.CEGA.cegaUsing"]
see_also = ["cega", "cega-query", "enclose", "cas-using"]
tutorials = ["trust"]
+++

::: usage
`cega using ‹c›`
: proves the goal from the certificate ‹c› by its soundness theorem, restricted to the domain of the goal when that domain is smaller.
:::

Some bounds take a while to prove, and I need them more than once. So I prove the bound once, store it in a certificate, and use it wherever it is needed with `cega using`. The function is not evaluated again: the proof is the certificate’s own theorem.

## Details and Options

- A certificate is one of the structures of SymLean with a soundness field: `EnclosureCert`, `BoundCert`, `ApproxCert`, `ResidualCert`, `ModelApproxCert` or `QuadratureCert`. A `CertificateRoute` to an enclosure, bound or residual certificate works too, as does a type registered with `cega_carrier`. An atlas enters through its `toResidualCert` or `toApproxCert`.
- `cega using c` first tries the theorem `c.sound` as it is. When the domain of the goal is smaller, the certificate is restricted to it, with the inclusion proved by `assumption`, `simp_all` or `aesop`.
- A term of any other type is refused. An ordinary proof goes in with `exact`.
- The proof keeps every hypothesis and axiom that the proof of ‹c› uses, a native-evaluation axiom included. `cega using` checks that the theorem fits the goal, not how ‹c› was made, and `#print axioms` shows what your theorem depends on.
- There are no options. The certificate propositions `EnclosedOn`, `BoundOn` and `ApproxOn` need `open CAS.Certificate`.

## Examples

### Basic Examples

A certificate for $\tfrac{1}{2} \le \cos x \le 1$ on $[0, 1]$, whose `sound` field `cega` proves once:

The next examples run after `open CAS.Certificate`.

```lean hidden
open CAS.Certificate
```

```lean
noncomputable def cosineEnclosure : EnclosureCert ℝ (Set.Icc 0 1) where
  fn := Real.cos
  lo := 1 / 2
  hi := 1
  sound := by
    intro x hx
    obtain ⟨h0, h1⟩ := hx
    constructor <;> cega
```

`cega using` turns it into the theorem:

```lean
example : EnclosedOn Real.cos (Set.Icc 0 1) (1 / 2 : ℝ) 1 := by
  cega using cosineEnclosure
```

### Scope

A smaller domain. The inclusion comes from a hypothesis:

```lean
example (s : Set ℝ) (hs : s ⊆ Set.Icc 0 1) : EnclosedOn Real.cos s (1 / 2 : ℝ) 1 := by
  cega using cosineEnclosure
```

### Applications

The enclosure as a step in an ordinary proof. Only the three standard axioms are used:

```lean
theorem half_le_cos (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 1 / 2 ≤ Real.cos x := by
  have h : EnclosedOn Real.cos (Set.Icc 0 1) (1 / 2 : ℝ) 1 := by
    cega using cosineEnclosure
  exact (h x ⟨h0, h1⟩).1

#print axioms half_le_cos
```

### Properties and Relations

[[cega-query|`cega?`]] confirms the call, and names the route:

```lean
example : EnclosedOn Real.cos (Set.Icc 0 1) (1 / 2 : ℝ) 1 := by
  cega? using cosineEnclosure
```

---

[[enclose]] computes an enclosure from scratch, where `cega using` reuses one:

```lean
#cas [enclose x in [0, 1]] (cos x)
```

### Possible Issues

A proof is not a certificate. Here `exact h` closes the goal:

```lean error
example (h : EnclosedOn Real.cos (Set.Icc 0 1) (1 / 2 : ℝ) 1) :
    EnclosedOn Real.cos (Set.Icc 0 1) (1 / 2 : ℝ) 1 := by
  cega using h
```

---

With `cosineEnclosure`, a goal with wider endpoints, $0 \le \cos x \le 2$, is refused:

```lean error
example : EnclosedOn Real.cos (Set.Icc 0 1) (0 : ℝ) 2 := by
  cega using cosineEnclosure
```

I project first and widen with `enclosedOn_mono`, whose two inequalities `norm_num` proves:

```lean
example : EnclosedOn Real.cos (Set.Icc 0 1) (0 : ℝ) 2 := by
  have h : EnclosedOn Real.cos (Set.Icc 0 1) (1 / 2 : ℝ) 1 := by
    cega using cosineEnclosure
  exact enclosedOn_mono h (by norm_num) (by norm_num)
```

---

A certificate can’t prove more than its own bounds, and tighter ones are refused:

```lean error
example : EnclosedOn Real.cos (Set.Icc 0 1) (1 / 2 : ℝ) (9 / 10) := by
  cega using cosineEnclosure
```

### Neat Examples

From the library’s examples: an atlas of two patches covering $[0, 1]$ becomes one residual certificate. The function is the defect $p' - p$ of $p(x) = 1 + x + x^2/2$ as a solution of $u' = u$, combined with its derivative under the weights $x$ and $1 - x$, with arbitrary amplitudes $a$, $b$ and a symbolic tolerance:

```lean quote=CAS/Examples/Numerics/WeightedResidual.lean
theorem weighted_defect_bound (a b eps : ℝ)
    (hright : |a| / 2 + |b| / 2 ≤ eps) :
    ResidualBound
      (fun x ↦ x * (a * defect x) + (1 - x) * (b * deriv defect x))
      (Set.Icc 0 1) eps := by
  have hleft : |a| / 16 + |b| / 2 ≤ eps := by linarith [abs_nonneg a]
  have h : ResidualBound (fun x ↦ ∑ j : Bool, weights j x • residuals a b j x)
      (Set.Icc 0 1) eps := by
    cega using (weightedAtlas a b eps hleft hright).toResidualCert
  simpa only [Fintype.sum_bool, weights, residuals, smul_eq_mul] using h
```

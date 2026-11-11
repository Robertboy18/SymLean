/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.Relations

/-!
# Enclosure certificates

`EnclosedOn f s lo hi` says that `lo ≤ f x ≤ hi` for every `x ∈ s`. An
`EnclosureCert` stores that proposition with the function and endpoints, so
CEGA and the symbolic layer can compose certificates as data while the final
result is still an ordinary Lean theorem. The interval rules `sum`, `neg`, `sub`, `scaleNonneg`
and `union` build new certificates from old ones, and `boundOn` and `residualBound` forget an
enclosure to an upper bound or a residual bound.

## Implementation notes

A backend may compute or search for the endpoints; the enclosure is accepted
only through the `sound` field, a Lean proof that `f` maps every point of the
patch into `[lo, hi]`, which the kernel checks when the certificate is built. A typical CEGA
use:

```text
symbolic expression + chart interval
    -> interval evaluator proposes [lo, hi]
    -> Lean proof builds `EnclosureCert`
    -> route layer converts it to a bound, residual, or approximation fact
```

The interval rules are the endpoint formulas of interval arithmetic, for example
`[a, b] - [c, d] = [a - d, b - c]`, stated for functions on a patch rather than for intervals.
They are either unconditional or take their side conditions as explicit arguments, as
`scaleNonneg` does for the sign of the scalar.

## References

* Ramon E. Moore, *Interval Analysis*, Prentice-Hall, Englewood Cliffs, N.J., 1966,
  <https://zbmath.org/?q=an:0176.13301>. For interval arithmetic.
-/

@[expose] public section

namespace CAS.Certificate

/--
A checked two-sided real enclosure for a function on a domain.

The endpoints are data used by later bounds and residual certificates. The
`sound` field proves that `fn` takes values in `[lo, hi]` on the domain.
-/
structure EnclosureCert (α : Type*) (s : Set α) where
  /-- The enclosed function. -/
  fn : α → ℝ
  /-- Lower endpoint. -/
  lo : ℝ
  /-- Upper endpoint. -/
  hi : ℝ
  /-- `lo ≤ fn ≤ hi` on `s`. -/
  sound : EnclosedOn fn s lo hi

namespace EnclosureCert

variable {α : Type*} {s : Set α}

/-! ## Constructors and elementary interval arithmetic -/

/-- The certificate of an existing enclosure theorem. -/
def ofEnclosedOn (f : α → ℝ) (lo hi : ℝ) (h : EnclosedOn f s lo hi) :
    EnclosureCert α s where
  fn := f
  lo := lo
  hi := hi
  sound := h

/-- A constant function has a zero-width enclosure. -/
def const (c : ℝ) (s : Set α) : EnclosureCert α s where
  fn := fun _ ↦ c
  lo := c
  hi := c
  sound := enclosedOn_const c s

/-- Weaken a certificate to a wider interval. -/
def weaken (c : EnclosureCert α s) {lo' hi' : ℝ}
    (hlo : lo' ≤ c.lo) (hhi : c.hi ≤ hi') : EnclosureCert α s where
  fn := c.fn
  lo := lo'
  hi := hi'
  sound := enclosedOn_mono c.sound hlo hhi

/-- Restrict an enclosure certificate to a smaller patch. -/
def restrict (c : EnclosureCert α s) (t : Set α) (hsub : t ⊆ s) :
    EnclosureCert α t where
  fn := c.fn
  lo := c.lo
  hi := c.hi
  sound := enclosedOn_mono_domain c.sound hsub

/-- Replace the enclosed function by an equal function on the certificate domain. -/
def replaceFn (c : EnclosureCert α s) (fn' : α → ℝ)
    (hfn : Set.EqOn fn' c.fn s) : EnclosureCert α s where
  fn := fn'
  lo := c.lo
  hi := c.hi
  sound := by
    intro x hx
    simpa [hfn hx] using c.sound x hx

/-- Restricting an enclosure certificate to a smaller patch keeps the enclosed function. -/
@[simp]
theorem restrict_fn (c : EnclosureCert α s) (t : Set α) (hsub : t ⊆ s) :
    (c.restrict t hsub).fn = c.fn :=
  rfl

/-- Restricting an enclosure certificate to a smaller patch keeps the lower endpoint. -/
@[simp]
theorem restrict_lo (c : EnclosureCert α s) (t : Set α) (hsub : t ⊆ s) :
    (c.restrict t hsub).lo = c.lo :=
  rfl

/-- Restricting an enclosure certificate to a smaller patch keeps the upper endpoint. -/
@[simp]
theorem restrict_hi (c : EnclosureCert α s) (t : Set α) (hsub : t ⊆ s) :
    (c.restrict t hsub).hi = c.hi :=
  rfl

/-- After replacing the enclosed function, the certificate carries the new function. -/
@[simp]
theorem replaceFn_fn (c : EnclosureCert α s) (fn' : α → ℝ)
    (hfn : Set.EqOn fn' c.fn s) : (c.replaceFn fn' hfn).fn = fn' :=
  rfl

/-- Replacing the enclosed function keeps the lower endpoint. -/
@[simp]
theorem replaceFn_lo (c : EnclosureCert α s) (fn' : α → ℝ)
    (hfn : Set.EqOn fn' c.fn s) : (c.replaceFn fn' hfn).lo = c.lo :=
  rfl

/-- Replacing the enclosed function keeps the upper endpoint. -/
@[simp]
theorem replaceFn_hi (c : EnclosureCert α s) (fn' : α → ℝ)
    (hfn : Set.EqOn fn' c.fn s) : (c.replaceFn fn' hfn).hi = c.hi :=
  rfl

/-- Expose domain restriction directly as an ordinary enclosure theorem. -/
theorem sound_restrict (c : EnclosureCert α s) (t : Set α) (hsub : t ⊆ s) :
    EnclosedOn c.fn t c.lo c.hi :=
  (c.restrict t hsub).sound

/-- Sum a finite family of enclosure certificates pointwise. -/
def sum {ι : Type*} (t : Finset ι) (c : ι → EnclosureCert α s) :
    EnclosureCert α s where
  fn := fun x ↦ ∑ i ∈ t, (c i).fn x
  lo := ∑ i ∈ t, (c i).lo
  hi := ∑ i ∈ t, (c i).hi
  sound := by
    intro x hx
    exact ⟨Finset.sum_le_sum fun i _hi ↦ ((c i).sound x hx).1,
      Finset.sum_le_sum fun i _hi ↦ ((c i).sound x hx).2⟩

/-- Negate an enclosure certificate pointwise. -/
def neg (a : EnclosureCert α s) : EnclosureCert α s where
  fn := fun x ↦ -a.fn x
  lo := -a.hi
  hi := -a.lo
  sound := enclosedOn_neg a.sound

/-- Subtract two enclosure certificates pointwise. -/
def sub (a b : EnclosureCert α s) : EnclosureCert α s where
  fn := fun x ↦ a.fn x - b.fn x
  lo := a.lo - b.hi
  hi := a.hi - b.lo
  sound := enclosedOn_sub a.sound b.sound

/-- Scale an enclosure by a nonnegative real. -/
def scaleNonneg (r : ℝ) (hr : 0 ≤ r) (a : EnclosureCert α s) :
    EnclosureCert α s where
  fn := fun x ↦ r * a.fn x
  lo := r * a.lo
  hi := r * a.hi
  sound := enclosedOn_scale_nonneg hr a.sound

/-! ## Patch operations -/

/-- Glue two-sided enclosure certificates on two patches.

The functions must agree extensionally as Lean functions.  The combined enclosure
uses the minimum lower endpoint and maximum upper endpoint from the local certificates. -/
def union {t : Set α} (a : EnclosureCert α s) (b : EnclosureCert α t)
    (hfn : a.fn = b.fn) : EnclosureCert α (s ∪ t) where
  fn := a.fn
  lo := min a.lo b.lo
  hi := max a.hi b.hi
  sound := by
    intro x hx
    rcases hx with hx | hx
    · exact ⟨le_trans (min_le_left a.lo b.lo) (a.sound x hx).1,
        le_trans (a.sound x hx).2 (le_max_left a.hi b.hi)⟩
    · have hb : b.lo ≤ a.fn x ∧ a.fn x ≤ b.hi := by
        simpa [hfn.symm] using b.sound x hx
      exact ⟨le_trans (min_le_right a.lo b.lo) hb.1,
        le_trans hb.2 (le_max_right a.hi b.hi)⟩

/-! ## Forgetful projections -/

/-- Forget a two-sided certificate to an upper-bound claim. -/
theorem boundOn (c : EnclosureCert α s) : BoundOn c.fn s c.hi :=
  enclosedOn_upper c.sound

/-- Forget a two-sided certificate to a residual bound when it lies in `[-ε, ε]`. -/
theorem residualBound (c : EnclosureCert α s) {ε : ℝ}
    (hlo : -ε ≤ c.lo) (hhi : c.hi ≤ ε) :
    ResidualBound c.fn s ε :=
  enclosedOn_residualBound c.sound hlo hhi

end EnclosureCert

end CAS.Certificate

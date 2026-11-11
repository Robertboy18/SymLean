/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.Enclosure

/-!
# Upper-bound certificates

`BoundOn f s c` says that `f ≤ c` on `s`. A `BoundCert` stores that theorem as
data, so CEGA routes can carry upper bounds alongside enclosures,
approximations, and residuals.

Product and quotient rules, Lipschitz propagation, Taylor remainders, and
validated numerical estimates all need certified magnitudes. Most bounds come
from one of two places:

* an interval enclosure, via `ofEnclosure` or `absOfEnclosure`;
* a local side-condition or atlas argument that bounds a denominator or a
  profile on a patch.

Only scalar upper bounds are certified here. Approximation, residual, and
quotient reasoning use them through their own certificate constructors.

## Implementation notes

A `BoundCert` holds `fn`, `upper` and, in `sound`, a proof of `BoundOn fn s upper`, which the
kernel checks when the certificate is built; whatever computed `upper` is not trusted.
`ofEnclosure` keeps the upper endpoint of an `EnclosureCert`, and `absOfEnclosure` bounds `|f|`
by `max |lo| |hi|`, the magnitude of the enclosing interval. `sum`, `union`, `scaleNonneg`,
`weaken` and `restrict` only combine proofs, with side conditions such as the sign of the scalar
passed as explicit arguments.
-/

@[expose] public section

namespace CAS.Certificate

/--
A checked real upper-bound certificate on a domain.

`fn` and `upper` are data for planners, and `sound` proves that the function is
bounded by `upper` on the patch.
-/
structure BoundCert (α : Type*) (s : Set α) where
  /-- The bounded function. -/
  fn : α → ℝ
  /-- Upper bound. -/
  upper : ℝ
  /-- `fn ≤ upper` on `s`. -/
  sound : BoundOn fn s upper

namespace BoundCert

variable {α : Type*} {s : Set α}

/-! ## Constructors and projections from enclosures -/

/-- The certificate of an existing upper-bound theorem. -/
def ofBoundOn (fn : α → ℝ) (upper : ℝ) (h : BoundOn fn s upper) :
    BoundCert α s where
  fn := fn
  upper := upper
  sound := h

/-- A constant function is bounded above by itself. -/
def const (c : ℝ) (s : Set α) : BoundCert α s where
  fn := fun _ ↦ c
  upper := c
  sound := by
    intro _x _hx
    exact le_rfl

/-- Every two-sided enclosure gives an upper-bound certificate. -/
def ofEnclosure (c : EnclosureCert α s) : BoundCert α s where
  fn := c.fn
  upper := c.hi
  sound := c.boundOn

/--
Every two-sided real enclosure gives an absolute-value upper-bound certificate.

If `f(x) ∈ [lo, hi]` on a patch, then `|f(x)| ≤ max |lo| |hi|` on that patch.
Product, quotient, and Lipschitz estimates need magnitude bounds, while interval evaluators
produce two-sided enclosures; this converts one to the other.
-/
def absOfEnclosure (c : EnclosureCert α s) : BoundCert α s where
  fn := fun x ↦ |c.fn x|
  upper := max |c.lo| |c.hi|
  sound := by
    intro x hx
    exact abs_le_max_abs_abs (c.sound x hx).1 (c.sound x hx).2

/-! ## Error-budget and domain management -/

/-- Weaken an upper-bound certificate to a larger upper bound. -/
def weaken (c : BoundCert α s) {upper' : ℝ} (hupper : c.upper ≤ upper') :
    BoundCert α s where
  fn := c.fn
  upper := upper'
  sound := by
    intro x hx
    exact le_trans (c.sound x hx) hupper

/-- Restrict an upper-bound certificate to a smaller patch. -/
def restrict (c : BoundCert α s) (t : Set α) (hsub : t ⊆ s) :
    BoundCert α t where
  fn := c.fn
  upper := c.upper
  sound := boundOn_mono_domain c.sound hsub

/-- Restricting a bound certificate to a smaller patch keeps the bounded function. -/
@[simp]
theorem restrict_fn (c : BoundCert α s) (t : Set α) (hsub : t ⊆ s) :
    (c.restrict t hsub).fn = c.fn :=
  rfl

/-- Restricting a bound certificate to a smaller patch keeps the upper bound. -/
@[simp]
theorem restrict_upper (c : BoundCert α s) (t : Set α) (hsub : t ⊆ s) :
    (c.restrict t hsub).upper = c.upper :=
  rfl

/-- Expose domain restriction directly as an ordinary upper-bound theorem. -/
theorem sound_restrict (c : BoundCert α s) (t : Set α) (hsub : t ⊆ s) :
    BoundOn c.fn t c.upper :=
  (c.restrict t hsub).sound

/-- Sum a finite family of upper-bound certificates pointwise. -/
def sum {ι : Type*} (t : Finset ι) (c : ι → BoundCert α s) : BoundCert α s where
  fn := fun x ↦ ∑ i ∈ t, (c i).fn x
  upper := ∑ i ∈ t, (c i).upper
  sound := by
    intro x hx
    exact Finset.sum_le_sum fun i _hi ↦ (c i).sound x hx

/-! ## Patch gluing and scaling -/

/-- Glue upper-bound certificates on two patches.

The functions must agree extensionally as Lean functions; the combined upper
bound is the maximum of the two local upper bounds. -/
def union {t : Set α} (a : BoundCert α s) (b : BoundCert α t)
    (hfn : a.fn = b.fn) : BoundCert α (s ∪ t) where
  fn := a.fn
  upper := max a.upper b.upper
  sound := by
    intro x hx
    rcases hx with hx | hx
    · exact le_trans (a.sound x hx) (le_max_left a.upper b.upper)
    · have hb : a.fn x ≤ b.upper := by
        simpa [hfn.symm] using b.sound x hx
      exact le_trans hb (le_max_right a.upper b.upper)

/-- Scale an upper-bound certificate by a nonnegative scalar; no lower bound is needed. -/
def scaleNonneg (c : BoundCert α s) (r : ℝ) (hr : 0 ≤ r) :
    BoundCert α s where
  fn := fun x ↦ r * c.fn x
  upper := r * c.upper
  sound := by
    intro x hx
    exact mul_le_mul_of_nonneg_left (c.sound x hx) hr

end BoundCert

end CAS.Certificate

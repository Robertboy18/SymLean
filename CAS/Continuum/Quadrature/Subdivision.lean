/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.Quadrature

/-!
# Subdivision trees for verified adaptive quadrature

An adaptive quadrature algorithm repeatedly subdivides an interval, proves a
local certificate on every accepted leaf, and sums the leaves.  The proof
object here does not depend on the rule or on the policy that selected the
subdivision points.

`QuadratureTree f a b` stores only mathematically relevant evidence:

* a leaf contains a `QuadratureCert f a b` and interval integrability;
* a split contains adjacent trees on `[a, m]` and `[m, b]`.

The tree compiles to the same backend-independent `QuadratureCert` used by
fixed-mesh rules.  Thus a tactic, an external adaptive driver, or a hand-built
proof may choose the mesh without adding anything that must be trusted.

## Implementation notes

`toCert` joins the children of a split with `QuadratureCert.addAdjacent`, which adds their values
and their error budgets. Its soundness proof splits the integral with
`intervalIntegral.integral_add_adjacent_intervals` and applies the triangle inequality, which is
why every leaf stores interval integrability. The adaptive searches of `Adaptive`, `PanelRule`
and `RationalAdaptive` return a `WithErrorAtMost` tree.
-/

@[expose] public section

open MeasureTheory

namespace CAS.Continuum

/--
A checked binary subdivision of an oriented interval.

The type indices ensure that child intervals meet exactly at their shared
split point.  No ordering is required because interval integrals are
oriented and the composition theorem is valid in either direction.
-/
inductive QuadratureTree
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : ℝ → ℝ → Type _
  | leaf {a b : ℝ}
      (cert : QuadratureCert f a b)
      (integrable : IntervalIntegrable f volume a b) :
      QuadratureTree f a b
  | split {a m b : ℝ}
      (left : QuadratureTree f a m)
      (right : QuadratureTree f m b) :
      QuadratureTree f a b

namespace QuadratureTree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ → E} {a m b : ℝ}

/-- Interval integrability propagated from the leaves through the tree. -/
protected theorem intervalIntegrable {a b : ℝ} :
    (tree : QuadratureTree f a b) → IntervalIntegrable f volume a b
  | .leaf _ h => h
  | .split left right =>
      left.intervalIntegrable.trans right.intervalIntegrable

/--
Compile a subdivision tree to one quadrature certificate.

Values and errors are associated according to the tree.  Soundness follows
solely from interval-integral additivity and the local leaf certificates.
-/
def toCert {a b : ℝ} :
    (tree : QuadratureTree f a b) → QuadratureCert f a b
  | .leaf cert _ => cert
  | .split left right =>
      (toCert left).addAdjacent (toCert right)
        left.intervalIntegrable right.intervalIntegrable

/-- The root certificate carries the tree's full integral error theorem. -/
theorem sound (tree : QuadratureTree f a b) :
    ‖(∫ x in a..b, f x) - tree.toCert.value‖ ≤ tree.toCert.error :=
  tree.toCert.sound

/-- Join adjacent subdivision trees under one new root. -/
def join
    (left : QuadratureTree f a m)
    (right : QuadratureTree f m b) :
    QuadratureTree f a b :=
  .split left right

/-- A one-leaf tree compiles to the certificate stored at that leaf. -/
@[simp]
theorem toCert_leaf
    (cert : QuadratureCert f a b)
    (integrable : IntervalIntegrable f volume a b) :
    (leaf cert integrable).toCert = cert :=
  rfl

/-- The value of a split is the sum of the two children's values, mirroring additivity of the
oriented interval integral over `a..m` and `m..b`. -/
@[simp]
theorem toCert_split_value
    (left : QuadratureTree f a m)
    (right : QuadratureTree f m b) :
    (split left right).toCert.value =
      left.toCert.value + right.toCert.value :=
  rfl

/-- Error budgets add across a split: the root bound is the sum of the two children's bounds,
which is exactly what the triangle inequality needs for the root to remain sound. -/
@[simp]
theorem toCert_split_error
    (left : QuadratureTree f a m)
    (right : QuadratureTree f m b) :
    (split left right).toCert.error =
      left.toCert.error + right.toCert.error :=
  rfl

/--
Any tree whose accumulated error is below `tol` certifies the corresponding
root error bound with that tolerance.
-/
theorem sound_le
    (tree : QuadratureTree f a b) {tol : ℝ}
    (htol : tree.toCert.error ≤ tol) :
    ‖(∫ x in a..b, f x) - tree.toCert.value‖ ≤ tol :=
  tree.sound.trans htol

/--
A subdivision tree whose accumulated error has been checked against a
requested tolerance.

Search procedures return this wrapper only after proving the comparison.
Consequently failure to find a sufficiently accurate tree is represented by
`none`; it is never replaced by an uncertified fallback.
-/
abbrev WithErrorAtMost
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a b tolerance : ℝ) :=
  { tree : QuadratureTree f a b // tree.toCert.error ≤ tolerance }

namespace WithErrorAtMost

variable {tolerance tolerance' : ℝ}

/-- Build an accepted tree from its accumulated-error proof. -/
def mk (tree : QuadratureTree f a b)
    (error_le : tree.toCert.error ≤ tolerance) :
    WithErrorAtMost f a b tolerance :=
  ⟨tree, error_le⟩

/-- Accepted checked subdivision tree. -/
def tree (result : WithErrorAtMost f a b tolerance) :
    QuadratureTree f a b :=
  result.1

/-- Its accumulated analytic error meets the requested tolerance. -/
theorem error_le (result : WithErrorAtMost f a b tolerance) :
    result.tree.toCert.error ≤ tolerance :=
  result.2

/-- Accepted results are determined by their subdivision trees. -/
@[ext]
theorem ext
    {first second : WithErrorAtMost f a b tolerance}
    (h : first.tree = second.tree) :
    first = second :=
  Subtype.ext h

/-- An accepted tree directly certifies the requested integral error. -/
theorem sound (result : WithErrorAtMost f a b tolerance) :
    ‖(∫ x in a..b, f x) - result.tree.toCert.value‖ ≤ tolerance :=
  result.tree.sound_le result.error_le

/-- Reuse an accepted tree under a weaker tolerance. -/
def weaken (result : WithErrorAtMost f a b tolerance)
    (h : tolerance ≤ tolerance') :
    WithErrorAtMost f a b tolerance' :=
  mk result.tree (result.error_le.trans h)

end WithErrorAtMost

end QuadratureTree

end CAS.Continuum

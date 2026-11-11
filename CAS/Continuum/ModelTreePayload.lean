/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.TaylorModel

/-!
# Payload-preserving adaptive model trees

Numerical backends sometimes need executable leaf data in addition to an
ordinary `ModelApproxCert`. `WithPayload` attaches such data to the leaves of a model tree.

* `WithPayload` stores an ordinary certificate and a client payload per leaf.
* `erase` recovers the underlying `RationalModelTree`.
* The model, error and soundness theorem are those of the erased tree.
* `AllLeaves` expresses any client relation between certificates and payloads.
* `Validated` is a payload tree with a proof of that relation, and
  `Validated.sound_of_adaptive` turns an `AdaptiveResult` over it into `ApproxOn`.
* `selectLeaf` returns the certificate and payload of the leaf that the piecewise model uses
  at a point (`model_eq_selectedLeaf`).

## Implementation notes

The payload is never trusted. Model, error and soundness are defined through `erase`, so they
ignore it, and a client relation between a certificate and its payload holds only where it is
proved leaf by leaf in `AllLeaves`; `selectLeaf_relation` hands it back at a point.
-/

@[expose] public section

open Set

namespace CAS.Continuum

open CAS.Certificate

namespace RationalModelTree

/-- A rational model tree with one endpoint-indexed payload at every leaf. -/
inductive WithPayload
    (f : ℝ → ℝ) (Payload : ℚ → ℚ → Type) :
    ℚ → ℚ → Type
  | leaf {a b : ℚ}
      (cert : ModelApproxCert ℝ ℝ (Icc (a : ℝ) (b : ℝ)))
      (lhs_eq : cert.toApproxCert.lhs = f)
      (payload : Payload a b) :
      WithPayload f Payload a b
  | split {a m b : ℚ}
      (left : WithPayload f Payload a m)
      (right : WithPayload f Payload m b) :
      WithPayload f Payload a b

namespace WithPayload

variable {f : ℝ → ℝ} {Payload : ℚ → ℚ → Type}
variable {a b : ℚ}

/-- Remove payloads and recover the authoritative model tree. -/
def erase :
    {a b : ℚ} → WithPayload f Payload a b → RationalModelTree f a b
  | _, _, .leaf cert original_eq _ => .leaf cert original_eq
  | _, _, .split left right => .split left.erase right.erase

/-- Piecewise model inherited from the erased tree. -/
noncomputable def model (tree : WithPayload f Payload a b) : ℝ → ℝ :=
  tree.erase.model

/-- Uniform error inherited from the erased tree. -/
def error (tree : WithPayload f Payload a b) : ℝ :=
  tree.erase.error

/-- Payload-tree error is nonnegative. -/
theorem error_nonneg (tree : WithPayload f Payload a b) :
    0 ≤ tree.error :=
  tree.erase.error_nonneg

/-- Payload trees inherit the ordinary uniform approximation theorem. -/
theorem sound (tree : WithPayload f Payload a b) :
    ApproxOn f tree.model (Icc (a : ℝ) (b : ℝ)) tree.error :=
  tree.erase.sound

/-- Certificate and payload selected at one point. -/
structure SelectedLeaf
    (Payload : ℚ → ℚ → Type) (x : ℝ) where
  /-- Rational left endpoint of the selected leaf's certified interval. -/
  left : ℚ
  /-- Rational right endpoint of the selected leaf's certified interval. -/
  right : ℚ
  /-- Uniform approximation certificate governing the selected leaf. -/
  cert : ModelApproxCert ℝ ℝ (Icc (left : ℝ) (right : ℝ))
  /-- Executable leaf data indexed by the same endpoints as `cert`. -/
  payload : Payload left right
  /-- The query point lies in the interval covered by the selected certificate. -/
  point_mem : x ∈ Icc (left : ℝ) (right : ℝ)

/--
Select the same local leaf used by the piecewise model.

The split point belongs to the left leaf, matching `RationalModelTree.model`.
-/
noncomputable def selectLeaf :
    {a b : ℚ} → (tree : WithPayload f Payload a b) →
      (x : ℝ) → x ∈ Icc (a : ℝ) (b : ℝ) →
        SelectedLeaf Payload x
  | _, _, .leaf cert _ payload, _x, hx =>
      { left := _
        right := _
        cert := cert
        payload := payload
        point_mem := hx }
  | _, _, .split (m := m) left right, x, hx =>
      if hxm : x ≤ (m : ℝ) then
        left.selectLeaf x ⟨hx.1, hxm⟩
      else
        right.selectLeaf x ⟨le_of_not_ge hxm, hx.2⟩

/-- Selection returns the local model used by the erased piecewise tree. -/
theorem model_eq_selectedLeaf
    (tree : WithPayload f Payload a b)
    (x : ℝ) (hx : x ∈ Icc (a : ℝ) (b : ℝ)) :
    tree.model x = (tree.selectLeaf x hx).cert.toApproxCert.rhs x := by
  induction tree with
  | leaf => rfl
  | @split a m b left right hleft hright =>
      change (if x ≤ (m : ℝ) then left.erase.model x else right.erase.model x) = _
      simp only [selectLeaf]
      by_cases hxm : x ≤ (m : ℝ)
      · rw [ite_eq_left hxm, dite_eq_left hxm]
        exact hleft ⟨hx.1, hxm⟩
      · rw [ite_eq_right hxm, dite_eq_right hxm]
        exact hright ⟨le_of_not_ge hxm, hx.2⟩

/-- A relation holds between the certificate and payload at every leaf. -/
def AllLeaves
    (Relation :
      {a b : ℚ} →
        ModelApproxCert ℝ ℝ (Icc (a : ℝ) (b : ℝ)) →
        Payload a b → Prop) :
    {a b : ℚ} → WithPayload f Payload a b → Prop
  | _, _, .leaf cert _ payload => Relation cert payload
  | _, _, .split left right =>
      left.AllLeaves Relation ∧ right.AllLeaves Relation

/-- The selected certificate/payload pair satisfies the all-leaves relation. -/
theorem selectLeaf_relation
    {Relation :
      {a b : ℚ} →
        ModelApproxCert ℝ ℝ (Icc (a : ℝ) (b : ℝ)) →
        Payload a b → Prop}
    (tree : WithPayload f Payload a b)
    (hvalid : tree.AllLeaves Relation)
    (x : ℝ) (hx : x ∈ Icc (a : ℝ) (b : ℝ)) :
    Relation (tree.selectLeaf x hx).cert
      (tree.selectLeaf x hx).payload := by
  induction tree with
  | leaf => exact hvalid
  | @split a m b left right hleft hright =>
      simp only [selectLeaf]
      by_cases hxm : x ≤ (m : ℝ)
      · rw [dite_eq_left hxm]
        exact hleft hvalid.1 ⟨hx.1, hxm⟩
      · rw [dite_eq_right hxm]
        exact hright hvalid.2 ⟨le_of_not_ge hxm, hx.2⟩

end WithPayload

/-- The certified object composed by adaptive search. -/
abbrev Validated
    (f : ℝ → ℝ) (Payload : ℚ → ℚ → Type)
    (Relation :
      {a b : ℚ} →
        ModelApproxCert ℝ ℝ (Icc (a : ℝ) (b : ℝ)) →
        Payload a b → Prop)
    (a b : ℚ) :=
  { tree : WithPayload f Payload a b // tree.AllLeaves Relation }

namespace Validated

variable {f : ℝ → ℝ} {Payload : ℚ → ℚ → Type}
variable
  {Relation :
    {a b : ℚ} →
      ModelApproxCert ℝ ℝ (Icc (a : ℝ) (b : ℝ)) →
      Payload a b → Prop}
variable {a b : ℚ}

/-- Payload tree whose leaf certificates provide the piecewise approximation. -/
def tree (result : Validated f Payload Relation a b) :
    WithPayload f Payload a b :=
  result.1

/-- Every payload leaf satisfies the requested relation. -/
theorem valid (result : Validated f Payload Relation a b) :
    result.tree.AllLeaves Relation :=
  result.2

/-- Piecewise model inherited from the underlying payload tree. -/
noncomputable def model
    (result : Validated f Payload Relation a b) : ℝ → ℝ :=
  result.tree.model

/-- Uniform error inherited from the underlying payload tree. -/
def error (result : Validated f Payload Relation a b) : ℝ :=
  result.tree.error

/-- A validated payload tree has nonnegative error. -/
theorem error_nonneg (result : Validated f Payload Relation a b) :
    0 ≤ result.error :=
  result.tree.error_nonneg

/-- A validated payload tree is an ordinary uniform approximation. -/
theorem sound (result : Validated f Payload Relation a b) :
    ApproxOn f result.model (Icc (a : ℝ) (b : ℝ)) result.error :=
  result.tree.sound

/-- Select one leaf from a validated payload tree. -/
noncomputable def selectLeaf
    (result : Validated f Payload Relation a b)
    (x : ℝ) (hx : x ∈ Icc (a : ℝ) (b : ℝ)) :
    WithPayload.SelectedLeaf Payload x :=
  result.tree.selectLeaf x hx

/-- The selected pair satisfies the validated leaf relation. -/
theorem selectLeaf_relation
    (result : Validated f Payload Relation a b)
    (x : ℝ) (hx : x ∈ Icc (a : ℝ) (b : ℝ)) :
    Relation (result.selectLeaf x hx).cert
      (result.selectLeaf x hx).payload :=
  result.tree.selectLeaf_relation result.valid x hx

/-- Successful validated adaptive search is ordinarily sound. -/
theorem sound_of_adaptive
    {tolerance : ℚ}
    (result :
      AdaptiveResult
        (fun result : Validated f Payload Relation a b ↦ result.error)
        (tolerance : ℝ)) :
    ApproxOn f result.result.model
      (Icc (a : ℝ) (b : ℝ)) (tolerance : ℝ) :=
  approxOn_mono_error result.result.sound result.error_le

end Validated

end RationalModelTree

end CAS.Continuum

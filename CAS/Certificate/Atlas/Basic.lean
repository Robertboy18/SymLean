/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Basic.Real.Basic
public import CAS.Domain.PatchCover

/-!
# Shared certificate-atlas carriers

A certificate atlas attaches a certificate to every patch of a `PatchCover` and records
that all of them concern one global function. `FunctionAtlasCert` holds this data and
`FunctionBudgetAtlasCert` adds a global error budget dominating every local one. The
approximation and residual atlases specialize these carriers and prove their own soundness
theorems.

## Implementation notes

The carriers prove nothing themselves. Agreement is an equality of functions, not agreement on
the patch, so a local certificate whose formula matches the global one only on its patch is first
moved to the global formula, for example with `ResidualCert.replaceResidual`.
`ApproxAtlasCert.sound` and `ResidualAtlasCert.sound` then combine the local `sound` proofs with
`cert_fn` and `cert_budget` through `PatchCover.lift`. The caller chooses the cover, the local
certificates and the global budget; the kernel checks only the proofs stored in the fields. The
index type is arbitrary, so the cover need not be finite.
-/

@[expose] public section

namespace CAS.Certificate

open CAS.Domain

/--
Patch-local certificates for one shared global function.

`certificateFunction` extracts the function certified on each patch.  The
agreement field says that every local certificate concerns the same global
function.
-/
structure FunctionAtlasCert (α E ι : Type*) (domain : Set α)
    (Certificate : Set α → Type*)
    (certificateFunction : {patch : Set α} → Certificate patch → α → E) where
  /-- Patches covering the target domain. -/
  cover : PatchCover α ι domain
  /-- Certificate attached to each patch. -/
  onPatch : (i : ι) → Certificate (cover.patch i)
  /-- Global function certified by the atlas. -/
  fn : α → E
  /-- Every patch-local certified function is the global function. -/
  cert_fn : ∀ i, certificateFunction (onPatch i) = fn

namespace FunctionAtlasCert

variable {α E ι : Type*} {domain : Set α}
  {Certificate : Set α → Type*}
  {certificateFunction : {patch : Set α} → Certificate patch → α → E}

/-- Attach a common function to certificates over an arbitrary patch cover. -/
def ofCover (cover : PatchCover α ι domain) (fn : α → E)
    (certAt : (i : ι) → Certificate (cover.patch i))
    (cert_fn : ∀ i, certificateFunction (certAt i) = fn) :
    FunctionAtlasCert α E ι domain Certificate certificateFunction where
  cover := cover
  onPatch := certAt
  fn := fn
  cert_fn := cert_fn

/-- Attach two certificates for the same function to a binary patch cover. -/
def ofBinaryCover {left right : Set α} (hcover : domain ⊆ left ∪ right)
    (leftCert : Certificate left) (rightCert : Certificate right)
    (hfn : certificateFunction rightCert = certificateFunction leftCert) :
    FunctionAtlasCert α E Bool domain Certificate certificateFunction where
  cover := PatchCover.binary hcover
  onPatch := fun b ↦
    match b with
    | true => leftCert
    | false => rightCert
  fn := certificateFunction leftCert
  cert_fn := by
    intro b
    cases b
    · exact hfn
    · rfl

end FunctionAtlasCert

/--
Patch-local certificates for one shared function and one global upper budget.

`ApproxAtlasCert` and `ResidualAtlasCert` are both built on this. `certificateBudget` gives
the patch-local budget; each such budget must be no larger than the global one.
-/
structure FunctionBudgetAtlasCert (α E ι : Type*) (domain : Set α)
    (Certificate : Set α → Type*)
    (certificateFunction : {patch : Set α} → Certificate patch → α → E)
    (certificateBudget : {patch : Set α} → Certificate patch → ℝ)
    extends
      FunctionAtlasCert α E ι domain Certificate certificateFunction where
  /-- Global budget valid on the covered domain. -/
  budget : ℝ
  /-- Every patch-local budget is bounded by the global budget. -/
  cert_budget : ∀ i, certificateBudget (onPatch i) ≤ budget

namespace FunctionBudgetAtlasCert

variable {α E ι : Type*} {domain : Set α}
  {Certificate : Set α → Type*}
  {certificateFunction : {patch : Set α} → Certificate patch → α → E}
  {certificateBudget : {patch : Set α} → Certificate patch → ℝ}

/-- Build a shared-function, upper-budget atlas over an arbitrary cover. -/
def ofCover (cover : PatchCover α ι domain) (fn : α → E) (budget : ℝ)
    (certAt : (i : ι) → Certificate (cover.patch i))
    (cert_fn : ∀ i, certificateFunction (certAt i) = fn)
    (cert_budget : ∀ i, certificateBudget (certAt i) ≤ budget) :
    FunctionBudgetAtlasCert α E ι domain Certificate
      certificateFunction certificateBudget where
  toFunctionAtlasCert :=
    FunctionAtlasCert.ofCover cover fn certAt cert_fn
  budget := budget
  cert_budget := cert_budget

/-- Combine two certificates using the maximum of their local budgets. -/
def ofBinaryCover {left right : Set α} (hcover : domain ⊆ left ∪ right)
    (leftCert : Certificate left) (rightCert : Certificate right)
    (hfn : certificateFunction rightCert = certificateFunction leftCert) :
    FunctionBudgetAtlasCert α E Bool domain Certificate
      certificateFunction certificateBudget where
  toFunctionAtlasCert :=
    FunctionAtlasCert.ofBinaryCover hcover leftCert rightCert hfn
  budget := max (certificateBudget leftCert) (certificateBudget rightCert)
  cert_budget := by
    intro b
    cases b
    · exact le_max_right _ _
    · exact le_max_left _ _

end FunctionBudgetAtlasCert

end CAS.Certificate

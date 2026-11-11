/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.Atlas.Approximation -- shake: keep

/-!
# Model approximation certificates

A `ModelApproxCert` is an `ApproxCert` from a source function to a reference model, paired with
a natural number `modelOrder` that records how the model was built; `taylorLeafCandidate` and
`TaylorJetCert.toModelApproxCert` store the order of their Taylor polynomial there. Only
construction (`ofApproxCert`, `ofApproxOn`), restriction, and soundness are defined for
`ModelApproxCert`. Algebraic operations and budget changes act on the underlying `ApproxCert`.

## Implementation notes

The order is a label. It carries no proof obligation and no theorem depends on it: the
mathematical content is the uniform error bound of the stored `ApproxCert`, whose proof the
kernel checks when the certificate is built, and `ModelApproxCert.sound` returns it. A
polynomial degree or a finite-dimensional model space would be a separate theorem.
-/

@[expose] public section

namespace CAS.Certificate

/--
A checked uniform approximation with model-order metadata.

The field `modelOrder` is an unconstrained label recording how the model was constructed;
only `toApproxCert` carries a proof.
-/
structure ModelApproxCert (α E : Type*) [NormedAddCommGroup E] (patch : Set α) where
  /-- Canonical approximation certificate from the source function to the reference function. -/
  toApproxCert : ApproxCert α E patch
  /-- Model order, a label without proof obligation (for a Taylor model, its order). -/
  modelOrder : Nat

namespace ModelApproxCert

variable {α E : Type*} [NormedAddCommGroup E] {patch : Set α}

/-- The reference function approximates the source within the stored error budget. -/
theorem sound (cert : ModelApproxCert α E patch) :
    ApproxOn cert.toApproxCert.lhs cert.toApproxCert.rhs patch
      cert.toApproxCert.eps :=
  cert.toApproxCert.sound

/-- Attach model-order metadata to an approximation certificate. -/
def ofApproxCert (modelOrder : Nat) (cert : ApproxCert α E patch) :
    ModelApproxCert α E patch where
  toApproxCert := cert
  modelOrder := modelOrder

/-- The certificate of an existing approximation theorem, with model-order metadata. -/
def ofApproxOn (original model : α → E) (modelOrder : Nat) (eps : ℝ)
    (h : ApproxOn original model patch eps) :
    ModelApproxCert α E patch :=
  ofApproxCert modelOrder (ApproxCert.ofApproxOn original model eps h)

/-- Restrict a model approximation certificate to a smaller patch. -/
def restrict (cert : ModelApproxCert α E patch) (smaller : Set α)
    (hsub : smaller ⊆ patch) : ModelApproxCert α E smaller :=
  ofApproxCert cert.modelOrder (cert.toApproxCert.restrict smaller hsub)

end ModelApproxCert

end CAS.Certificate

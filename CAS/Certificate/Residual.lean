/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.Approximation

/-!
# Residual certificates

A `ResidualCert` stores a residual function, a tolerance `eps`, and a proof of
`ResidualBound residual s eps`, the statement that the residual is uniformly `eps`-small on
the patch `s`. A symbolic backend proves the case `eps = 0` by simplifying a differential
residual to zero; a numerical backend bounds it by a positive tolerance.

Residuals are functions in their own right, so a route can move between:

* exact symbolic identities, where `eps = 0`;
* interval estimates, where `eps > 0`;
* approximation-to-zero facts, via `toApproxCert`;
* weak-form or PDE goals that use the same residual function after an
  integral or analytic-derivative identity.

The certificate records the bound, not how the residual was computed.

## Implementation notes

The kernel checks the proof of `ResidualBound residual s eps` in `sound` when a certificate is
built; the tolerance and any interval behind it are proposals of the backend. An exact identity
enters through `ofEqOnZero` with budget `0`, an interval bound through `ofResidualBound`, for
example after `RealIntervalBackend.residualBound_of_memReal_le`. `toApproxCert` reads the same
proof as an approximation of the residual by zero, and `eqOn_zero_of_eps_eq_zero` recovers the
exact identity from a zero budget.
-/

@[expose] public section

namespace CAS.Certificate

/--
A checked residual bound on a domain.

`residual` is the function being checked, `eps` is the uniform tolerance, and
`sound` is the proof of the bound. Exact symbolic PDE checks are the case
`eps = 0`; validated/numerical checks use positive `eps`.  As with
`ApproxCert`, soundness forces `eps` to be nonnegative on a nonempty domain;
a negative budget is possible only when the domain is empty.
-/
structure ResidualCert (α E : Type*) [NormedAddCommGroup E] (s : Set α) where
  /-- The residual function. -/
  residual : α → E
  /-- Uniform residual error.  It is nonnegative whenever `s` is nonempty. -/
  eps : ℝ
  /-- The residual is uniformly `eps`-small on `s`. -/
  sound : ResidualBound residual s eps

namespace ResidualCert

variable {α E : Type*} [NormedAddCommGroup E] {s : Set α}

/-! ## Constructors and approximation by zero -/

/-- The certificate of an existing residual bound. -/
def ofResidualBound (residual : α → E) (eps : ℝ)
    (h : ResidualBound residual s eps) : ResidualCert α E s where
  residual := residual
  eps := eps
  sound := h

/-- A zero residual has zero error. -/
def zero (s : Set α) : ResidualCert α E s where
  residual := fun _ ↦ 0
  eps := 0
  sound := by
    intro x _hx
    simp

/-- Equality to zero on the domain gives a zero-error residual certificate. -/
def ofEqOnZero (residual : α → E) (h : Set.EqOn residual (fun _ ↦ 0) s) :
    ResidualCert α E s where
  residual := residual
  eps := 0
  sound := approxOn_of_eqOn h

/-- Convert a residual certificate to an approximation-by-zero certificate. -/
def toApproxCert (c : ResidualCert α E s) : ApproxCert α E s :=
  ApproxCert.ofResidualBound c.residual c.eps c.sound

/-! ## Error-budget invariant -/

/-- Every residual budget on a nonempty domain is nonnegative. -/
theorem eps_nonneg (c : ResidualCert α E s) (hs : s.Nonempty) : 0 ≤ c.eps :=
  c.toApproxCert.eps_nonneg hs

/-- A residual budget is nonnegative unless its certified domain is empty. -/
theorem eps_nonneg_or_eq_empty (c : ResidualCert α E s) : 0 ≤ c.eps ∨ s = ∅ :=
  c.toApproxCert.eps_nonneg_or_eq_empty

/-! ## Error-budget and domain management -/

/-- Weaken a residual certificate to a larger error budget. -/
def weaken (c : ResidualCert α E s) {eps' : ℝ} (heps : c.eps ≤ eps') :
    ResidualCert α E s where
  residual := c.residual
  eps := eps'
  sound := approxOn_mono_error c.sound heps

/-- Restrict a residual certificate to a smaller patch. -/
def restrict (c : ResidualCert α E s) (t : Set α) (hsub : t ⊆ s) :
    ResidualCert α E t where
  residual := c.residual
  eps := c.eps
  sound := residualBound_mono_domain c.sound hsub

/-- Restricting the domain leaves the residual function unchanged. -/
@[simp]
theorem restrict_residual (c : ResidualCert α E s) (t : Set α) (hsub : t ⊆ s) :
    (c.restrict t hsub).residual = c.residual :=
  rfl

/-- Restricting the domain leaves the error budget unchanged. -/
@[simp]
theorem restrict_eps (c : ResidualCert α E s) (t : Set α) (hsub : t ⊆ s) :
    (c.restrict t hsub).eps = c.eps :=
  rfl

/-- Expose domain restriction directly as an ordinary residual theorem. -/
theorem sound_restrict (c : ResidualCert α E s) (t : Set α) (hsub : t ⊆ s) :
    ResidualBound c.residual t c.eps :=
  (c.restrict t hsub).sound

/-! ## Patch gluing and exact-zero projections -/

/-- Glue residual certificates on two patches.

The residual functions must agree extensionally as Lean functions; the combined
error is the maximum of the two local residual budgets. -/
def union {t : Set α} (a : ResidualCert α E s) (b : ResidualCert α E t)
    (hres : a.residual = b.residual) : ResidualCert α E (s ∪ t) where
  residual := a.residual
  eps := max a.eps b.eps
  sound := by
    intro x hx
    rcases hx with hx | hx
    · exact le_trans (a.sound x hx) (le_max_left a.eps b.eps)
    · have hb : ‖a.residual x - 0‖ ≤ b.eps := by
        simpa [hres.symm] using b.sound x hx
      exact le_trans hb (le_max_right a.eps b.eps)

/-- A zero-error residual certificate gives equality to zero on the domain. -/
theorem eqOn_zero_of_eps_eq_zero (c : ResidualCert α E s) (heps : c.eps = 0) :
    Set.EqOn c.residual (fun _ ↦ 0) s :=
  eqOn_of_approxOn_zero (by simpa [ResidualBound, heps] using c.sound)

end ResidualCert

end CAS.Certificate

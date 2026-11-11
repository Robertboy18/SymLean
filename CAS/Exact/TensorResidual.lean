/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Exact.ZeroResidual

/-!
# Tensor symbolic residuals

A `TensorResidual n rows cols` is a matrix of symbolic residual entries over `ℝ^n`. Each entry
is checked by a scalar route, and the entrywise results assemble into equality with zero
(`eqOn_zero`), a zero-error certificate (`tensorResidualCertZero`), and a tensor-valued
zero residual bound (`residualBound_zero`) on the same domain. The `Ready` variants use
the unconditional `cas` route, which emits no side obligations; the others use the
side-conditioned route and take the domain proofs of its obligations as hypotheses.
-/

@[expose] public section

namespace CAS

namespace Exact

open MeasureTheory
open CAS.Certificate

/-! ### Componentwise tensor residuals

Tensor identities reduce to scalar identities at each pair of indices, so a `TensorResidual`
stores exactly those symbolic entries, and every tensor statement is assembled from the scalar
checks of its entries.
-/

/-- A finite matrix of symbolic residual entries over an `n`-dimensional input. -/
def TensorResidual (n rows cols : Nat) :=
  Fin rows → Fin cols → Verified.Expr (Fin n)

namespace TensorResidual

/-- The exact symbolic route for one tensor residual entry. -/
def entryRoute {n rows cols : Nat} (route : TensorResidual n rows cols)
    (i : Fin rows) (j : Fin cols) : SymbolicClaimRoute n :=
  SymbolicClaimRoute.cas (route i j)

/-- The side-conditioned symbolic route for one tensor residual entry. -/
def entrySideRoute {n rows cols : Nat} (route : TensorResidual n rows cols)
    (i : Fin rows) (j : Fin cols) : SymbolicClaimRoute n :=
  SymbolicClaimRoute.withSideConditions (route i j)

/-- Interpret a symbolic tensor residual as a real tensor-valued function. -/
noncomputable def tensorFn {n rows cols : Nat} (route : TensorResidual n rows cols) :
    ℝ^n → Fin rows → Fin cols → ℝ :=
  fun x i j ↦ (route i j).eval x

/-- Entry-level side-condition discharge predicate. -/
def EntrySideHoldsOn {n rows cols : Nat} (route : TensorResidual n rows cols)
    (i : Fin rows) (j : Fin cols) (s : Set (ℝ^n)) : Prop :=
  (route.entrySideRoute i j).SideHoldsOn s

/-- A ready entry route proves equality between that entry and zero. -/
theorem entry_eqOn_zero_ready {n rows cols : Nat} (route : TensorResidual n rows cols)
    (s : Set (ℝ^n)) (i : Fin rows) (j : Fin cols)
    (hzero : (route.entryRoute i j).rhs = (0 : Verified.Expr (Fin n))) :
    Set.EqOn (exprFn (route i j)) zeroFn s := by
  simpa [entryRoute] using
    (route.entryRoute i j).eqOn_zero_ready s hzero rfl

/-- A side-conditioned entry route proves equality between that entry and zero. -/
theorem entry_eqOn_zero {n rows cols : Nat} (route : TensorResidual n rows cols)
    (s : Set (ℝ^n)) (i : Fin rows) (j : Fin cols)
    (hside : route.EntrySideHoldsOn i j s)
    (hzero : (route.entrySideRoute i j).rhs = (0 : Verified.Expr (Fin n))) :
    Set.EqOn (exprFn (route i j)) zeroFn s := by
  simpa [entrySideRoute, EntrySideHoldsOn] using
    (route.entrySideRoute i j).eqOn_zero s hside hzero

/-- Ready entry routes prove equality to zero for the whole tensor residual. -/
theorem eqOn_zero_ready {n rows cols : Nat} (route : TensorResidual n rows cols)
    (s : Set (ℝ^n))
    (hzero : ∀ i : Fin rows, ∀ j : Fin cols,
      (route.entryRoute i j).rhs = (0 : Verified.Expr (Fin n))) :
    Set.EqOn route.tensorFn (fun _ ↦ 0) s := by
  intro x hx
  funext i j
  simpa [tensorFn, exprFn, zeroFn] using route.entry_eqOn_zero_ready s i j (hzero i j) hx

/-- Side-conditioned entry routes prove equality to zero for the whole tensor residual. -/
theorem eqOn_zero {n rows cols : Nat} (route : TensorResidual n rows cols)
    (s : Set (ℝ^n))
    (hside : ∀ i : Fin rows, ∀ j : Fin cols, route.EntrySideHoldsOn i j s)
    (hzero : ∀ i : Fin rows, ∀ j : Fin cols,
      (route.entrySideRoute i j).rhs = (0 : Verified.Expr (Fin n))) :
    Set.EqOn route.tensorFn (fun _ ↦ 0) s := by
  intro x hx
  funext i j
  simpa [tensorFn, exprFn, zeroFn] using route.entry_eqOn_zero s i j (hside i j) (hzero i j) hx

/-- Ready entry routes give a zero-error certificate for the whole tensor residual. -/
noncomputable def tensorResidualCertZeroReady {n rows cols : Nat}
    (route : TensorResidual n rows cols) (s : Set (ℝ^n))
    (hzero : ∀ i : Fin rows, ∀ j : Fin cols,
      (route.entryRoute i j).rhs = (0 : Verified.Expr (Fin n))) :
    ResidualCert (ℝ^n) (Fin rows → Fin cols → ℝ) s :=
  ResidualCert.ofEqOnZero route.tensorFn
    (route.eqOn_zero_ready s hzero)

/-- Side-conditioned entry routes give a zero-error certificate for the whole tensor residual. -/
noncomputable def tensorResidualCertZero {n rows cols : Nat}
    (route : TensorResidual n rows cols) (s : Set (ℝ^n))
    (hside : ∀ i : Fin rows, ∀ j : Fin cols, route.EntrySideHoldsOn i j s)
    (hzero : ∀ i : Fin rows, ∀ j : Fin cols,
      (route.entrySideRoute i j).rhs = (0 : Verified.Expr (Fin n))) :
    ResidualCert (ℝ^n) (Fin rows → Fin cols → ℝ) s :=
  ResidualCert.ofEqOnZero route.tensorFn
    (route.eqOn_zero s hside hzero)

/-- Ready entry routes prove a tensor-valued zero residual bound. -/
theorem residualBound_zero_ready {n rows cols : Nat}
    (route : TensorResidual n rows cols) (s : Set (ℝ^n))
    (hzero : ∀ i : Fin rows, ∀ j : Fin cols,
      (route.entryRoute i j).rhs = (0 : Verified.Expr (Fin n))) :
    ResidualBound route.tensorFn s 0 :=
  (route.tensorResidualCertZeroReady s hzero).sound

/-- Side-conditioned entry routes prove a tensor-valued zero residual bound. -/
theorem residualBound_zero {n rows cols : Nat}
    (route : TensorResidual n rows cols) (s : Set (ℝ^n))
    (hside : ∀ i : Fin rows, ∀ j : Fin cols, route.EntrySideHoldsOn i j s)
    (hzero : ∀ i : Fin rows, ∀ j : Fin cols,
      (route.entrySideRoute i j).rhs = (0 : Verified.Expr (Fin n))) :
    ResidualBound route.tensorFn s 0 :=
  (route.tensorResidualCertZero s hside hzero).sound

end TensorResidual

end Exact

end CAS

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.Passes.Basic
public import CAS.ClosedForm.Pipeline.SideClaim

/-!
# Unconditional checked claims

The symbolic transformations that preserve denotation without assumptions, as `SideClaimRoute`s
with an empty nonvanishing list built by `SideClaimRoute.exact`. `checkedClaimRoute` runs the
ordinary pass list `checkedPasses` (`structural`, `trig`, `algebra`, `factor-common`) to a fixed
point, and `factorClaimRoute` runs the staged factorization `factorRouteOutput`, one algebraic
normalization followed by one common-factor reconstruction. `simplifyPipeline` runs the same
`checkedPasses`, so the run, the reported pass list and the soundness proof share one pass
sequence. Names and pass lists are diagnostic metadata only.
-/

@[expose] public section

namespace CAS.Verified.Expr

/-- Staged factorization used when expansion and reconstruction should not share a fixed point. -/
def factorRouteOutput {ι : Type*} [DecidableEq ι] (expr : Verified.Expr ι) :
    Verified.Expr ι :=
  factorCommonAddDeep (Alg.normalize expr)

/-- The staged exact factorization route preserves denotation. -/
@[simp] theorem eval_factorRouteOutput {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι) :
    (factorRouteOutput expr).eval ρ = expr.eval ρ := by
  simp [factorRouteOutput]

/-- The staged factorization `factorRouteOutput` as an unconditional checked claim. -/
def factorClaimRoute {ι : Type*} [DecidableEq ι] (expr : Verified.Expr ι) :
    SideClaimRoute ι :=
  SideClaimRoute.exact expr (factorRouteOutput expr) (fun ρ ↦ eval_factorRouteOutput ρ expr)
    [{ name := "algebra", kind := .checked },
     { name := "factor-common", kind := .checked }]

/-- The canonical ordered pass list for exact normalization.

The configured pipeline shares this definition with `checkedClaimRoute`,
so the run, the reported pass list and the soundness proof use the same pass sequence. -/
def checkedPasses {ι : Type*} [DecidableEq ι] : List (Pass ι) :=
  [structuralPass, trigPass, algebraPass, factorPass]

/-- Planner-visible unconditional claim for ordinary fixed-point execution. -/
def checkedClaimRoute {ι : Type*} [DecidableEq ι] (fuel : Nat)
    (expr : Verified.Expr ι) : SideClaimRoute ι :=
  SideClaimRoute.exact expr (runFixed (checkedPasses (ι := ι)) fuel expr)
    (fun ρ ↦ eval_runFixed ρ _ fuel expr)
    ((checkedPasses (ι := ι)).map Pass.info)

/-- The unconditional simplification passes add no nonzero assumptions, for any fuel. -/
@[simp] theorem checkedClaimRoute_nonzero {ι : Type*} [DecidableEq ι] (fuel : Nat)
    (expr : Verified.Expr ι) :
    (checkedClaimRoute fuel expr).nonzero = [] :=
  rfl

/-- Factoring preserves evaluation without imposing nonzero assumptions. -/
@[simp] theorem factorClaimRoute_nonzero {ι : Type*} [DecidableEq ι] (expr : Verified.Expr ι) :
    (factorClaimRoute expr).nonzero = [] :=
  rfl

end CAS.Verified.Expr

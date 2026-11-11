/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Differential.Expression

/-!
# Domain requirements for symbolic differential expressions

The symbolic derivative of a lowered expression is the true derivative at points where the
differentiated expression is valid in the sense of `Verified.Expr.ValidAt`: denominators and
logarithm arguments nonzero, inverse sine and cosine arguments different from `±1`, square-root
arguments and real-power bases positive. `AnalyticSideCondition` asks for this validity of the
operand at every `pderiv` node, and of the operand and its first partials at every `laplacian`
node. `analyticRequirements` collects the same conditions as a finite
`Verified.Expr.ValidityRequirements`, and `analyticSideCondition_of_requirements` proves that the
finite collection implies the recursive condition.
-/

@[expose] public section

namespace CAS

namespace DiffExpr
/-- Analytic side-conditions needed when differential nodes are interpreted by actual Lean
partial derivatives or Laplacians. -/
def AnalyticSideCondition {n : Nat} {σ : Type*}
    (ansatz : σ → Verified.Expr (Fin n)) (x : ℝ^n) : DiffExpr n σ → Prop
  | .atom _ | .unknown _ => True
  | .add a b | .mul a b | .sub a b | .div a b =>
      AnalyticSideCondition ansatz x a ∧ AnalyticSideCondition ansatz x b
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a |
      .exp a | .log a | .sqrt a =>
      AnalyticSideCondition ansatz x a
  | .pderiv _ a =>
      AnalyticSideCondition ansatz x a ∧ (lower ansatz a).ValidAt x
  | .laplacian a =>
      AnalyticSideCondition ansatz x a ∧
        (lower ansatz a).ValidAt x ∧
        ∀ i : Fin n, (((lower ansatz a).diff i).ValidAt x)

/-! ## Analytic requirements

`AnalyticSideCondition` is the proposition needed to interpret derivative-bearing differential
expressions using actual Euclidean derivatives. Its finite symbolic evidence uses
`Verified.Expr.ValidityRequirements` directly: denominator and real-logarithm arguments must be
nonzero, inverse-sine and inverse-cosine arguments must avoid their nondifferentiable endpoints,
and real-square-root arguments must be positive. -/

/-- Merge a list of validity requirements by concatenating their nonzero lists and their
positive lists. -/
def collectValidityRequirements {ι : Type*}
    (requirements : List (Verified.Expr.ValidityRequirements ι)) :
    Verified.Expr.ValidityRequirements ι where
  nonzero := requirements.flatMap fun requirement ↦ requirement.nonzero
  positive := requirements.flatMap fun requirement ↦ requirement.positive

/-- Extract the checked-expression validity requirements needed by differential operators.

Only lowered expressions whose symbolic derivatives are compared with Lean's analytic derivatives
contribute new obligations. The result has the same requirement type and semantics as
`Verified.Expr.validityRequirements`. -/
def analyticRequirements {n : Nat} {σ : Type*} (ansatz : σ → Verified.Expr (Fin n)) :
    DiffExpr n σ → Verified.Expr.ValidityRequirements (Fin n)
  | .atom _ | .unknown _ => collectValidityRequirements []
  | .add a b | .mul a b | .sub a b | .div a b =>
      collectValidityRequirements
        [analyticRequirements ansatz a, analyticRequirements ansatz b]
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a |
      .exp a | .log a | .sqrt a =>
      analyticRequirements ansatz a
  | .pderiv _ a =>
      collectValidityRequirements
        [analyticRequirements ansatz a, (lower ansatz a).validityRequirements]
  | .laplacian a =>
      let lowered := lower ansatz a
      collectValidityRequirements
        ([analyticRequirements ansatz a, lowered.validityRequirements] ++
          List.ofFn (fun i : Fin n ↦ (lowered.diff i).validityRequirements))

private theorem holds_of_mem_collectValidityRequirements {ι : Type*} {ρ : ι → ℝ}
    {requirements : List (Verified.Expr.ValidityRequirements ι)}
    {requirement : Verified.Expr.ValidityRequirements ι}
    (h : (collectValidityRequirements requirements).Holds ρ)
    (hmem : requirement ∈ requirements) : requirement.Holds ρ :=
  ⟨fun d hd ↦ h.1 d (List.mem_flatMap.mpr ⟨requirement, hmem, hd⟩),
    fun d hd ↦ h.2 d (List.mem_flatMap.mpr ⟨requirement, hmem, hd⟩)⟩

/-- The canonical validity requirements imply the recursive analytic side condition. -/
theorem analyticSideCondition_of_requirements {n : Nat} {σ : Type*}
    (ansatz : σ → Verified.Expr (Fin n)) (x : ℝ^n) :
    ∀ e : DiffExpr n σ, (analyticRequirements ansatz e).Holds x →
      DiffExpr.AnalyticSideCondition ansatz x e
  | .atom _, _ | .unknown _, _ => trivial
  | .add a b, h | .mul a b, h | .sub a b, h | .div a b, h =>
      ⟨analyticSideCondition_of_requirements ansatz x a
          (holds_of_mem_collectValidityRequirements h (by simp)),
        analyticSideCondition_of_requirements ansatz x b
          (holds_of_mem_collectValidityRequirements h (by simp))⟩
  | .neg a, h | .pow a _, h | .sin a, h | .cos a, h | .atan a, h | .asin a, h |
      .acos a, h | .exp a, h | .log a, h | .sqrt a, h =>
      analyticSideCondition_of_requirements ansatz x a h
  | .pderiv _ a, h =>
      ⟨analyticSideCondition_of_requirements ansatz x a
          (holds_of_mem_collectValidityRequirements h (by simp)),
        Verified.Expr.ValidityRequirements.validAt_of_holds x _
          (holds_of_mem_collectValidityRequirements h (by simp))⟩
  | .laplacian a, h =>
      ⟨analyticSideCondition_of_requirements ansatz x a
          (holds_of_mem_collectValidityRequirements h (by simp)),
        Verified.Expr.ValidityRequirements.validAt_of_holds x _
          (holds_of_mem_collectValidityRequirements h (by simp)),
        fun i ↦ Verified.Expr.ValidityRequirements.validAt_of_holds x _
          (holds_of_mem_collectValidityRequirements h (by simp))⟩

end DiffExpr

end CAS

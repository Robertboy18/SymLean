/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.Configured

/-!
# Canonical nonzero side conditions

`compactNonzero` turns the nonzero obligations emitted by the side-aware normalizers into short
factor-level obligations. A denominator recorded after polynomial expansion, such as
`√u * x² + √u * y²`, reaches the caller as `√u ≠ 0` and `x² + y² ≠ 0`. The compact list implies
the original one (`sideHolds_of_compactNonzero`) but need not be equivalent to it. The
antiderivative check (`IntegrationCheck.AntiderivativeCert.requirements`) and the summand route
of `cas` (`DerivativeBridge.certifyAbstractedSumDifference`) compact their obligations this way.

## Main definitions

* `compactNonzeroOne`, `compactNonzero`: the compact obligations of one expression and of a
  list.

## Main results

* `eval_ne_zero_of_compactNonzeroOne`, `sideHolds_of_compactNonzero`: the compact obligations
  imply the original ones.
* `eval_eq_of_summandRun_compact`, `eval_eq_of_abstractedSummandRun_compact`: the certification
  statements of the summand route with compacted conditions.

## Implementation notes

For each obligation, `compactNonzeroResult` collects repeated square-root products with
`sqrtProductCollectSidePass` and keeps that pass's own conditions, extracts the symbolic factors
common to every additive term with `factorCommonAddDeep`, splits products and positive powers
with `Alg.sideFactors`, normalizes each factor with the unconditional `simplifyPipeline`, and
deduplicates with `Alg.cleanSide`. No factorization oracle is trusted: every step either
preserves evaluation (the soundness of the square-root pass, `eval_factorCommonAddDeep`,
`eval_simplifyPipeline_runFixed`) or comes with its implication
(`Alg.eval_ne_zero_of_sideFactors`), so `eval_ne_zero_of_compactNonzeroOne` is a direct
composition. An irreducible sum stays one obligation.
-/

@[expose] public section

namespace CAS.Verified.Expr

/--
Normalized expression and sufficient nonzero obligations for one original
nonzero condition.
-/
def compactNonzeroResult {ι : Type*} [DecidableEq ι]
    (expr : Verified.Expr ι) : Alg.NormResult ι :=
  let collected :=
    (sqrtProductCollectSidePass (ι := ι)).run expr
  let factored := factorCommonAddDeep collected.expr
  let factors := (Alg.sideFactors factored).map
    (simplifyPipeline (ι := ι)).runFixed
  { expr := factored
    nonzero := Alg.cleanSide
      (collected.nonzero ++ factors) }

/-- Canonical sufficient obligations for one nonzero expression. -/
def compactNonzeroOne {ι : Type*} [DecidableEq ι]
    (expr : Verified.Expr ι) : List (Verified.Expr ι) :=
  (compactNonzeroResult expr).nonzero

/-- The compact obligations for one expression imply that it is nonzero. -/
theorem eval_ne_zero_of_compactNonzeroOne
    {ι : Type*} [DecidableEq ι] {ρ : ι → ℝ}
    (expr : Verified.Expr ι)
    (h : Alg.SideHolds ρ (compactNonzeroOne expr)) :
    expr.eval ρ ≠ 0 := by
  have hraw := Alg.sideHolds_of_cleanSide h
  rw [← (sqrtProductCollectSidePass (ι := ι)).sound ρ expr hraw.append_left,
    ← eval_factorCommonAddDeep]
  refine Alg.eval_ne_zero_of_sideFactors ρ _ fun factor hfactor ↦ ?_
  simpa using hraw.append_right _ (List.mem_map.mpr ⟨factor, hfactor, rfl⟩)

/--
Normalize, factor, and deduplicate a list of nonzero obligations.

This operation may leave an irreducible sum as one obligation. Square-root
collection retains its own side conditions; factorization and normalization
then give sufficient factor obligations. The resulting list implies the
original conditions, but need not be equivalent to them.
-/
def compactNonzero {ι : Type*} [DecidableEq ι]
    (side : List (Verified.Expr ι)) : List (Verified.Expr ι) :=
  Alg.cleanSide (side.flatMap compactNonzeroOne)

/-- Compact nonzero obligations imply every original obligation. -/
theorem sideHolds_of_compactNonzero
    {ι : Type*} [DecidableEq ι] {ρ : ι → ℝ}
    {side : List (Verified.Expr ι)}
    (h : Alg.SideHolds ρ (compactNonzero side)) :
    Alg.SideHolds ρ side := fun expr hexpr ↦
  eval_ne_zero_of_compactNonzeroOne expr fun factor hfactor ↦
    Alg.sideHolds_of_cleanSide h factor (List.mem_flatMap.mpr ⟨expr, hexpr, hfactor⟩)

/--
The certification statement of the summand route with compacted conditions: the summand run
has the normal form `0`, and the essential conditions of the *compacted* recorded list are
`side`. Compaction factors common terms and splits products, so a condition such as
`√u * x² + √u * y² ≠ 0` reaches the caller as `√u ≠ 0` and `x² + y² ≠ 0`, which the
side-condition tactic proves from a positivity hypothesis on the radicand.
-/
theorem eval_eq_of_summandRun_compact {ι : Type*} [DecidableEq ι]
    (summands : List (Verified.Expr ι)) (stated : Verified.Expr ι) (ρ : ι → ℝ)
    (side : List (Verified.Expr ι))
    (hrun : (summandRun summands stated).expr = .nat 0 ∧
      essentialSide (compactNonzero (summandRun summands stated).nonzero) = side)
    (hside : Alg.SideHolds ρ side) :
    (Verified.Expr.addList summands).eval ρ = stated.eval ρ := by
  obtain ⟨hzero, rfl⟩ := hrun
  exact eval_eq_of_summandRun_essential summands stated ρ _ ⟨hzero, rfl⟩ fun d hd ↦
    sideHolds_of_compactNonzero (sideHolds_of_essentialSide hside) d (List.mem_of_mem_filter hd)

/--
The certification statement of the summand route with a shared radicand abstracted and compacted
conditions (`abstractedSummandRun`): wherever the environment sends the abstraction variable `u`
to the value of the radicand and the essential conditions of the compacted recorded list hold, the
sum evaluates to the stated value.
-/
theorem eval_eq_of_abstractedSummandRun_compact {ι : Type*} [DecidableEq ι]
    (summands : List (Verified.Expr ι)) (stated pattern : Verified.Expr ι) (u : ι)
    (ρ : ι → ℝ) (side : List (Verified.Expr ι))
    (hrun : (abstractedSummandRun summands stated pattern u).expr = .nat 0 ∧
      essentialSide (compactNonzero (abstractedSummandRun summands stated pattern u).nonzero) =
        side)
    (hu : ρ u = pattern.eval ρ) (hside : Alg.SideHolds ρ side) :
    (Verified.Expr.addList summands).eval ρ = stated.eval ρ := by
  obtain ⟨hzero, rfl⟩ := hrun
  exact eval_eq_of_abstractedSummandRun_essential summands stated pattern u ρ _ ⟨hzero, rfl⟩ hu
    fun d hd ↦ sideHolds_of_compactNonzero (sideHolds_of_essentialSide hside) d
      (List.mem_of_mem_filter hd)

end CAS.Verified.Expr

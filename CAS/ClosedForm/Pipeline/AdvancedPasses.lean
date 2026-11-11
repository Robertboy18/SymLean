/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.BottomUp
public import CAS.ClosedForm.Pipeline.Passes.Factorization

/-!
# Square-root pairing, factor reconstruction, and deep cancellation passes

Three side passes that work on what the rational and fraction normal forms leave behind:
pairing of separated square-root factors in a product, extraction of a factor common to all
summands of a sum, and cancellation of denominator factors that also occur in the numerator. In
`configuredSidePipeline` the first two run among the side passes after the base normalizer, and
deep cancellation runs both before and after it.

## Main definitions

* `sqrtProductCollectFactors`, `sqrtProductCollectDeepCleanup`, `sqrtProductCollectSidePass`:
  pair two identical factors `sqrt a` that are separated inside a long product and replace them
  by `a`, recording the obligation `sqrt a ≠ 0`, which is `0 < a` for Mathlib's `Real.sqrt`.
* `commonAddFactorSidePass`: the unconditional common-factor extraction `factorCommonAddDeep`,
  which is also the rewrite of the base pass `factor-common`, as a side pass. It emits no
  obligations.
* `deepFactorCancelCleanup`, `deepFactorCancelSidePass`: in a quotient `num / den`, cancel
  every factor of the product tree `den` that also occurs in the product tree `num`, recording
  each cancelled factor as a nonzero obligation. `Alg.sideFactors` reduces a cancelled power to
  its base and drops a nonzero natural or integer literal. The identity
  `(f * n) / (f * d) = n / d` is false for totalized division when `f = 0`, which is why the
  obligation is needed.

## Implementation notes

`sqrtProductCollectDeepCleanup` is `BottomUp.run` applied to the top-level collector, so its
soundness follows from `BottomUp.eval_run` once two facts about the top-level step are known: it
preserves inherited obligations, and it preserves evaluation under its own obligations. At a
product node the collector takes the first factor `sqrt a` that has a partner later in the
product, removes the partner with `cancelOneFactor?` and puts `a` in place of the pair. One
traversal therefore makes at most one pairing per product node, and the iteration of the side
passes repeats it. The proof divides by `sqrt a` (`eval_cancelOneFactor?`) before it applies
`Real.mul_self_sqrt`, so it needs `sqrt a ≠ 0`, more than the `0 ≤ a` of the identity
`sqrt a * sqrt a = a` itself.

`deepFactorCancelCleanup` is deep in a different sense. It fires only on a top-level quotient,
but searches the entire product trees of numerator and denominator for matching factors. Among
the side passes after the base normalizer, `commonAddFactorSidePass` runs directly before it, so
a factor that it pulls out of a sum can be cancelled in the same round.
-/

@[expose] public section

namespace CAS.Verified.Expr

/-- Pair identical square-root factors inside a flattened product.

The `sqrt-square` pass catches syntactically adjacent patterns such as
`sqrt(a) * sqrt(a)` and `(sqrt(a))^2`.  Fraction-normalized PDE residuals often produce long
product chains where matching square-root factors are separated by many ordinary factors.  This
collector searches the remaining product for a matching `sqrt(a)`, replaces the pair by `a`, and
emits the side condition `sqrt(a) ≠ 0`.

It performs one pairing per call; the fixed-point side pipeline repeats it. -/
def sqrtProductCollectFactors {ι : Type*} [DecidableEq ι] :
    List (Verified.Expr ι) → Alg.NormResult ι
  | [] => { expr := .nat 1, nonzero := [] }
  | factor :: rest =>
      match factor with
      | .sqrt a =>
          match cancelOneFactor? (.sqrt a) (mkMulList rest) with
          | some restExpr =>
              { expr := mkMul a restExpr, nonzero := [.sqrt a] }
          | none =>
              let tail := sqrtProductCollectFactors rest
              { expr := mkMul factor tail.expr, nonzero := tail.nonzero }
      | _ =>
          let tail := sqrtProductCollectFactors rest
          { expr := mkMul factor tail.expr, nonzero := tail.nonzero }

/-- Soundness of the flattened product square-root collector. -/
theorem eval_sqrtProductCollectFactors {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) :
    ∀ factors : List (Verified.Expr ι),
      Alg.SideHolds ρ (sqrtProductCollectFactors factors).nonzero →
        (sqrtProductCollectFactors factors).expr.eval ρ = (mkMulList factors).eval ρ
  | [], _ => by
      simp [sqrtProductCollectFactors, mkMulList]
  | factor :: rest, hside => by
      cases factor with
      | sqrt a =>
          simp only [sqrtProductCollectFactors] at hside ⊢
          cases hcancel : cancelOneFactor? (Verified.Expr.sqrt a) (mkMulList rest) with
          | some restExpr =>
              simp only [hcancel] at hside
              have hsqrt : Real.sqrt (a.eval ρ) ≠ 0 := hside.of_singleton
              simp only [eval_mkMul, eval_cancelOneFactor? ρ _ _ restExpr hcancel hsqrt, mkMulList,
                Verified.Expr.eval]
              nth_rw 1 [← Real.mul_self_sqrt (Real.sqrt_ne_zero'.1 hsqrt).le]
              rw [mul_assoc, mul_div_cancel₀ _ hsqrt]
          | none =>
              simp only [hcancel] at hside
              simp [mkMulList, eval_mkMul, eval_sqrtProductCollectFactors ρ rest hside]
      | _ =>
          simp only [sqrtProductCollectFactors] at hside ⊢
          simp [mkMulList, eval_mkMul, eval_sqrtProductCollectFactors ρ rest hside]

/-- Apply the top-level square-root product collector after recursively rebuilding an expression. -/
def sqrtProductCollectTopAfter {ι : Type*} [DecidableEq ι]
    (rebuilt : Verified.Expr ι) (inherited : List (Verified.Expr ι)) : Alg.NormResult ι :=
  match rebuilt with
  | .mul a b =>
      let top := sqrtProductCollectFactors (productFactors (.mul a b))
      { expr := top.expr, nonzero := Alg.cleanSide (inherited ++ top.nonzero) }
  | expr => { expr := expr, nonzero := Alg.cleanSide inherited }

/-- The inherited side conditions are available from a `sqrtProductCollectTopAfter` result. -/
theorem sideHolds_inherited_of_sqrtProductCollectTopAfter {ι : Type*} [DecidableEq ι]
    {ρ : ι → ℝ} (rebuilt : Verified.Expr ι) (inherited : List (Verified.Expr ι))
    (hside : Alg.SideHolds ρ (sqrtProductCollectTopAfter rebuilt inherited).nonzero) :
    Alg.SideHolds ρ inherited := by
  cases rebuilt
  case mul => exact (Alg.sideHolds_of_cleanSide hside).append_left
  all_goals exact Alg.sideHolds_of_cleanSide hside

/-- Soundness of applying the top-level square-root product collector after recursive rebuilding. -/
theorem eval_sqrtProductCollectTopAfter {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (rebuilt : Verified.Expr ι) (inherited : List (Verified.Expr ι))
    (hside : Alg.SideHolds ρ (sqrtProductCollectTopAfter rebuilt inherited).nonzero) :
    (sqrtProductCollectTopAfter rebuilt inherited).expr.eval ρ = rebuilt.eval ρ := by
  cases rebuilt
  case mul a b =>
    rw [← eval_mkMulList_productFactors ρ (.mul a b)]
    exact eval_sqrtProductCollectFactors ρ _ (Alg.sideHolds_of_cleanSide hside).append_right
  all_goals rfl

/-- Recursive square-root product collector.

This is the deep version used by the side pipeline.  It first recursively rewrites children, then
looks at the rebuilt node as a product tree and pairs one separated pair of identical square roots.
The fixed-point side pipeline repeats this pass. -/
def sqrtProductCollectDeepCleanup {ι : Type*} [DecidableEq ι] :
    Verified.Expr ι → Alg.NormResult ι :=
  BottomUp.run sqrtProductCollectTopAfter

/-- Soundness of recursive square-root product collection. -/
theorem eval_sqrtProductCollectDeepCleanup {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) :
    ∀ (expr : Verified.Expr ι),
      Alg.SideHolds ρ (sqrtProductCollectDeepCleanup expr).nonzero →
        (sqrtProductCollectDeepCleanup expr).expr.eval ρ = expr.eval ρ := by
  simpa [sqrtProductCollectDeepCleanup] using
    BottomUp.eval_run sqrtProductCollectTopAfter
      sideHolds_inherited_of_sqrtProductCollectTopAfter
      eval_sqrtProductCollectTopAfter ρ

/-- Side pass for collecting separated identical square-root product factors. -/
def sqrtProductCollectSidePass {ι : Type*} [DecidableEq ι] : SidePass ι where
  name := "sqrt-product-collect"
  run := sqrtProductCollectDeepCleanup
  sound := by
    intro ρ expr hside
    exact eval_sqrtProductCollectDeepCleanup ρ expr hside

/-- Side pass for generic additive common-factor reconstruction. -/
def commonAddFactorSidePass {ι : Type*} [DecidableEq ι] : SidePass ι where
  name := "common-add-factor"
  run := fun expr ↦ { expr := factorCommonAddDeep expr, nonzero := [] }
  sound := by
    intro ρ expr hside
    exact eval_factorCommonAddDeep ρ expr

/-- Outcome of cancelling a list of denominator factors against a numerator product tree, as
produced by `cancelDenominatorFactors`. -/
structure PartialFactorCancelResult (ι : Type*) where
  /-- The numerator after every available denominator-factor cancellation. -/
  numerator : Verified.Expr ι
  /-- The denominator factors that could not be canceled. -/
  denominatorFactors : List (Verified.Expr ι)
  /-- Nonzero obligations for the factors removed from the quotient. -/
  nonzero : List (Verified.Expr ι)
  /-- Whether at least one denominator factor was canceled. -/
  changed : Bool

/-- Cancel every denominator factor that can be found in the numerator product tree.

Unmatched denominator factors are kept in `denominatorFactors`.  Canceled factors are emitted as
nonzero side conditions; unmatched denominator factors do not need side conditions because they are
not being removed from the quotient.
-/
def cancelDenominatorFactors {ι : Type*} [DecidableEq ι] :
    Verified.Expr ι → List (Verified.Expr ι) → PartialFactorCancelResult ι
  | num, [] =>
      { numerator := num, denominatorFactors := [], nonzero := [], changed := false }
  | num, factor :: rest =>
      match cancelOneFactor? factor num with
      | some num' =>
          let next := cancelDenominatorFactors num' rest
          { numerator := next.numerator
            denominatorFactors := next.denominatorFactors
            nonzero := Alg.sideFactors factor ++ next.nonzero
            changed := true }
      | none =>
          let next := cancelDenominatorFactors num rest
          { numerator := next.numerator
            denominatorFactors := factor :: next.denominatorFactors
            nonzero := next.nonzero
            changed := next.changed }

private theorem eval_cancelDenominatorFactors {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (num : Verified.Expr ι) (factors : List (Verified.Expr ι))
    (hside : Alg.SideHolds ρ (cancelDenominatorFactors num factors).nonzero) :
    (cancelDenominatorFactors num factors).numerator.eval ρ /
        (mkMulList (cancelDenominatorFactors num factors).denominatorFactors).eval ρ =
      num.eval ρ / (mkMulList factors).eval ρ := by
  induction factors generalizing num with
  | nil => simp [cancelDenominatorFactors, mkMulList]
  | cons factor rest ih =>
      simp only [cancelDenominatorFactors] at hside ⊢
      cases hcancel : cancelOneFactor? factor num with
      | some num' =>
          simp only [hcancel] at hside ⊢
          rw [ih num' hside.append_right, eval_cancelOneFactor? ρ factor num num' hcancel
            (Alg.eval_ne_zero_of_sideFactors ρ factor hside.append_left)]
          simp only [mkMulList, eval_mkMul, div_div]
      | none =>
          simp only [hcancel] at hside ⊢
          simp only [mkMulList, eval_mkMul, div_mul_eq_div_div_swap, ih num hside]

/-- Cancel a factored denominator whenever at least one denominator factor appears in the
numerator tree. -/
def deepFactorCancelCleanup {ι : Type*} [DecidableEq ι] :
    Verified.Expr ι → Alg.NormResult ι
  | .div num den =>
      let out := cancelDenominatorFactors num (productFactors den)
      if out.changed then
        { expr := mkDiv out.numerator (mkMulList out.denominatorFactors),
          nonzero := Alg.cleanSide out.nonzero }
      else
        { expr := .div num den, nonzero := [] }
  | expr => { expr := expr, nonzero := [] }

/-- Soundness of deep product-tree factor cancellation. -/
theorem eval_deepFactorCancelCleanup {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι)
    (hside : Alg.SideHolds ρ (deepFactorCancelCleanup expr).nonzero) :
    (deepFactorCancelCleanup expr).expr.eval ρ = expr.eval ρ := by
  cases expr with
  | div num den =>
      simp only [deepFactorCancelCleanup] at hside ⊢
      split_ifs at hside ⊢
      · rw [eval_mkDiv, eval_cancelDenominatorFactors ρ num _ (Alg.sideHolds_of_cleanSide hside),
          eval_mkMulList_productFactors]
        rfl
      · rfl
  | _ => rfl

/-- Side pass for deep product-tree factor cancellation. -/
def deepFactorCancelSidePass {ι : Type*} [DecidableEq ι] : SidePass ι where
  name := "deep-factor-cancel"
  run := deepFactorCancelCleanup
  sound := by
    intro ρ expr hside
    exact eval_deepFactorCancelCleanup ρ expr hside


end CAS.Verified.Expr

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.BottomUp
public import CAS.ClosedForm.Pipeline.Passes.NumericLiteral

/-!
# Side-aware normalization passes

Side passes for rational expressions, exact numeric ratios, and squares of square roots. Each
rewrite either preserves evaluation unconditionally or records the nonzero assumptions its
soundness proof needs. The two rational normalizers of `Expression.Rational` are wrapped as side
passes, together with two small cleanups of what the rational normal form leaves behind.

## Main definitions

* `rationalSidePass`: `Alg.normalizeWithSide`, which cross-multiplies sums of syntactic
  quotients and records the denominators.
* `fractionSidePass`: `Alg.normalizeFractionWithSide`, the single-fraction normal form used for
  residuals with mixed plain and fractional terms (heat kernels, Green's functions, and other
  exponential-over-polynomial ansatzes).
* `unitRatioCleanup`, `unitRatioSidePass`: fold a quotient of two numeric literals with nonzero
  denominator into one rational constant, at the root of the expression only. No obligation is
  emitted because the denominator is checked to be a nonzero literal; symbolic `x / x` is left
  alone.
* `sqrtSquareCleanup`, `sqrtSquareDeepCleanup`, `sqrtSquareSidePass`: rewrite `(sqrt a)^2` and
  `sqrt a * sqrt a` to `a`, emitting `sqrt a ≠ 0`.

## Implementation notes

We record the obligation of the square-root rewrite as `sqrt a ≠ 0` because the
`NormResult.nonzero` list holds nonzero facts only. For Mathlib's `Real.sqrt` this says `0 < a`
(`Real.sqrt_ne_zero'`), slightly more than the `0 ≤ a` that `Real.sq_sqrt` and
`Real.mul_self_sqrt` need, and the command output prints the entry as `a > 0`. The cleanup
matches its two patterns syntactically, with both square roots as the two factors of one product
node; a pair separated by other factors is left to `sqrtProductCollectSidePass`.
-/

@[expose] public section

namespace CAS.Verified.Expr

/-- The conservative side-aware rational normalizer `Alg.normalizeWithSide` as a side pass: it
cross-multiplies sums of syntactic quotients and records their denominators. -/
def rationalSidePass {ι : Type*} [DecidableEq ι] : SidePass ι where
  name := "rational-side"
  run := Alg.normalizeWithSide
  sound := by
    intro ρ expr hside
    exact Alg.eval_normalizeWithSide ρ expr hside

/-- Side-condition-aware pass that compiles an expression to one fraction.

This route is stronger than `rational-side` on residuals with mixed plain/fractional terms or
nested quotients.  It is the normal form needed by heat kernels, Green functions, and
other closed-form PDE ansatzes with exponential factors over polynomial denominators.
-/
def fractionSidePass {ι : Type*} [DecidableEq ι] : SidePass ι where
  name := "fraction-normal-form"
  run := Alg.normalizeFractionWithSide
  sound := by
    intro ρ expr hside
    exact Alg.eval_normalizeFractionWithSide ρ expr hside

/-- Side-pass cleanup for exact nonzero numeric ratios such as `2/2`, `2/4`, and `(-6)/3`.

This does not rewrite symbolic `x/x`: Lean's total division has `0/0 = 0`, so that
rewrite would need a nonzero side condition.  The pass only handles syntactically numeric,
provably nonzero denominators and emits no new obligations. -/
def unitRatioCleanup {ι : Type*} : Verified.Expr ι → Alg.NormResult ι
  | .div a b =>
      match NumericLiteral.parse? a, NumericLiteral.parse? b with
      | some qa, some qb =>
          if qb = 0 then
            { expr := .div a b, nonzero := [] }
          else
            { expr := mkRatConst (qa / qb), nonzero := [] }
      | _, _ => { expr := .div a b, nonzero := [] }
  | expr => { expr := expr, nonzero := [] }

/-- Soundness of `unitRatioCleanup`. -/
theorem eval_unitRatioCleanup {ι : Type*} (ρ : ι → ℝ) (expr : Verified.Expr ι) :
    (unitRatioCleanup expr).expr.eval ρ = expr.eval ρ := by
  cases expr with
  | div a b =>
      simp only [unitRatioCleanup]
      split
      · rename_i qa qb ha hb
        split_ifs
        · rfl
        · simp [NumericLiteral.eval_parse?_eq_some ρ a qa ha,
            NumericLiteral.eval_parse?_eq_some ρ b qb hb]
      · rfl
  | _ => rfl

/-- Side-condition pass for exact nonzero numeric unit ratios. -/
def unitRatioSidePass {ι : Type*} : SidePass ι where
  name := "unit-ratio"
  run := unitRatioCleanup
  sound := by
    intro ρ expr _hside
    exact eval_unitRatioCleanup ρ expr

/-- Side-conditioned square-root square cleanup.

`(sqrt a)^2` and `sqrt a * sqrt a` are rewritten to `a`, while emitting `sqrt a ≠ 0` as a
side condition.  That side condition implies `0 < a`, hence the usual real identity
`(sqrt a)^2 = a` applies. -/
def sqrtSquareCleanup {ι : Type*} [DecidableEq ι] :
    Verified.Expr ι → Alg.NormResult ι
  | .pow (Verified.Expr.sqrt a) 2 =>
      { expr := a, nonzero := [.sqrt a] }
  | .mul (Verified.Expr.sqrt a) (.sqrt b) =>
      if a = b then
        { expr := a, nonzero := [.sqrt a] }
      else
        { expr := .mul (Verified.Expr.sqrt a) (.sqrt b), nonzero := [] }
  | expr => { expr := expr, nonzero := [] }

/-- Soundness of side-conditioned square-root square cleanup. -/
theorem eval_sqrtSquareCleanup {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι)
    (hside : Alg.SideHolds ρ (sqrtSquareCleanup expr).nonzero) :
    (sqrtSquareCleanup expr).expr.eval ρ = expr.eval ρ := by
  cases expr with
  | pow base k =>
      cases base with
      | sqrt a =>
          rcases k with _ | _ | _ | k
          · rfl
          · rfl
          · simp [sqrtSquareCleanup, Real.sq_sqrt (Real.sqrt_ne_zero'.1 hside.of_singleton).le]
          · rfl
      | _ => rfl
  | mul left right =>
      cases left with
      | sqrt a =>
          cases right with
          | sqrt b =>
              simp only [sqrtSquareCleanup] at hside ⊢
              split_ifs at hside ⊢ with h
              · subst h
                simp [Real.mul_self_sqrt (Real.sqrt_ne_zero'.1 hside.of_singleton).le]
              · rfl
          | _ => rfl
      | _ => rfl
  | _ => rfl

/-- Apply the top-level square-root cleanup after recursively rebuilding an expression.

The `inherited` side conditions come from recursive subterms; any new side conditions come from
the top-level `sqrtSquareCleanup` check. -/
def sqrtSquareTopAfter {ι : Type*} [DecidableEq ι]
    (rebuilt : Verified.Expr ι) (inherited : List (Verified.Expr ι)) : Alg.NormResult ι :=
  let top := sqrtSquareCleanup rebuilt
  { expr := top.expr, nonzero := Alg.cleanSide (inherited ++ top.nonzero) }

/-- The inherited side conditions are available from a `sqrtSquareTopAfter` result. -/
theorem sideHolds_inherited_of_sqrtSquareTopAfter {ι : Type*} [DecidableEq ι]
    {ρ : ι → ℝ} (rebuilt : Verified.Expr ι) (inherited : List (Verified.Expr ι))
    (hside : Alg.SideHolds ρ (sqrtSquareTopAfter rebuilt inherited).nonzero) :
    Alg.SideHolds ρ inherited :=
  (Alg.sideHolds_of_cleanSide hside).append_left

/-- Soundness of applying the top-level square-root cleanup after recursive rebuilding. -/
theorem eval_sqrtSquareTopAfter {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (rebuilt : Verified.Expr ι) (inherited : List (Verified.Expr ι))
    (hside : Alg.SideHolds ρ (sqrtSquareTopAfter rebuilt inherited).nonzero) :
    (sqrtSquareTopAfter rebuilt inherited).expr.eval ρ = rebuilt.eval ρ :=
  eval_sqrtSquareCleanup ρ rebuilt (Alg.sideHolds_of_cleanSide hside).append_right

/-- Recursive square-root square cleanup.

This walks the whole expression tree, rewrites square-root squares at every rebuilt node, and
accumulates all side conditions needed by the recursive subroutes and the local top-level route. -/
def sqrtSquareDeepCleanup {ι : Type*} [DecidableEq ι] :
    Verified.Expr ι → Alg.NormResult ι :=
  BottomUp.run sqrtSquareTopAfter

/-- Soundness of recursive square-root square cleanup. -/
theorem eval_sqrtSquareDeepCleanup {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) :
    ∀ (expr : Verified.Expr ι),
      Alg.SideHolds ρ (sqrtSquareDeepCleanup expr).nonzero →
        (sqrtSquareDeepCleanup expr).expr.eval ρ = expr.eval ρ := by
  simpa [sqrtSquareDeepCleanup] using
    BottomUp.eval_run sqrtSquareTopAfter
      sideHolds_inherited_of_sqrtSquareTopAfter eval_sqrtSquareTopAfter ρ

/-- Side pass for the checked square-root square cleanup. -/
def sqrtSquareSidePass {ι : Type*} [DecidableEq ι] : SidePass ι where
  name := "sqrt-square"
  run := sqrtSquareDeepCleanup
  sound := by
    intro ρ expr hside
    exact eval_sqrtSquareDeepCleanup ρ expr hside


end CAS.Verified.Expr

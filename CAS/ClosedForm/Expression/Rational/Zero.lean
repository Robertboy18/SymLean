/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Expression.Rational

/-!
# Checked symbolic zero tests

`Alg.zeroCheck` runs the single-fraction normalizer `normalizeFractionWithSide` as a zero test. Its
`NormResult` holds the normal form being tested in `expr` and the denominator conditions that
were assumed in `nonzero`. The theorems turn a normal form that is literally `0` into a statement
about real-valued evaluation; `ZeroCheck.eval_eq_of_zeroCheck_sub_eq_zero` is the second attempt
of the exact equality tactic `symbolic_eq`, after the unconditional normalizer.

## Main definitions

* `zeroCheck`: run `normalizeFractionWithSide` on an expression.
* `ZeroCheck.succeeds`: the Boolean test "normal form is literally `0` and no denominator
  conditions remain", decided by `decide` so that it reflects into a propositional equality.

## Main results

* `ZeroCheck.eval_eq_zero_of_expr_eq_zero`: a normal form that is literally `0` proves
  `expr.eval ρ = 0` at valuations where the emitted denominators are nonzero.
* `ZeroCheck.eval_eq_of_zeroCheck_sub_eq_zero`: the equality form used by the exact equality
  tactics, which run the fraction normal form on `lhs - rhs`.

## Implementation notes

Because `Verified.Expr.eval` uses totalized real division, an expression whose normal form is
`0` only after clearing a denominator `d` is zero at valuations with `d ≠ 0`; the `nonzero`
list records exactly these obligations, and `succeeds` demands that the list be empty. The
tactics compute the normal form with `decide +kernel` and leave the obligations to
`symbolic_assumptions`; the proof is `eval_normalizeFractionWithSide`. The test is sound but not
complete: inside the arguments of the elementary functions the fraction normal form neither
cancels common factors nor sorts terms, so `sqrt ((x^4 - y^4) / (x^2 - y^2))` and
`sqrt (x^2 + y^2)` stay distinct atoms, as do two atoms that differ only in the order of a sum.
`symbolic_eq` then tries `Alg.canonicalForm`.
-/

@[expose] public section

namespace CAS.Verified.Expr.Alg

/-- Normalize an expression and collect the denominator conditions needed for the result. -/
def zeroCheck {ι : Type*} [DecidableEq ι] (expr : Verified.Expr ι) : NormResult ι :=
  normalizeFractionWithSide expr

namespace ZeroCheck

/-- Decide whether normalization produced zero without any remaining denominator conditions.

This uses propositional equality through `decide`, rather than the expression datatype's
computational `BEq`, so a true result can be reflected back into a Lean equality. -/
def succeeds {ι : Type*} [DecidableEq ι] (check : NormResult ι) : Bool :=
  decide (check.expr = 0) && check.nonzero.isEmpty

/-- The normal form produced by `zeroCheck` evaluates to the same real number as the input,
at every valuation where the collected denominators are nonzero. -/
theorem eval_expr_eq {ι : Type*} [DecidableEq ι]
    (ρ : ι → ℝ) (expr : Verified.Expr ι)
    (hside : SideHolds ρ (zeroCheck expr).nonzero) :
    (zeroCheck expr).expr.eval ρ = expr.eval ρ :=
  eval_normalizeFractionWithSide ρ expr hside

/-- If the normal form is literally `0`, the input evaluates to `0` wherever the denominator
conditions hold. -/
theorem eval_eq_zero_of_expr_eq_zero {ι : Type*} [DecidableEq ι]
    (ρ : ι → ℝ) (expr : Verified.Expr ι)
    (hside : SideHolds ρ (zeroCheck expr).nonzero)
    (hzero : (zeroCheck expr).expr = 0) :
    expr.eval ρ = 0 := by
  rw [← eval_expr_eq ρ expr hside, hzero]
  simp

/-- If the fraction normal form of `lhs - rhs` is literally `0`, the two expressions evaluate
equally wherever the collected denominator conditions hold. This is the zero test behind the
exact equality tactics. For `lhs = x / x` and `rhs = 1`, for example, `fractionResult`
cross-multiplies the residual `x / x - 1` over the denominator `x`, so its fraction normal form
is `0` under the collected condition `x ≠ 0`. -/
theorem eval_eq_of_zeroCheck_sub_eq_zero {ι : Type*} [DecidableEq ι]
    (ρ : ι → ℝ) (lhs rhs : Verified.Expr ι)
    (hside : SideHolds ρ (zeroCheck (lhs - rhs)).nonzero)
    (hzero : (zeroCheck (lhs - rhs)).expr = 0) :
    lhs.eval ρ = rhs.eval ρ :=
  sub_eq_zero.mp (eval_eq_zero_of_expr_eq_zero ρ (lhs - rhs) hside hzero)

/-- An empty list of denominator conditions holds vacuously at every valuation. -/
theorem sideHolds_of_nonzero_eq_nil {ι : Type*}
    (check : NormResult ι) (ρ : ι → ℝ)
    (h : check.nonzero = []) :
    SideHolds ρ check.nonzero := fun d hd ↦ by
  simp [h] at hd

end ZeroCheck
end CAS.Verified.Expr.Alg

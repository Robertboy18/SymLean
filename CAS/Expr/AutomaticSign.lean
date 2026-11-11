/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Syntax

/-!
# Structural sign facts for checked expressions

The executable checks `nonnegative`, `positive`, and `nonzero` recognize, from the shape of an
expression alone, a small fragment of expressions whose sign does not depend on the variable
environment. Their soundness theorems are `eval_nonneg_of_nonnegative_eq_true`,
`eval_pos_of_positive_eq_true`, and `eval_ne_zero_of_nonzero_eq_true`. They remove side
conditions that hold automatically from reports and from certificate planning. A result of
`false` means only that this structural check did not prove the fact.

## Implementation notes

We decide each fact by structural recursion, without search: the answer at a node comes from
the answers at its children and from a few base facts. Literals are decided by their sign;
`π`, `e` and exponentials are positive; square roots, squares `a ^ 2` and products `a * a` are
nonnegative. A sum is positive when one summand is positive and the other nonnegative, and
`nonzero` defers to `positive` at literals, `π`, `e`, sums, exponentials and square roots.
Variables, subtractions, logarithms and the trigonometric and inverse trigonometric functions
always give `false`. Each soundness theorem is an induction on the expression with one Mathlib
lemma per node, such as `mul_self_nonneg`, `Real.sqrt_pos` and `Real.rpow_pos_of_pos`.
-/

@[expose] public section

namespace CAS.Verified.Expr.AutomaticSign

/-- Whether the structural checker proves that an expression is nonnegative. -/
def nonnegative {ι : Type*} [DecidableEq ι] : Verified.Expr ι → Bool
  | .nat _ => true
  | .int value => decide (0 ≤ value)
  | .rat numerator _ => decide (0 ≤ numerator)
  | .pi | .e | .exp _ | .sqrt _ => true
  | .add left right => nonnegative left && nonnegative right
  | .mul left right =>
      if left = right then true else nonnegative left && nonnegative right
  | .pow _ 0 | .pow _ 2 => true
  | .rpow base _ => nonnegative base
  | _ => false

/-- Whether the structural checker proves that an expression is positive. -/
def positive {ι : Type*} [DecidableEq ι] : Verified.Expr ι → Bool
  | .nat value => value != 0
  | .int value => decide (0 < value)
  | .rat numerator denominator => decide (0 < numerator) && denominator != 0
  | .pi | .e | .exp _ => true
  | .add left right =>
      (positive left && nonnegative right) || (nonnegative left && positive right)
  | .mul left right => positive left && positive right
  | .div left right => positive left && positive right
  | .pow _ 0 => true
  | .pow argument (_ + 1) => positive argument
  | .sqrt argument => positive argument
  | .rpow base _ => positive base
  | _ => false

/-- Whether the structural checker proves that an expression is nonzero. -/
def nonzero {ι : Type*} [DecidableEq ι] : Verified.Expr ι → Bool
  | expression@(.nat _) | expression@(.int _) | expression@(.rat _ _) |
      expression@(.pi) | expression@(.e) | expression@(.add _ _) |
      expression@(.exp _) | expression@(.sqrt _) =>
      positive expression
  | .neg argument => nonzero argument
  | .mul left right => nonzero left && nonzero right
  | .div left right => nonzero left && nonzero right
  | .pow _ 0 => true
  | .pow argument (_ + 1) => nonzero argument
  | .rpow base _ => positive base
  | _ => false

/-- A successful structural nonnegativity check is semantically sound. -/
theorem eval_nonneg_of_nonnegative_eq_true {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expression : Verified.Expr ι) (h : nonnegative expression = true) :
    0 ≤ expression.eval ρ := by
  induction expression with
  | var | sub | div | neg | sin | cos | atan | asin | acos | log => simp [nonnegative] at h
  | nat value => exact Nat.cast_nonneg value
  | int value => exact Int.cast_nonneg (by simpa [nonnegative] using h)
  | rat numerator denominator =>
    simp only [nonnegative, decide_eq_true_eq] at h
    exact div_nonneg (Int.cast_nonneg h) (Nat.cast_nonneg _)
  | pi => exact Real.pi_pos.le
  | e => exact (Real.exp_pos 1).le
  | exp => exact (Real.exp_pos _).le
  | sqrt => exact Real.sqrt_nonneg _
  | add left right ihLeft ihRight =>
    simp only [nonnegative, Bool.and_eq_true] at h
    exact add_nonneg (ihLeft h.1) (ihRight h.2)
  | mul left right ihLeft ihRight =>
    simp only [nonnegative] at h
    split at h
    · subst right
      exact mul_self_nonneg (left.eval ρ)
    · simp only [Bool.and_eq_true] at h
      exact mul_nonneg (ihLeft h.1) (ihRight h.2)
  | pow argument exponent ih =>
    rcases exponent with _ | _ | _ | exponent
    · simp
    · simp [nonnegative] at h
    · exact sq_nonneg (argument.eval ρ)
    · simp [nonnegative] at h
  | rpow base exponent ihBase ihExponent =>
    exact Real.rpow_nonneg (ihBase (by simpa [nonnegative] using h)) _

/-- A successful structural positivity check is semantically sound. -/
theorem eval_pos_of_positive_eq_true {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expression : Verified.Expr ι) (h : positive expression = true) :
    0 < expression.eval ρ := by
  induction expression with
  | var | sub | neg | sin | cos | atan | asin | acos | log => simp [positive] at h
  | nat value => exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by simpa [positive] using h))
  | int value => exact Int.cast_pos.mpr (by simpa [positive] using h)
  | rat numerator denominator =>
    simp only [positive, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at h
    exact div_pos (Int.cast_pos.mpr h.1) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h.2))
  | pi => exact Real.pi_pos
  | e => exact Real.exp_pos 1
  | exp => exact Real.exp_pos _
  | add left right ihLeft ihRight =>
    simp only [positive, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | h
    · exact add_pos_of_pos_of_nonneg (ihLeft h.1) (eval_nonneg_of_nonnegative_eq_true ρ right h.2)
    · exact add_pos_of_nonneg_of_pos (eval_nonneg_of_nonnegative_eq_true ρ left h.1) (ihRight h.2)
  | mul left right ihLeft ihRight =>
    simp only [positive, Bool.and_eq_true] at h
    exact mul_pos (ihLeft h.1) (ihRight h.2)
  | div left right ihLeft ihRight =>
    simp only [positive, Bool.and_eq_true] at h
    exact div_pos (ihLeft h.1) (ihRight h.2)
  | pow argument exponent ih =>
    rcases exponent with _ | exponent
    · simp
    · exact pow_pos (ih h) _
  | sqrt argument ih => exact Real.sqrt_pos.2 (ih h)
  | rpow base exponent ihBase ihExponent =>
    exact Real.rpow_pos_of_pos (ihBase (by simpa [positive] using h)) _

/-- A successful structural nonzero check is semantically sound. -/
theorem eval_ne_zero_of_nonzero_eq_true {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expression : Verified.Expr ι) (h : nonzero expression = true) :
    expression.eval ρ ≠ 0 := by
  induction expression with
  | nat | int | rat | pi | e | add | exp | sqrt => exact (eval_pos_of_positive_eq_true ρ _ h).ne'
  | var | sub | sin | cos | atan | asin | acos | log => simp [nonzero] at h
  | mul left right ihLeft ihRight =>
    simp only [nonzero, Bool.and_eq_true] at h
    exact mul_ne_zero (ihLeft h.1) (ihRight h.2)
  | div left right ihLeft ihRight =>
    simp only [nonzero, Bool.and_eq_true] at h
    exact div_ne_zero (ihLeft h.1) (ihRight h.2)
  | neg argument ih => exact neg_ne_zero.mpr (ih h)
  | pow argument exponent ih =>
    rcases exponent with _ | exponent
    · simp
    · exact pow_ne_zero _ (ih h)
  | rpow base exponent ihBase ihExponent =>
    exact (Real.rpow_pos_of_pos (eval_pos_of_positive_eq_true ρ base (by simpa [nonzero] using h))
      _).ne'

end CAS.Verified.Expr.AutomaticSign

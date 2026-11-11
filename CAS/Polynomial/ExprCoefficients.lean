/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Syntax
public import CAS.Polynomial.CoefficientList

/-!
# Coefficient lists of expressions in one variable

`Verified.Expr.coeffs` reads the coefficient list, lowest degree first, of an expression built
from numerals, the variable, `+`, `-`, `*`, natural powers and division by a constant, and
`Verified.Expr.isPoly` says whether an expression is of this form; then its value is that of the
list (`eval_eq_coeffEval_coeffs`). Both are computable, so the kernel evaluates them.

`telescopes F f` checks, with the numerators and denominators of `F` and `f` read this way, the
identity `F (x) + f (x + 1) = F (x + 1)` with the denominators cleared, and
`eval_add_eval_eq_of_telescopes` gives the identity wherever the three denominators are nonzero.
It is the induction step of a closed form `F` of `∑ f`, as in `#cas [sum k a n]`: proved this
way, the step of a closed form of degree `d` costs the kernel some products of coefficient lists
of length `d`, where `ring` would build a proof term for each product of two monomials.
-/

@[expose] public section

namespace CAS.Verified.Expr

open CAS.Polynomial

/-- The coefficient list, lowest degree first, of an expression in one variable built from
numerals, the variable, `+`, `-`, `*`, natural powers and division by a constant. It is only
meaningful where `isPoly` holds. -/
def coeffs : Expr (Fin 1) → List ℚ
  | .nat n => [(n : ℚ)]
  | .int n => [(n : ℚ)]
  | .rat p q => [(p : ℚ) / q]
  | .var _ => [0, 1]
  | .add a b => coeffAdd a.coeffs b.coeffs
  | .sub a b => coeffAdd a.coeffs (coeffScale (-1) b.coeffs)
  | .neg a => coeffScale (-1) a.coeffs
  | .mul a b => coeffMul a.coeffs b.coeffs
  | .pow a n => coeffPow a.coeffs n
  | .div a b => coeffScale (b.coeffs.headD 0)⁻¹ a.coeffs
  | _ => []

/-- Whether an expression in one variable is built from numerals, the variable, `+`, `-`, `*`,
natural powers and division by a constant. -/
def isPoly : Expr (Fin 1) → Bool
  | .nat _ | .int _ | .rat _ _ | .var _ => true
  | .add a b | .sub a b | .mul a b => a.isPoly && b.isPoly
  | .neg a | .pow a _ => a.isPoly
  | .div a b => a.isPoly && b.isPoly && decide (b.coeffs.length ≤ 1)
  | _ => false

/-- A coefficient list with at most one entry is constant: it evaluates at every real `x` to its
first entry, or `0` for the empty list. -/
theorem _root_.CAS.Polynomial.coeffEval_of_length_le_one {l : List ℚ} (h : l.length ≤ 1)
    (x : ℝ) : coeffEval l x = l.headD 0 := by
  rcases l with _ | ⟨c, _ | ⟨d, l⟩⟩
  · simp
  · simp
  · simp only [List.length_cons] at h
    omega

/-- The value of a polynomial expression is that of its coefficient list. -/
theorem eval_eq_coeffEval_coeffs {expr : Expr (Fin 1)} (h : expr.isPoly = true) (x : ℝ) :
    expr.eval ![x] = coeffEval expr.coeffs x := by
  induction expr with
  | nat n => simp [coeffs]
  | int n => simp [coeffs]
  | rat p q => simp [coeffs]
  | var i =>
    obtain rfl : i = 0 := Subsingleton.elim i 0
    simp [coeffs]
  | add a b iha ihb =>
    simp only [isPoly, Bool.and_eq_true] at h
    simp only [eval, coeffs, coeffEval_coeffAdd, iha h.1, ihb h.2]
  | sub a b iha ihb =>
    simp only [isPoly, Bool.and_eq_true] at h
    simp only [eval, coeffs, coeffEval_coeffAdd, coeffEval_coeffScale, iha h.1, ihb h.2]
    push_cast
    ring
  | mul a b iha ihb =>
    simp only [isPoly, Bool.and_eq_true] at h
    simp only [eval, coeffs, coeffEval_coeffMul, iha h.1, ihb h.2]
  | neg a ih =>
    simp only [isPoly] at h
    simp only [eval, coeffs, coeffEval_coeffScale, ih h]
    push_cast
    ring
  | pow a n ih =>
    simp only [isPoly] at h
    simp only [eval, coeffs, coeffEval_coeffPow, ih h]
  | div a b iha ihb =>
    simp only [isPoly, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨ha, hb⟩, hlength⟩ := h
    rw [eval, iha ha, ihb hb, coeffs, coeffEval_coeffScale, coeffEval_of_length_le_one hlength]
    push_cast
    ring
  | _ => simp [isPoly] at h

/-- The numerator of an expression read as a quotient: `a` for `a / b`, and the expression
itself otherwise. -/
def num : Expr (Fin 1) → Expr (Fin 1)
  | .div a _ => a
  | expr => expr

/-- The denominator of an expression read as a quotient: `b` for `a / b`, and `1` otherwise. -/
def den : Expr (Fin 1) → Expr (Fin 1)
  | .div _ b => b
  | _ => .nat 1

/-- Every expression in one variable evaluates, in every environment `ρ`, to the quotient of the
values of its numerator `num` and denominator `den`. -/
theorem eval_eq_num_div_den (expr : Expr (Fin 1)) (ρ : Fin 1 → ℝ) :
    expr.eval ρ = expr.num.eval ρ / expr.den.eval ρ := by
  cases expr with
  | div a b => rfl
  | _ => simp [num, den]

/-- Whether `F (x) + f (x + 1) = F (x + 1)` holds with the denominators cleared, for numerators
and denominators of `F` and `f` that are polynomial expressions: with `F = N / D`,
`f (x + 1) = T / U` and `N₁`, `D₁` the shifts of `N`, `D`, that `N U D₁ + T D D₁ = N₁ D U`. -/
def telescopes (F f : Expr (Fin 1)) : Bool :=
  F.num.isPoly && F.den.isPoly && f.num.isPoly && f.den.isPoly &&
    let N := F.num.coeffs
    let D := F.den.coeffs
    let T := coeffShift 1 f.num.coeffs
    let U := coeffShift 1 f.den.coeffs
    let D₁ := coeffShift 1 D
    coeffEq (coeffAdd (coeffMul (coeffMul N U) D₁) (coeffMul (coeffMul T D) D₁))
      (coeffMul (coeffMul (coeffShift 1 N) D) U)

/-- The step `F (x) + f (y) = F (y)` at `y = 1 + x`, from the check `telescopes F f` and the
denominators of `F` at `x` and `y` and of `f` at `y` being nonzero. -/
theorem eval_add_eval_eq_of_telescopes {F f : Expr (Fin 1)} {x y : ℝ} (hy : y = 1 + x)
    (h : telescopes F f = true) (hx : F.den.eval ![x] ≠ 0) (hFy : F.den.eval ![y] ≠ 0)
    (hfy : f.den.eval ![y] ≠ 0) : F.eval ![x] + f.eval ![y] = F.eval ![y] := by
  subst hy
  simp only [telescopes, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hN, hD⟩, hT⟩, hU⟩, h⟩ := h
  have identity := coeffEval_eq_of_coeffEq h x
  simp only [coeffEval_coeffAdd, coeffEval_coeffMul, coeffEval_coeffShift, Rat.cast_one] at identity
  rw [← eval_eq_coeffEval_coeffs hN, ← eval_eq_coeffEval_coeffs hN,
    ← eval_eq_coeffEval_coeffs hD, ← eval_eq_coeffEval_coeffs hD,
    ← eval_eq_coeffEval_coeffs hT, ← eval_eq_coeffEval_coeffs hU] at identity
  rw [eval_eq_num_div_den F, eval_eq_num_div_den f, eval_eq_num_div_den F,
    div_add_div _ _ hx hfy, div_eq_div_iff (mul_ne_zero hx hfy) hFy]
  linear_combination identity

end CAS.Verified.Expr

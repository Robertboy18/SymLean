/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Syntax

/-!
# Operators for verified expressions

Ordinary arithmetic notation for the reflected expression syntax. The operator equations and
semantic lemmas form the small rewriting interface used by symbolic algorithms and their soundness
proofs.

The instances only construct syntax. Mathematical meaning remains in
`Verified.Expr.eval`, and analytic domain requirements remain in
`Verified.Expr.ValidAt`.
-/

@[expose] public section

namespace CAS

namespace Verified.Expr

/-- Natural-number literals as symbolic constants. -/
instance {ι : Type*} (n : Nat) : OfNat (Verified.Expr ι) n := ⟨.nat n⟩

/-- Symbolic addition notation. -/
instance {ι : Type*} : Add (Verified.Expr ι) := ⟨.add⟩

/-- Symbolic multiplication notation. -/
instance {ι : Type*} : Mul (Verified.Expr ι) := ⟨.mul⟩

/-- Symbolic subtraction notation. -/
instance {ι : Type*} : Sub (Verified.Expr ι) := ⟨.sub⟩

/-- Symbolic negation notation. -/
instance {ι : Type*} : Neg (Verified.Expr ι) := ⟨.neg⟩

/-- Symbolic division notation. -/
instance {ι : Type*} : Div (Verified.Expr ι) := ⟨.div⟩

/-- Symbolic natural-power notation. -/
instance {ι : Type*} : Pow (Verified.Expr ι) Nat := ⟨.pow⟩

/-!
The symbolic operators are definitionally the corresponding expression
constructors. These equations keep typeclass projections out of later
proofs without making raw constructor expansion a global simp normal form.
-/

/-- `a + b` on expressions is the constructor `.add a b`. -/
theorem add_eq_constructor {ι : Type*} (a b : Verified.Expr ι) :
    a + b = .add a b := rfl

/-- `a * b` on expressions is the constructor `.mul a b`. -/
theorem mul_eq_constructor {ι : Type*} (a b : Verified.Expr ι) :
    a * b = .mul a b := rfl

/-- `a - b` on expressions is the constructor `.sub a b`. -/
theorem sub_eq_constructor {ι : Type*} (a b : Verified.Expr ι) :
    a - b = .sub a b := rfl

/-- `a ^ k` on expressions, for a natural exponent, is the constructor `.pow a k`. -/
theorem pow_eq_constructor {ι : Type*} (a : Verified.Expr ι) (k : Nat) :
    a ^ k = .pow a k := rfl

/-- Evaluation of a symbolic sum is the real sum of the evaluations. -/
@[simp] theorem eval_add_operator {ι : Type*} (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    (a + b).eval ρ = a.eval ρ + b.eval ρ := rfl

/-- Evaluation of a symbolic product is the real product of the evaluations. -/
@[simp] theorem eval_mul_operator {ι : Type*} (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    (a * b).eval ρ = a.eval ρ * b.eval ρ := rfl

/-- Evaluation of a symbolic difference is the real difference of the evaluations. -/
@[simp] theorem eval_sub_operator {ι : Type*} (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    (a - b).eval ρ = a.eval ρ - b.eval ρ := rfl

/-- Evaluation of a symbolic negation is the real negation of the evaluation. -/
@[simp] theorem eval_neg_operator {ι : Type*} (ρ : ι → ℝ)
    (a : Verified.Expr ι) :
    (-a).eval ρ = -a.eval ρ := rfl

/-- Evaluation of a symbolic quotient is the real quotient of the evaluations. Real division
is total, so no side condition appears here; the domain requirement lives in `ValidAt`. -/
@[simp] theorem eval_div_operator {ι : Type*} (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    (a / b).eval ρ = a.eval ρ / b.eval ρ := rfl

/-- Evaluation of a symbolic natural power is the real power of the evaluation. -/
@[simp] theorem eval_pow_operator {ι : Type*} (ρ : ι → ℝ)
    (a : Verified.Expr ι) (k : Nat) :
    (a ^ k).eval ρ = a.eval ρ ^ k := rfl

/-- A sum is valid at `ρ` exactly when both summands are. -/
@[simp] theorem validAt_add_operator {ι : Type*} (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    ValidAt ρ (a + b) ↔ ValidAt ρ a ∧ ValidAt ρ b := Iff.rfl

/-- A product is valid at `ρ` exactly when both factors are. -/
@[simp] theorem validAt_mul_operator {ι : Type*} (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    ValidAt ρ (a * b) ↔ ValidAt ρ a ∧ ValidAt ρ b := Iff.rfl

/-- A difference is valid at `ρ` exactly when both operands are. -/
@[simp] theorem validAt_sub_operator {ι : Type*} (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    ValidAt ρ (a - b) ↔ ValidAt ρ a ∧ ValidAt ρ b := Iff.rfl

/-- A negation is valid at `ρ` exactly when its argument is. -/
@[simp] theorem validAt_neg_operator {ι : Type*} (ρ : ι → ℝ)
    (a : Verified.Expr ι) :
    ValidAt ρ (-a) ↔ ValidAt ρ a := Iff.rfl

/-- A quotient is valid at `ρ` when both operands are valid and the denominator does not
vanish at `ρ`. This is the only place ordinary arithmetic notation acquires a side condition. -/
@[simp] theorem validAt_div_operator {ι : Type*} (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    ValidAt ρ (a / b) ↔
      ValidAt ρ a ∧ ValidAt ρ b ∧ b.eval ρ ≠ 0 := Iff.rfl

/-- A natural power is valid at `ρ` exactly when its base is. -/
@[simp] theorem validAt_pow_operator {ι : Type*} (ρ : ι → ℝ)
    (a : Verified.Expr ι) (k : Nat) :
    ValidAt ρ (a ^ k) ↔ ValidAt ρ a := Iff.rfl

/-- Symbolic differentiation is additive: the sum rule at the syntax level. -/
@[simp] theorem diff_add_operator {ι : Type*} [DecidableEq ι]
    (v : ι) (a b : Verified.Expr ι) :
    diff v (a + b) = .add (diff v a) (diff v b) := rfl

/-- The symbolic product rule, in the fixed shape `a' b + a b'` produced by `diff`. -/
@[simp] theorem diff_mul_operator {ι : Type*} [DecidableEq ι]
    (v : ι) (a b : Verified.Expr ι) :
    diff v (a * b) =
      .add (.mul (diff v a) b) (.mul a (diff v b)) := rfl

/-- Symbolic differentiation commutes with subtraction. -/
@[simp] theorem diff_sub_operator {ι : Type*} [DecidableEq ι]
    (v : ι) (a b : Verified.Expr ι) :
    diff v (a - b) = .sub (diff v a) (diff v b) := rfl

/-- Symbolic differentiation commutes with negation. -/
@[simp] theorem diff_neg_operator {ι : Type*} [DecidableEq ι]
    (v : ι) (a : Verified.Expr ι) :
    diff v (-a) = .neg (diff v a) := rfl

/-- The symbolic quotient rule `(a' b - a b') / b ^ 2`. The syntactic derivative is always
defined; the analytic identification requires `b` nonvanishing, recorded in `ValidAt`. -/
@[simp] theorem diff_div_operator {ι : Type*} [DecidableEq ι]
    (v : ι) (a b : Verified.Expr ι) :
    diff v (a / b) =
      .div (.sub (.mul (diff v a) b) (.mul a (diff v b))) (.pow b 2) := rfl

/-- The symbolic power rule `k a ^ (k - 1) a'` with truncated natural subtraction in the
exponent; for `k = 0` the leading factor `.nat 0` makes the result evaluate to zero. -/
@[simp] theorem diff_pow_operator {ι : Type*} [DecidableEq ι]
    (v : ι) (a : Verified.Expr ι) (k : Nat) :
    diff v (a ^ k) =
      .mul (.mul (.nat k) (.pow a (k - 1))) (diff v a) := rfl

end Verified.Expr

end CAS

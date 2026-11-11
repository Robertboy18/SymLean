/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Syntax

/-!
# Smart constructors for verified expressions

Local, semantics-preserving expression rewrites used by the exact symbolic engine. Each
constructor performs a bounded pattern match (neutral elements, literal folding, coefficient
collection, signs, the exponential laws, and the special values, reflections and `π` shifts of
sine and cosine) and has an evaluation theorem that holds at every valuation, with Mathlib's
total division, logarithm, square root, and real power.

## Main definitions

* `mkIntConst`, `mkRatConst`: the literal constructors for an integer and a rational number.
* `mkAdd`, `mkSub`, `mkMul`, `mkDiv`, `mkNeg`, `mkPow`, `mkNatMul`, `mkCoeffMul`: the arithmetic
  constructors.
* `mkSin`, `mkCos`, `mkExp`, `mkLog`, `mkSqrt`, `mkRpow`: the elementary-function constructors.

Recursive normalization is in `CAS.Expr.Simplify`; rendering and substitution have no
dependency on these algebraic rewrites.
-/

@[expose] public section

namespace CAS

open scoped BigOperators

namespace Verified.Expr

/-- Smart addition constructor used by the lightweight expression simplifier. -/
def mkAdd {ι : Type*} (a b : Verified.Expr ι) : Verified.Expr ι :=
  match a, b with
  | .nat 0, expr => expr
  | expr, .nat 0 => expr
  | .int 0, expr => expr
  | expr, .int 0 => expr
  | .nat m, .nat n => .nat (m + n)
  | .int m, .int n => .int (m + n)
  | _, _ => .add a b

/-- `mkAdd` preserves evaluation. -/
@[simp] theorem eval_mkAdd {ι : Type*} (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    (mkAdd a b).eval ρ = a.eval ρ + b.eval ρ := by
  unfold mkAdd
  split <;> simp [Nat.cast_add, Int.cast_add]

/-- Smart constructor for a natural scalar times an expression. -/
def mkNatMul {ι : Type*} (k : Nat) (expr : Verified.Expr ι) : Verified.Expr ι :=
  match k with
  | 0 => .nat 0
  | 1 => expr
  | _ => .mul (.nat k) expr

/-- `mkNatMul k expr` evaluates to `k` times the value of `expr`. -/
@[simp] theorem eval_mkNatMul {ι : Type*} (ρ : ι → ℝ) (k : Nat)
    (expr : Verified.Expr ι) :
    (mkNatMul k expr).eval ρ = (k : ℝ) * expr.eval ρ := by
  rcases k with _ | _ | k <;> simp [mkNatMul]

/-- Canonical symbolic integer literal, using `.nat 0` for zero. -/
def mkIntConst {ι : Type*} (k : Int) : Verified.Expr ι :=
  if 0 ≤ k then .nat k.toNat else .int k

/-- The canonical integer literal evaluates to the cast of `k`, whichever constructor was
chosen. -/
@[simp] theorem eval_mkIntConst {ι : Type*} (ρ : ι → ℝ) (k : Int) :
    (mkIntConst (ι := ι) k).eval ρ = (k : ℝ) := by
  unfold mkIntConst
  split_ifs with h
  · simp only [eval]
    exact_mod_cast Int.toNat_of_nonneg h
  · simp

/-- Canonical symbolic rational literal.

The checked expression language stores rationals as integer numerator plus natural denominator.
Using Lean's normalized `Rat` here lets the algebraic normalizer combine rational coefficients,
and `eval_mkRatConst` ties the constructor to ordinary real evaluation.
-/
def mkRatConst {ι : Type*} (q : Rat) : Verified.Expr ι :=
  if q = 0 then
    .nat 0
  else if q.den = 1 then
    mkIntConst q.num
  else
    .rat q.num q.den

/-- The canonical rational literal evaluates to the real cast of `q`. -/
@[simp] theorem eval_mkRatConst {ι : Type*} (ρ : ι → ℝ) (q : Rat) :
    (mkRatConst (ι := ι) q).eval ρ = (q : ℝ) := by
  unfold mkRatConst
  split_ifs with h0 hden
  · simp [h0]
  · simp [hden, Rat.cast_def]
  · simp [Rat.cast_def]

/-- `mkRat num den` casts to the real quotient `num / den`, including the degenerate case
`den = 0` where both sides are `0`. -/
@[simp] theorem rat_cast_mkRat_real (num : Int) (den : Nat) :
    ((mkRat num den : Rat) : ℝ) = (num : ℝ) / (den : ℝ) := by
  rw [← Rat.divInt_ofNat, Rat.cast_divInt, Int.cast_natCast]

/-- Nonrecursive coefficient multiplication used inside `mkMul`.

This helper gives nested scalar collection a way to rebuild `c * expr` without recursively
calling the full smart multiplication search. -/
def mkCoeffMul {ι : Type*} (coeff expr : Verified.Expr ι) : Verified.Expr ι :=
  match coeff with
  | .nat 0 => .nat 0
  | .int 0 => .nat 0
  | .nat 1 => expr
  | .int 1 => expr
  | _ => .mul coeff expr

/-- `mkCoeffMul` preserves evaluation. -/
@[simp] theorem eval_mkCoeffMul {ι : Type*} (ρ : ι → ℝ)
    (coeff expr : Verified.Expr ι) :
    (mkCoeffMul coeff expr).eval ρ = coeff.eval ρ * expr.eval ρ := by
  unfold mkCoeffMul
  split <;> simp

/-- Smart multiplication constructor used by the lightweight expression simplifier.
Rational literals use total division: a zero denominator denotes zero and folds accordingly. -/
def mkMul {ι : Type*} (a b : Verified.Expr ι) : Verified.Expr ι :=
  match a, b with
  | .exp ea, .exp eb => .exp (mkAdd ea eb)
  | .nat 0, _ => .nat 0
  | _, .nat 0 => .nat 0
  | .int 0, _ => .nat 0
  | _, .int 0 => .nat 0
  | .nat 1, expr => expr
  | expr, .nat 1 => expr
  | .int 1, expr => expr
  | expr, .int 1 => expr
  | .nat m, .nat n => .nat (m * n)
  | .nat m, .int n => mkIntConst ((m : Int) * n)
  | .int m, .nat n => mkIntConst (m * (n : Int))
  | .int m, .int n => .int (m * n)
  | .rat num den, .nat n =>
      mkRatConst (Rat.divInt num (den : Int) * (n : Rat))
  | .nat n, .rat num den =>
      mkRatConst ((n : Rat) * Rat.divInt num (den : Int))
  | .rat num den, .int z =>
      mkRatConst (Rat.divInt num (den : Int) * (z : Rat))
  | .int z, .rat num den =>
      mkRatConst ((z : Rat) * Rat.divInt num (den : Int))
  | .rat num₁ den₁, .rat num₂ den₂ =>
      mkRatConst (Rat.divInt num₁ (den₁ : Int) * Rat.divInt num₂ (den₂ : Int))
  | .rat num₁ den₁, .mul (.rat num₂ den₂) expr =>
      mkCoeffMul
        (mkRatConst (Rat.divInt num₁ (den₁ : Int) * Rat.divInt num₂ (den₂ : Int))) expr
  | .rat num₁ den₁, .mul expr (.rat num₂ den₂) =>
      mkCoeffMul
        (mkRatConst (Rat.divInt num₁ (den₁ : Int) * Rat.divInt num₂ (den₂ : Int))) expr
  | .mul (.rat num₁ den₁) expr, .rat num₂ den₂ =>
      mkCoeffMul
        (mkRatConst (Rat.divInt num₁ (den₁ : Int) * Rat.divInt num₂ (den₂ : Int))) expr
  | .mul expr (.rat num₁ den₁), .rat num₂ den₂ =>
      mkCoeffMul
        (mkRatConst (Rat.divInt num₁ (den₁ : Int) * Rat.divInt num₂ (den₂ : Int))) expr
  | .rat num den, .mul (.nat n) expr =>
      mkCoeffMul (mkRatConst (Rat.divInt num (den : Int) * (n : Rat))) expr
  | .rat num den, .mul expr (.nat n) =>
      mkCoeffMul (mkRatConst (Rat.divInt num (den : Int) * (n : Rat))) expr
  | .mul (.nat n) expr, .rat num den =>
      mkCoeffMul (mkRatConst ((n : Rat) * Rat.divInt num (den : Int))) expr
  | .mul expr (.nat n), .rat num den =>
      mkCoeffMul (mkRatConst ((n : Rat) * Rat.divInt num (den : Int))) expr
  | .rat num den, .mul (.int z) expr =>
      mkCoeffMul (mkRatConst (Rat.divInt num (den : Int) * (z : Rat))) expr
  | .rat num den, .mul expr (.int z) =>
      mkCoeffMul (mkRatConst (Rat.divInt num (den : Int) * (z : Rat))) expr
  | .mul (.int z) expr, .rat num den =>
      mkCoeffMul (mkRatConst ((z : Rat) * Rat.divInt num (den : Int))) expr
  | .mul expr (.int z), .rat num den =>
      mkCoeffMul (mkRatConst ((z : Rat) * Rat.divInt num (den : Int))) expr
  | .nat n, .mul (.rat num den) expr =>
      mkCoeffMul (mkRatConst ((n : Rat) * Rat.divInt num (den : Int))) expr
  | .nat n, .mul expr (.rat num den) =>
      mkCoeffMul (mkRatConst ((n : Rat) * Rat.divInt num (den : Int))) expr
  | .mul (.rat num den) expr, .nat n =>
      mkCoeffMul (mkRatConst (Rat.divInt num (den : Int) * (n : Rat))) expr
  | .mul expr (.rat num den), .nat n =>
      mkCoeffMul (mkRatConst (Rat.divInt num (den : Int) * (n : Rat))) expr
  | .int z, .mul (.rat num den) expr =>
      mkCoeffMul (mkRatConst ((z : Rat) * Rat.divInt num (den : Int))) expr
  | .int z, .mul expr (.rat num den) =>
      mkCoeffMul (mkRatConst ((z : Rat) * Rat.divInt num (den : Int))) expr
  | .mul (.rat num den) expr, .int z =>
      mkCoeffMul (mkRatConst (Rat.divInt num (den : Int) * (z : Rat))) expr
  | .mul expr (.rat num den), .int z =>
      mkCoeffMul (mkRatConst (Rat.divInt num (den : Int) * (z : Rat))) expr
  | .neg (.nat 1), expr => .neg expr
  | expr, .neg (.nat 1) => .neg expr
  | .neg (.int 1), expr => .neg expr
  | expr, .neg (.int 1) => .neg expr
  | .int (-1), expr => .neg expr
  | expr, .int (-1) => .neg expr
  | .nat m, .mul (.nat n) expr => mkNatMul (m * n) expr
  | .nat m, .mul expr (.nat n) => mkNatMul (m * n) expr
  | .mul (.nat m) expr, .nat n => mkNatMul (m * n) expr
  | .mul expr (.nat m), .nat n => mkNatMul (m * n) expr
  | _, _ => .mul a b

/-- `mkMul` preserves evaluation. -/
@[simp] theorem eval_mkMul {ι : Type*} (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    (mkMul a b).eval ρ = a.eval ρ * b.eval ρ := by
  unfold mkMul
  repeat split <;>
    simp [Nat.cast_mul, Int.cast_mul, rat_cast_mkRat_real, mul_div_mul_comm,
      eval_mkCoeffMul, Real.exp_add, mul_assoc, mul_left_comm, mul_comm]


/-- Smart subtraction constructor used by the lightweight expression simplifier. -/
def mkSub {ι : Type*} [DecidableEq ι] (a b : Verified.Expr ι) : Verified.Expr ι :=
  if a = b then
    .nat 0
  else
    match a, b with
    | expr, .nat 0 => expr
    | expr, .int 0 => expr
    | .nat 0, expr => .neg expr
    | .int 0, expr => .neg expr
    | .nat m, .nat n => mkIntConst ((m : Int) - (n : Int))
    | .int m, .int n => mkIntConst (m - n)
    | .nat m, .int n => mkIntConst ((m : Int) - n)
    | .int m, .nat n => mkIntConst (m - (n : Int))
    | .rat num₁ den₁, .rat num₂ den₂ =>
        mkRatConst (Rat.divInt num₁ (den₁ : Int) - Rat.divInt num₂ (den₂ : Int))
    | .rat num den, .nat n =>
        mkRatConst (Rat.divInt num (den : Int) - (n : Rat))
    | .nat n, .rat num den =>
        mkRatConst ((n : Rat) - Rat.divInt num (den : Int))
    | .rat num den, .int z =>
        mkRatConst (Rat.divInt num (den : Int) - (z : Rat))
    | .int z, .rat num den =>
        mkRatConst ((z : Rat) - Rat.divInt num (den : Int))
    | _, _ => .sub a b

/-- `mkSub` preserves evaluation. -/
@[simp] theorem eval_mkSub {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    (mkSub a b).eval ρ = a.eval ρ - b.eval ρ := by
  unfold mkSub
  split_ifs with h
  · simp [h]
  · split <;> simp [Int.cast_sub]

/-- Smart division constructor used by the lightweight expression simplifier.

This uses only identities valid for Lean's total real division, such as `0 / x = 0` and
`x / 1 = x`. It can erase denominator nodes and their `ValidAt` obligations: `1 / 0`, for example,
becomes literal zero. The evaluation theorem does not transport `ValidAt` backwards. Analytic
validity must be checked for the expression to which a derivative theorem is applied. -/
def mkDiv {ι : Type*} (a b : Verified.Expr ι) : Verified.Expr ι :=
  match a, b with
  | .exp ea, .exp eb => .exp (.sub ea eb)
  | .nat 1, .exp eb => .exp (.neg eb)
  | .int 1, .exp eb => .exp (.neg eb)
  | .nat 0, _ => .nat 0
  | .int 0, _ => .nat 0
  | expr, .nat 1 => expr
  | expr, .int 1 => expr
  | .nat m, .nat n =>
      mkRatConst ((m : Rat) / (n : Rat))
  | .nat m, .int z =>
      mkRatConst ((m : Rat) / (z : Rat))
  | .int z, .nat n =>
      mkRatConst ((z : Rat) / (n : Rat))
  | .int m, .int z =>
      mkRatConst ((m : Rat) / (z : Rat))
  | .rat num₁ den₁, .rat num₂ den₂ =>
      mkRatConst (Rat.divInt num₁ (den₁ : Int) / Rat.divInt num₂ (den₂ : Int))
  | .rat num den, .nat n =>
      mkRatConst (Rat.divInt num (den : Int) / (n : Rat))
  | .nat n, .rat num den =>
      mkRatConst ((n : Rat) / Rat.divInt num (den : Int))
  | .rat num den, .int z =>
      mkRatConst (Rat.divInt num (den : Int) / (z : Rat))
  | .int z, .rat num den =>
      mkRatConst ((z : Rat) / Rat.divInt num (den : Int))
  | .mul (.nat m) expr, .nat n =>
      mkCoeffMul (mkRatConst ((m : Rat) / (n : Rat))) expr
  | .mul expr (.nat m), .nat n =>
      mkCoeffMul (mkRatConst ((m : Rat) / (n : Rat))) expr
  | .mul (.int z) expr, .nat n =>
      mkCoeffMul (mkRatConst ((z : Rat) / (n : Rat))) expr
  | .mul expr (.int z), .nat n =>
      mkCoeffMul (mkRatConst ((z : Rat) / (n : Rat))) expr
  | .mul (.rat num den) expr, .nat n =>
      mkCoeffMul (mkRatConst (Rat.divInt num (den : Int) / (n : Rat))) expr
  | .mul expr (.rat num den), .nat n =>
      mkCoeffMul (mkRatConst (Rat.divInt num (den : Int) / (n : Rat))) expr
  | .mul (.nat m) expr, .int z =>
      mkCoeffMul (mkRatConst ((m : Rat) / (z : Rat))) expr
  | .mul expr (.nat m), .int z =>
      mkCoeffMul (mkRatConst ((m : Rat) / (z : Rat))) expr
  | .mul (.int m) expr, .int z =>
      mkCoeffMul (mkRatConst ((m : Rat) / (z : Rat))) expr
  | .mul expr (.int m), .int z =>
      mkCoeffMul (mkRatConst ((m : Rat) / (z : Rat))) expr
  | .mul (.rat num den) expr, .int z =>
      mkCoeffMul (mkRatConst (Rat.divInt num (den : Int) / (z : Rat))) expr
  | .mul expr (.rat num den), .int z =>
      mkCoeffMul (mkRatConst (Rat.divInt num (den : Int) / (z : Rat))) expr
  | .mul (.nat m) expr, .rat num den =>
      mkCoeffMul (mkRatConst ((m : Rat) / Rat.divInt num (den : Int))) expr
  | .mul expr (.nat m), .rat num den =>
      mkCoeffMul (mkRatConst ((m : Rat) / Rat.divInt num (den : Int))) expr
  | .mul (.int z) expr, .rat num den =>
      mkCoeffMul (mkRatConst ((z : Rat) / Rat.divInt num (den : Int))) expr
  | .mul expr (.int z), .rat num den =>
      mkCoeffMul (mkRatConst ((z : Rat) / Rat.divInt num (den : Int))) expr
  | .mul (.rat num₁ den₁) expr, .rat num₂ den₂ =>
      mkCoeffMul
        (mkRatConst (Rat.divInt num₁ (den₁ : Int) / Rat.divInt num₂ (den₂ : Int))) expr
  | .mul expr (.rat num₁ den₁), .rat num₂ den₂ =>
      mkCoeffMul
        (mkRatConst (Rat.divInt num₁ (den₁ : Int) / Rat.divInt num₂ (den₂ : Int))) expr
  | .mul (.nat m) expr, .mul (.nat n) denExpr =>
      .div (mkMul (mkRatConst ((m : Rat) / (n : Rat))) expr) denExpr
  | .mul (.nat m) expr, .mul denExpr (.nat n) =>
      .div (mkMul (mkRatConst ((m : Rat) / (n : Rat))) expr) denExpr
  | .mul expr (.nat m), .mul (.nat n) denExpr =>
      .div (mkMul (mkRatConst ((m : Rat) / (n : Rat))) expr) denExpr
  | .mul expr (.nat m), .mul denExpr (.nat n) =>
      .div (mkMul (mkRatConst ((m : Rat) / (n : Rat))) expr) denExpr
  | expr, .mul (.nat n) denExpr =>
      .div (mkMul (mkRatConst ((1 : Rat) / (n : Rat))) expr) denExpr
  | expr, .mul denExpr (.nat n) =>
      .div (mkMul (mkRatConst ((1 : Rat) / (n : Rat))) expr) denExpr
  | expr, .mul (.int z) denExpr =>
      .div (mkMul (mkRatConst ((1 : Rat) / (z : Rat))) expr) denExpr
  | expr, .mul denExpr (.int z) =>
      .div (mkMul (mkRatConst ((1 : Rat) / (z : Rat))) expr) denExpr
  | expr, .mul (.rat num den) denExpr =>
      .div
        (mkMul (mkRatConst ((1 : Rat) / Rat.divInt num (den : Int))) expr)
        denExpr
  | expr, .mul denExpr (.rat num den) =>
      .div
        (mkMul (mkRatConst ((1 : Rat) / Rat.divInt num (den : Int))) expr)
        denExpr
  | expr, .nat n =>
      mkCoeffMul (mkRatConst ((1 : Rat) / (n : Rat))) expr
  | expr, .int z =>
      mkCoeffMul (mkRatConst ((1 : Rat) / (z : Rat))) expr
  | expr, .rat num den =>
      mkCoeffMul (mkRatConst ((1 : Rat) / Rat.divInt num (den : Int))) expr
  | _, _ => .div a b

/-- `mkDiv` preserves evaluation. No nonvanishing hypothesis is needed: the constant folding
it performs agrees with totalized real division even when a denominator is zero. -/
@[simp] theorem eval_mkDiv {ι : Type*} (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    (mkDiv a b).eval ρ = a.eval ρ / b.eval ρ := by
  unfold mkDiv
  split <;>
    simp [eval_mkCoeffMul, Rat.cast_divInt,
      div_eq_mul_inv, Real.exp_sub, Real.exp_neg, mul_assoc, mul_left_comm, mul_comm]

/-- Smart negation constructor used by the lightweight expression simplifier. -/
def mkNeg {ι : Type*} (a : Verified.Expr ι) : Verified.Expr ι :=
  match a with
  | .nat 0 => .nat 0
  | .int 0 => .nat 0
  | .nat n => .int (-(n : Int))
  | .int n => mkIntConst (-n)
  | .rat num den => mkRatConst (-Rat.divInt num (den : Int))
  | .neg expr => expr
  | _ => .neg a

/-- `mkNeg` preserves evaluation. -/
@[simp] theorem eval_mkNeg {ι : Type*} (ρ : ι → ℝ)
    (a : Verified.Expr ι) :
    (mkNeg a).eval ρ = -a.eval ρ := by
  unfold mkNeg
  split <;> simp [Int.cast_neg]

/-- Smart natural-power constructor used by the lightweight expression simplifier. -/
def mkPow {ι : Type*} (a : Verified.Expr ι) (k : Nat) : Verified.Expr ι :=
  match k with
  | 0 => .nat 1
  | 1 => a
  | _ =>
      match a with
      | .nat m => .nat (m ^ k)
      | .int m => .int (m ^ k)
      | .rat num den => mkRatConst ((Rat.divInt num (den : Int)) ^ k)
      | .neg (.nat m) => .int ((-(m : Int)) ^ k)
      | .neg (.int m) => .int ((-m) ^ k)
      | _ => .pow a k

/-- `mkPow` preserves evaluation, including the folded integer-literal powers. -/
@[simp] theorem eval_mkPow {ι : Type*} (ρ : ι → ℝ)
    (a : Verified.Expr ι) (k : Nat) :
    (mkPow a k).eval ρ = a.eval ρ ^ k := by
  unfold mkPow
  split <;> (try split) <;> simp [Rat.divInt_ofNat]

/-- Smart symbolic sine constructor used by the lightweight expression simplifier.
The `2π` fold expects `π + π`, the shape retained by `simplifyAdd`. -/
def mkSin {ι : Type*} (a : Verified.Expr ι) : Verified.Expr ι :=
  match a with
  | .nat 0 => .nat 0
  | .int 0 => .nat 0
  | .pi => .nat 0
  | .add .pi .pi => .nat 0
  | .neg .pi => .nat 0
  | .sub .pi b => .sin b
  | .sub b .pi => .neg (.sin b)
  | .add .pi b => .neg (.sin b)
  | .add b .pi => .neg (.sin b)
  | .neg b => mkNeg (.sin b)
  | _ => .sin a

/-- `mkSin` preserves evaluation. The rewrites are the special values `sin 0 = sin (±π) =
sin (2π) = 0`, the reflection `sin (π - b) = sin b`, the shifts `sin (b ± π) = -sin b`, and
the odd-function law. -/
@[simp] theorem eval_mkSin {ι : Type*} (ρ : ι → ℝ) (a : Verified.Expr ι) :
    (mkSin a).eval ρ = Real.sin (a.eval ρ) := by
  unfold mkSin
  split <;> simp [Real.sin_neg, Real.sin_add, sub_eq_add_neg]

/-- Smart symbolic cosine constructor used by the lightweight expression simplifier.
The `2π` fold expects `π + π`, the shape retained by `simplifyAdd`. -/
def mkCos {ι : Type*} (a : Verified.Expr ι) : Verified.Expr ι :=
  match a with
  | .nat 0 => .nat 1
  | .int 0 => .nat 1
  | .pi => .int (-1)
  | .add .pi .pi => .nat 1
  | .neg .pi => .int (-1)
  | .sub .pi b => .neg (.cos b)
  | .sub b .pi => .neg (.cos b)
  | .add .pi b => .neg (.cos b)
  | .add b .pi => .neg (.cos b)
  | .neg b => .cos b
  | _ => .cos a

/-- `mkCos` preserves evaluation. The rewrites are the special values `cos 0 = cos (2π) = 1`,
`cos (±π) = -1`, the reflection and shifts `cos (π - b) = cos (b ± π) = -cos b`, and the
even-function law. -/
@[simp] theorem eval_mkCos {ι : Type*} (ρ : ι → ℝ) (a : Verified.Expr ι) :
    (mkCos a).eval ρ = Real.cos (a.eval ρ) := by
  unfold mkCos
  split <;> simp [Real.cos_neg, Real.cos_add, sub_eq_add_neg]

/-- Smart symbolic exponential constructor used by the lightweight expression simplifier. -/
def mkExp {ι : Type*} (a : Verified.Expr ι) : Verified.Expr ι :=
  match a with
  | .nat 0 => .nat 1
  | .int 0 => .nat 1
  | .nat 1 => .e
  | .int 1 => .e
  | _ => .exp a

/-- `mkExp` preserves evaluation (`exp 0 = 1`, `exp 1 = e`). -/
@[simp] theorem eval_mkExp {ι : Type*} (ρ : ι → ℝ) (a : Verified.Expr ι) :
    (mkExp a).eval ρ = Real.exp (a.eval ρ) := by
  unfold mkExp
  split <;> simp

/-- Smart symbolic logarithm constructor used by the lightweight expression simplifier. -/
def mkLog {ι : Type*} (a : Verified.Expr ι) : Verified.Expr ι :=
  match a with
  | .nat 1 => .nat 0
  | .int 1 => .nat 0
  | .e => .nat 1
  | .exp b => b
  | _ => .log a

/-- `mkLog` preserves evaluation. The rewrite `log (exp b) = b` is unconditional in Mathlib
(`Real.log_exp`), and `log 1 = 0`, `log e = 1` hold for the totalized logarithm. -/
@[simp] theorem eval_mkLog {ι : Type*} (ρ : ι → ℝ) (a : Verified.Expr ι) :
    (mkLog a).eval ρ = Real.log (a.eval ρ) := by
  unfold mkLog
  split <;> simp [Real.log_exp]

/-- Smart symbolic square-root constructor used by the lightweight expression simplifier. -/
def mkSqrt {ι : Type*} (a : Verified.Expr ι) : Verified.Expr ι :=
  match a with
  | .nat 0 => .nat 0
  | .int 0 => .nat 0
  | .nat 1 => .nat 1
  | .int 1 => .nat 1
  | _ => .sqrt a

/-- `mkSqrt` preserves evaluation (`√0 = 0`, `√1 = 1`). -/
@[simp] theorem eval_mkSqrt {ι : Type*} (ρ : ι → ℝ) (a : Verified.Expr ι) :
    (mkSqrt a).eval ρ = Real.sqrt (a.eval ρ) := by
  unfold mkSqrt
  split <;> simp

/-- Smart real-power constructor used by the lightweight expression simplifier.

A natural-literal exponent is lowered to the natural power `mkPow a n`, so `a ^ (0 : ℝ)` and
`a ^ (1 : ℝ)` fold to `1` and `a`, and a power of an exponential is folded to a single
exponential. Both rewrites are unconditional identities of Mathlib's total `Real.rpow`. -/
def mkRpow {ι : Type*} (a b : Verified.Expr ι) : Verified.Expr ι :=
  match a, b with
  | _, .nat n => mkPow a n
  | .exp u, _ => mkExp (mkMul u b)
  | _, _ => .rpow a b

/-- `mkRpow` preserves evaluation. The natural-literal rewrite is `Real.rpow_natCast`
(`x ^ (n : ℝ) = x ^ n`) and the exponential rewrite is `Real.exp_mul`
(`exp (u * v) = exp u ^ v`); neither needs a sign hypothesis. -/
@[simp] theorem eval_mkRpow {ι : Type*} (ρ : ι → ℝ) (a b : Verified.Expr ι) :
    (mkRpow a b).eval ρ = a.eval ρ ^ b.eval ρ := by
  unfold mkRpow
  split <;> simp [Real.rpow_natCast, Real.exp_mul]

end Verified.Expr
end CAS

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.SmartConstructors
public import CAS.Expr.Operators

/-!
# Recursive simplification of verified expressions

Lightweight recursive normalizers for the reflected expression language. They rebuild each syntax
node with the checked smart constructors and therefore preserve real-valued evaluation.

`simplify` performs local algebraic reductions. `trigSimplify` also applies the post-pass
`trigPostTop`, which reduces the sine-cosine sum-of-squares identities, at every rebuilt node.
The soundness theorems are `eval_simplify` and `eval_trigSimplify`. The results are simplified,
not canonical: equal expressions can simplify to different syntax.

## Implementation notes

We simplify bottom up. Both normalizers first simplify the children of a node and then rebuild it
with one local step: a smart constructor of `CAS.Expr.SmartConstructors`, or one of the
combinators `simplifyAdd`, `simplifyMul`, `simplifySub`, `simplifyDivRecursive` and
`simplifyPow`. Every step has its own evaluation lemma and none of them needs a hypothesis, since
Mathlib's division, logarithm, square root and real power are total. So `eval_simplify` and
`eval_trigSimplify` hold at every assignment, and their proofs are one structural induction
closed by `simp_all`.

Each step is a bounded pattern match with syntactic equality tests and no search. The
trigonometric post-pass recognizes `sin t ^ 2 + cos t ^ 2`, `sin t * sin t + cos t * cos t`, the
negated product form and the swapped orders, with the same argument `t` throughout; the identity
behind all of them is Mathlib's `Real.sin_sq_add_cos_sq`.
-/

@[expose] public section

namespace CAS

namespace Verified.Expr

/-- Additive simplification used by the recursive symbolic simplifier.
The sum `π + π` is retained because `mkSin` and `mkCos` recognize that literal shape.
All other equal summands are doubled. -/
def simplifyAdd {ι : Type*} [DecidableEq ι] (a b : Verified.Expr ι) : Verified.Expr ι :=
  if a = mkNeg b then
    .nat 0
  else if mkNeg a = b then
    .nat 0
  else if a = b then
    match a with
    | .pi => mkAdd a b
    | _ => mkMul 2 a
  else
    match a, b with
    | .rat num₁ den₁, .rat num₂ den₂ =>
        mkRatConst (Rat.divInt num₁ (den₁ : Int) + Rat.divInt num₂ (den₂ : Int))
    | .rat num den, .nat n =>
        mkRatConst (Rat.divInt num (den : Int) + (n : Rat))
    | .nat n, .rat num den =>
        mkRatConst ((n : Rat) + Rat.divInt num (den : Int))
    | .rat num den, .int z =>
        mkRatConst (Rat.divInt num (den : Int) + (z : Rat))
    | .int z, .rat num den =>
        mkRatConst ((z : Rat) + Rat.divInt num (den : Int))
    | _, _ => mkAdd a b

/-- `simplifyAdd` preserves evaluation: cancelling `a + (-a)`, doubling `a + a` except
for the retained `π + π`, and folding rational literals are sound for real arithmetic. -/
@[simp] theorem eval_simplifyAdd {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    (simplifyAdd a b).eval ρ = a.eval ρ + b.eval ρ := by
  unfold simplifyAdd
  split_ifs with h1 h2 h3
  · simp [h1, eval_mkNeg]
  · simp [← h2, eval_mkNeg]
  · subst h3
    cases a <;> simp [eval_mkAdd, eval_mkMul, two_mul]
  · split <;> simp [Rat.cast_add, eval_mkAdd]

/-- Multiplicative simplification used by the recursive symbolic simplifier. -/
def simplifyMul {ι : Type*} (a b : Verified.Expr ι) : Verified.Expr ι :=
  match a, b with
  | .neg a', .neg b' => mkMul a' b'
  | .neg a', _ => mkNeg (mkMul a' b)
  | _, .neg b' => mkNeg (mkMul a b')
  | a, .div numerator denominator =>
      mkDiv (mkMul a numerator) denominator
  | .div numerator denominator, b =>
      mkDiv (mkMul numerator b) denominator
  | _, _ => mkMul a b

/-- `simplifyMul` preserves evaluation. -/
@[simp] theorem eval_simplifyMul {ι : Type*} (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    (simplifyMul a b).eval ρ = a.eval ρ * b.eval ρ := by
  cases a <;> cases b <;>
    simp [simplifyMul, eval_mkMul, eval_mkNeg, eval_mkDiv,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Subtractive simplification used by the recursive symbolic simplifier. -/
def simplifySub {ι : Type*} [DecidableEq ι] (a b : Verified.Expr ι) : Verified.Expr ι :=
  match b with
  | .neg b' => simplifyAdd a b'
  | _ => mkSub a b

/-- `simplifySub` preserves evaluation; rewriting `a - (-b)` as `a + b` is the only case that
is not a direct smart-constructor call. -/
@[simp] theorem eval_simplifySub {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    (simplifySub a b).eval ρ = a.eval ρ - b.eval ρ := by
  cases b <;> simp [simplifySub, sub_eq_add_neg, eval_mkSub]

private theorem mul_mul_inv_pow_add_two (a x : ℝ) (n : Nat) :
    a * x * (x ^ (n + 2))⁻¹ = a * (x ^ (n + 1))⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← div_eq_mul_inv, ← div_eq_mul_inv, pow_succ _ (n + 1), mul_div_mul_right _ _ hx]

/-- Divisive simplification that does not inspect symbolic variable equality. -/
def simplifyDiv {ι : Type*} (a b : Verified.Expr ι) : Verified.Expr ι :=
  match a, b with
  | .neg a', .neg b' => mkDiv a' b'
  | .neg a', _ => mkNeg (mkDiv a' b)
  | _, .neg b' => mkNeg (mkDiv a b')
  | _, _ => mkDiv a b

/-- `simplifyDiv` preserves evaluation. It only moves negations out of the numerator and
denominator before calling `mkDiv`; because real division is total, no nonvanishing
hypothesis is needed. Common factors are not cancelled here (see `simplifyPowerDiv`). -/
@[simp] theorem eval_simplifyDiv {ι : Type*} (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    (simplifyDiv a b).eval ρ = a.eval ρ / b.eval ρ := by
  cases a <;> cases b <;> simp [simplifyDiv, eval_mkDiv, eval_mkNeg, div_eq_mul_inv]

/-- Cancel one common factor when a positive denominator power remains. -/
def simplifyPowerDiv {ι : Type*} [DecidableEq ι]
    (a b : Verified.Expr ι) : Verified.Expr ι :=
  match a, b with
  | .mul c x, .pow y (n + 2) =>
      if x = y then
        mkDiv c (mkPow y (n + 1))
      else if c = y then
        mkDiv x (mkPow y (n + 1))
      else
        mkDiv (.mul c x) (.pow y (n + 2))
  | _, _ => mkDiv a b

/-- Power-quotient simplification preserves evaluation even at a zero denominator,
using Lean's total real division. -/
@[simp] theorem eval_simplifyPowerDiv {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    (simplifyPowerDiv a b).eval ρ = a.eval ρ / b.eval ρ := by
  unfold simplifyPowerDiv
  split <;> (try split) <;> (try split) <;>
    simp [eval_mkDiv, div_eq_mul_inv, mul_mul_inv_pow_add_two, mul_comm, *]

/-- Divisive simplification used by the recursive symbolic simplifier. -/
def simplifyDivRecursive {ι : Type*} [DecidableEq ι]
    (a b : Verified.Expr ι) : Verified.Expr ι :=
  match a, b with
  | .neg a', .neg b' => simplifyPowerDiv a' b'
  | .neg a', _ => mkNeg (simplifyPowerDiv a' b)
  | _, .neg b' => mkNeg (simplifyPowerDiv a b')
  | _, _ => simplifyPowerDiv a b

/-- Moving signs and simplifying powers in a quotient preserves its value without
requiring the denominator to be nonzero. -/
@[simp] theorem eval_simplifyDivRecursive {ι : Type*} [DecidableEq ι]
    (ρ : ι → ℝ) (a b : Verified.Expr ι) :
    (simplifyDivRecursive a b).eval ρ = a.eval ρ / b.eval ρ := by
  cases a <;> cases b <;>
    simp [simplifyDivRecursive, eval_simplifyPowerDiv, eval_mkNeg, div_eq_mul_inv]

/-- Natural-power simplification used by the recursive symbolic simplifier. -/
def simplifyPow {ι : Type*} (a : Verified.Expr ι) (k : Nat) : Verified.Expr ι :=
  match a, k with
  | .pow b m, k => mkPow b (m * k)
  | _, k => mkPow a k

/-- `simplifyPow` preserves evaluation; the only nontrivial case is `(b ^ m) ^ k = b ^ (m k)`. -/
@[simp] theorem eval_simplifyPow {ι : Type*} (ρ : ι → ℝ)
    (a : Verified.Expr ι) (k : Nat) :
    (simplifyPow a k).eval ρ = a.eval ρ ^ k := by
  cases a <;> simp [simplifyPow, eval_mkPow, pow_mul]

/-- Reduce the supported top-level trigonometric sum-of-squares identities. -/
def trigPostTop {ι : Type*} [DecidableEq ι] : Verified.Expr ι → Verified.Expr ι
  | .add (.pow (.sin t) 2) (.pow (.cos s) 2) =>
      if t = s then .nat 1 else .add (.pow (.sin t) 2) (.pow (.cos s) 2)
  | .add (.pow (.cos t) 2) (.pow (.sin s) 2) =>
      if t = s then .nat 1 else .add (.pow (.cos t) 2) (.pow (.sin s) 2)
  | .add (.mul (.sin t₁) (.sin t₂)) (.mul (.cos s₁) (.cos s₂)) =>
      if t₁ = t₂ ∧ t₁ = s₁ ∧ s₁ = s₂ then
        .nat 1
      else
        .add (.mul (.sin t₁) (.sin t₂)) (.mul (.cos s₁) (.cos s₂))
  | .add (.mul (.cos t₁) (.cos t₂)) (.mul (.sin s₁) (.sin s₂)) =>
      if t₁ = t₂ ∧ t₁ = s₁ ∧ s₁ = s₂ then
        .nat 1
      else
        .add (.mul (.cos t₁) (.cos t₂)) (.mul (.sin s₁) (.sin s₂))
  | .add (.neg (.mul (.sin t₁) (.sin t₂))) (.neg (.mul (.cos s₁) (.cos s₂))) =>
      if t₁ = t₂ ∧ t₁ = s₁ ∧ s₁ = s₂ then
        .int (-1)
      else
        .add (.neg (.mul (.sin t₁) (.sin t₂))) (.neg (.mul (.cos s₁) (.cos s₂)))
  | .add (.neg (.mul (.cos t₁) (.cos t₂))) (.neg (.mul (.sin s₁) (.sin s₂))) =>
      if t₁ = t₂ ∧ t₁ = s₁ ∧ s₁ = s₂ then
        .int (-1)
      else
        .add (.neg (.mul (.cos t₁) (.cos t₂))) (.neg (.mul (.sin s₁) (.sin s₂)))
  | expr => expr

/-- The trigonometric post-pass preserves evaluation. Every rewrite it performs is an instance
of `sin² t + cos² t = 1` (Mathlib's `Real.sin_sq_add_cos_sq`) after syntactic matching of the
arguments. -/
@[simp] theorem eval_trigPostTop {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι) :
    (trigPostTop expr).eval ρ = expr.eval ρ := by
  unfold trigPostTop
  split <;> (try split)
  all_goals
    try casesm* _ ∧ _
    subst_vars
    simp [← sq, ← neg_add, -neg_add_rev]

/-- Recursively simplify a reflected expression with the checked smart constructors.

The normalizer removes neutral elements, zero factors, double negations,
trivial divisions by one, and trivial powers. Stronger canonicalization lives
in separate checked passes. -/
def simplify {ι : Type*} [DecidableEq ι] : Verified.Expr ι → Verified.Expr ι
  | .nat k => .nat k
  | .int k => .int k
  | .rat num den => .rat num den
  | .pi => .pi
  | .e => .e
  | .var i => .var i
  | .add a b => simplifyAdd (simplify a) (simplify b)
  | .mul a b => simplifyMul (simplify a) (simplify b)
  | .sub a b => simplifySub (simplify a) (simplify b)
  | .div a b => simplifyDivRecursive (simplify a) (simplify b)
  | .neg a => mkNeg (simplify a)
  | .pow a k => simplifyPow (simplify a) k
  | .sin a => mkSin (simplify a)
  | .cos a => mkCos (simplify a)
  | .atan a => .atan (simplify a)
  | .asin a => .asin (simplify a)
  | .acos a => .acos (simplify a)
  | .exp a => mkExp (simplify a)
  | .log a => mkLog (simplify a)
  | .sqrt a => mkSqrt (simplify a)
  | .rpow a b => mkRpow (simplify a) (simplify b)

/-- Recursively simplify an expression and apply the checked trigonometric post-pass.

The post-pass runs at every rebuilt node, so supported identities are reduced
even when they occur inside a larger expression. -/
def trigSimplify {ι : Type*} [DecidableEq ι] : Verified.Expr ι → Verified.Expr ι
  | .nat k => .nat k
  | .int k => .int k
  | .rat num den => .rat num den
  | .pi => .pi
  | .e => .e
  | .var i => .var i
  | .add a b => trigPostTop (simplifyAdd (trigSimplify a) (trigSimplify b))
  | .mul a b => trigPostTop (simplifyMul (trigSimplify a) (trigSimplify b))
  | .sub a b => trigPostTop (simplifySub (trigSimplify a) (trigSimplify b))
  | .div a b =>
      trigPostTop (simplifyDivRecursive (trigSimplify a) (trigSimplify b))
  | .neg a => trigPostTop (mkNeg (trigSimplify a))
  | .pow a k => trigPostTop (simplifyPow (trigSimplify a) k)
  | .sin a => trigPostTop (mkSin (trigSimplify a))
  | .cos a => trigPostTop (mkCos (trigSimplify a))
  | .atan a => trigPostTop (.atan (trigSimplify a))
  | .asin a => trigPostTop (.asin (trigSimplify a))
  | .acos a => trigPostTop (.acos (trigSimplify a))
  | .exp a => trigPostTop (mkExp (trigSimplify a))
  | .log a => trigPostTop (mkLog (trigSimplify a))
  | .sqrt a => trigPostTop (mkSqrt (trigSimplify a))
  | .rpow a b => trigPostTop (mkRpow (trigSimplify a) (trigSimplify b))

/-- Soundness of the recursive simplifier: `simplify` never changes the value of an
expression at any assignment. -/
@[simp] theorem eval_simplify {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι) :
    (simplify expr).eval ρ = expr.eval ρ := by
  induction expr <;> simp_all [simplify]

/-- Soundness of the simplifier with the trigonometric post-pass: `trigSimplify` never changes
the value of an expression at any assignment. -/
@[simp] theorem eval_trigSimplify {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι) :
    (trigSimplify expr).eval ρ = expr.eval ρ := by
  induction expr <;> simp_all [trigSimplify]

end Verified.Expr

end CAS

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.BottomUp
public import CAS.ClosedForm.Pipeline.Passes.NumericLiteral

/-!
# Square roots of perfect-square numerals

The side pass that evaluates `sqrt n` for a numeral radicand `n` that is a perfect square:
`sqrt 9` becomes `3`, `sqrt (1 / 4)` and `sqrt (rat 1 4)` become `1/2`, and `sqrt 2` is left
alone. The polynomial normalizer treats `sqrt 9` as an atom unrelated to the numeral `3`, so
without this pass `sqrt 9 - 3` does not normalize to zero.

## Main definitions

* `perfectSquareRoot?`, `perfectSquareRootRat?`: checked perfect-square roots of numerals.
* `sqrtNumeralCleanup`: the rewrite of one square-root node.
* `sqrtNumeralSidePass`: the pass, named `sqrt-numeral`; it records no obligation.

## Main results

* `sqrt_cast_eq_of_perfectSquareRootRat?`: an accepted root is the real square root of the
  radicand.
* `eval_sqrtNumeralCleanup`, `eval_sqrtNumeralDeepCleanup`: the rewrites preserve evaluation
  unconditionally.

## Implementation notes

We find the candidate root of a natural numeral by a fuel-bounded bisection
(`integerSqrtBisect`), which the kernel evaluates like every other step of the normalizer;
`Nat.sqrt` of the core library is defined by well-founded recursion, which the kernel does not
reduce reliably. The candidate `k` is accepted only when `k * k = n` holds, checked inside the
pass (`checkSquareRoot?`), so the search is untrusted and the soundness theorem depends only on
the check. A rational radicand is accepted when it is nonnegative and its numerator and
denominator are both perfect squares (`perfectSquareRootRat?`). The radicand may be a literal
`nat`, `int`, or `rat` node or a quotient of two such literals with nonzero denominator
(`radicandValue?`, through the numeric parser `NumericLiteral.parse?`). The real identity behind
the rewrite is `Real.sqrt_mul_self`.
-/

@[expose] public section

namespace CAS.Verified.Expr

/-- Bisection for the integer square root of `n` on the bracket `[lo, hi)`, which the caller
starts with `lo * lo ≤ n < hi * hi`; the bracket is halved until it is a unit interval or the
fuel runs out. The result is checked by `checkSquareRoot?`, so no property is proved here. -/
def integerSqrtBisect (n : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then lo
      else
        let mid := (lo + hi) / 2
        if mid * mid ≤ n then integerSqrtBisect n fuel mid hi
        else integerSqrtBisect n fuel lo mid

/-- Accept `k` as the square root of `n` exactly when `k * k = n`. -/
def checkSquareRoot? (n k : Nat) : Option Nat :=
  if k * k = n then some k else none

/-- An accepted root squares to the radicand. -/
theorem mul_self_eq_of_checkSquareRoot? {n k k' : Nat} (h : checkSquareRoot? n k = some k') :
    k' * k' = n := by
  unfold checkSquareRoot? at h
  split_ifs at h with hk
  exact Option.some.inj h ▸ hk

/-- The square root of a natural numeral that is a perfect square: the bisection candidate,
accepted only if its square is `n`. The fuel `n + 1` exceeds the number of halvings of the
initial bracket `[0, n + 1)`. -/
def perfectSquareRoot? (n : Nat) : Option Nat :=
  checkSquareRoot? n (integerSqrtBisect n (n + 1) 0 (n + 1))

/-- An accepted natural root squares to the radicand. -/
theorem mul_self_eq_of_perfectSquareRoot? {n k : Nat} (h : perfectSquareRoot? n = some k) :
    k * k = n :=
  mul_self_eq_of_checkSquareRoot? h

/-- The square root of a rational numeral when it is nonnegative and its numerator and
denominator are perfect squares. -/
def perfectSquareRootRat? (q : Rat) : Option Rat :=
  if q < 0 then none
  else
    match perfectSquareRoot? q.num.toNat, perfectSquareRoot? q.den with
    | some k, some m => some ((k : Rat) / (m : Rat))
    | _, _ => none

/-- An accepted rational root is the real square root of the radicand
(`Real.sqrt_mul_self`). -/
theorem sqrt_cast_eq_of_perfectSquareRootRat? {q r : Rat}
    (h : perfectSquareRootRat? q = some r) : Real.sqrt (q : ℝ) = (r : ℝ) := by
  unfold perfectSquareRootRat? at h
  split_ifs at h with hq
  split at h
  · rename_i k m hk hm
    obtain rfl := Option.some.inj h
    have hnum : (q.num : ℝ) = k * k := by
      rw [← Int.toNat_of_nonneg (Rat.num_nonneg.mpr (not_lt.mp hq)),
        ← mul_self_eq_of_perfectSquareRoot? hk]
      push_cast
      ring
    have hden : (q.den : ℝ) = m * m := by
      exact_mod_cast (mul_self_eq_of_perfectSquareRoot? hm).symm
    rw [Rat.cast_def, hnum, hden, mul_div_mul_comm, Real.sqrt_mul_self (by positivity)]
    push_cast
    ring
  · cases h

/-- The exact rational value of a numeral radicand: a literal `nat`, `int`, or `rat` node, or a
quotient of two such literals with nonzero denominator. -/
def radicandValue? {ι : Type*} : Verified.Expr ι → Option Rat
  | .div a b =>
      match NumericLiteral.parse? a, NumericLiteral.parse? b with
      | some qa, some qb => if qb = 0 then none else some (qa / qb)
      | _, _ => none
  | expr => NumericLiteral.parse? expr

/-- A radicand with a recognized value evaluates to that value. -/
theorem eval_radicandValue? {ι : Type*} (ρ : ι → ℝ) (expr : Verified.Expr ι) (q : Rat)
    (h : radicandValue? expr = some q) : expr.eval ρ = (q : ℝ) := by
  cases expr
  case div a b =>
    simp only [radicandValue?] at h
    split at h
    · rename_i qa qb ha hb
      split_ifs at h
      obtain rfl := Option.some.inj h
      simp [NumericLiteral.eval_parse?_eq_some ρ a qa ha,
        NumericLiteral.eval_parse?_eq_some ρ b qb hb]
    · cases h
  all_goals exact NumericLiteral.eval_parse?_eq_some ρ _ q h

/-- Evaluate one square-root node whose radicand is a perfect-square numeral; every other node
is left unchanged. -/
def sqrtNumeralCleanup {ι : Type*} : Verified.Expr ι → Verified.Expr ι
  | .sqrt a =>
      match radicandValue? a with
      | some q =>
          match perfectSquareRootRat? q with
          | some r => mkRatConst r
          | none => .sqrt a
      | none => .sqrt a
  | expr => expr

/-- The node rewrite preserves evaluation. -/
theorem eval_sqrtNumeralCleanup {ι : Type*} (ρ : ι → ℝ) (expr : Verified.Expr ι) :
    (sqrtNumeralCleanup expr).eval ρ = expr.eval ρ := by
  cases expr
  case sqrt a =>
    cases hq : radicandValue? a with
    | none => simp [sqrtNumeralCleanup, hq]
    | some q =>
        cases hr : perfectSquareRootRat? q with
        | none => simp [sqrtNumeralCleanup, hq, hr]
        | some r =>
            simp only [sqrtNumeralCleanup, hq, hr, eval_mkRatConst, Verified.Expr.eval]
            rw [eval_radicandValue? ρ a q hq, sqrt_cast_eq_of_perfectSquareRootRat? hr]
  all_goals rfl

/-- Apply the numeral square-root evaluation to a rebuilt node. The inherited conditions are
passed through and no new one is recorded. -/
def sqrtNumeralTopAfter {ι : Type*} (rebuilt : Verified.Expr ι)
    (inherited : List (Verified.Expr ι)) : Alg.NormResult ι :=
  { expr := sqrtNumeralCleanup rebuilt, nonzero := inherited }

/-- Recursive numeral square-root evaluation throughout an expression. -/
def sqrtNumeralDeepCleanup {ι : Type*} [DecidableEq ι] : Verified.Expr ι → Alg.NormResult ι :=
  BottomUp.run sqrtNumeralTopAfter

/-- The recursive evaluation records no side condition. -/
theorem sqrtNumeralDeepCleanup_nonzero {ι : Type*} [DecidableEq ι] (expr : Verified.Expr ι) :
    (sqrtNumeralDeepCleanup expr).nonzero = [] := by
  induction expr <;> simp_all [sqrtNumeralDeepCleanup, BottomUp.run, sqrtNumeralTopAfter]

/-- Soundness of the recursive evaluation. -/
theorem eval_sqrtNumeralDeepCleanup {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι) :
    (sqrtNumeralDeepCleanup expr).expr.eval ρ = expr.eval ρ :=
  BottomUp.eval_run sqrtNumeralTopAfter (fun _ _ h ↦ h)
    (fun ρ rebuilt _ _ ↦ eval_sqrtNumeralCleanup ρ rebuilt) ρ expr
    (fun d hd ↦ by
      rw [show (BottomUp.run sqrtNumeralTopAfter expr).nonzero = [] from
        sqrtNumeralDeepCleanup_nonzero expr] at hd
      simp at hd)

/-- Side pass evaluating square roots of perfect-square numerals; it records no obligation. -/
def sqrtNumeralSidePass {ι : Type*} [DecidableEq ι] : SidePass ι where
  name := "sqrt-numeral"
  run := sqrtNumeralDeepCleanup
  sound ρ expr _ := eval_sqrtNumeralDeepCleanup ρ expr

end CAS.Verified.Expr

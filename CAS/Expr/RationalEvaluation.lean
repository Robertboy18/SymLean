/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Syntax

/-!
# Exact rational evaluation of verified expressions

`evalRat?` is an executable exact evaluator for the rational algebraic fragment of the
symbolic expression language at a rational environment. It is partial: constants such as `π`
and `e`, transcendental functions, square roots, malformed rational literals, and division by
zero return `none`.

`evalRat?_sound` relates every successful computation to the real-valued `Verified.Expr.eval`
semantics. Numerical backends can therefore use successful rational results without
a second semantics for expressions.
-/

@[expose] public section

namespace CAS.Verified.Expr

/--
Evaluate the rational algebraic fragment of a verified expression exactly.

The environment supplies exact rational values for variables. Unsupported
transcendental expressions and invalid divisions fail closed.
-/
def evalRat? {ι : Type*} (ρ : ι → ℚ) : Verified.Expr ι → Option ℚ
  | .nat n => some n
  | .int n => some n
  | .rat num den =>
      if den = 0 then none else some ((num : ℚ) / (den : ℚ))
  | .pi | .e => none
  | .var i => some (ρ i)
  | .add a b => do
      let x ← evalRat? ρ a
      let y ← evalRat? ρ b
      pure (x + y)
  | .mul a b => do
      let x ← evalRat? ρ a
      let y ← evalRat? ρ b
      pure (x * y)
  | .sub a b => do
      let x ← evalRat? ρ a
      let y ← evalRat? ρ b
      pure (x - y)
  | .div a b => do
      let x ← evalRat? ρ a
      let y ← evalRat? ρ b
      if y = 0 then none else pure (x / y)
  | .neg a => do
      let x ← evalRat? ρ a
      pure (-x)
  | .pow a n => do
      let x ← evalRat? ρ a
      pure (x ^ n)
  | .sin _ | .cos _ | .atan _ | .asin _ | .acos _ | .exp _ | .log _ | .sqrt _ => none
  | .rpow _ _ => none

/-- Successful exact rational evaluation agrees with real expression evaluation. -/
theorem evalRat?_sound {ι : Type*} (ρ : ι → ℚ)
    {expr : Verified.Expr ι} {q : ℚ}
    (h : evalRat? ρ expr = some q) :
    expr.eval (fun i ↦ (ρ i : ℝ)) = (q : ℝ) := by
  induction expr generalizing q with
  | pi | e | sin | cos | atan | asin | acos | exp | log | sqrt | rpow => simp [evalRat?] at h
  | nat | int | var =>
    cases Option.some.inj h
    simp
  | rat num den =>
    obtain ⟨-, ⟨⟩⟩ := Option.ite_none_left_eq_some.mp h
    simp
  | add a b iha ihb | mul a b iha ihb | sub a b iha ihb =>
    simp only [evalRat?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    rcases h with ⟨x, ha, y, hb, rfl⟩
    simp only [Verified.Expr.eval, iha ha, ihb hb, Rat.cast_add, Rat.cast_mul, Rat.cast_sub]
  | div a b iha ihb =>
    rcases Option.bind_eq_some_iff.mp h with ⟨x, ha, h⟩
    rcases Option.bind_eq_some_iff.mp h with ⟨y, hb, h⟩
    split at h
    · contradiction
    · cases Option.some.inj h
      simp only [Verified.Expr.eval, iha ha, ihb hb, Rat.cast_div]
  | neg a ih | pow a n ih =>
    simp only [evalRat?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    rcases h with ⟨x, ha, rfl⟩
    simp only [Verified.Expr.eval, ih ha, Rat.cast_neg, Rat.cast_pow]

end CAS.Verified.Expr

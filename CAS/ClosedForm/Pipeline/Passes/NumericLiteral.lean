/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.Core -- shake: keep

/-!
# Exact numeric literals

One canonical interpretation `parse?` of the numeric leaves in a checked symbolic expression.
It rejects malformed rational literals, and `eval_parse?_eq_some` proves that every accepted
rational value agrees with real-valued expression evaluation.

`Verified.Expr` has three numeric literal constructors, `nat`, `int`, and `rat num den` (the
constants `pi` and `e` are leaves too, but not literals). The last one is syntax rather than a
normalized rational: nothing prevents `den = 0`, in which case `eval` returns `num / 0 = 0` by
totalized division. `parse?` maps the well-formed literals to `ℚ` and rejects a zero denominator,
so passes that fold or compare numeric coefficients (common-factor extraction, unit-ratio cleanup,
the literal bases and exponents of the real-power pass, numeral square roots) can work in `ℚ` and
transfer their results to `ℝ` through `eval_parse?_eq_some`.
-/

@[expose] public section

namespace CAS.Verified.Expr
namespace NumericLiteral

/-- Interpret a syntactically numeric literal as a normalized rational number.

Malformed rational literals with denominator `0` are rejected: Lean's real division is
total, but the checked symbolic language treats such literals as invalid for analytic use. -/
def parse? {ι : Type*} : Verified.Expr ι → Option Rat
  | .nat n => some (n : Rat)
  | .int z => some (z : Rat)
  | .rat num den =>
      if den = 0 then none else some (Rat.divInt num (den : Int))
  | _ => none

/-- A literal accepted by `parse?` evaluates to the cast of the parsed rational; in particular
`rat num den` with `den ≠ 0` evaluates to `num / den` in `ℝ`. -/
theorem eval_parse?_eq_some {ι : Type*} (ρ : ι → ℝ) :
    ∀ (expr : Verified.Expr ι) (q : Rat),
      parse? expr = some q → expr.eval ρ = (q : ℝ)
  | .nat n, _, rfl => by simp
  | .int z, _, rfl => by simp
  | .rat num den, q, h => by
      simp only [parse?] at h
      split_ifs at h
      obtain rfl := Option.some.inj h
      simp


end NumericLiteral
end CAS.Verified.Expr

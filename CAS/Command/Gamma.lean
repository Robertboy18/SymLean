/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Algebra.Basic
public import CAS.Command.SpecialFunctions
public import CAS.Analysis.SpecialFunctions.Gamma

/-!
# Values of the Gamma function: `#cas (gamma q)`

`#cas (gamma q)` evaluates `Real.Gamma q` at an integer or half-integer `q`, as Mathematica's
`Gamma[q]` does, and proves `Real.Gamma q = v` or `Real.Gamma q = a * √π / b`. Positive integers
give factorials, half-integers rational multiples of `√π`. At `0, -1, -2, …` Mathlib's
`Real.Gamma` is `0` (`Real.Gamma_neg_nat_eq_zero`), where Mathematica returns `ComplexInfinity`;
the report states Mathlib's value and says so.

## Main definitions

* `CAS.Command.Gamma.value?`: the exact value at an integer or half-integer.
* `CAS.Command.Gamma.factScript`: the proof of that value, shared with bare `cas`
  (`CAS.Command.AlgebraGoals`).
* `CAS.Command.Gamma.logGamma`: the report of the call `gamma q`.

## Implementation notes

Each value is one rewrite with a closed formula: `Real.Gamma_nat_eq_factorial` at the positive
integers, `Real.Gamma_nat_add_half` at `k + 1/2` and our
`CAS.Analysis.SpecialFunctions.Gamma_half_sub_nat` at `1/2 - k`, proved in
`CAS/Analysis/SpecialFunctions/Gamma.lean`. The factorial in the formula is evaluated by the
kernel and a `norm_num` step matches the printed value. A walk from `Γ (1) = 1` or
`Γ (1/2) = √π` to `q` one unit at a time with `Γ (s + 1) = s Γ (s)` would grow with `|q|`; with
the closed formulas the proof is one rewrite for every `|q| ≤ 1001/2`, the range of the command
(`inRange`).
-/

public meta section

namespace CAS.Command.Gamma

open Lean Elab Command Meta Term
open CAS.Command.InfoView

/-- Whether `|q| ≤ 1001/2`, the range in which values are computed. With `|q| = k + r / d` for
`k = ⌊|q|⌋`, `d = den q` and `r < d`, this holds exactly when `k < 500`, or `k = 500` and
`r ≤ d / 2`. We compare these rather than `2 |num q|` with `1001 d`, so that no number larger than
`|num q|` and `d` is formed. -/
def inRange (q : ℚ) : Bool :=
  let k := q.num.natAbs / q.den
  k < 500 || (k = 500 && q.num.natAbs % q.den ≤ q.den / 2)

/-- `n! = 1 · 2 ⋯ n`. -/
def factorial (n : Nat) : Nat := Id.run do
  let mut p := 1
  for i in [1:n + 1] do p := p * i
  return p

/-- `(2k - 1)‼ = 1 · 3 ⋯ (2k - 1)`, and `1` for `k = 0`. -/
def oddFactorial (k : Nat) : Nat := Id.run do
  let mut p := 1
  for i in [0:k] do p := p * (2 * i + 1)
  return p

/-- The value of `Γ q` as `(v, radical)`, meaning `v * √π` when `radical` and `v` otherwise, at
an integer `q ≥ 1` or a half-integer `q` with `|q| ≤ 1001/2`; `none` at the poles and
elsewhere. -/
def value? (q : ℚ) : Option (ℚ × Bool) :=
  if !inRange q then none
  else if q.den = 1 then
    if q ≤ 0 then none else some ((factorial (q.num.toNat - 1) : ℚ), false)
  else if q.den = 2 then
    if 0 < q then
      let k := (q - 1 / 2).num.toNat
      some ((oddFactorial k : ℚ) / ((2 ^ k : Nat) : ℚ), true)
    else
      let k := (1 / 2 - q).num.toNat
      let sign : ℚ := if k % 2 = 0 then 1 else -1
      some (sign * ((2 ^ k : Nat) : ℚ) / (oddFactorial k : ℚ), true)
  else none

/-- The value `v` or `v * √π` as printed: `24`, `√π`, `-2√π`, `3√π/4`. -/
def valueText (v : ℚ) (radical : Bool) : String :=
  if !radical then toString v
  else
    let sign := if v.num < 0 then "-" else ""
    let coefficient := if v.num.natAbs = 1 then "" else toString v.num.natAbs
    let denominator := if v.den = 1 then "" else s!"/{v.den}"
    s!"{sign}{coefficient}√π{denominator}"

/-- The term `v`, or `a * √π / b` for `v = a / b`, written `√π`, `-√π`, `a * √π`, `-a * √π` and
without `/ b` when `b = 1`. -/
def radicalSyntax (v : ℚ) (radical : Bool) : TermElabM (TSyntax `term) := do
  if !radical then
    return (← `(($(← ratSyntax v) : ℝ)))
  let a : TSyntax `term := ⟨Syntax.mkNumLit (toString v.num.natAbs)⟩
  let numerator ←
    if v.num.natAbs = 1 then (if v.num < 0 then `(-√Real.pi) else `(√Real.pi))
    else if v.num < 0 then `(-$a * √Real.pi)
    else `($a * √Real.pi)
  if v.den = 1 then
    return numerator
  let b : TSyntax `term := ⟨Syntax.mkNumLit (toString v.den)⟩
  `($numerator / $b)

/-- A tactic proving `fact : Real.Gamma q = v` (or `= a * √π / b`) for `value? q = some (v, _)`,
by one rewrite with `Real.Gamma_nat_eq_factorial`, `Real.Gamma_nat_add_half` or
`CAS.Analysis.SpecialFunctions.Gamma_half_sub_nat`. -/
def factScript (q : ℚ) (fact : TSyntax `ident) : TermElabM (Option (TSyntax `tactic)) := do
  let some (v, _) := value? q | return none
  let qT ← `(($(← ratSyntax q) : ℝ))
  let rhs ← radicalSyntax v (q.den = 2)
  let num (n : Nat) : TSyntax `term := ⟨Syntax.mkNumLit (toString n)⟩
  -- The formula, with its argument written as `q` and its factorial evaluated.
  let formula ← if q.den = 1 then
      let n := q.num.toNat - 1
      `(tactic| (
        have h := Real.Gamma_nat_eq_factorial $(num n)
        rw [show ((($(num n) : ℕ)) : ℝ) + 1 = $qT by norm_num,
          show Nat.factorial $(num n) = $(num (factorial n)) by decide +kernel] at h))
    else if 0 < q then
      let k := (q - 1 / 2).num.toNat
      `(tactic| (
        have h := Real.Gamma_nat_add_half $(num k)
        rw [show ((($(num k) : ℕ)) : ℝ) + 1 / 2 = $qT by norm_num,
          show Nat.doubleFactorial (2 * $(num k) - 1) = $(num (oddFactorial k)) by
            decide +kernel] at h))
    else
      let k := (1 / 2 - q).num.toNat
      `(tactic| (
        have h := CAS.Analysis.SpecialFunctions.Gamma_half_sub_nat $(num k)
        rw [show (1 / 2 - ((($(num k) : ℕ)) : ℝ)) = $qT by norm_num,
          show Nat.doubleFactorial (2 * $(num k) - 1) = $(num (oddFactorial k)) by
            decide +kernel] at h))
  -- `2 ^ k` with `k ≤ 501` is above `norm_num`'s default bound of `256` on evaluated powers.
  return some (← `(tactic|
    have $fact : Real.Gamma $qT = $rhs := by
      $formula:tactic
      rw [h] <;> (set_option exponentiation.threshold 1024 in norm_num)))

/-- Run `#cas (gamma q)` for the argument `input`. -/
def logGamma (ref : Syntax) (input : Syntax) : CommandElabM Unit := do
  let q ← SpecialFunctions.parseRational "gamma" input
  unless q.den = 1 || q.den = 2 do
    throwErrorAt input "gamma: exact values are computed at integers and half-integers; \
      `{Arguments.argumentText input}` is neither"
  unless inRange q do
    throwErrorAt input "gamma: exact values are computed for |q| ≤ 1001/2; \
      `{Arguments.argumentText input}` is outside that range"
  let pole := q.den = 1 && q ≤ 0
  let some (v, radical) := (if pole then some (0, false) else value? q)
    | throwErrorAt input "gamma: internal error"
  let qT ← liftTermElabM do `(($(← ratSyntax q) : ℝ))
  let statement ← liftTermElabM do `(Real.Gamma $qT = $(← radicalSyntax v radical))
  let fact := mkIdent `hΓ
  let tactic ← liftTermElabM do
    if pole then
      let n : TSyntax `term := ⟨Syntax.mkNumLit (toString q.num.natAbs)⟩
      `(tactic| (
        have h := Real.Gamma_neg_nat_eq_zero $n
        rw [show -((($n : ℕ)) : ℝ) = $qT by norm_num] at h
        exact h))
    else
      let some script ← factScript q fact | throwError "gamma: internal error"
      `(tactic| ($script:tactic; exact $fact:ident))
  let (proposition, proof) ← liftTermElabM <| Algebra.proveStatement "gamma" statement tactic
  logReport ref {
    domain := "ℝ"
    input := toString q
    inputType := "rational number"
    output := if pole then s!"0 (Mathlib's value at the pole {q}; Mathematica: ComplexInfinity)"
      else valueText v radical
    outputType := "exact value of Γ"
  } #[← liftTermElabM <| Algebra.checkedEvidence "gamma"
    (if pole then "Mathlib's Gamma at a pole" else "Gamma by a closed formula")
    proposition proof]

end CAS.Command.Gamma

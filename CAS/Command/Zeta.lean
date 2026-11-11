/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.SpecialFunctions.Bernoulli
public import CAS.Command.Arguments
public import CAS.Command.InfiniteSum
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.ZetaValues
public meta import CAS.Analysis.SpecialFunctions.Bernoulli

/-!
# Bernoulli numbers and values of the zeta function

* `#cas (BernoulliB n)` is the Bernoulli number `Bₙ`, as Mathematica's `BernoulliB[n]`, with
  Mathlib's convention `B₁ = -1/2` (Mathlib's `bernoulli`; `bernoulli'` has `B'₁ = 1/2`). The
  theorem is `bernoulli n = q` in `ℚ`.
* `#cas (zeta s)` is `ζ(s)` at an integer `s`, as Mathematica's `Zeta[s]`, for Mathlib's
  `riemannZeta`: at even `s = 2k > 0` the theorem is `riemannZeta s = q π ^ s` (Mathlib's
  `riemannZeta_two_mul_nat`), at `s = -k ≤ 0` it is `riemannZeta s = q`
  (`riemannZeta_neg_nat_eq_bernoulli`). At `s = 1`, the pole, the call is refused: Mathlib gives
  `riemannZeta 1` a value (`riemannZeta_one`), but it is not a value of the series. At odd
  `s ≥ 3` it refuses as an unsupported formula.
* `#cas [sum k a ∞] (c / k ^ (2m))` for rational `c ≠ 0` and natural `1 ≤ a ≤ 50` proves
  `HasSum (fun k : ℕ ↦ c / ((k + a : ℕ) : ℝ) ^ (2m)) (c (q π ^ (2m) - ∑_{0 < j < a} 1 / j ^ (2m)))`
  from Mathlib's `hasSum_zeta_nat` shifted by `a` (`hasSum_nat_add_iff'`), as Mathematica's
  `Sum[c/k^(2m), {k, a, Infinity}]`. The infinite sums of `CAS.Command.InfiniteSum` take every
  summand of another form.

The Bernoulli numbers come from the integer numerators
`CAS.Analysis.SpecialFunctions.bernoulliNumerators`: the command computes them to state the number,
and the kernel evaluates them again and decides the rational equation (`decide +kernel`) after
`bernoulli_eq_numerators`. The index is at most `maxBernoulliIndex`: `n ≤ 60`, `s ≤ 60`,
`s ≥ -59`, `2m ≤ 60`.
-/

public meta section

namespace CAS.Command.Zeta

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Analysis.SpecialFunctions

/-- The largest index of a Bernoulli number these commands compute. -/
def maxBernoulliIndex : Nat := 60

/-- The Bernoulli number `Bₙ` (Mathlib's `bernoulli`), from the integer numerators of
`bernoulli_eq_numerators`. -/
def bernoulliValue (n : Nat) : ℚ := ((bernoulliNumerators n).getD n 0 : ℚ) / (n + 1).factorial

/-- A rational as term syntax of type `ℚ`. -/
def ratTerm (q : ℚ) : TermElabM (TSyntax `term) := do `(($(← ratSyntax q) : ℚ))

/-- A tactic proving `fact : bernoulli n = Bₙ`: the kernel evaluates the integer numerators of
`bernoulli_eq_numerators` and decides the rational equation. -/
def bernoulliFact (n : Nat) (fact : TSyntax `ident) : TermElabM (TSyntax `tactic) := do
  let nLit : TSyntax `term := ⟨Syntax.mkNumLit (toString n)⟩
  `(tactic| have $fact : bernoulli $nLit = $(← ratTerm (bernoulliValue n)) := by
      rw [CAS.Analysis.SpecialFunctions.bernoulli_eq_numerators]
      decide +kernel)

/-- Read a natural number, or refuse. -/
def parseNatural (operation : String) (stx : Syntax) : CommandElabM Nat := do
  let q ← SpecialFunctions.parseRational operation stx
  unless q.den = 1 && 0 ≤ q do throwErrorAt stx "{operation}: expected a natural number"
  return q.num.toNat

/-- `q π ^ e` in the calculator printer: `pi^e/d`, `n*pi^e/d` or `n*pi^e`, with a leading `-`
when `q < 0`. -/
def piText (q : ℚ) (e : Nat) : String := rationalMultipleText q (.pow .pi e)

/-- `|q| π ^ e` as complex or real term syntax (the sign of `q` is the caller's). -/
def piSyntax (q : ℚ) (e : Nat) (complex : Bool) : TermElabM (TSyntax `term) := do
  let eLit : TSyntax `term := ⟨Syntax.mkNumLit (toString e)⟩
  let power ← if complex then `((Real.pi : ℂ) ^ $eLit) else `(Real.pi ^ $eLit)
  let numerator ← if q.num = 1 then pure power else
    let n : TSyntax `term := ⟨Syntax.mkNumLit (toString q.num.natAbs)⟩
    `($n * $power)
  if q.den = 1 then return numerator
  let d : TSyntax `term := ⟨Syntax.mkNumLit (toString q.den)⟩
  `($numerator / $d)

/-- Run `#cas (BernoulliB n)` for the argument `input`. -/
def logBernoulli (ref : Syntax) (input : Syntax) : CommandElabM Unit := do
  let n ← Arguments.natArgument "BernoulliB" "its argument" ⟨input⟩
  if n > maxBernoulliIndex then
    throwErrorAt input "BernoulliB computes Bₙ for n ≤ {maxBernoulliIndex}"
  let value := bernoulliValue n
  let nLit : TSyntax `term := ⟨Syntax.mkNumLit (toString n)⟩
  let (proposition, proof) ← liftTermElabM do
    let fact := mkIdent `hB
    let statement ← `(bernoulli $nLit = $(← ratTerm value))
    let script ← bernoulliFact n fact
    Algebra.proveStatement "BernoulliB" statement (← `(tactic| ($script; exact $fact:ident)))
  logReport ref {
    domain := "ℚ (Mathlib's bernoulli, B₁ = -1/2)"
    input := toString n
    inputType := "natural number"
    output := toString value
    outputType := "Bernoulli number"
  } #[← liftTermElabM <| Algebra.checkedEvidence "BernoulliB"
    "Bernoulli number from the kernel-evaluated numerators" proposition proof]

/-- Run `#cas (zeta s)` for the argument `input`. -/
def logZeta (ref : Syntax) (input : Syntax) : CommandElabM Unit := do
  let s ← SpecialFunctions.parseRational "zeta" input
  unless s.den = 1 do throwErrorAt input "zeta: exact values are computed at integers"
  let s := s.num
  if s = 1 then
    throwErrorAt input "zeta: s = 1 is the pole of ζ; Mathlib's riemannZeta 1 is a convention, \
      not a value of the series, and is not reported"
  if s > 0 && s % 2 = 1 then
    throwErrorAt input "zeta: unsupported formula at the odd integer \
      `{Arguments.argumentText input}`; exact values are computed at even positive and at \
      nonpositive integers"
  let fact := mkIdent `hB
  if s > 0 then
    let k := s.toNat / 2
    if 2 * k > maxBernoulliIndex then
      throwErrorAt input "zeta: exact values are computed for s ≤ {maxBernoulliIndex}"
    -- `ζ(2k) = (-1) ^ (k + 1) 2 ^ (2k - 1) B_{2k} / (2k)! π ^ (2k)`.
    let q : ℚ := (-1) ^ (k + 1) * 2 ^ (2 * k - 1) * bernoulliValue (2 * k) /
      ((2 * k).factorial : ℚ)
    let kLit : TSyntax `term := ⟨Syntax.mkNumLit (toString k)⟩
    let sLit : TSyntax `term := ⟨Syntax.mkNumLit (toString s.toNat)⟩
    let (proposition, proof) ← liftTermElabM do
      let statement ← `(riemannZeta ($sLit : ℂ) = $(← piSyntax q (2 * k) true))
      let script ← bernoulliFact (2 * k) fact
      Algebra.proveStatement "zeta" statement (← `(tactic| (
        $script:tactic
        have h := riemannZeta_two_mul_nat (k := $kLit) (by norm_num)
        rw [show 2 * $kLit = $sLit by norm_num, $fact:ident] at h
        rw [show (($sLit : ℂ)) = 2 * (($kLit : ℕ) : ℂ) by norm_num, h]
        norm_num [Nat.factorial]
        ring)))
    logReport ref {
      domain := "ℂ (Mathlib's riemannZeta)"
      input := s!"s = {s}"
      inputType := "even positive integer"
      output := piText q (2 * k)
      outputType := "exact value of ζ"
    } #[← liftTermElabM <| Algebra.checkedEvidence "zeta"
      "ζ(2k) by Bernoulli numbers (riemannZeta_two_mul_nat)" proposition proof]
  else
    let k := s.natAbs
    -- `B_{k+1}` needs `k + 1 ≤ maxBernoulliIndex`; we compare `k` itself, which forms no
    -- number above the argument.
    if k ≥ maxBernoulliIndex then
      throwErrorAt input "zeta: exact values are computed for s ≥ {1 - (maxBernoulliIndex : Int)}"
    -- `ζ(-k) = (-1) ^ k B_{k+1} / (k + 1)`.
    let q : ℚ := (-1) ^ k * bernoulliValue (k + 1) / (k + 1 : ℚ)
    let kLit : TSyntax `term := ⟨Syntax.mkNumLit (toString k)⟩
    let (proposition, proof) ← liftTermElabM do
      let sT ← if k = 0 then `((0 : ℂ)) else `((-$kLit : ℂ))
      let qT ← `(($(← ratSyntax q) : ℂ))
      let statement ← `(riemannZeta $sT = $qT)
      let script ← bernoulliFact (k + 1) fact
      Algebra.proveStatement "zeta" statement (← `(tactic| (
        $script:tactic
        have h := riemannZeta_neg_nat_eq_bernoulli $kLit
        rw [show $kLit + 1 = $(⟨Syntax.mkNumLit (toString (k + 1))⟩) by norm_num, $fact:ident] at h
        norm_num at h ⊢
        try exact h
        try (rw [h]; norm_num))))
    logReport ref {
      domain := "ℂ (Mathlib's riemannZeta)"
      input := s!"s = {s}"
      inputType := "nonpositive integer"
      output := toString q
      outputType := "exact value of ζ"
    } #[← liftTermElabM <| Algebra.checkedEvidence "zeta"
      "ζ(-k) by Bernoulli numbers (riemannZeta_neg_nat_eq_bernoulli)" proposition proof]

/-- The summand `c / k ^ e` (with `c` rational and `e` a natural), or `none`. -/
def zetaSummand? (f : Verified.Expr (Fin 1)) : Option (ℚ × Nat) :=
  match f with
  | .div c (.pow (.var _) e) =>
      if c.containsVar 0 then none else (Verified.Expr.evalRat? (fun _ ↦ 0) c).map (·, e)
  | .mul c (.div (.nat 1) (.pow (.var _) e)) =>
      if c.containsVar 0 then none else (Verified.Expr.evalRat? (fun _ ↦ 0) c).map (·, e)
  | _ => none

/-- Run `#cas [sum k a ∞] (c / k ^ (2m))`. A summand of another form is left to the infinite sums
of `CAS.Command.InfiniteSum` (`throwUnsupportedSyntax`). -/
def logZetaSum (ref : Syntax) (k : TSyntax `ident) (aStx : Syntax) (input : Syntax) :
    CommandElabM Unit := do
  let reified? ← try some <$> parseExact input [k.getId] catch _ => pure none
  let some f := (match reified? with
      | some ⟨[_], expression, _⟩ => some expression
      | _ => none)
    | throwUnsupportedSyntax
  let some (c, e) := zetaSummand? f | throwUnsupportedSyntax
  let a ← parseNatural "sum" aStx
  if a = 0 then
    throwErrorAt aStx "sum: the summand {c}/{k.getId}^{e} is undefined at {k.getId} = 0; start \
      the sum at 1"
  if a > 50 then throwErrorAt aStx "sum: the lower bound is at most 50"
  if e < 2 then throwErrorAt input "sum: the series of 1/{k.getId}^{e} diverges"
  if e % 2 = 1 then
    throwErrorAt input "sum: unsupported formula for the odd exponent {e} (ζ({e}))"
  if e > maxBernoulliIndex then
    throwErrorAt input "sum: exponents up to {maxBernoulliIndex} are supported"
  if c = 0 then throwErrorAt input "sum: the summand is zero"
  let m := e / 2
  let q : ℚ := (-1) ^ (m + 1) * 2 ^ (e - 1) * bernoulliValue e / (e.factorial : ℚ)
  let r : ℚ := ((List.range a).drop 1).foldl (fun total j ↦ total + 1 / (j : ℚ) ^ e) 0
  let fact := mkIdent `hB
  let n := mkIdent k.getId
  let eLit : TSyntax `term := ⟨Syntax.mkNumLit (toString e)⟩
  let mLit : TSyntax `term := ⟨Syntax.mkNumLit (toString m)⟩
  let aLit : TSyntax `term := ⟨Syntax.mkNumLit (toString a)⟩
  let (proposition, proof) ← liftTermElabM do
    let cT ← `(($(← ratSyntax c) : ℝ))
    let main ← if c * q = 1 then `(Real.pi ^ $eLit)
      else if 0 < c * q then piSyntax (c * q) e false
      else `(-$(← piSyntax (-(c * q)) e false))
    let value ← if a = 1 then pure main
      else if c * r < 0 then `($main + ($(← ratSyntax (-(c * r))) : ℝ))
      else `($main - ($(← ratSyntax (c * r)) : ℝ))
    let statement ← `(HasSum (fun $n:ident : ℕ ↦ $cT / ((($n + $aLit : ℕ)) : ℝ) ^ $eLit) $value)
    let script ← bernoulliFact e fact
    Algebra.proveStatement "sum" statement (← `(tactic| (
      $script:tactic
      have hz := hasSum_zeta_nat (k := $mLit) (by norm_num)
      rw [show 2 * $mLit = $eLit by norm_num, $fact:ident] at hz
      have hc := ((hasSum_nat_add_iff' $aLit).mpr hz).mul_left $cT
      convert hc using 1
      · funext $n:ident
        push_cast
        ring
      · norm_num [Finset.sum_range_succ, Nat.factorial]
        try ring)))
  let valueText := if a = 1 then piText (c * q) e
    else if c * r < 0 then s!"{piText (c * q) e} + {-(c * r)}"
    else s!"{piText (c * q) e} - {c * r}"
  logReport ref {
    domain := s!"{k.getId} ∈ ℕ, {k.getId} ≥ {a}"
    input := s!"{c}/{k.getId}^{e}"
    inputType := "summand"
    output := valueText
    outputType := "sum of the series (ζ value)"
  } #[← liftTermElabM <| Algebra.checkedEvidence "sum"
    "Sum of the series by hasSum_zeta_nat" proposition proof]

end CAS.Command.Zeta

namespace CAS.Command

open Lean Elab Command

/-- The sum `∑_{k ≥ a} c / k ^ (2m)` for rational `c ≠ 0`, `1 ≤ a ≤ 50` and `2 ≤ 2m ≤ 60`, by
the values of the zeta function, as Mathematica's `Sum[c/k^(2m), {k, a, Infinity}]`; any other
summand is left to the infinite sums of `CAS.Command.InfiniteSum`. -/
elab_rules : command
  | `(#cas [sum $k:ident $a:term ∞] $f:term) => Zeta.logZetaSum f k a f

end CAS.Command

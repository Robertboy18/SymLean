/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.NIntegrate
public import CAS.Continuum.Quadrature.PowerSubstitution
public meta import CAS.Continuum.Quadrature.PowerSubstitution
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Integrands with a square root or a fractional power at `0`

`#cas [nintegrate x in [0, b]] f`, where `f` contains `sqrt x` or `x ^ (p / q : ℝ)`, substitutes
`x = u ^ k` with `k` the common denominator of the exponents, so that the integrand
`f (u ^ k) k u ^ (k - 1)` on `[0, b ^ (1 / k)]` is smooth, and certifies it with the batch
Simpson check (`of_powerIntegralCheck`). When `b` is not the `k`-th power of a rational, the
interval is split at a rational `c ^ k < b`, the part `[c ^ k, b]` is checked directly, and the
two parts are added with the rounding error in the bound (`of_powerSplitCheck`). The theorem is
`|∫ x in 0..b, f x - c| ≤ 10 ^ (-d)`, as for smooth integrands. Integrands without such a
power of `x`, or on other intervals, go to the general `nintegrate` command of
`CAS/Command/NIntegrate.lean`.

## Implementation notes

The rule here is tried before the one of `CAS/Command/NIntegrate.lean`. It declines
(`throwUnsupportedSyntax`) unless the interval is `[0, b]` with `b > 0`, `rootIndex` finds a root
of `x` and `BatchSimpson.substPower` rewrites the integrand, and also for a digit count outside 1
to 12, which the rule there refuses. The search proposes `k` (`rootIndex`), the split point
(`splitPoint`, used when `ratRoot?` finds no rational `k`-th root of `b`), and the panel counts
and values of `NIntegrate.batchSearch` for `BatchSimpson.powerIntegrand k G` and, in the split
case, for `f` on `[c ^ k, b]`. There both parts are searched to `d + 2` places within
`10 ^ (-d) / 4` each, which leaves half of the error `10 ^ (-d)` for rounding their sum to `d`
places. The validity of the integrands comes from `CAS.CEGA.Integration.validityOn?`. The kernel
decides the Boolean hypothesis of `of_powerIntegralCheck` or `of_powerSplitCheck`
(`CAS.CEGA.Elaboration.decideClosedCertificate`), so it recomputes `substPower k f = some G` as
well as the panels. These theorems, the change of variables `integral_eq_of_substPower` and the
account of what is classical are in `CAS/Continuum/Quadrature/PowerSubstitution.lean`.
-/

public meta section

namespace CAS.Command.NIntegrateSingular

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Continuum
open CAS.Command.NIntegrate

/-- The common denominator of the powers of the variable under `sqrt` and `^ (p / q)`. -/
partial def rootIndex : Verified.Expr (Fin 1) → Nat
  | .sqrt (.var _) => 2
  | .rpow (.var _) (.div (.nat p) (.nat q)) => if q = 0 then 1 else q / Nat.gcd p q
  | .rpow (.var _) (.rat p q) => if q = 0 then 1 else q / Nat.gcd p.natAbs q
  | .add a b | .mul a b | .sub a b | .div a b | .rpow a b => Nat.lcm (rootIndex a) (rootIndex b)
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a
  | .sqrt a => rootIndex a
  | _ => 1

/-- The integer `k`-th root of `n`, rounded down. -/
def iroot (n k : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := n + 1
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if mid ^ k ≤ n then lo := mid else hi := mid
  return lo

/-- The rational `c` with `c ^ k = q`, when there is one. -/
def ratRoot? (q : ℚ) (k : Nat) : Option ℚ :=
  if q < 0 then none else
  let n := iroot q.num.toNat k
  let d := iroot q.den k
  if n ^ k = q.num.toNat && d ^ k = q.den then some ((n : ℚ) / d) else none

/-- A rational `c > 0` with `c ^ k < b`, close to `b ^ (1 / k)` from below. -/
def splitPoint (b : ℚ) (k : Nat) : ℚ := Id.run do
  for e in [4:20] do
    let scale : Nat := 2 ^ e
    let c : ℚ := (iroot ((b * (scale : ℚ) ^ k).floor.toNat) k : ℚ) / scale
    if 0 < c && c ^ k < b then return c
  return 0

/-- Run `#cas [nintegrate x in [0, b]] f` for an integrand with a root of `x`. -/
def logSingular (ref : Syntax) (digits : Nat) (coordinate : TSyntax `ident) (aStx bStx : Syntax)
    (input : Syntax) : CommandElabM Unit := do
  if digits = 0 || digits > 12 then throwUnsupportedSyntax
  let a ← SpecialFunctions.parseRational "nintegrate" aStx
  let b ← SpecialFunctions.parseRational "nintegrate" bStx
  unless a = 0 && 0 < b do throwUnsupportedSyntax
  let reified ← parseExact input [coordinate.getId]
  let expr : Verified.Expr (Fin 1) ← match reified with
    | ⟨[_], expression, _⟩ => pure expression
    | _ => throwUnsupportedSyntax
  let k := rootIndex expr
  unless k > 1 do throwUnsupportedSyntax
  let some G := BatchSimpson.substPower k expr | throwUnsupportedSyntax
  let integrand := BatchSimpson.powerIntegrand k G
  let scale : ℚ := 10 ^ digits
  let tolerance : ℚ := 1 / scale
  let renderValue (v : ℚ) : String :=
    if v < 0 then "-" ++ Digits.renderDecimal (v * scale).num.natAbs digits
    else Digits.renderDecimal (v * scale).num.natAbs digits
  let budget := max (maxHeartbeats.get (← getOptions)) 1000000
  let result ← liftTermElabM <| withTheReader Core.Context (fun context ↦
      { context with maxHeartbeats := budget * 1000 }) <| withCurrHeartbeats do
    let quoted ← quoteVerifiedExpr expr
    let quotedG ← quoteVerifiedExpr G
    let quotedF ← quoteVerifiedExpr integrand
    let derivative := integrand.symbolicDerivative 4
    let quote := SpecialFunctions.quoteRat
    match ratRoot? b k with
    | some c =>
        let some validity ← CAS.CEGA.Integration.validityOn? quotedF 0 c quote
          | throwError "nintegrate: the integrand after the substitution x = u ^ {k} is not \
              smooth on [0, {c}]"
        let precision := DigitsEval.precisionFor digits
        let some (v, panels) := batchSearch precision integrand derivative 0 c digits tolerance
          | throwError "nintegrate: no batch certificate with at most 1024 panels"
        let partialProof ← mkAppOptM ``BatchSimpson.of_powerIntegralCheck
          #[some (CAS.CEGA.Integration.quotePrecision precision), some quoted, some quotedG,
            some (← quoteVerifiedExpr derivative), some (toExpr k), some (← quote c),
            some (← quote b), some (toExpr panels), some (← SpecialFunctions.quoteDecimal digits v),
            some (← SpecialFunctions.quoteDecimal digits tolerance), some validity]
        let .forallE _ checkType _ _ ← whnfR (← inferType partialProof)
          | throwError "nintegrate: unexpected certificate theorem shape"
        let check ← CAS.CEGA.Elaboration.decideClosedCertificate checkType false
        let proof ← Digits.cleanProof (mkApp partialProof check)
          (Series.seriesCleanLemmas ++ [``Rat.cast_pow]) [``Verified.Expr.univariateEval]
        let report ← evidenceReportMessage
          #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
            s!"Substitution x = u ^ {k} and certified Simpson panels" proof]
        pure (v, m!"substitution x = u^{k} on [0, {b}], {panels} panels on [0, {c}] in u",
          report)
    | none =>
        let c := splitPoint b k
        unless 0 < c do throwError "nintegrate: no split point below {b}"
        let ck := c ^ k
        let some validity ← CAS.CEGA.Integration.validityOn? quotedF 0 c quote
          | throwError "nintegrate: the integrand after the substitution x = u ^ {k} is not \
              smooth on [0, {c}]"
        let some validity₂ ← CAS.CEGA.Integration.validityOn? quoted ck b quote
          | throwError "nintegrate: the integrand is not smooth on [{ck}, {b}]"
        let precision := DigitsEval.precisionFor (digits + 2)
        let places := digits + 2
        let partTolerance : ℚ := tolerance / 4
        let derivative₂ := expr.symbolicDerivative 4
        let some (v₁, panels₁) :=
            batchSearch precision integrand derivative 0 c places partTolerance
          | throwError "nintegrate: no batch certificate on [0, {c}] with at most 1024 panels"
        let some (v₂, panels₂) :=
            batchSearch precision expr derivative₂ ck b places partTolerance
          | throwError "nintegrate: no batch certificate on [{ck}, {b}] with at most 1024 panels"
        let v : ℚ := (⌊(v₁ + v₂) * scale + 1 / 2⌋ : ℚ) / scale
        let decimal := SpecialFunctions.quoteDecimal
        let partialProof ← mkAppOptM ``BatchSimpson.of_powerSplitCheck
          #[some (CAS.CEGA.Integration.quotePrecision precision), some quoted, some quotedG,
            some (← quoteVerifiedExpr derivative), some (← quoteVerifiedExpr derivative₂),
            some (toExpr k), some (← quote c), some (← quote ck), some (← quote b),
            some (toExpr panels₁),
            some (toExpr panels₂), some (← decimal places v₁), some (← decimal places v₂),
            some (← decimal places partTolerance), some (← decimal places partTolerance),
            some (← decimal digits v), some (← decimal digits tolerance), some validity,
            some validity₂]
        let .forallE _ checkType _ _ ← whnfR (← inferType partialProof)
          | throwError "nintegrate: unexpected certificate theorem shape"
        let check ← CAS.CEGA.Elaboration.decideClosedCertificate checkType false
        let proof ← Digits.cleanProof (mkApp partialProof check)
          (Series.seriesCleanLemmas ++ [``Rat.cast_pow]) [``Verified.Expr.univariateEval]
        let report ← evidenceReportMessage
          #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
            s!"Substitution x = u ^ {k} on [0, {ck}] and certified Simpson panels" proof]
        pure (v, m!"substitution x = u^{k} on [0, {ck}] with {panels₁} panels on [0, {c}] in \
          u; {panels₂} panels on [{ck}, {b}]", report)
  let (v, description, report) := result
  logReport ref {
    domain := s!"{coordinate.getId} ∈ [{a}, {b}]"
    input := surfaceText input
    inputType := "scalar ℝ"
    output := s!"{renderValue v} ± 10^-{digits}"
    outputType := "certified value of the integral"
  } #[computationNode "Certified quadrature" #[description], report]

end CAS.Command.NIntegrateSingular

namespace CAS.Command

open Lean Elab Command

elab_rules : command
  | `(#cas $cfg:optConfig [nintegrate $x:ident in [$a:term, $b:term]] $expr:term) => do
      NIntegrateSingular.logSingular expr (← parseDigitsOption "nintegrate" cfg 6) x a b expr

end CAS.Command

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Series
public import CAS.Continuum.Quadrature.BatchSimpson
public meta import CAS.Continuum.Quadrature.BatchSimpson
public import CAS.CEGA.Integration
public meta import CAS.CEGA.Integration
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Certified numerical integration: `#cas [nintegrate x in [a, b]]`

`#cas [nintegrate x in [a, b]] f` returns a decimal value `c` of `∫ x in a..b, f x` and proves
`|∫ x in a..b, f x - c| ≤ 10 ^ (-d)` with `d = 6` (`(digits := d)` changes it, up to 12), as
Mathematica's `NIntegrate` does without an error proof.
Integrands with `sqrt x` or a fractional power of `x` at `0` are made smooth by a
substitution first (`CAS/Command/NIntegrateSingular.lean`). Any other integrand without a validity
certificate on `[a, b]` is refused with a pointer to bare `cega`, which bounds such an integral
by range panels that need only continuity, and decimals that 1024 panels do not fix are refused
with the advice to ask for fewer.

## Implementation notes

The proof is the batch Simpson certificate of `CAS/Continuum/Quadrature/BatchSimpson.lean`, whose
notes and reference cover the error bound. `batchSearch` proposes the panel count and the rounded
value: the panel count doubles from 4 to 1024 until the enclosure
`panels (BatchSimpson.panel p f d)`, in which interval evaluation bounds the simplified fourth
symbolic derivative on every panel, fixes the requested decimals. The validity of `f` and its first
four derivatives on `[a, b]` comes from the CEGA domain checker, evaluated by the kernel
(`CAS.CEGA.Integration.validityOn?` in `CAS/CEGA/Integration.lean`). The kernel then decides the
Boolean hypothesis of `BatchSimpson.of_integralCheck_abs`
(`CAS.CEGA.Elaboration.decideClosedCertificate`), so one evaluation of `integralCheck` checks all
panels instead of one proof term per panel. The batch route, with its kernel check and its report,
runs under a budget of at least one million heartbeats. With 16 panels it certifies six decimals of
`1 / (1 + x ^ 2)` and eight of `sin` on `[0, 1]` (`CAS/Examples/NIntegrate.lean`).
-/

public meta section

namespace CAS.Command.NIntegrate

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Continuum

/-- The value of a one-variable expression at a rational point, by interval evaluation. -/
def sample (expr : Verified.Expr (Fin 1)) (x : ℚ) : Option ℚ := do
  let closed : Verified.Expr (Fin 0) := expr.mapVars fun _ ↦ .rat x.num x.den
  let I ← DigitsEval.eval ⟨96, 48, 120⟩ DigitsEval.closedEnv closed
  return (I.lo + I.hi) / 2

/-- The composite Simpson sum with `n` panels. -/
def simpson (expr : Verified.Expr (Fin 1)) (a b : ℚ) (n : Nat) : Option ℚ := do
  let h := (b - a) / n
  let mut total : ℚ := 0
  for k in [0:n] do
    let left := a + h * k
    let fl ← sample expr left
    let fm ← sample expr (left + h / 2)
    let fr ← sample expr (left + h)
    total := total + h / 6 * (fl + 4 * fm + fr)
  return total

/-- The value, rounded to `places` decimals, and the panel count, doubling from 4 to 1024,
whose batch Simpson enclosure lies within `tolerance` of the value. With `value? = some c` the
value is `c`, proposed elsewhere, and only the panel count is searched. -/
def batchSearch (precision : DigitsEval.Precision) (expr derivative : Verified.Expr (Fin 1))
    (a b : ℚ) (places : Nat) (tolerance : ℚ) (value? : Option ℚ := none) :
    Option (ℚ × Nat) := Id.run do
  let scale : ℚ := 10 ^ places
  let mut n : Nat := 4
  while n ≤ 1024 do
    if let some I := panels (BatchSimpson.panel precision expr derivative) a ((b - a) / (n : ℚ)) n
      then
      let c : ℚ := value?.getD ((⌊(I.lo + I.hi) / 2 * scale + 1 / 2⌋ : ℚ) / scale)
      if c - tolerance ≤ I.lo && I.hi ≤ c + tolerance then return some (c, n)
    n := 2 * n
  return none

/-- The batch Simpson route: the value, the panel count and the checked statement; with
`value? = some c` (a decimal with `digits` places) the statement is about `c`. -/
def batchRoute (digits : Nat) (expr : Verified.Expr (Fin 1)) (a b : ℚ)
    (value? : Option ℚ := none) : MetaM (Option (ℚ × Nat × Lean.Expr)) := do
  let quoted ← quoteVerifiedExpr expr
  let some validity ← CAS.CEGA.Integration.validityOn? quoted a b SpecialFunctions.quoteRat
    | return none
  let derivative := expr.symbolicDerivative 4
  let precision := DigitsEval.precisionFor digits
  let tolerance : ℚ := 1 / 10 ^ digits
  let some (c, panels) := batchSearch precision expr derivative a b digits tolerance value?
    | return none
  let partialProof ← mkAppOptM ``BatchSimpson.of_integralCheck_abs
    #[some (CAS.CEGA.Integration.quotePrecision precision), some quoted,
      some (← quoteVerifiedExpr derivative),
      some (← SpecialFunctions.quoteRat a), some (← SpecialFunctions.quoteRat b),
      some (toExpr panels), some (← SpecialFunctions.quoteDecimal digits c),
      some (← SpecialFunctions.quoteDecimal digits tolerance), some validity]
  let .forallE _ checkType _ _ ← whnfR (← inferType partialProof)
    | throwError "nintegrate: unexpected certificate theorem shape"
  let check ← CAS.CEGA.Elaboration.decideClosedCertificate checkType false
  let proof ← Digits.cleanProof (mkApp partialProof check)
    (Series.seriesCleanLemmas ++ [``Rat.cast_pow]) [``Verified.Expr.univariateEval]
  return some (c, panels, proof)

/-- Run `#cas [nintegrate x in [a, b]] f`. -/
def logIntegral (ref : Syntax) (digits : Nat) (coordinate : TSyntax `ident) (aStx bStx : Syntax)
    (input : Syntax) : CommandElabM Unit := do
  if digits = 0 || digits > 12 then
    throwErrorAt ref "nintegrate accepts between 1 and 12 digits"
  let a ← SpecialFunctions.parseRational "nintegrate" aStx
  let b ← SpecialFunctions.parseRational "nintegrate" bStx
  unless a < b do throwErrorAt ref "nintegrate needs rational limits a < b"
  let reified ← parseExact input [coordinate.getId]
  let expr : Verified.Expr (Fin 1) ← match reified with
    | ⟨[_], expression, _⟩ => pure expression
    | _ => throwErrorAt input "nintegrate needs an integrand in {coordinate.getId} alone"
  let scale : ℚ := 10 ^ digits
  let renderValue (v : ℚ) : String :=
    if v < 0 then "-" ++ Digits.renderDecimal (v * scale).num.natAbs digits
    else Digits.renderDecimal (v * scale).num.natAbs digits
  -- The batch route, with its kernel check and report, runs under a budget of at least one
  -- million heartbeats.
  let budget := max (maxHeartbeats.get (← getOptions)) 1000000
  let batch ← liftTermElabM <| withTheReader Core.Context (fun context ↦
      { context with maxHeartbeats := budget * 1000 }) <| withCurrHeartbeats do
    match ← batchRoute digits expr a b with
    | none => pure none
    | some (c, panels, proof) =>
        let report ← evidenceReportMessage
          #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
            "Certified Simpson panels in one kernel check" proof]
        pure (some (c, panels, report))
  if let some (c, panels, report) := batch then
    logReport ref {
      domain := s!"{coordinate.getId} ∈ [{a}, {b}]"
      input := surfaceText input
      inputType := "scalar ℝ"
      output := s!"{renderValue c} ± 10^-{digits}"
      outputType := "certified value of the integral"
    } #[
      computationNode "Certified quadrature" #[
        m!"Batch Simpson certificate with {panels} panels; fourth-derivative bounds by \
          interval evaluation of the simplified symbolic derivative"],
      report]
    return
  -- Without a validity certificate the integrand is not smooth on `[a, b]`; with one, the
  -- panels ran out before the enclosure fixed the decimals.
  let validity? ← liftTermElabM <| withTheReader Core.Context (fun context ↦
      { context with maxHeartbeats := budget * 1000 }) <| withCurrHeartbeats do
    CAS.CEGA.Integration.validityOn? (← quoteVerifiedExpr expr) a b SpecialFunctions.quoteRat
  if validity?.isSome then
    throwErrorAt input "nintegrate: 1024 Simpson panels do not fix {digits} decimals of the \
      integral on [{a}, {b}]; ask for fewer digits"
  throwErrorAt input "nintegrate: the domain checker found no fourth-derivative validity \
    certificate for the integrand on [{a}, {b}] and no substitution removes the singularity; a \
    bound such as `(∫ x in a..b, f x) ≤ c` is proved by `cega`, whose range panels need only \
    continuity"

end CAS.Command.NIntegrate

namespace CAS.Command

open Lean Elab Command

/-- `#cas [nintegrate x in [a, b]] f` computes a decimal value `c` of the integral of `f` from `a`
to `b` with `d` places and proves that `c` is within `10 ^ (-d)` of the integral.

## Theorem
For the printed `c ± 10^-d`, the report proves `|(∫ x in a..b, f) - c| ≤ 1 / 10 ^ d`
(`CAS.Continuum.BatchSimpson.of_integralCheck_abs`).

## Conditions and limits
`a < b` are closed rational expressions, such as `-1` or `3/2`; a bound is refused when its
evaluation needs a number with more than `10000` digits (`SpecialFunctions.parseRational`). `f` is
an expression in `x` alone, in the calculator grammar of `#cas [N d]`. The proof is a composite
Simpson rule whose remainder comes from an enclosure of the fourth derivative of `f` on every
panel. The panel count doubles from 4 to 1024 until the enclosure fixes the decimals, and the CEGA
domain checker proves that `f` and its first four derivatives are defined on `[a, b]`. A factor
`sqrt x` or a fractional power of `x` at `0` is removed by a substitution first. An integrand
without this certificate, such as one with a singularity in `[a, b]`, is refused, and so are
decimals that 1024 panels do not fix.

## Options
`(digits := d)`: the number of decimal places, 1 to 12, default 6.

## Examples
```lean
#cas [nintegrate x in [0, 1]] (exp (-x^2))
```
```output
Output (certified value of the integral): 0.746824 ± 10^-6
```
```lean
#cas (digits := 8) [nintegrate x in [0, 1]] (sin x)
```
```output
Output (certified value of the integral): 0.45969770 ± 10^-8
```
```lean
#cas [nintegrate x in [0, 1]] (sqrt x)
```
```output
Output (certified value of the integral): 0.666667 ± 10^-6
```

## In a proof
```lean
theorem nintegrate_gauss :
    |(∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) - 746824 / 10 ^ 6| ≤ 1 / 10 ^ 6 := by
  cega
```
The tactic `cega` proves the printed statement.

## See also
Mathematica `NIntegrate`, SymPy `Integral.evalf`. The modes `integrate`, `N` and `ndsolve`, and
the tactic `cega`, which also proves bounds such as `(∫ x in a..b, f x) ≤ c` for continuous
integrands. Oracle route: `#cas [nintegrate x in [a, b], oracle := sympy] f`, which proves an
enclosure around the oracle's estimate.

## Possible issues
```lean
#cas [nintegrate x in [0, 1]] (1 / x)
```
```output
nintegrate: the domain checker found no fourth-derivative validity certificate for the integrand
on [0, 1] and no substitution removes the singularity
```
`1 / x` has a pole at `0` and no finite integral on `[0, 1]`. For an integrand that is continuous
on `[a, b]` but has no such certificate, `cega` proves bounds on the integral.
```lean
#cas (digits := 16) [nintegrate x in [0, 1]] (x)
```
```output
nintegrate accepts between 1 and 12 digits
```
Ask for at most 12 places.
```lean
#cas [nintegrate x in [1, 0]] (x)
```
```output
nintegrate needs rational limits a < b
```
Write the smaller limit first; `∫ x in b..a, f` is `-∫ x in a..b, f`.
-/
syntax (name := casNIntegrateCommand)
  "#cas" optConfig "[" &"nintegrate" cegaIntervalBinding "]" term : command

elab_rules : command
  | `(#cas $cfg:optConfig [nintegrate $x:ident in [$a:term, $b:term]] $expr:term) => do
      NIntegrate.logIntegral expr (← parseDigitsOption "nintegrate" cfg 6) x a b expr

end CAS.Command

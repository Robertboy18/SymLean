/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.Laurent
public import CAS.Command.Series
public meta import CAS.Calculus.Laurent
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Laurent series: `#cas [series x a n]` at a pole

`#cas [series x a n] (g / h)`, where the denominator vanishes at `a` to order `m`, prints the
Laurent series of the quotient through `(x - a) ^ n`, with the pole terms
`c₋ₘ (x - a) ^ (-m) + ⋯`, as Mathematica's `Series[g/h, {x, a, n}]` does, and proves

`(fun x ↦ g x / h x - ∑ k, c_k (x - a) ^ k) =o[𝓝[≠] a] fun x ↦ (x - a) ^ n`

with integer powers `k ≥ -m`. A removable singularity, such as `sin x / x` at `0`, gives the
Taylor series of the quotient. Other expressions stay with the Taylor command of
`CAS/Command/Series.lean`, to which the rule here falls back.

## Implementation notes

The Taylor coefficients `cN` of `g` through order `n + m` and `cD` of `h` through order `n + 2m`
are exact rationals, computed as for `#cas [series x a n]` itself, and need `g` and `h` valid at
`a` only. We divide the two series in meta code, solving the triangular system
`cN_j = ∑ i ≤ j, cs_i cD_(m + j - i)` for the Laurent coefficients `cs`. The kernel decides
`seriesCheck` for both Taylor lists and `laurentCheck` for the division in one closed check
(`CAS.CEGA.Elaboration.decideClosedCertificate`), and `laurent_of_check` of
`CAS/Calculus/Laurent.lean` turns it into the expansion of the quotient through
`laurent_of_isLittleO`.
-/

public meta section

namespace CAS.Command.Laurent

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Command.SpecialFunctions
open CAS.Command.Series
open CAS.Verified.Expr

/-- `∑ cs_i (x - a) ^ (i - m)` in increasing powers, then the remainder. -/
def render (name : String) (a : ℚ) (cs : List ℚ) (m n : Nat) : String :=
  let shifted := if a < 0 then s!"{name} + {-a}" else s!"{name} - {a}"
  let base := if a = 0 then name else s!"({shifted})"
  let powerOf (k : Nat) : String := if k = 1 then base else s!"{base}^{k}"
  let terms := cs.zipIdx.filterMap fun (c, i) ↦
    if c = 0 then none else
    let negative := decide (c < 0)
    let magnitude := if negative then -c else c
    let text :=
      if i < m then
        let k := m - i
        if magnitude.den = 1 then s!"{magnitude.num}/{powerOf k}"
        else s!"{magnitude.num}/({magnitude.den}*{powerOf k})"
      else if i = m then toString magnitude
      else
        let k := i - m
        if magnitude = 1 then powerOf k else s!"{magnitude}*{powerOf k}"
    some (negative, text)
  let body := match terms with
    | [] => "0"
    | (negative, first) :: rest =>
        rest.foldl (fun total (term : Bool × String) ↦
          total ++ (if term.1 then " - " else " + ") ++ term.2)
          ((if negative then "-" else "") ++ first)
  let remainder := if a = 0 then s!"o({name}^{n})" else s!"o({base}^{n})"
  s!"{body} + {remainder}"

/-- Run `#cas [series x a n] (g / h)` at a zero of `h`. -/
def logLaurent (ref : Syntax) (coordinate : TSyntax `ident) (centre : Syntax) (n : Nat)
    (input : Syntax) : CommandElabM Unit := do
  if n > 12 then throwUnsupportedSyntax
  let a ← parseCentre centre
  let (reified, expr) ← parseUnivariate coordinate input
  let .div num den := expr | throwUnsupportedSyntax
  unless derivativeAt den 0 a == some 0 do throwUnsupportedSyntax
  let some (m, _) := order? den a 12
    | throwErrorAt input "series: the denominator has no nonzero derivative of order at most 12 \
        at {a} that is an exact rational number"
  let coefficients (source : Verified.Expr (Fin 1)) (order : Nat) : CommandElabM (List ℚ) :=
    (List.range (order + 1)).mapM fun k ↦ do
      match derivativeAt source k a with
      | some value => pure (value / k.factorial)
      | none => throwErrorAt input "series: the derivative of order {k} at {a} is not an exact \
          rational number"
  let cN ← coefficients num (n + m)
  let cD ← coefficients den (n + 2 * m)
  let lead := cD.getD m 0
  let mut cs : Array ℚ := #[]
  for j in [0:n + m + 1] do
    let known := (List.range j).foldl (fun total i ↦
      total + cs.getD i 0 * cD.getD (m + (j - i)) 0) 0
    cs := cs.push ((cN.getD j 0 - known) / lead)
  let proof ← liftTermElabM do
    let quotedNum ← quoteVerifiedExpr num
    let quotedDen ← quoteVerifiedExpr den
    let validNum ← requireValidityAt "series" "numerator" quotedNum (n + m + 1) a
    let validDen ← requireValidityAt "series" "denominator" quotedDen (n + 2 * m + 1) a
    let list (l : List ℚ) : MetaM Lean.Expr := do
      mkListLit (mkConst ``Rat) (← l.mapM fun c ↦ quoteRat c)
    let partialProof ← mkAppM ``laurent_of_check
      #[quotedNum, quotedDen, toExpr m, toExpr n, ← quoteRat a, validNum, validDen, ← list cN,
        ← list cD, ← list cs.toList]
    let .forallE _ checkType _ _ ← whnfR (← inferType partialProof)
      | throwError "series: unexpected certificate theorem shape"
    let check ← CAS.CEGA.Elaboration.decideClosedCertificate checkType false
    Digits.cleanProof (mkApp partialProof check) (seriesCleanLemmas ++ [``Nat.cast_ofNat,
        ``Nat.cast_zero, ``Nat.cast_one, ``zpow_neg, ``zpow_ofNat, ``zpow_one, ``zpow_zero])
      [``Verified.Expr.univariateEval] (simprocs := true)
  let report ← liftTermElabM do
    evidenceReportMessage #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
      "Laurent expansion with a little-o remainder" proof]
  let name := renderName coordinate.getId
  let pole := (List.range m).find? (fun i ↦ cs.getD i 0 != 0) |>.map (m - ·)
  logReport ref {
    domain := s!"{name} → {a}, {name} ≠ {a}"
    input := reified.render
    inputType := "scalar ℝ"
    output := render name a cs.toList m n
    outputType := match pole with
      | some k => s!"Laurent series with a pole of order {k}"
      | none => "Taylor series of a removable singularity"
  } #[
    computationNode "Series division" #[
      m!"the denominator vanishes to order {m}; numerator coefficients {cN}, denominator \
        coefficients {cD}"],
    report]

end CAS.Command.Laurent

namespace CAS.Command

open Lean Elab Command

elab_rules : command
  | `(#cas [series $x:ident $a:casSeriesCentre $n:num] $expr:term) =>
      Laurent.logLaurent expr x a n.getNat expr

end CAS.Command

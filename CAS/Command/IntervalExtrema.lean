/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Minimize

/-!
# Extrema of polynomials on an interval: `#cas [minimize x in [a, b]]`

`#cas [minimize x in [a, b]] p` returns the minimum of a real polynomial `p` over the closed
interval `[a, b]` with rational `a < b`, and proves it:

* when the search finds the minimum at a rational point `x₀` (an endpoint or a rational root
  of `p'` that the rational-root search finds), the exact statement
  `(∀ x ∈ Set.Icc a b, m ≤ p x) ∧ x₀ ∈ Set.Icc a b ∧ p x₀ = m`;
* otherwise the certified enclosure `(∀ x ∈ Set.Icc a b, lo ≤ p x) ∧ x₁ ∈ Set.Icc a b ∧
  p x₁ ≤ hi`, with decimals `lo`, `hi` at most `2 · 10 ^ (-d)` apart (`d = 3`; `(digits := d)`
  changes it, up to 6) and a rational witness `x₁` of the interval with `p x₁ ≤ hi`: the
  minimum value lies in `[lo, hi]`. The theorem bounds the value, not the position of the
  minimizer, and the report says `witness`, not `near`.

`#cas [maximize x in [a, b]] p` is the same for `-p`, with the inequalities reversed. Unlike the
global commands, every polynomial has both extrema on a compact interval, whatever its degree.

## Implementation notes

The candidates are the endpoints and the real roots of `p'` from the root list of
`#cas [reduce]` (`Minimize.criticalPoints`, see `CAS/Command/Minimize.lean`), clamped to
`[a, b]`; nothing in the search is trusted, and a missed candidate can only make the proof fail.
The bound `∀ x ∈ Set.Icc a b, m ≤ p x` comes from the interval case of the sign route of bare
`cas` (`Goals.closeSign`, `CAS/Command/Goals.lean`), under a budget of at least two million
heartbeats: the root list of `p - m` has `a` and `b` as cell boundaries, so a minimum at an
endpoint or at an interior rational point is an exact root location, and
`nonneg_on_Icc_of_reduceCheck` (`CAS/Polynomial/RealRoot/SignReduce.lean`) needs a positive cut
only in the gaps that meet `[a, b]`. For a constant `p` the bound compares two numerals, and
`norm_num` proves it, as it proves the membership and the value.
-/

public meta section

namespace CAS.Command.IntervalExtrema

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.Algebra (Dense)
open CAS.Command.Minimize (decimalSyntax decimalText placesOf criticalPoints)

/-- The point `x` of `[a, b]` rounded to the fewest places among `d + 2, d + 4, …, 20` at which
`p x ≤ bound` and that stay in `[a, b]`, or `x` itself. -/
def nearPointIn (p : Dense) (a b x bound : ℚ) (digits : Nat) : ℚ := Id.run do
  let mut k := digits + 2
  while k ≤ 20 do
    let scale : ℚ := 10 ^ k
    let y : ℚ := (⌊x * scale + 1 / 2⌋ : ℚ) / scale
    if a ≤ y && y ≤ b && Dense.eval p y ≤ bound then return y
    k := k + 2
  return x

/-- Run `#cas [minimize x in [a, b]] p` (`maximize := false`) or `#cas [maximize x in [a, b]] p`. -/
def logExtremumIn (ref : Syntax) (maximize : Bool) (digits : Nat) (coordinate : TSyntax `ident)
    (aStx bStx : Syntax) (input : Syntax) : CommandElabM Unit := do
  let operation := if maximize then "maximize" else "minimize"
  if digits = 0 || digits > 6 then
    throwErrorAt ref "{operation} accepts between 1 and 6 digits"
  let a ← SpecialFunctions.parseRational operation aStx
  let b ← SpecialFunctions.parseRational operation bStx
  unless a < b do throwErrorAt ref "{operation} needs rational endpoints a < b"
  let (reified, expr) ← Series.parseUnivariate coordinate input
  let some sparse := Verified.Expr.Alg.mvPolyOf? expr
    | throwErrorAt input "{operation} needs a polynomial in {coordinate.getId} with rational \
        coefficients"
  let original := Dense.ofSparse sparse
  -- Minimize `q = ±p` on `[a, b]`.
  let q := if maximize then Dense.scale (-1) original else Dense.trim original
  let critical := (criticalPoints q).filterMap fun (c, exact) ↦
    if a < c && c < b then some (c, exact)
    else if c ≤ a && a - c < 1 / 10 ^ 18 then some (a, false)
    else if b ≤ c && c - b < 1 / 10 ^ 18 then some (b, false)
    else none
  let candidates := (a, true) :: (b, true) :: critical
  let some (x₀, exact) := candidates.foldl (fun best c ↦ match best with
      | none => some c
      | some best => if Dense.eval q c.1 < Dense.eval q best.1 then some c else some best) none
    | throwErrorAt input "{operation}: no candidate point"
  let value := Dense.eval q x₀
  let sign : ℚ := if maximize then -1 else 1
  let x := coordinate.getId
  let binder := mkIdent x
  let body ← (FullSimplify.Form.ofExpr reified.names expr).toSyntax
  let lam ← `(fun $binder:ident : ℝ ↦ $body)
  let (statement, bound, outputText) ← liftTermElabM do
    let aT ← `(($(← ratSyntax a) : ℝ))
    let bT ← `(($(← ratSyntax b) : ℝ))
    let domain ← `(Set.Icc $aT $bT)
    if exact then
      let v ← `(($(← ratSyntax (sign * value)) : ℝ))
      let p ← `(($(← ratSyntax x₀) : ℝ))
      let bound ← if maximize then `(∀ $binder:ident ∈ $domain, $body ≤ $v)
        else `(∀ $binder:ident ∈ $domain, $v ≤ $body)
      return (← `($bound ∧ $p ∈ $domain ∧ $lam $p = $v), bound,
        s!"{if maximize then "max" else "min"} = {sign * value} at {x} = {x₀}")
    else
      let scale : ℚ := 10 ^ digits
      let mut lo : ℚ := (⌊value * scale⌋ : ℚ) / scale
      if value - lo < 1 / 10 ^ (digits + 5) then lo := lo - 1 / scale
      let hi : ℚ := (⌈value * scale⌉ : ℚ) / scale
      let x₁ := nearPointIn q a b x₀ hi digits
      let p ← decimalSyntax (placesOf x₁ 30) x₁
      let (loT, hiT) := if maximize then (-hi, -lo) else (lo, hi)
      let loS ← decimalSyntax digits loT
      let hiS ← decimalSyntax digits hiT
      let bound ← if maximize then `(∀ $binder:ident ∈ $domain, $body ≤ $hiS)
        else `(∀ $binder:ident ∈ $domain, $loS ≤ $body)
      let attained ← if maximize then `($loS ≤ $lam $p) else `($lam $p ≤ $hiS)
      return (← `($bound ∧ $p ∈ $domain ∧ $attained), bound,
        s!"{if maximize then "max" else "min"} ∈ [{decimalText digits loT}, \
          {decimalText digits hiT}], witness {x} = {decimalText (placesOf x₁ 30) x₁} with value \
          {if maximize then "≥ " ++ decimalText digits loT else "≤ " ++ decimalText digits hiT}")
  -- The sign certificate of the bound runs under a budget of at least two million heartbeats.
  let budget := max (maxHeartbeats.get (← getOptions)) 2000000
  let (proposition, proof) ← liftTermElabM <| withTheReader Core.Context (fun context ↦
      { context with maxHeartbeats := budget * 1000 }) <| withCurrHeartbeats do
    -- The bound on the interval, by the interval case of the sign route of bare `cas`.
    let boundType ← elabType bound
    synthesizeSyntheticMVarsNoPostponing
    let boundGoal ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars boundType)
    -- A constant has no root list; its bound compares two numerals.
    let remaining ← Lean.Elab.Tactic.run boundGoal.mvarId! do
      if Dense.degree q = 0 then
        Lean.Elab.Tactic.evalTactic (← `(tactic| intro _ _; norm_num))
      else CAS.Command.Goals.closeSign
    unless remaining.isEmpty do
      throwError "{operation}: the sign route left the bound on the interval unproved"
    let boundProof ← exprToSyntax (← instantiateMVars boundGoal)
    Algebra.proveStatement operation statement
      (← `(tactic| exact ⟨$boundProof, by norm_num [Set.mem_Icc], by norm_num⟩))
  logReport ref {
    domain := s!"{x} ∈ [{a}, {b}]"
    input := reified.render
    inputType := "polynomial"
    output := outputText
    outputType := if exact then s!"exact {if maximize then "maximum" else "minimum"} on the \
        interval"
      else s!"certified enclosure of the {if maximize then "maximum" else "minimum"} on the \
        interval"
  } #[
    computationNode "Candidates" #[
      m!"Endpoints and real roots of the derivative in the interval (not proof): \
        {candidates.length}"],
    ← liftTermElabM <| Algebra.checkedEvidence operation
      (if exact then "Bound on the interval attained at the point"
        else "Bound on the interval and a witness value")
      proposition proof]

end CAS.Command.IntervalExtrema

namespace CAS.Command

open Lean Elab Command

/-- `#cas [minimize x in [a, b]] p` is the minimum of the polynomial `p` on the closed interval
`[a, b]` with rational endpoints `a < b`, exact when the search finds a rational point attaining
it and otherwise a certified enclosure with a witness point of the interval; see
`#cas [minimize x]`. The theorem is
`(∀ x ∈ Set.Icc a b, m ≤ p) ∧ x₀ ∈ Set.Icc a b ∧ (fun x ↦ p) x₀ = m`, or its enclosure form.
-/
syntax (name := casMinimizeInCommand)
  "#cas" optConfig "[" &"minimize" cegaIntervalBinding "]" term : command

/-- `#cas [maximize x in [a, b]] p` is the maximum of `p` on the closed interval `[a, b]` with
rational endpoints `a < b`; see `#cas [minimize x in [a, b]]` and `#cas [maximize x]`.
-/
syntax (name := casMaximizeInCommand)
  "#cas" optConfig "[" &"maximize" cegaIntervalBinding "]" term : command

elab_rules : command
  | `(#cas $cfg:optConfig [minimize $x:ident in [$a:term, $b:term]] $e:term) => do
      IntervalExtrema.logExtremumIn e false (← parseDigitsOption "minimize" cfg 3) x a b e
  | `(#cas $cfg:optConfig [maximize $x:ident in [$a:term, $b:term]] $e:term) => do
      IntervalExtrema.logExtremumIn e true (← parseDigitsOption "maximize" cfg 3) x a b e

end CAS.Command

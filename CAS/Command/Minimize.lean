/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Algebra.Basic
public import CAS.Command.Goals
public import CAS.Command.Reduce
public import CAS.Command.Series
public import CAS.ExactTactic

/-!
# Global extrema of polynomials: `#cas [minimize x]`, `#cas [maximize x]`

`#cas [minimize x] p` returns the minimum of a real polynomial `p` over all of `ℝ` and proves
it:

* when the minimum is attained at a rational point `x₀` (a rational root of `p'`), the exact
  statement `(∀ x : ℝ, m ≤ p x) ∧ (fun x ↦ p x) x₀ = m`;
* otherwise the certified enclosure `(∀ x : ℝ, lo ≤ p x) ∧ (fun x ↦ p x) x₁ ≤ hi` with decimals
  `lo`, `hi` at most `2 · 10 ^ (-d)` apart (`d = 3`; `(digits := d)` changes it, up to 6) and a
  rational point `x₁` near the minimizer: the minimum value lies in `[lo, hi]` (the theorem
  bounds the value, not the position of the minimizer, and does not give the minimum as an
  exact algebraic number).

`#cas [maximize x] p` is the same for `-p`, with the inequalities reversed. A polynomial of odd
degree, or of even degree with the wrong sign of the leading coefficient, has no minimum
(maximum) and is refused.

## Implementation notes

The candidates (`criticalPoints`) are the real roots of `p'`, isolated by the root list of
`#cas [reduce]` (`Reduce.rootData` in `CAS/Command/Reduce.lean`, which runs
`RootIsolation.generate`; rational roots exactly, the others in intervals of width `10 ^ (-20)`),
and evaluated in exact rational arithmetic; nothing in the search is trusted. The bound
`∀ x, m ≤ p x` is proved by the sign route of bare `cas` (`Goals.closeSign` in
`CAS/Command/Goals.lean`, with the root-list certificate `nonneg_of_reduceCheck` of
`CAS/Polynomial/RealRoot/SignReduce.lean` for `p - m`), under a budget of at least two million
heartbeats, and the value at the point by `norm_num`.

The cost of the sign certificate grows as `lo` approaches the minimum: `p - lo` then has a pair
of complex roots close to the real axis, and the root-free cells must separate them.
-/

public meta section

namespace CAS.Command.Minimize

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.Algebra (Dense)

/-- The decimal `m / 10 ^ d` as real term syntax, or the rational when `q` has more places. -/
def decimalSyntax (digits : Nat) (q : ℚ) : TermElabM (TSyntax `term) := do
  let m := q * 10 ^ digits
  if m.den ≠ 1 || digits = 0 then return ← `(($(← ratSyntax q) : ℝ))
  let numerator : TSyntax `term := ⟨Syntax.mkNumLit (toString m.num.natAbs)⟩
  let places : TSyntax `term := ⟨Syntax.mkNumLit (toString digits)⟩
  if m.num < 0 then `((-$numerator / 10 ^ $places : ℝ)) else `(($numerator / 10 ^ $places : ℝ))

/-- `q` in decimal notation with `digits` places, exact when `q` has at most that many. -/
def decimalText (digits : Nat) (q : ℚ) : String :=
  let m := q * 10 ^ digits
  if m.den ≠ 1 then toString q else
  let body := Digits.renderDecimal m.num.natAbs digits
  if m.num < 0 then "-" ++ body else body

/-- The fewest decimal places, at most `bound`, that write `q` exactly, or `bound`. -/
def placesOf (q : ℚ) (bound : Nat) : Nat := Id.run do
  for k in [0:bound + 1] do
    if (q * 10 ^ k).den = 1 then return k
  return bound

/-- The real critical points of `p` (roots of `p'`): exact rationals, and points of isolating
intervals of width `10 ^ (-20)` with the flag `false`. -/
def criticalPoints (p : Dense) : List (ℚ × Bool) :=
  let d := Dense.derivative p
  if Dense.isZero d then [] else
  match Reduce.rootData (Dense.toSparse d) with
  | .ok data => data.locs.map fun
      | .exact q => (q, true)
      | .interval lo hi => ((lo + hi) / 2, false)
  | .error _ => []

/-- The point `x` rounded to the fewest places among `d + 2, d + 4, …, 20` at which
`p x ≤ bound`, or `x` itself. -/
def nearPoint (p : Dense) (x bound : ℚ) (digits : Nat) : ℚ := Id.run do
  let mut k := digits + 2
  while k ≤ 20 do
    let scale : ℚ := 10 ^ k
    let y : ℚ := (⌊x * scale + 1 / 2⌋ : ℚ) / scale
    if Dense.eval p y ≤ bound then return y
    k := k + 2
  return x

/-- Run `#cas [minimize x] p` (`maximize := false`) or `#cas [maximize x] p`. -/
def logExtremum (ref : Syntax) (maximize : Bool) (digits : Nat) (coordinate : TSyntax `ident)
    (input : Syntax) : CommandElabM Unit := do
  let operation := if maximize then "maximize" else "minimize"
  if digits = 0 || digits > 6 then
    throwErrorAt ref "{operation} accepts between 1 and 6 digits"
  let (reified, expr) ← Series.parseUnivariate coordinate input
  let some sparse := Verified.Expr.Alg.mvPolyOf? expr
    | throwErrorAt input "{operation} needs a polynomial in {coordinate.getId} with rational \
        coefficients"
  let original := Dense.ofSparse sparse
  -- Minimize `q = ±p`.
  let q := if maximize then Dense.scale (-1) original else Dense.trim original
  let n := Dense.degree q
  if n % 2 = 1 || (n > 0 && Dense.lead q < 0) then
    throwErrorAt input "{operation}: the polynomial is unbounded {if maximize then "above" else
      "below"} (degree {n}, leading coefficient {Dense.lead original}), so it has no \
      {if maximize then "maximum" else "minimum"}"
  let candidates := if n = 0 then [((0 : ℚ), true)] else criticalPoints q
  let some (x₀, exact) := candidates.foldl (fun best c ↦ match best with
      | none => some c
      | some b => if Dense.eval q c.1 < Dense.eval q b.1 then some c else some b) none
    | throwErrorAt input "{operation}: no critical point found"
  let value := Dense.eval q x₀
  let sign : ℚ := if maximize then -1 else 1
  let x := coordinate.getId
  -- A synthetic binder: the body refers to the variable by name.
  let binder := mkIdent x
  let body ← (FullSimplify.Form.ofExpr reified.names expr).toSyntax
  let lam ← `(fun $binder:ident : ℝ ↦ $body)
  let (statement, outputText, point) ← liftTermElabM do
    if exact then
      let v ← `(($(← ratSyntax (sign * value)) : ℝ))
      let p ← `(($(← ratSyntax x₀) : ℝ))
      let bound ← if maximize then `(∀ $binder:ident : ℝ, $body ≤ $v)
        else `(∀ $binder:ident : ℝ, $v ≤ $body)
      return (← `($bound ∧ $lam $p = $v),
        s!"{if maximize then "max" else "min"} = {sign * value} at {x} = {x₀}", x₀)
    else
      let scale : ℚ := 10 ^ digits
      let mut lo : ℚ := (⌊value * scale⌋ : ℚ) / scale
      if value - lo < 1 / 10 ^ (digits + 5) then lo := lo - 1 / scale
      let hi : ℚ := (⌈value * scale⌉ : ℚ) / scale
      let x₁ := nearPoint q x₀ hi digits
      let p ← decimalSyntax (placesOf x₁ 30) x₁
      -- For `maximize` the bounds of `-p` are negated.
      let (loT, hiT) := if maximize then (-hi, -lo) else (lo, hi)
      let loS ← decimalSyntax digits loT
      let hiS ← decimalSyntax digits hiT
      let bound ← if maximize then `(∀ $binder:ident : ℝ, $body ≤ $hiS)
        else `(∀ $binder:ident : ℝ, $loS ≤ $body)
      let attained ← if maximize then `($loS ≤ $lam $p) else `($lam $p ≤ $hiS)
      return (← `($bound ∧ $attained),
        s!"{if maximize then "max" else "min"} ∈ [{decimalText digits loT}, \
          {decimalText digits hiT}] near {x} = {decimalText (placesOf x₁ 30) x₁}", x₁)
  let _ := point
  -- The sign certificate of the bound runs under a budget of at least two million heartbeats.
  let budget := max (maxHeartbeats.get (← getOptions)) 2000000
  let (proposition, proof) ← liftTermElabM <| withTheReader Core.Context (fun context ↦
      { context with maxHeartbeats := budget * 1000 }) <| withCurrHeartbeats <|
    Algebra.proveStatement operation statement (← `(tactic| (refine ⟨?_, ?_⟩; cas; norm_num)))
  logReport ref {
    domain := s!"{x} ∈ ℝ"
    input := reified.render
    inputType := "polynomial"
    output := outputText
    outputType := if exact then s!"exact global {if maximize then "maximum" else "minimum"}"
      else s!"certified enclosure of the global {if maximize then "maximum" else "minimum"}"
  } #[
    computationNode "Critical points" #[
      m!"Real roots of the derivative from the root list (not proof): {candidates.length}"],
    ← liftTermElabM <| Algebra.checkedEvidence operation
      (if exact then "Global bound attained at the point" else "Global bound and a nearby value")
      proposition proof]

end CAS.Command.Minimize

namespace CAS.Command

open Lean Elab Command

/-- `#cas [minimize x] p` computes the global minimum of the real polynomial `p` in `x` and proves
it, exactly when a rational point attains it and otherwise as a certified decimal enclosure.

## Theorem
At a rational minimizer `x₀` with minimum `m`, the report proves
`(∀ x : ℝ, m ≤ p) ∧ (fun x ↦ p) x₀ = m`. Otherwise it proves
`(∀ x : ℝ, lo ≤ p) ∧ (fun x ↦ p) x₁ ≤ hi` for the printed decimals `lo`, `hi` and a rational
point `x₁` near the minimizer, so the minimum lies in `[lo, hi]`; the theorem bounds the value,
not the position of the minimizer. The bound comes from the sign certificate of `cas` for
`p - m` (`CAS.Polynomial.RealRoot.nonneg_of_reduceCheck`) and the value from `norm_num`.

## Conditions and limits
`p` is a polynomial in `x` with rational coefficients and no other variable. A polynomial of odd
degree, or of even degree with a negative leading coefficient, has no minimum and is refused. The
candidates are the real roots of the derivative; a minimum at an irrational point is enclosed,
and more digits make the sign certificate slower. `#cas [minimize x in [a, b]] p` minimizes over
a closed interval with rational endpoints `a < b`, where every polynomial has a minimum.

## Options
`(digits := d)`: the enclosure `[lo, hi]` has width at most `2 * 10 ^ (-d)`; `d` is 1 to 6,
default 3.

## Examples
```lean
#cas [minimize x] (x^2 - 2*x + 4)
```
```output
Output (exact global minimum): min = 3 at x = 1
```
```lean
#cas [minimize x] (x^4 - x)
```
```output
Output (certified enclosure of the global minimum): min ∈ [-0.473, -0.472] near x = 0.62996
```
```lean
#cas [minimize x in [0, 2]] (x^2 - 2*x)
```
```output
Output (exact minimum on the interval): min = -1 at x = 1
```

## In a proof
```lean
theorem minimize_quadratic : ∀ x : ℝ, 3 ≤ x ^ 2 - 2 * x + 4 := by
  cas
```

## See also
Mathematica `Minimize`, SymPy `minimum`. The modes `maximize`, `reduce` and `enclose`, and the
tactic `cas`, which proves the bound `∀ x : ℝ, m ≤ p`.

## Possible issues
```lean
#cas [minimize x] (x^3 - x)
```
```output
minimize: the polynomial is unbounded below (degree 3, leading coefficient 1), so it has no minimum
```
Minimize on a closed interval instead: `#cas [minimize x in [-1, 1]] (x^3 - x)`.
```lean
#cas [minimize x] (sin x)
```
```output
minimize needs a polynomial in x with rational coefficients
```
The tactic `cega` proves bounds for other functions on intervals.
```lean
#cas (digits := 7) [minimize x] (x^4 - x)
```
```output
minimize accepts between 1 and 6 digits
```
Ask for at most 6 digits.
-/
syntax (name := casMinimizeCommand) "#cas" optConfig "[" &"minimize" ident "]" term : command

/-- `#cas [maximize x] p` computes the global maximum of the real polynomial `p` in `x` and proves
it; it is `#cas [minimize x]` for `-p`, with the inequalities reversed.

## Theorem
At a rational maximizer `x₀` with maximum `M`, the report proves
`(∀ x : ℝ, p ≤ M) ∧ (fun x ↦ p) x₀ = M`, and otherwise `(∀ x : ℝ, p ≤ hi) ∧ lo ≤ (fun x ↦ p) x₁`
for the printed decimals `lo`, `hi` and a rational point `x₁`. On an interval the bound is
`∀ x ∈ Set.Icc a b, p ≤ M`, and the point is proved to lie in `Set.Icc a b`.

## Conditions and limits
As for `#cas [minimize x]`: `p` is a polynomial in `x` with rational coefficients. A polynomial
of odd degree, or of even degree with a positive leading coefficient, has no maximum and is
refused. On a closed interval `[a, b]` with rational `a < b` every polynomial has a maximum.

## Options
`(digits := d)`, 1 to 6, default 3, as for `#cas [minimize x]`.

## Examples
```lean
#cas [maximize x] (3 + 2*x - x^2)
```
```output
Output (exact global maximum): max = 4 at x = 1
```
```lean
#cas [maximize x in [0, 1]] (x * (1 - x) * (x + 1))
```
```output
Output (certified enclosure of the maximum on the interval): max ∈ [0.384, 0.385], witness
x = 0.57735 with value ≥ 0.384
```

## In a proof
```lean
theorem maximize_quadratic : ∀ x : ℝ, 3 + 2 * x - x ^ 2 ≤ 4 := by
  cas
```

## See also
Mathematica `Maximize`, SymPy `maximum`. The modes `minimize`, `reduce` and `enclose`, and the
tactic `cas`, which proves the bound `∀ x : ℝ, p ≤ M`.

## Possible issues
```lean
#cas [maximize x] (x^2 + 1)
```
```output
maximize: the polynomial is unbounded above (degree 2, leading coefficient 1), so it has no maximum
```
Maximize on a closed interval instead: `#cas [maximize x in [-1, 1]] (x^2 + 1)`.
```lean
#cas [maximize x in [1, 0]] (x)
```
```output
maximize needs rational endpoints a < b
```
Write the smaller endpoint first.
-/
syntax (name := casMaximizeCommand) "#cas" optConfig "[" &"maximize" ident "]" term : command

elab_rules : command
  | `(#cas $cfg:optConfig [minimize $x:ident] $e:term) => do
      Minimize.logExtremum e false (← parseDigitsOption "minimize" cfg 3) x e
  | `(#cas $cfg:optConfig [maximize $x:ident] $e:term) => do
      Minimize.logExtremum e true (← parseDigitsOption "maximize" cfg 3) x e

end CAS.Command

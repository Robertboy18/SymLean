/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.OrthogonalPolynomials
public import CAS.Analysis.SpecialFunctions.BesselJ

/-!
# Certified digits of the Bessel function `J_n`

`#cas [N d] (BesselJ n q)` (Mathematica's `N[BesselJ[n, q], d]`) encloses Mathlib's
`Complex.besselJ` at an integer order `n` and a rational point `q`. It proves
`∃ r : ℝ, Complex.besselJ ((n : ℤ) : ℂ) ((q : ℚ) : ℂ) = r ∧ (lo : ℝ) ≤ r ∧ r ≤ hi ∧
hi - lo ≤ 1 / 10 ^ d`: the value is real and lies in `[lo, hi]`, two decimals with `d + 1` places
whose distance is at most `10 ^ (-d)`, and this width is part of the theorem (by `norm_num`):
here `d` bounds the absolute width of the enclosure, it does not promise `d`
significant digits as `#cas [N d] e` does (near a zero of `J_n` there are fewer). It prints this
enclosure; at `q = 0`, where `lo = hi`, it prints the exact value.

The limits are `|n| ≤ 50`, `|q| ≤ 50` with a denominator of at most `1000`, and `1 ≤ d ≤ 30`
(`N` accepts at most 2000 digits elsewhere); a `BesselJ n q` outside them is refused with an
error. The limits bound the normalized `n` and `q`, not the cost of evaluating the input
expressions. `CAS.Command.Calls` reads the call.

## Implementation notes

The series, its tail bound and the checker are in `CAS/Analysis/SpecialFunctions/BesselJ.lean`.
The untrusted `besselPlan` sums the series of `J_|n| (q)` term by term, from
`t₀ = (q / 2) ^ |n| / |n|!` with `t_{N+1} = -t_N (q / 2) ^ 2 / ((N + 1) (|n| + N + 1))`, up to
the smallest `N ≥ 1` with `2 (q / 2) ^ 2 ≤ (N + 1) (|n| + N + 1)` and
`2 |t_N| ≤ 10 ^ (-(d + 2))`. We negate the partial sum for a negative odd order, widen it by
`2 |t_N|` and round outward to `d + 1` places. The proof is `besselJ_int_enclosure` with the
checker `besselCheckInt` decided by the kernel (`decide +kernel`): it recomputes the partial
sum and the tail condition of `besselJ_tail_bound`, and uses Mathlib's `Complex.besselJ_neg_int`
for a negative order, so the plan only chooses `N` and a wrong one makes the check fail.
-/

public meta section

namespace CAS.Command.BesselJ

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.Digits

/-- The largest `|n|`. -/
def maxOrder : Nat := 50
/-- The largest `|q|`. -/
def maxArgument : ℚ := 50
/-- The largest denominator of `q`. -/
def maxDenominator : Nat := 1000
/-- The most digits. -/
def maxBesselDigits : Nat := 30

/-- The absolute value of a rational. -/
def ratAbs (x : ℚ) : ℚ := if x < 0 then -x else x

/-- The number of terms `N`, the partial sum `S` of `N` terms of the series of `J_m (q)` and
the bound `2 |t_N|` on its tail: the smallest `N ≥ 1` with `2 (q / 2) ^ 2 ≤ (N + 1) (m + N + 1)`
and `2 |t_N| ≤ 10 ^ (-(digits + 2))`. -/
def besselPlan (m : Nat) (q : ℚ) (digits : Nat) : Option (Nat × ℚ × ℚ) := Id.run do
  let x := q / 2
  let tolerance : ℚ := 1 / 10 ^ (digits + 2)
  let mut factorial : Nat := 1
  for k in [1:m + 1] do
    factorial := factorial * k
  let mut t : ℚ := x ^ m / (factorial : ℚ)
  let mut S : ℚ := 0
  let mut N : Nat := 0
  for _ in [0:2000] do
    if 1 ≤ N && 2 * x ^ 2 ≤ ((N : ℚ) + 1) * ((m : ℚ) + N + 1) && 2 * ratAbs t ≤ tolerance then
      return some (N, S, 2 * ratAbs t)
    S := S + t
    t := t * (-(x ^ 2)) / ((((N + 1) * (m + N + 1) : Nat)) : ℚ)
    N := N + 1
  return none

/-- Run `#cas [N d] (BesselJ n q)`. -/
def logBesselValue (ref : Syntax) (digits : Nat) (order argument input : Syntax) :
    CommandElabM Unit := do
  checkDigitCount ref "N" digits
  if digits > maxBesselDigits then
    throwErrorAt ref "BesselJ accepts at most {maxBesselDigits} digits"
  let nQ ← SpecialFunctions.parseRational "N" order
  unless nQ.den = 1 do
    throwErrorAt order "BesselJ accepts integer orders"
  let n : Int := nQ.num
  if n.natAbs > maxOrder then
    throwErrorAt order "BesselJ accepts orders with |n| ≤ {maxOrder}"
  let q ← SpecialFunctions.parseRational "N" argument
  if ratAbs q > maxArgument || q.den > maxDenominator then
    throwErrorAt argument
      "BesselJ accepts rational points with |q| ≤ {maxArgument} and a denominator of at most \
      {maxDenominator}"
  let some (N, S, T) := besselPlan n.natAbs q digits
    | throwErrorAt input "BesselJ: no number of terms found"
  -- The sign of `J_n = (-1) ^ |n| J_|n|` for a negative odd order.
  let flip := n < 0 && n.natAbs % 2 = 1
  let centre : ℚ := if flip then -S else S
  let k := digits + 1
  let loZ : Int := ⌊(centre - T) * 10 ^ k⌋
  let hiZ : Int := ⌈(centre + T) * 10 ^ k⌉
  unless hiZ - loZ ≤ 10 do
    throwErrorAt input "BesselJ: the enclosure is wider than 10^-{digits}"
  let lo : ℚ := (loZ : ℚ) / 10 ^ k
  let hi : ℚ := (hiZ : ℚ) / 10 ^ k
  let (proposition, proof) ← liftTermElabM do
    let nT ← ratSyntax (n : ℚ)
    let qT ← ratSyntax q
    let loT ← ratSyntax lo
    let hiT ← ratSyntax hi
    let NT : TSyntax `term := ⟨Syntax.mkNumLit (toString N)⟩
    let dT : TSyntax `term := ⟨Syntax.mkNumLit (toString digits)⟩
    let statement ← `(∃ r : ℝ, Complex.besselJ (($nT : ℤ) : ℂ) (($qT : ℚ) : ℂ) = (r : ℂ) ∧
      (($loT : ℚ) : ℝ) ≤ r ∧ r ≤ (($hiT : ℚ) : ℝ) ∧
      (($hiT : ℚ) : ℝ) - (($loT : ℚ) : ℝ) ≤ 1 / 10 ^ $dT)
    -- The enclosure from the kernel's check of the series, the width by `norm_num`.
    Algebra.proveStatement "BesselJ" statement (← `(tactic|
      exact (CAS.Analysis.SpecialFunctions.Bessel.besselJ_int_enclosure ($nT) $NT ($qT) ($loT)
        ($hiT) (by decide +kernel)).elim fun r h ↦ ⟨r, h.1, h.2.1, h.2.2, by norm_num⟩))
  let (output, outputType) :=
    if loZ = hiZ then (s!"{lo}", "exact value")
    else (renderOutcome (.enclosure loZ hiZ k),
      s!"decimal enclosure of width at most 10^-{digits}, with {countText N "term"} of the series")
  logReport ref {
    domain := "Bessel function J_n at a rational point"
    input := surfaceText input
    inputType := "scalar ℝ"
    output
    outputType
  } #[← liftTermElabM <| Algebra.checkedEvidence "BesselJ"
    s!"Enclosure of BesselJ {n} {q}" proposition proof]

end CAS.Command.BesselJ

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.SpecialFunctions.Legendre.Coefficients
public import CAS.CEGA
public import CAS.Command.Arguments
public import CAS.Command.Digits
public import CAS.Continuum.Interval.Rational.DecimalCheck
public import CAS.Expr.RationalEvaluation
public meta import CAS.Analysis.SpecialFunctions.Legendre.Coefficients
public meta import CAS.Command.Digits
public meta import CAS.Continuum.Interval.Rational.DecimalCheck
public meta import CAS.Expr.RationalEvaluation
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Legendre polynomials in the calculator

`#cas (LegendreP n x)` prints the Legendre polynomial `P_n` in monomials, as Mathematica's
`LegendreP[n, x]` does, and proves `∀ x, (legendre n).eval x = …`. At a rational `q`,
`#cas (LegendreP n q)` proves the exact value `v`, and `#cas [N d] (LegendreP n q)` adds its
first `d` significant digits, truncated toward zero, for `1 ≤ d ≤ 2000` as for `#cas [N d] e`.
The theorem of the digits states both the value and the decimal bounds of `#cas [N d] e`, and
the output prints `v = digits` when the digits are exact and `v ≈ digits` otherwise.
`CAS.Command.Calls` reads the calls in all three forms.

The helpers `quoteRat`, `rationalArgument`, `parseRational`, `unparen`, `quoteDecimal`,
`renderRoot`, `valueOutcome?`, `boundsSyntax` and `valueOutput` are shared by the other `#cas`
commands. `parseRational` evaluates an argument with the size guard of `CAS.Command.Arguments`,
and the value at a rational point is evaluated the same way, by `Arguments.polyEvalBelow?`.

## Implementation notes

The theory is in `CAS/Analysis/SpecialFunctions/Legendre/Coefficients.lean`, which expands
`P_n (x) = P̃_n ((1 - x) / 2)` binomially into rational monomial coefficients
(`legendre_eval_eq_sum_coeff`). We compute the coefficients with the faster sum
`legendreCoeff`, and the kernel checks each one, a closed rational computation, through
`legendreMonomialCoeff_eq_legendreCoeff` and `decide +kernel`; `push_cast` and one `ring` then
give the monomials. The value at `q` is `legendre_eval_ratCast` with its rational sum decided in
the same way, and the decimal bounds of the value follow from it by `norm_num`. The degree is at
most `maxLegendreDegree`.
-/

public meta section

namespace CAS.Command.SpecialFunctions

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Continuum
open CAS.Analysis.SpecialFunctions
open CAS.Command.Digits

/-- Simplification lemmas for rational literals cast to `ℝ`. -/
def ratCastLemmas : List Name :=
  [``Rat.cast_div, ``Rat.cast_ofNat, ``Rat.cast_neg, ``Rat.cast_one, ``Rat.cast_zero,
    ``Rat.cast_natCast, ``Rat.cast_intCast]

/-- A rational number as a Lean term `n`, `-n`, `n / d` or `-n / d` of type `ℚ`. -/
def quoteRat (q : ℚ) : MetaM Lean.Expr := do
  let ratType := mkConst ``Rat
  let numerator ← mkNumeral ratType q.num.natAbs
  let numerator ← if q.num < 0 then mkAppM ``Neg.neg #[numerator] else pure numerator
  if q.den = 1 then return numerator
  mkAppM ``HDiv.hDiv #[numerator, ← mkNumeral ratType q.den]

/-- The value of the closed calculator expression `stx`, an argument of the mode `command`, by
`Arguments.rationalValue`: `notRational` when it is not a rational expression or its evaluation
divides by zero, and `tooLarge` when its evaluation meets a literal, or would form a number, with
a numerator or a denominator of more than `Arguments.maxResultDigits` digits. A decimal literal
of `stx` that `Arguments.oversizedDecimal?` refuses gives `tooLarge` before the calculator's
parser reads `stx`; a refusal of the parser is thrown. -/
def rationalArgument (command : String) (stx : Syntax) :
    CommandElabM (Except Arguments.RationalRefusal ℚ) := do
  if (Arguments.oversizedDecimal? stx).isSome then return .error .tooLarge
  return Arguments.rationalValue (← parseClosed command stx)

/-- Read a closed rational calculator expression such as `3 / 2` or `-1`, an argument of the mode
`command`, which the refusals name, by `rationalArgument`. The value is that of
`CAS.Verified.Expr.evalRat?`; an argument is refused, quoted as written, when its evaluation
meets a literal, or would form a number, with a numerator or a denominator of more than
`Arguments.maxResultDigits` digits, and a decimal literal whose mantissa has more digits is
refused first, quoted as written (`Arguments.refuseMantissa`).

Every number that the evaluation forms passes the guard, so an argument with a small value is
refused when its evaluation forms a large number: `10 ^ 10000 - 10 ^ 10000` is refused. The
size refusal of an operand also comes before a division by zero, so `(10 ^ 10000) / 0` is
refused for its size. This holds for every command that reads its numbers here: the calls of
`gamma`, `zeta`, `BesselJ` and the polynomial families at a rational point, the points of
`limit`, the bounds of `nintegrate`, `findRoot`, `maximize`, `minimize` and `sum`, the centres
of `series`, and the initial data of `dsolve`. -/
def parseRational (command : String) (stx : Syntax) : CommandElabM ℚ := do
  if let some (literal, .mantissa) := Arguments.oversizedDecimal? stx then
    Arguments.refuseMantissa command literal
  match ← rationalArgument command stx with
  | .ok q => return q
  | .error .notRational => throwErrorAt stx "{command}: expected a rational number"
  | .error .tooLarge =>
      throwErrorAt stx "{command}: evaluating `{Arguments.argumentText stx}` needs a number with \
        more than {Arguments.maxResultDigits} digits, the most that a rational argument may use"

/-- Strip parentheses. -/
partial def unparen (stx : Syntax) : Syntax :=
  match stx with
  | `(($inner)) => unparen inner
  | _ => stx

/-- A rational number as `m / 10 ^ d` when it has `d` decimals, and as `quoteRat` otherwise. -/
def quoteDecimal (digits : Nat) (q : ℚ) : MetaM Lean.Expr := do
  let scale : ℚ := 10 ^ digits
  let m := q * scale
  if m.den = 1 then
    let ratType := mkConst ``Rat
    let numerator ← mkNumeral ratType m.num.natAbs
    let numerator ← if m.num < 0 then mkAppM ``Neg.neg #[numerator] else pure numerator
    mkAppM ``HDiv.hDiv #[numerator,
      ← mkAppM ``HPow.hPow #[← mkNumeral ratType 10, toExpr digits]]
  else quoteRat q

/-- Render a root interval: its digits when it is a decimal interval of width `10 ^ (-d)`. -/
def renderRoot (digits : Nat) (root : ℚ × ℚ) : String :=
  let scale : ℚ := 10 ^ digits
  let m := ⌊root.1 * scale⌋
  if (m : ℚ) / scale = root.1 && root.2 = ((m : ℚ) + 1) / scale then
    -- The truncation toward zero of a value in `(m, m + 1) / 10 ^ d`.
    if 0 ≤ m then renderDecimal m.toNat digits
    else "-" ++ renderDecimal (-(m + 1)).toNat digits
  else
    s!"({root.1}, {root.2})"

/-! ## Exact values and their digits -/

/-- The rational number that the digits of an outcome denote (the lower end of an enclosure). -/
def outcomeValue : CAS.Command.Digits.Outcome → ℚ
  | .positiveDecimal m k => (m : ℚ) / 10 ^ k
  | .negativeDecimal m k => -((m : ℚ) / 10 ^ k)
  | .positiveScaled m k => (m : ℚ) * 10 ^ k
  | .negativeScaled m k => -((m : ℚ) * 10 ^ k)
  | .enclosure lo _ k => (lo : ℚ) / 10 ^ k

/-- The first `d` significant digits of `value`, truncated toward zero, or a decimal enclosure
when they are not resolved; `none` for the value `0` and for `digits = none`. -/
def valueOutcome? (digits : Option Nat) (value : ℚ) : Option CAS.Command.Digits.Outcome :=
  match digits with
  | some d => if value = 0 then none else
      some ((resolve? d (RationalInterval.const value)).getD
        (enclosureOutcome d (RationalInterval.const value)))
  | none => none

/-- The decimal bounds of `#cas [N d] e` for the outcome, about the real term `t`. -/
def boundsSyntax (t : TSyntax `term) (outcome : CAS.Command.Digits.Outcome) :
    Term.TermElabM (TSyntax `term) := do
  let lit (n : Nat) : TSyntax `term := ⟨Syntax.mkNumLit (toString n)⟩
  match outcome with
  | .positiveDecimal m k =>
      `(($(lit m) : ℝ) / 10 ^ $(lit k) ≤ $t ∧ $t < ($(lit m) + 1) / 10 ^ $(lit k))
  | .negativeDecimal m k =>
      `(-(($(lit m) : ℝ) + 1) / 10 ^ $(lit k) < $t ∧ $t ≤ -($(lit m) : ℝ) / 10 ^ $(lit k))
  | .positiveScaled m k =>
      `(($(lit m) : ℝ) * 10 ^ $(lit k) ≤ $t ∧ $t < ($(lit m) + 1) * 10 ^ $(lit k))
  | .negativeScaled m k =>
      `(-(($(lit m) : ℝ) + 1) * 10 ^ $(lit k) < $t ∧ $t ≤ -($(lit m) : ℝ) * 10 ^ $(lit k))
  | .enclosure lo hi k => do
      let loT ← ratSyntax ((lo : ℚ) / 10 ^ k)
      let hiT ← ratSyntax ((hi : ℚ) / 10 ^ k)
      `(($loT : ℝ) ≤ $t ∧ $t ≤ ($hiT : ℝ))

/-- The output and its kind for the exact value `value` and its outcome
`valueOutcome? digits value`: `v = digits` when the digits denote `v`, `v ≈ digits` when they
truncate it, and `v ∈ [lo, hi]` for an enclosure. -/
def valueOutput (value : ℚ) (digits : Option Nat) :
    Option CAS.Command.Digits.Outcome → String × String
  | none => (s!"{value}", "exact rational value")
  | some (.enclosure lo hi k) =>
      (s!"{value} ∈ {renderOutcome (.enclosure lo hi k)}",
        "exact rational value and a decimal enclosure")
  | some outcome =>
      let relation := if outcomeValue outcome = value then "=" else "≈"
      (s!"{value} {relation} {renderOutcome outcome}",
        s!"exact rational value and its first {digits.getD 0} significant digits, truncated")

/-! ## Legendre polynomials -/

/-- Largest degree accepted by the Legendre commands. -/
def maxLegendreDegree : Nat := 30

/-- The monomial sum `∑ c_j x ^ j` over the nonzero coefficients, highest degree first, as
term syntax with subtraction for negative coefficients. -/
def monomialSum (x : TSyntax `ident) (coefficients : List ℚ) :
    CommandElabM (TSyntax `term) := do
  let monomial (c : ℚ) (j : Nat) : CommandElabM (TSyntax `term) := do
    let cTerm ← ratSyntax c
    match j with
    | 0 => `(($cTerm : ℝ))
    | 1 => `(($cTerm : ℝ) * $x)
    | _ =>
        let jLit : TSyntax `term := ⟨Syntax.mkNumLit (toString j)⟩
        `(($cTerm : ℝ) * $x ^ $jLit)
  let nonzero := (coefficients.zipIdx.filter (·.1 != 0)).reverse
  match nonzero with
  | [] => `((0 : ℝ))
  | (c, j) :: rest =>
      rest.foldlM (fun total (c, j) ↦ do
        if c < 0 then `($total - $(← monomial (-c) j)) else `($total + $(← monomial c j)))
        (← monomial c j)

/-- Render a rational coefficient polynomial in the variable `var`. -/
def renderPolynomial (coefficients : List ℚ) (var : String := "x") : String :=
  let terms := (coefficients.zipIdx.filter (·.1 != 0)).reverse.map fun (c, j) ↦
    let magnitude := if c < 0 then -c else c
    let base := match j with
      | 0 => toString magnitude
      | 1 => if magnitude = 1 then var else s!"{magnitude}*{var}"
      | _ => if magnitude = 1 then s!"{var}^{j}" else s!"{magnitude}*{var}^{j}"
    (decide (c < 0), base)
  match terms with
  | [] => "0"
  | (negative, first) :: rest =>
      rest.foldl (fun total (neg, term) ↦ total ++ (if neg then " - " else " + ") ++ term)
        ((if negative then "-" else "") ++ first)

/-- Run `#cas (LegendreP n x)`, in the variable `var`. -/
def logLegendre (ref : Syntax) (n : Nat) (var : Name := `x) : CommandElabM Unit := do
  if n > maxLegendreDegree then
    throwErrorAt ref "LegendreP accepts degrees up to {maxLegendreDegree}"
  let coefficients := (List.range (n + 1)).map (legendreCoeff n)
  let x := mkIdent var
  let rhs ← monomialSum x coefficients
  let nLit : TSyntax `term := ⟨Syntax.mkNumLit (toString n)⟩
  let rewrites : Array (TSyntax ``Lean.Parser.Tactic.rwRule) ←
      coefficients.zipIdx.toArray.mapM fun (c, j) ↦ do
    let jLit : TSyntax `term := ⟨Syntax.mkNumLit (toString j)⟩
    let cTerm ← ratSyntax c
    `(Lean.Parser.Tactic.rwRule|
        show CAS.Analysis.SpecialFunctions.legendreMonomialCoeff $nLit $jLit = ($cTerm : ℚ) by
          rw [CAS.Analysis.SpecialFunctions.legendreMonomialCoeff_eq_legendreCoeff]
          decide +kernel)
  let statement ← `(∀ $x:ident : ℝ, (CAS.Analysis.SpecialFunctions.legendre $nLit).eval $x = $rhs)
  let proofSyntax ← `(by
    intro $x:ident
    rw [CAS.Analysis.SpecialFunctions.legendre_eval_eq_sum_coeff]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [$rewrites,*]
    push_cast
    ring)
  let report ← liftTermElabM do
    let proposition ← Term.elabTerm statement none
    let proof ← Term.withoutErrToSorry <| Term.elabTerm proofSyntax (some proposition)
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    evidenceReportMessage #[← proofStep "Monomial expansion of the Legendre polynomial"
      ``legendre_eval_eq_sum_coeff proof]
  logReport ref {
    domain := s!"{var} ∈ ℝ"
    input := s!"LegendreP {n} {var}"
    inputType := s!"polynomial in {var}"
    output := renderPolynomial coefficients (renderName var)
    outputType := "polynomial with exact rational coefficients"
  } #[
    computationNode "Checked coefficients" #[
      m!"Coefficients of {var}^0, …, {var}^{n}: {coefficients}",
      m!"Guarantee: the displayed polynomial equals P_{n} at every real {var}"
    ],
    report
  ]

/-- Run `#cas (LegendreP n q)` at a rational `q`: the exact value, and with `digits = some d`
(`#cas [N d] (LegendreP n q)`) also its first `d` significant digits, truncated toward zero, with
their decimal bounds in the theorem. The call `input` is refused when `Arguments.polyEvalBelow?`
needs a number with more than `Arguments.maxResultDigits` digits to evaluate the value. -/
def logLegendreValue (ref : Syntax) (digits : Option Nat) (n : Nat) (argument input : Syntax) :
    CommandElabM Unit := do
  if let some d := digits then checkDigitCount ref "N" d
  if n > maxLegendreDegree then
    throwErrorAt ref "LegendreP accepts degrees up to {maxLegendreDegree}"
  let q ← parseRational (if digits.isSome then "N" else "LegendreP") argument
  let some value := Arguments.polyEvalBelow? ((List.range (n + 1)).map (legendreCoeff n)) q
    | Arguments.refuseEvaluationSize "LegendreP" input
  let outcome? := valueOutcome? digits value
  let nLit : TSyntax `term := ⟨Syntax.mkNumLit (toString n)⟩
  let report ← liftTermElabM do
    let qTerm ← ratSyntax q
    let vTerm ← ratSyntax value
    let lhs ← `((CAS.Analysis.SpecialFunctions.legendre $nLit).eval ($qTerm : ℝ))
    let valueProof ← `(by
      have h := CAS.Analysis.SpecialFunctions.legendre_eval_ratCast $nLit ($qTerm : ℚ)
      rw [show (∑ j ∈ Finset.range ($nLit + 1),
          CAS.Analysis.SpecialFunctions.legendreMonomialCoeff $nLit j * ($qTerm : ℚ) ^ j) =
            ($vTerm : ℚ) by
          simp only [CAS.Analysis.SpecialFunctions.legendreMonomialCoeff_eq_legendreCoeff]
          decide +kernel] at h
      push_cast at h ⊢
      exact h)
    let (statement, proofSyntax) ← match outcome? with
      | none => pure (← `($lhs = ($vTerm : ℝ)), valueProof)
      | some outcome => pure (← `($lhs = ($vTerm : ℝ) ∧ $(← boundsSyntax lhs outcome)),
          ← `(by
            have hV : $lhs = ($vTerm : ℝ) := $valueProof
            exact ⟨hV, by rw [hV] <;> norm_num⟩))
    let proposition ← Term.elabTerm statement none
    let proof ← Term.withoutErrToSorry <| Term.elabTerm proofSyntax (some proposition)
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    evidenceReportMessage #[← proofStep
      (if outcome?.isSome then "Exact value and digits of the Legendre polynomial"
        else "Exact value of the Legendre polynomial")
      ``legendre_eval_ratCast proof]
  let (output, outputType) := valueOutput value digits outcome?
  logReport ref {
    domain := "Legendre polynomial at a rational point"
    input := surfaceText input
    inputType := "scalar ℝ"
    output
    outputType
  } #[report]

end CAS.Command.SpecialFunctions

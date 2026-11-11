/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Common
public import CAS.Polynomial.Quadratic
public import CAS.Polynomial.Sparse.UnivariateCalculus
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Checked equation solving and relation reduction

`#cas [solve x] (lhs = rhs)` describes the complete real solution set of a polynomial equation
with rational coefficients in one real variable. `#cas [reduce x]` also accepts affine
inequalities and disequalities. Constant equations and relations return `True` or `False`. The
sparse computation only proposes coefficients; a proof of equivalence with the original relation
is checked before any result is reported.

## Implementation notes

The elaborator declared here takes equations of degree at most two and affine comparisons. Ring
normalization proves the identity of the difference of the two sides with
`a * (x * x) + b * x + c`; linear arithmetic or the quadratic formula proves the complete
equivalence, the latter through Mathlib's `quadratic_eq_zero_iff_of_discrim_eq_zero` and the
bridges of `CAS/Polynomial/Quadratic.lean` (`CAS.Polynomial.quadratic_eq_zero_iff_false`,
`CAS.Polynomial.quadratic_eq_zero_iff_sqrt`, `CAS.Polynomial.quadratic_eq_zero_iff_centre`).
Irrational roots are written around the centre `-b / (2 a)` as `x = c + √n / k ∨ x = c - √n / k`
with natural numbers `n` and `k` (`CAS.Polynomial.sqrt_div_eq_sqrt_mul_div`), and a double root
is reported once. We write the proof as tactic syntax, so the search only chooses `a`, `b`, `c`
and the printed form; the kernel checks the elaborated proof when `evidenceReportMessage`
validates the report.

Equations of degree three or more, and the other polynomial and rational relations of
`#cas [reduce x]`, go to `CAS.Command.Reduce`, which states their real roots exactly. Further
variables and transcendental functions are refused, with a pointer to
`#cas [findRoot x in [a, b]]` for a certified numerical root.
-/

public meta section

namespace CAS.Command

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Tactic.Explanation

private inductive Relation where
  | eq | ne | lt | le | gt | ge
  deriving BEq

private partial def parseRelation (input : Syntax) :
    CommandElabM (Relation × Syntax × Syntax) := do
  match input with
  | `(($inner:term)) => parseRelation inner
  | `($lhs:term = $rhs:term) => pure (.eq, lhs, rhs)
  | `($lhs:term ≠ $rhs:term) => pure (.ne, lhs, rhs)
  | `($lhs:term < $rhs:term) => pure (.lt, lhs, rhs)
  | `($lhs:term ≤ $rhs:term) => pure (.le, lhs, rhs)
  | `($lhs:term > $rhs:term) => pure (.gt, lhs, rhs)
  | `($lhs:term ≥ $rhs:term) => pure (.ge, lhs, rhs)
  | _ => throwErrorAt input "expected a real equation or comparison"

private def rationalSyntax (q : ℚ) : CommandElabM (TSyntax `term) := do
  let numerator : TSyntax `term := ⟨Syntax.mkNumLit (toString q.num.natAbs)⟩
  let numerator ← if q.num < 0 then `(-$numerator) else pure numerator
  if q.den = 1 then return numerator
  let denominator : TSyntax `term := ⟨Syntax.mkNumLit (toString q.den)⟩
  `($numerator / $denominator)

private def relationSyntax (relation : Relation) (lhs rhs : TSyntax `term) :
    CommandElabM (TSyntax `term) :=
  match relation with
  | .eq => `($lhs = $rhs)
  | .ne => `($lhs ≠ $rhs)
  | .lt => `($lhs < $rhs)
  | .le => `($lhs ≤ $rhs)
  | .gt => `($lhs > $rhs)
  | .ge => `($lhs ≥ $rhs)

private def reverseRelation : Relation → Relation
  | .lt => .gt
  | .le => .ge
  | .gt => .lt
  | .ge => .le
  | relation => relation

private def rationalHolds (relation : Relation) (value : ℚ) : Bool :=
  match relation with
  | .eq => value == 0
  | .ne => value != 0
  | .lt => value < 0
  | .le => value ≤ 0
  | .gt => value > 0
  | .ge => value ≥ 0

private def rationalSqrt? (value : ℚ) : Option ℚ := do
  if value < 0 then none else do
    let numerator := Nat.sqrt value.num.natAbs
    let denominator := Nat.sqrt value.den
    if numerator ^ 2 = value.num.natAbs && denominator ^ 2 = value.den then
      some ((numerator : ℚ) / denominator)
    else none

private def logSolve (ref : Syntax) (solveOnly : Bool) (coordinate : TSyntax `ident)
    (input : TSyntax `term) : CommandElabM Unit := do
  let (relation, lhs, rhs) ← parseRelation input
  if solveOnly && relation != .eq then
    throwErrorAt input "solve expects an equation; use reduce for an affine comparison"
  let left : TSyntax `term := ⟨lhs⟩
  let right : TSyntax `term := ⟨rhs⟩
  let difference ← `($left - $right)
  let reified ← parseExact difference [coordinate.getId]
  let index ← coordinateAt coordinate reified coordinate.getId
  let some polynomial := Verified.Expr.Alg.mvPolyOf? (Verified.Expr.simplify reified.expr)
    | throwErrorAt input "supported fragment: polynomials with rational coefficients in one real \
        variable; for other equations, #cas [findRoot {coordinate.getId} in [a, b]] (f = g) \
        finds a certified root in an interval"
  let degree := Polynomial.Sparse.degreeAt index polynomial
  if degree > 2 || (relation != .eq && degree > 1) then
    throwErrorAt input
      "supported fragment: equations of degree at most two and affine comparisons"
  let coefficient := fun power : Nat ↦ polynomial.foldl (fun sum term ↦
    if term.2 index = power then sum + term.1 else sum) (0 : ℚ)
  let a := coefficient 2
  let b := coefficient 1
  let c := coefficient 0
  let aTerm ← rationalSyntax a
  let bTerm ← rationalSyntax b
  let cTerm ← rationalSyntax c
  let x : TSyntax `term := ⟨coordinate.raw⟩
  let normalized ← relationSyntax relation (← `($aTerm * ($x * $x) + $bTerm * $x + $cTerm))
    (← `(0))
  let (output, finish) ← if a = 0 then do
    let output ← if b = 0 then
        if rationalHolds relation c then `(True) else `(False)
      else
        relationSyntax (if b < 0 then reverseRelation relation else relation) x
          (← rationalSyntax (-c / b))
    let finish ← if relation == .ne && b != 0 then
        `(tactic| constructor <;> intro h <;> contrapose! h <;> linarith)
      else `(tactic| norm_num at * <;> constructor <;> intro h <;> linarith)
    pure (output, finish)
  else do
    let d := b ^ 2 - 4 * a * c
    if d < 0 then
      pure (← `(False), ← `(tactic|
        exact Polynomial.quadratic_eq_zero_iff_false $aTerm $bTerm $cTerm $x
          (by norm_num [discrim])))
    else if d = 0 then
      let output ← relationSyntax .eq x (← rationalSyntax (-b / (2 * a)))
      pure (output, ← `(tactic|
        convert quadratic_eq_zero_iff_of_discrim_eq_zero
          (a := ($aTerm : ℝ)) (b := $bTerm) (c := $cTerm)
          (by norm_num) (by norm_num [discrim]) $x using 1 <;> norm_num))
    else if let some root := rationalSqrt? d then
      let plus ← rationalSyntax ((-b + root) / (2 * a))
      let minus ← rationalSyntax ((-b - root) / (2 * a))
      pure (← `($x = $plus ∨ $x = $minus), ← `(tactic|
        convert Polynomial.quadratic_eq_zero_iff_sqrt $aTerm $bTerm $cTerm $x
          (by norm_num) (by norm_num [discrim]) using 1 <;> norm_num [discrim]))
    else
      -- The roots `centre ± √(n / m)` with `n / m = d / (4 a ^ 2)` in lowest terms, written
      -- `√(n j) / k` with `m j = k ^ 2`: `j = 1` when `m` is a square, `j = k = m` otherwise.
      let centre := -b / (2 * a)
      let D := d / (4 * a ^ 2)
      let m := D.den
      let (j, k) := if Nat.sqrt m ^ 2 = m then (1, Nat.sqrt m) else (m, m)
      let numeral (n : Nat) : TSyntax `term := ⟨Syntax.mkNumLit (toString n)⟩
      let radicand := numeral (D.num.natAbs * j)
      let rad ← if k = 1 then `(Real.sqrt $radicand) else `(Real.sqrt $radicand / $(numeral k))
      let centreTerm ← rationalSyntax centre
      let output ← if centre = 0 then `($x = $rad ∨ $x = -$rad)
        else `($x = $centreTerm + $rad ∨ $x = $centreTerm - $rad)
      pure (output, ← `(tactic| (
        have hcentre : -($bTerm : ℝ) / (2 * $aTerm) = $centreTerm := by norm_num
        have hroot : Real.sqrt (discrim ($aTerm : ℝ) $bTerm $cTerm / (4 * $aTerm ^ 2)) = $rad := by
          rw [show discrim ($aTerm : ℝ) $bTerm $cTerm / (4 * $aTerm ^ 2) =
              $(numeral D.num.natAbs) / $(numeral m) by norm_num [discrim],
            Polynomial.sqrt_div_eq_sqrt_mul_div (n := $(numeral D.num.natAbs))
              (m := $(numeral m)) (j := $(numeral j)) (k := $(numeral k))
              (by norm_num) (by norm_num) (by norm_num)]
          all_goals norm_num
        refine (Polynomial.quadratic_eq_zero_iff_centre $aTerm $bTerm $cTerm $x (by norm_num)
          (by norm_num [discrim])).trans ?_
        rw [hcentre, hroot]
        all_goals norm_num)))
  let proposition ← `(∀ ($coordinate : ℝ), $input ↔ $output)
  let reduceTactic ← if relation == .ne then
      `(tactic| constructor <;> intro h <;> contrapose! h <;> linarith)
    else `(tactic| constructor <;> intro h <;> linarith)
  let proofSyntax ← `(by
    intro $coordinate:ident
    have normalization : $difference = $aTerm * ($x * $x) + $bTerm * $x + $cTerm := by
      ring
    have reduction : $input ↔ $normalized := by
      $reduceTactic:tactic
    refine reduction.trans ?_
    $finish:tactic)
  let (report, renderedOutput) ← liftTermElabM do
    let proposition ← Term.elabTerm proposition none
    let proof ← Term.withoutErrToSorry <| Term.elabTerm proofSyntax (some proposition)
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    let report ← evidenceReportMessage #[← UncheckedExplanationStep.ofProof
      "Complete solution predicate for every real value" proof]
    let renderedOutput ← forallTelescope proposition fun _ body ↦
      renderProp body.getAppArgs[1]!
    pure (report, renderedOutput)
  logReport ref {
    domain := s!"{renderName coordinate.getId} ∈ ℝ"
    input := surfaceText input.raw
    inputType := "real relation"
    output := renderedOutput
    outputType := "equivalent real solution predicate"
  } #[m!"Guarantee: the input and output are equivalent for every real value", report]

end CAS.Command

namespace CAS.Command

open Lean Elab Command

/-- `#cas [solve x] (lhs = rhs)` describes every real solution of a polynomial equation in the real
variable `x` and proves that the description is complete.

## Theorem
The report proves `∀ x : ℝ, lhs = rhs ↔ P x` for the printed predicate `P x`, a disjunction
`x = r₁ ∨ … ∨ x = rₖ`, `True` or `False`. The roots of an equation of degree at most two are
written with square roots, from the quadratic formula. For degree three or more a rational root is
written as a rational and an irrational one as `AlgRoot.real a lo hi`, the only root of the
polynomial with coefficient list `a` in the rational interval `(lo, hi)` of width `10 ^ (-8)`; the
theorem also states `lo < AlgRoot.real a lo hi < hi`, and the output names the root `ρ0`, `ρ1`, …
with its interval (`CAS.Polynomial.RealRoot.solve_of_solveCheck`).

## Conditions and limits
`lhs` and `rhs` are polynomials with rational coefficients in `x` alone, of any degree. A multiple
root is listed once. For several unknowns, `#cas [solve x, y, …] (e₁ ∧ … ∧ eₘ)` solves linear
systems with rational coefficients by exact elimination, square linear systems whose coefficients
are polynomials in one parameter by the cases of the parameter, and polynomial systems with
finitely many complex solutions through a lexicographic Gröbner basis and the certified real roots
of its eliminant; the theorem `∀ x y … : ℝ, e₁ ∧ … ∧ eₘ ↔ S` lists the real solutions `S`.

## Options
None.

## Examples
```lean
#cas [solve x] (x ^ 2 = 2)
```
```output
Output (equivalent real solution predicate): x = sqrt(2) ∨ x = -sqrt(2)
```
```lean
#cas [solve x] (x ^ 3 - 2 = 0)
```
```output
Output (equivalent real solution predicate): x = ρ0
ρ0: the root of x^3 - 2 in (1.25992104, 1.25992105)
```
```lean
#cas [solve x, y] (x^2 + y^2 = 5 ∧ x * y = 2)
```
```output
Output (complete list of real solutions): {x = -1, y = -2}, {x = -2, y = -1}, {x = 2, y = 1},
{x = 1, y = 2}
```

## In a proof
```lean
theorem solve_square : ∀ x : ℝ, x ^ 2 = 1 ↔ x = 1 ∨ x = -1 := by
  cas
```

## See also
Mathematica `Solve` and `Reduce`, SymPy `solveset` and `solve`. The modes `reduce`, `roots`,
`roots z in ℂ`, `findRoot` and `groebner`. Oracle route: `#cas [solve x, y, oracle := sympy] e`,
which proves that each solution the oracle proposes satisfies the equations; that they are all
the solutions is the oracle's claim.

## Possible issues
```lean
#cas [solve x] (sin x = 0)
```
```output
supported fragment: polynomials with rational coefficients in one real variable; for other
equations, #cas [findRoot x in [a, b]] (f = g) finds a certified root in an interval
```
For other equations, `#cas [findRoot x in [a, b]] (f = g)` certifies one root in an interval.
```lean
#cas [solve x] (x < 1)
```
```output
solve expects an equation; use reduce for an affine comparison
```
Use `#cas [reduce x]` for a comparison.
```lean
#cas [solve x, y] (x^2 + y^2 = 1)
```
```output
solve: the system has infinitely many complex solutions; the nonlinear solver takes systems
with finitely many
```
Add equations until the system has finitely many complex solutions.
-/
syntax (name := casSolveCommand) "#cas" "[" &"solve" ident "]" term : command

/-- `#cas [reduce x] (lhs < rhs)` reduces an equation, disequation or comparison of polynomials in
the real variable `x` to an equivalent condition on `x`, a union of intervals whose endpoints are
the real roots of `lhs - rhs`.

## Theorem
For an affine relation, and for an equation of degree at most two, the report proves
`∀ x : ℝ, rel ↔ P x` for the printed condition `P x`. Otherwise it proves
`∃ ρ, (bounds on ρ 0, ρ 1, …) ∧ ∀ x : ℝ, rel ↔ P x`. The rational roots of `lhs - rhs` are
written as rationals, and each other root as `ρ j`, located in a rational interval of width
`10 ^ (-20)`; `∃ ρ` is dropped when every root is rational
(`CAS.Polynomial.RealRoot.of_reduceCheck`).

## Conditions and limits
The relation is `=`, `≠`, `<`, `≤`, `>` or `≥` between polynomials with rational coefficients in
`x` alone, of any degree. A quotient `p / q` compared with `0` is reduced through the product
`p * q`, which has the same sign as `p / q` under Lean's convention `p / 0 = 0`. A relation that
holds for every `x` gives `True`, and one that holds for none gives `False`.

## Options
None.

## Examples
```lean
#cas [reduce x] (-2 * x + 3 ≤ 7)
```
```output
Output (equivalent real solution predicate): x ≥ -2
```
```lean
#cas [reduce x] (x^2 < 2)
```
```output
Output (equivalent condition on the real roots): ρ0 < x < ρ1, where ρ0 = -1.41421356237309504880…,
ρ1 = 1.41421356237309504880…
```
```lean
#cas [reduce x] ((x - 1) / (x + 2) > 0)
```
```output
Output (equivalent condition on the real roots): x < -2 ∨ 1 < x
```

## In a proof
```lean
theorem reduce_positive : ∀ x : ℝ, 0 < x ^ 2 - x + 1 := by
  cas
```

## See also
Mathematica `Reduce`, SymPy `solve_univariate_inequality`. The modes `solve`, `roots` and
`minimize`.

## Possible issues
```lean
#cas [reduce x] (x^2 + 1)
```
```output
expected a real equation or comparison
```
Write a relation, such as `x^2 + 1 > 0`.
```lean
#cas [reduce x] (sin x > 0)
```
```output
supported fragment: polynomials with rational coefficients in one real variable; for other
equations, #cas [findRoot x in [a, b]] (f = g) finds a certified root in an interval
```
Only polynomial and rational relations are reduced. The tactic `cas` proves a sign condition that
holds for every `x`, such as `∀ x : ℝ, 0 < x ^ 2 - x + 1`, but not the equivalence
`∀ x : ℝ, 0 < x ^ 2 - 3 * x + 2 ↔ x < 1 ∨ 2 < x` that the report states.
-/
syntax (name := casReduceCommand) "#cas" "[" &"reduce" ident "]" term : command

elab_rules : command
  | `(#cas [solve $coordinate:ident] $input:term) =>
      logSolve input true coordinate input
  | `(#cas [reduce $coordinate:ident] $input:term) =>
      logSolve input false coordinate input

end CAS.Command

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import CAS
import CASOracle.Solve

/-!
# Solution families of differential equations proposed by an oracle

`#cas [dsolve y x, oracle := o] (equation)`, for an equation in `x`, `y`, `y'`, `y''`, … (any
expressions of the checked language, coefficients depending on `x` included), asks the oracle for
a family `F(c₁, …, cₘ, x)` and proves, with `F⁽ᵏ⁾` the symbolic derivatives of `F`,

`∀ c₁ … cₘ x, conditions → HasDerivAt (fun x ↦ F) F' x ∧ … ∧ HasDerivAt (fun x ↦ F⁽ʳ⁻¹⁾) F⁽ʳ⁾ x
  ∧ equation[y⁽ᵏ⁾ := F⁽ᵏ⁾]`

where `r` is the order, and proves the conditions at one rational point. The theorem says that
the family solves the equation. That it is the general solution (every solution has this form)
is the oracle's claim, shown as a hint; `#cas [dsolve y x]` proves completeness for the linear
equations with constant coefficients it solves.

The oracles with a `dsolve` task are `sympy` and `sage`.

## Implementation notes

We compute the derivatives `F⁽ᵏ⁾` ourselves and state them with `HasDerivAt`, which makes the
family classically differentiable where it solves the equation: Mathlib's `deriv` is `0` where a
function is not differentiable, so an equation about `deriv` alone would say less. The
conditions are the nonvanishing of the denominators and logarithm arguments, and the positivity
of the square-root arguments and real power bases, of `F`, of its derivatives, and of the
equation with `F` substituted (so that `1 / 0 = 0` cannot make a pole of the equation a
solution); they come from the expressions, not from the oracle. The conjuncts are closed by the
first of `cas`, `field_simp; ring` and `simp only [ne_eq] at *; field_simp; ring` that closes
them all.

Conditions that hold nowhere would make the theorem vacuous, so a second checked step proves
them at a rational point. We pick the first of two fixed points at which an uncertified interval
evaluation (`valueAt`) finds them true, and prove each condition there by `norm_num`,
`positivity` or `cega`; a family with no such point, or whose conditions cannot be proved at it,
is refused.
-/

namespace CASOracle.DSolve

open Lean Elab Command Meta Term
open CAS CAS.Command CAS.Command.InfoView
open CASOracle.Accept CASOracle.Wire CASOracle.Integrate

/-- The side conditions of an expression: the denominators and logarithm arguments, which must
not vanish (`true`), and the square-root arguments and real-power bases, which must be
positive (`false`). -/
partial def conditions {n : Nat} : Verified.Expr (Fin n) → List (Verified.Expr (Fin n) × Bool)
  | .div a b => (b, true) :: (conditions a ++ conditions b)
  | .log a => (a, true) :: conditions a
  | .sqrt a => (a, false) :: conditions a
  | .rpow a b => (a, false) :: (conditions a ++ conditions b)
  | .add a b | .mul a b | .sub a b => conditions a ++ conditions b
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a => conditions a
  | _ => []

/-- The value of an expression at a rational point, by interval evaluation (untrusted; it only
screens the conditions). -/
def valueAt {n : Nat} (expression : Verified.Expr (Fin n)) (point : Fin n → ℚ) : Option ℚ := do
  let closed : Verified.Expr (Fin 0) :=
    expression.mapVars fun i ↦ .rat (point i).num (point i).den
  let I ← CAS.Continuum.DigitsEval.eval ⟨96, 48, 120⟩ CAS.Continuum.DigitsEval.closedEnv closed
  return (I.lo + I.hi) / 2

/-- `#cas [dsolve y x, oracle := o] (equation)`. -/
syntax (name := casDSolveOracleCommand)
  "#cas" "[" &"dsolve" ident ident ", " &"oracle" " := " ident "]" term : command

/-- Elaborates `#cas [dsolve y x, oracle := o] (equation)`: the oracle's solution, checked in Lean
before it is reported. -/
@[command_elab casDSolveOracleCommand]
def elabDSolve : CommandElab := fun stx ↦ do
  let `(#cas [dsolve $y:ident $x:ident, oracle := $o:ident] $input:term) := stx
    | throwUnsupportedSyntax
  let oracle ← liftCoreM (oracleOf o)
  let equation : Term := ⟨SpecialFunctions.unparen input⟩
  let `($l = $r) := equation | throwErrorAt input "dsolve: write the equation as `lhs = rhs`"
  -- The order: the most primes on `y` among the identifiers of the equation.
  let derivativeName (k : Nat) : Name :=
    Name.mkSimple (y.getId.toString ++ String.ofList (List.replicate k '\''))
  let inferred ← parseInferred (← `($l - $r))
  let order := (List.range 5).foldl (fun acc k ↦
    if inferred.names.contains (derivativeName k) then k else acc) 0
  unless 1 ≤ order do throwErrorAt input "dsolve: the equation has no derivative of {y.getId}"
  let names := x.getId :: (List.range (order + 1)).map derivativeName
  let n := names.length
  let parseSide (side : Term) : CommandElabM (Verified.Expr (Fin n)) := do
    let reified ← parseExact side names
    if h : reified.names.length = n then return h ▸ reified.expr
    throwErrorAt side "dsolve: unexpected variables"
  let lhs ← parseSide l
  let rhs ← parseSide r
  let equationWire (i : Fin n) : String := if i.val = 0 then "v0" else s!"d{i.val - 1}"
  let derivativeNames := (List.range (order + 1)).map (s!"d{·}")
  let found ← liftTermElabM do
    let text ← Translate.write (Translate.requestLanguage oracle) equationWire
      (Verified.Expr.sub lhs rhs)
    askPython oracle "dsolve" ["constants", "solution"]
      s!"{pyRead text ("v0" :: derivativeNames)}, {pyVariables ["v0"]}[0], \
        {pyVariables derivativeNames}"
  let constantsText ← liftCoreM <| payload oracle found "constants"
  let some m := smallNat? constantsText
    | throwError "the oracle's constant count {constantsText} is not a small natural number"
  unless m ≤ order do throwError "the oracle's family has {m} constants, more than the order"
  -- The family over `x` (coordinate `0`) and the constants `C1, …, Cm` (coordinates `1, …, m`).
  let familyWire (i : Fin (m + 1)) : String := if i.val = 0 then "v0" else s!"C{i.val}"
  let answer ← liftCoreM <| payload oracle found "solution"
  let family ← try liftTermElabM <| Translate.readAnswer oracle familyWire answer
    catch error => throwErrorAt input "dsolve: the family proposed by {oracle.name} is \
        refused: {error.toMessageData}"
  let zero : Fin (m + 1) := ⟨0, Nat.succ_pos m⟩
  -- The derivatives of the family, each admitted as the family was before it is simplified.
  let mut derivatives : Array (Verified.Expr (Fin (m + 1))) := #[family]
  for _ in [0:order] do
    let raw := derivatives.back!.diff zero
    if let some why := Translate.admit raw (m + 1) then
      throwErrorAt input "dsolve: the family proposed by {oracle.name} is refused: its \
        derivative: {why}"
    derivatives := derivatives.push raw.simplify
  -- The conditions of the family, of its derivatives, and of the equation with the family
  -- substituted (so that Lean's `1 / 0 = 0` cannot make a pole of the equation a solution).
  let substitute (side : Verified.Expr (Fin n)) : Verified.Expr (Fin (m + 1)) :=
    side.mapVars fun i ↦ if i.val = 0 then .var zero else derivatives[i.val - 1]!
  let mut sides : Array (Verified.Expr (Fin (m + 1)) × Bool) := #[]
  for derivative in derivatives ++ #[substitute lhs, substitute rhs] do
    for c in conditions derivative do
      unless sides.any (fun (side, b) ↦ side == c.1 && b == c.2) do
        sides := sides.push c
  -- A point where the conditions hold, chosen by an uncertified evaluation and then proved
  -- below, so that the theorem is not vacuous.
  let points : List (Fin (m + 1) → ℚ) := [fun i ↦ if i.val = 0 then 37 / 100 else 13 / 10 + i.val,
    fun i ↦ if i.val = 0 then 29 / 10 else 7 / 10 + 2 * i.val]
  let some point := points.find? (fun point ↦ sides.all fun (side, nonzero) ↦
      match valueAt side point with
      | some v => if nonzero then v ≠ 0 else 0 < v
      | none => false)
    | throwErrorAt input "dsolve: the conditions of the family proposed by {oracle.name} fail \
        at every test point, so a theorem under them could be vacuous; refused"
  let constantIdents := (List.range m).toArray.map fun i ↦ mkIdent (Name.mkSimple s!"c{i + 1}")
  let familyVar (i : Fin (m + 1)) : Term :=
    if i.val = 0 then x else constantIdents.getD (i.val - 1) x
  let dTerms ← derivatives.mapM fun derivative ↦ liftMacroM <| toTerm familyVar derivative
  let equationVar (i : Fin n) : Term := if i.val = 0 then x else dTerms[i.val - 1]!
  let mut conjuncts : Array Term := #[]
  for k in [0:order] do
    conjuncts := conjuncts.push (← `(HasDerivAt (fun $x:ident : ℝ ↦ $(dTerms[k]!))
      $(dTerms[k+1]!) $x))
  conjuncts := conjuncts.push (← `($(← liftMacroM <| toTerm equationVar lhs) =
    $(← liftMacroM <| toTerm equationVar rhs)))
  let some last := conjuncts.back? | throwError "dsolve: nothing to prove"
  let mut body := last
  for c in conjuncts.pop.reverse do
    body ← `($c ∧ $body)
  let conditionTerms ← sides.mapM fun (side, nonzero) ↦ do
    let t ← liftMacroM <| toTerm familyVar side
    if nonzero then `($t ≠ 0) else `(0 < $t)
  for c in conditionTerms.reverse do
    body ← `($c → $body)
  let binders := constantIdents.push x
  let statement ← `(∀ $binders* : ℝ, $body)
  let hypotheses := (List.range conditionTerms.size).toArray.map fun i ↦
    mkIdent (Name.mkSimple s!"h{i}")
  let holes : Array Term ← (List.range conjuncts.size).toArray.mapM fun _ ↦ `(?_)
  let closers : List (TSyntax `tactic) := [← `(tactic| cas), ← `(tactic| (field_simp; ring)),
    ← `(tactic| (simp only [ne_eq] at *; field_simp; ring))]
  let mut proofs : List Term := []
  for closer in closers do
    let split ← if conjuncts.size = 1 then `(tactic| skip)
      else `(tactic| refine ⟨$(Syntax.TSepArray.ofElems holes),*⟩)
    proofs := proofs ++ [← `(by
      intro $(binders ++ hypotheses)*
      $split:tactic
      all_goals $closer:tactic)]
  -- The conditions at the chosen point, each proved.
  let pointTerms ← (List.finRange (m + 1)).toArray.mapM fun i ↦ do
    `(($(← ratSyntax (point i)) : ℝ))
  let pointVar (i : Fin (m + 1)) : Term := pointTerms[i.val]!
  let mut admissible : Array (Lean.Expr × Lean.Expr) := #[]
  for (side, nonzero) in sides do
    let t ← liftMacroM <| toTerm pointVar side
    let statement ← if nonzero then `($t ≠ 0) else `(0 < $t)
    let closers : List (TSyntax `tactic) := [← `(tactic| norm_num), ← `(tactic| positivity),
      ← `(tactic| cega), ← `(tactic| (apply ne_of_gt; cega)), ← `(tactic| (apply ne_of_lt; cega))]
    let attempts ← closers.mapM fun closer ↦ `(by $closer:tactic)
    let some conjunct ← liftTermElabM <| firstProved "dsolve" statement attempts
      | throwErrorAt input "dsolve: the conditions of the family proposed by {oracle.name} \
          could not be proved at a test point; refused"
    admissible := admissible.push conjunct
  let pointText := ", ".intercalate <| (List.finRange (m + 1)).map fun i ↦
    s!"{if i.val = 0 then x.getId.toString else s!"c{i.val}"} = {point i}"
  withAuditedEvidence "dsolve" do
    let some (proposition, proof) ← liftTermElabM <| firstProved "dsolve" statement proofs
      | throwErrorAt input "dsolve: the family proposed by {oracle.name}, \
          {(FullSimplify.Form.ofExpr (x.getId :: constantIdents.toList.map (·.getId))
            family).tidy.render}, is refused: substituting it into the equation could not be \
          proved"
    let mut steps := #[("The family is differentiable and solves the equation", proposition,
      proof)]
    if let some (lastP, lastQ) := admissible.back? then
      let (p, q) ← liftTermElabM <| admissible.pop.foldrM (init := (lastP, lastQ))
        fun (p, q) (accP, accQ) ↦ do return (mkAnd p accP, ← mkAppM ``And.intro #[q, accQ])
      steps := steps.push (s!"The conditions hold at {pointText}", p, q)
    let report ← liftTermElabM <| evidence steps
    let shown := (FullSimplify.Form.ofExpr (x.getId :: constantIdents.toList.map (·.getId))
      family).tidy.render
    logReport input {
      domain := s!"{x.getId} ∈ ℝ under the conditions"
      input := surfaceText input.raw
      inputType := s!"differential equation of order {order}"
      output := s!"{y.getId}({x.getId}) = {shown}"
      outputType := "a family of solutions (checked); that it is the general solution is not"
      conditions? := if conditionTerms.isEmpty then none else
        some (", ".intercalate (sides.toList.map fun (side, nonzero) ↦
          let shown := (FullSimplify.Form.ofExpr
            (x.getId :: constantIdents.toList.map (·.getId)) side).tidy.render
          if nonzero then s!"{shown} ≠ 0" else s!"{shown} > 0"))
    } #[hintsNode oracle #[m!"every solution of the equation has this form"], report]

end CASOracle.DSolve

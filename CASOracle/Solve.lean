/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import CAS
import CASOracle.Integrate

/-!
# Exact solutions proposed by an oracle, checked by substitution

`#cas [solve x, y, oracle := o] (eq₁ ∧ eq₂ ∧ …)` asks the oracle for the real solutions of a
system of equations in the checked expression language. Each solution `(a, b, …)`, a tuple of
closed expressions (rationals, radicals, `π`, …), becomes one theorem: every equation holds at
the point, together with the nonvanishing of every denominator of the equations there. That the
solutions found are all the real solutions is the oracle's claim, shown as a hint; an empty list
proves nothing.

The oracles with a `solve` task are `sympy` and `sage`.

## Implementation notes

We substitute `x := a, y := b, …` at once into every original equation, and we add the
denominators because Lean's `x / 0 = 0` could otherwise make a pole a solution. Each conjunct is
proved by the first of `norm_num`, `cas`, `ring_nf; norm_num` and `field_simp; ring_nf` that
closes it (`proveConjunct`). A solution whose substitution cannot be proved is refused and listed
with the hints.
-/

namespace CASOracle.Solve

open Lean Elab Command Meta Term
open CAS CAS.Command CAS.Command.InfoView
open CASOracle.Accept CASOracle.Wire CASOracle.Integrate

/-- The equations of a conjunction `e₁ ∧ e₂ ∧ …`, each `lhs = rhs`. -/
partial def equations (stx : Syntax) : CommandElabM (Array (Term × Term)) := do
  let stx := SpecialFunctions.unparen stx
  match stx with
  | `($a ∧ $b) => return (← equations a) ++ (← equations b)
  | `($l = $r) => return #[(l, r)]
  | _ => throwErrorAt stx "solve: write the system as `lhs = rhs ∧ …`"

/-- The denominators of an expression. -/
partial def denominators {n : Nat} : Verified.Expr (Fin n) → List (Verified.Expr (Fin n))
  | .div a b => b :: (denominators a ++ denominators b)
  | .add a b | .mul a b | .sub a b | .rpow a b => denominators a ++ denominators b
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a
  | .sqrt a => denominators a
  | _ => []

/-- `#cas [solve x, y, oracle := o] (system)`. -/
syntax (name := casSolveOracleCommand)
  "#cas" "[" &"solve" (atomic(ident ", "))+ &"oracle" " := " ident "]" term : command

/-- Prove `statement` with the first closer that works. -/
def proveConjunct (statement : Term) : TermElabM (Option (Lean.Expr × Lean.Expr)) := do
  for closer in [← `(tactic| norm_num), ← `(tactic| cas), ← `(tactic| (ring_nf; norm_num)),
      ← `(tactic| (field_simp; ring_nf))] do
    if let some result ← tryProve "solve" statement (← `(by $closer:tactic)) then
      return some result
  return none

/-- Elaborates `#cas [solve x, y, oracle := o] (system)`: the oracle's solutions, checked in Lean
before they are reported. -/
@[command_elab casSolveOracleCommand]
def elabSolve : CommandElab := fun stx ↦ do
  let `(#cas [solve $[$xs:ident, ]* oracle := $o:ident] $input:term) := stx
    | throwUnsupportedSyntax
  let oracle ← liftCoreM (oracleOf o)
  let names := xs.toList.map (·.getId)
  let n := names.length
  let parseSide (side : Term) : CommandElabM (Verified.Expr (Fin n)) := do
    let reified ← parseExact side names
    if h : reified.names.length = n then return h ▸ reified.expr
    throwErrorAt side "solve: unexpected variables"
  let system ← (← equations input).mapM fun (l, r) ↦ do return (← parseSide l, ← parseSide r)
  if system.size > 20 then throwErrorAt input "solve: at most 20 equations"
  let solutions ← liftTermElabM do
    let names := wireNames n
    let equations ← system.mapM fun (l, r) ↦
      Translate.write (Translate.requestLanguage oracle) wireName (Verified.Expr.sub l r)
    let found ← askPython oracle "solve" ["solution"]
      s!"[{", ".intercalate (equations.toList.map (pyRead · names))}], {pyVariables names}"
      (allowEmpty := true)
    -- One point per record: one closed expression per variable.
    (← payloads oracle found "solution" 50).mapM fun record ↦ do
      let values := Translate.row record
      unless values.length = n do
        throwError "the oracle's solution {record} does not have {n} values"
      values.toArray.mapM (Translate.readAnswer oracle (fun i : Fin 0 ↦ i.elim0))
  if solutions.isEmpty then
    throwErrorAt input "solve: {oracle.name} reports no real solution (which proves nothing)"
  withAuditedEvidence "solve" do
    let mut steps := #[]
    let mut shown := #[]
    let mut refused := #[]
    for point in solutions do
      let pointTerms ← point.mapM fun v ↦ liftMacroM <| toTerm Fin.elim0 v
      let var (i : Fin n) : Term := pointTerms[i.val]!
      let rendered := ", ".intercalate <| (List.finRange n).map fun i ↦
        s!"{names.getD i.val `x} = {(FullSimplify.Form.ofExpr [] point[i.val]!).tidy.render}"
      let mut conjuncts : Array (Lean.Expr × Lean.Expr) := #[]
      let mut failed := false
      for (l, r) in system do
        let statement ← `($(← liftMacroM <| toTerm var l) = $(← liftMacroM <| toTerm var r))
        let denominatorStatements ← ((denominators l ++ denominators r).toArray).mapM fun d ↦ do
          `($(← liftMacroM <| toTerm var d) ≠ 0)
        for statement in #[statement] ++ denominatorStatements do
          match ← liftTermElabM (proveConjunct statement) with
          | some conjunct => conjuncts := conjuncts.push conjunct
          | none => failed := true
      if failed then
        refused := refused.push rendered
        continue
      let some (lastP, lastQ) := conjuncts.back? | continue
      let (proposition, proof) ← liftTermElabM <| conjuncts.pop.foldrM (init := (lastP, lastQ))
        fun (p, q) (accP, accQ) ↦ do
          return (mkAnd p accP, ← mkAppM ``And.intro #[q, accQ])
      steps := steps.push (s!"The equations hold at {rendered}", proposition, proof)
      shown := shown.push s!"({rendered})"
    if steps.isEmpty then
      throwErrorAt input "solve: no solution proposed by {oracle.name} could be checked \
        (refused: {refused.toList})"
    let report ← liftTermElabM <| evidence steps
    logReport input {
      domain := s!"{", ".intercalate (names.map toString)} ∈ ℝ"
      input := surfaceText input.raw
      inputType := if system.size = 1 then "equation" else s!"{system.size} equations"
      output := " ∨ ".intercalate shown.toList
      outputType := "solutions checked by substitution; completeness not checked"
    } #[hintsNode oracle (#[m!"these are all the real solutions"] ++
        refused.map (m!"{·}: the substitution could not be proved, refused")), report]

end CASOracle.Solve

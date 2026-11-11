/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.LinearAlgebra.Basic
public import CAS.Command.SpecialFunctions
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Linear systems

`#cas [solve x, y, …] (e₁ = f₁ ∧ e₂ = f₂ ∧ …)` solves a system of linear equations with
rational coefficients by exact Gaussian elimination and proves the equivalence of the system
with its solved form for every real assignment: a unique solution `x = a ∧ y = b ∧ …`, the
pivot unknowns as affine functions of the free ones, or `False`. The syntax
`casSolveSystemCommand` is declared here; `CAS.Command.ParamSystems` and
`CAS.Command.PolySystems` add elaborators for systems with a parameter and for nonlinear systems.

## Implementation notes

The answer is found in compiled code by Gauss-Jordan elimination over `ℚ`
(`LinearAlgebra.QMatrix.rowReduce`, `CAS/Command/LinearAlgebra/Basic.lean`) on the augmented rows
`[A | b]`; a pivot in the last column means the system is inconsistent. Nothing of the elimination
is trusted: `linarith` on the real formulas proves the equivalence of the system with the stated
solved form (`solvedTactic`), or the negation of an inconsistent system. `proveWith` elaborates
the proof, and the kernel checks it when `evidenceReportMessage` validates the report.
-/

public meta section

namespace CAS.Command.Systems

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Command.SpecialFunctions

/-- The conjuncts of a conjunction. -/
partial def conjuncts (stx : Syntax) : List Syntax :=
  match unparen stx with
  | `($a ∧ $b) => conjuncts a ++ conjuncts b
  | other => [other]

/-- The coefficients and the constant of an affine expression, if it is affine. -/
def affineCoefficients {n : Nat} (expr : Verified.Expr (Fin n)) : Option (Array ℚ × ℚ) := do
  let p ← Verified.Expr.Alg.mvPolyOf? (Verified.Expr.simplify expr)
  let mut coefficients : Array ℚ := Array.replicate n 0
  let mut constant : ℚ := 0
  for (c, monomial) in p do
    let degree := (List.finRange n).foldl (· + monomial ·) 0
    if degree = 0 then constant := constant + c
    else if degree = 1 then
      let some i := (List.finRange n).find? (monomial · = 1) | none
      coefficients := coefficients.set! i.val (coefficients[i.val]! + c)
    else none
  return (coefficients, constant)

/-- `a + ∑ cᵢ xᵢ` as term syntax over the named unknowns. -/
def affineSyntax (names : Array Name) (constant : ℚ) (coefficients : Array ℚ) :
    CommandElabM (TSyntax `term) := do
  let mut terms : Array (ℚ × TSyntax `term) := #[]
  for i in [0:names.size] do
    let c := coefficients[i]!
    if c != 0 then terms := terms.push (c, ⟨mkIdent names[i]!⟩)
  let constantTerm ← ratSyntax constant
  let constantSyntax ← `(($constantTerm : ℝ))
  if terms.isEmpty then return constantSyntax
  let mut result : Option (TSyntax `term) :=
    if constant = 0 then none else some constantSyntax
  for (c, x) in terms do
    let magnitude ← ratSyntax (if c < 0 then -c else c)
    let monomial ← if c = 1 || c = -1 then pure x else `(($magnitude : ℝ) * $x)
    result := some <| ← match result with
      | none => if c < 0 then `(-$monomial) else pure monomial
      | some total => if c < 0 then `($total - $monomial) else `($total + $monomial)
  return result.get!

/-- Render `a + ∑ cᵢ xᵢ` as a sum of signed terms, as `affineSyntax` builds it: the constant
first unless it is zero and there are other terms, then each unknown with a nonzero coefficient,
written `x`, `-x` or `c*x` with its name as `renderName` prints it, each later term joined by
` + ` or ` - ` after its sign. -/
def renderAffine (names : Array Name) (constant : ℚ) (coefficients : Array ℚ) : String :=
  let signed (c : ℚ) : Bool × ℚ := (decide (c < 0), if c < 0 then -c else c)
  let parts := (List.range names.size).filterMap fun i ↦
    let (negative, magnitude) := signed coefficients[i]!
    let name := renderName names[i]!
    if magnitude = 0 then none
    else some (negative, if magnitude = 1 then name else s!"{magnitude}*{name}")
  let (negative, magnitude) := signed constant
  let terms :=
    (if constant = 0 && !parts.isEmpty then [] else [(negative, toString magnitude)]) ++ parts
  match terms with
  | [] => toString constant
  | (negative, first) :: rest =>
      rest.foldl (fun text (minus, term) ↦ text ++ (if minus then " - " else " + ") ++ term)
        ((if negative then "-" else "") ++ first)

/-- The solved form of a linear system with augmented rows `[A | b]` over the named unknowns:
`none` when it is inconsistent, otherwise the answer `x = … ∧ y = … ∧ ⋯` (pivot unknowns as
affine functions of the free ones), its rendering, and the free unknowns. -/
def solvedForm (names : Array Name) (rows : Array (Array ℚ)) :
    CommandElabM (Option (TSyntax `term × Array String × List Nat)) := do
  let n := names.size
  let (reduced, _, pivots) := LinearAlgebra.QMatrix.rowReduce rows
  if pivots.contains n then return none
  let free := (List.range n).filter (!pivots.contains ·)
  let mut solved : Array (TSyntax `term) := #[]
  let mut rendered : Array String := #[]
  for r in [0:pivots.size] do
    let p := pivots[r]!
    let row := reduced[r]!
    let coefficients := (Array.range n).map fun j ↦ if free.contains j then -row[j]! else 0
    let rhs ← affineSyntax names row[n]! coefficients
    solved := solved.push (← `($(mkIdent names[p]!) = $rhs))
    rendered := rendered.push
      s!"{renderName names[p]!} = {renderAffine names row[n]! coefficients}"
  let answer ← match solved.toList.reverse with
    | [] => `(True)
    | last :: rest => rest.foldlM (fun total eq ↦ `($eq ∧ $total)) last
  return some (answer, rendered, free)

/-- The tactic proving `system ↔ answer` for a solved linear system, after the unknowns are
introduced. -/
def solvedTactic : CommandElabM (TSyntax `tactic) :=
  `(tactic| (
    constructor
    · intro hsystem
      try casesm* _ ∧ _
      repeat' constructor
      all_goals linarith
    · intro hanswer
      try casesm* _ ∧ _
      repeat' constructor
      all_goals linarith))

/-- Run `#cas [solve x, y, …] system`. -/
def logLinearSystem (ref : Syntax) (unknowns : Array (TSyntax `ident)) (input : Syntax) :
    CommandElabM Unit := do
  let names := unknowns.map (·.getId)
  let equations := conjuncts input
  let mut rows : Array (Array ℚ) := #[]
  for equation in equations do
    let (lhs, rhs) ← match equation with
      | `($l:term = $r:term) => pure (l, r)
      | _ => throwErrorAt equation "expected an equation `lhs = rhs`"
    let difference ← `($lhs - $rhs)
    let reified ← parseExact difference names.toList
    unless reified.names.length = names.size do
      throwErrorAt equation "the equation mentions symbols other than the unknowns"
    let some (coefficients, constant) := affineCoefficients reified.expr
      | throwErrorAt equation "solve for several unknowns accepts linear equations with \
          rational coefficients"
    rows := rows.push (coefficients.push (-constant))
  let n := names.size
  let (_, _, pivots) := LinearAlgebra.QMatrix.rowReduce rows
  let inconsistent := pivots.contains n
  let binders := unknowns
  let system : TSyntax `term := ⟨unparen input⟩
  if inconsistent then
    let statement ← `(∀ $binders* : ℝ, ¬ ($system))
    let tactic ← `(tactic| (intro $binders* hsystem; try casesm* _ ∧ _; linarith))
    let proof ← proveWith statement tactic
    let report ← liftTermElabM do
      evidenceReportMessage
        #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
          "The system has no real solution" proof]
    let domain := s!"({renderNames names.toList}) ∈ ℝ^{n}"
    logReport ref {
      domain
      input := surfaceText input
      inputType := "linear system"
      output := "False"
      outputType := "equivalent real solution predicate"
    } #[report]
    return
  -- Pivot unknowns as affine functions of the free ones.
  let some (answer, rendered, free) ← solvedForm names rows
    | throwError "solve: unexpected inconsistent system"
  let statement ← `(∀ $binders* : ℝ, ($system) ↔ $answer)
  let solveTactic ← solvedTactic
  let tactic ← `(tactic| (intro $binders*; $solveTactic))
  let proof ← proveWith statement tactic
  let report ← liftTermElabM do
    evidenceReportMessage
      #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
        "Equivalence with the solved form for every real assignment" proof]
  let output := if rendered.isEmpty then "True" else " ∧ ".intercalate rendered.toList
  let freeNames := free.map fun j ↦ renderName names[j]!
  logReport ref {
    domain := s!"({renderNames names.toList}) ∈ ℝ^{n}"
    input := surfaceText input
    inputType := "linear system"
    output
    outputType := if free.isEmpty then "unique solution"
      else s!"solutions with free parameters {freeNames}" } #[report]

end CAS.Command.Systems

namespace CAS.Command

open Lean Elab Command

/-- `#cas [solve x, y, …] (e₁ ∧ … ∧ eₘ)` solves a system of equations in several real unknowns and
proves `∀ x y … : ℝ, e₁ ∧ … ∧ eₘ ↔ S` for the printed real solutions `S`; see `#cas [solve x]`
for the linear, parametric and polynomial systems it takes.
-/
syntax (name := casSolveSystemCommand) "#cas" "[" &"solve" ident ", " ident,+ "]" term :
  command

elab_rules : command
  | `(#cas [solve $x:ident, $xs:ident,*] $system:term) =>
      Systems.logLinearSystem system (#[x] ++ xs.getElems) system

end CAS.Command

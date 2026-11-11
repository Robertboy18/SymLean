/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import CAS
import CASOracle.Integrate

/-!
# Closed forms of sums proposed by an oracle, checked by induction

`#cas [sum k a n, oracle := o] f` asks the oracle for a closed form `F` of
`∑ k ∈ Finset.Icc a n, f k` and proves, for a natural lower bound `a`,

`∀ n : ℕ, a ≤ n → ∑ k ∈ Finset.Icc a n, f k = F n`

The guard `a ≤ n` is part of the theorem and of the report: below it the sum is empty and the
closed form need not vanish. A closed form outside the checked language (harmonic numbers,
factorials, `Γ`) is refused.

The oracles with a `sum` task are `sympy` and `sage`.

## Implementation notes

We prove the identity by induction from `n = a` (`Nat.le_induction`), which leaves two
identities about `F`. The base case `f a = F a` is closed by `norm_num`. The telescoping step
`F m + f (m + 1) = F (m + 1)`, a rational-function identity in `m`, is closed by the first of
`push_cast; ring`, `push_cast; field_simp; ring` and `push_cast; cas` with `a ≤ m` in context
(for denominators that vanish below the lower bound). A real power `r ^ n` in the oracle's
answer is read as the natural power.
-/

namespace CASOracle.Sum

open Lean Elab Command Meta Term
open CAS CAS.Command CAS.Command.InfoView
open CASOracle.Accept CASOracle.Wire CASOracle.Integrate

/-- `#cas [sum k a n, oracle := o] f`. -/
syntax (name := casSumOracleCommand)
  "#cas" "[" &"sum" ident num ident ", " &"oracle" " := " ident "]" term : command

/-- Elaborates `#cas [sum k a n, oracle := o] f`: the oracle's closed form of the sum, checked in
Lean before it is reported. -/
@[command_elab casSumOracleCommand]
def elabSum : CommandElab := fun stx ↦ do
  let `(#cas [sum $k:ident $a:num $n:ident, oracle := $o:ident] $input:term) := stx
    | throwUnsupportedSyntax
  let oracle ← liftCoreM (oracleOf o)
  let lower := a.getNat
  let f : Verified.Expr (Fin 1) ← match ← parseExact input [k.getId] with
    | ⟨[_], expression, _⟩ => pure expression
    | _ => throwErrorAt input "sum: the summand must be an expression in {k.getId}"
  let closed ← liftTermElabM do
    let text ← Translate.write (Translate.requestLanguage oracle) wireName f
    let found ← askPython oracle "sum" ["closed_form"]
      s!"{pyRead text ["v0"]}, *{pyVariables ["v0"]}, {lower}, *{pyVariables ["n0"]}"
    let answer ← payload oracle found "closed_form"
    try Translate.readAnswer oracle (fun _ : Fin 1 ↦ "n0") answer
    catch error => throwErrorAt input "sum: the closed form proposed by {oracle.name} is \
      refused: {error.toMessageData}"
  let kReal ← `(($k : ℝ))
  let nReal ← `(($n : ℝ))
  let summand ← liftMacroM <| toTerm (fun _ ↦ kReal) f (natVar := fun _ ↦ some k)
  let closedForm ← liftMacroM <| toTerm (fun _ ↦ nReal) closed (natVar := fun _ ↦ some n)
  let aLit : Term := ⟨Syntax.mkNumLit (toString lower)⟩
  let statement ← `(∀ $n:ident : ℕ, $aLit ≤ $n →
    ∑ $k:ident ∈ Finset.Icc $aLit $n, $summand = $closedForm)
  let steps : List (TSyntax `tactic) := [← `(tactic| (push_cast; ring)),
    ← `(tactic| (push_cast; field_simp; ring)),
    ← `(tactic| (have hm' : ($aLit : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
                 push_cast; cas))]
  let mut proofs : List Term := []
  for step in steps do
    proofs := proofs ++ [← `(by
      intro $n:ident h
      induction $n:ident, h using Nat.le_induction with
      | base => norm_num
      | succ m hm ih =>
          rw [Finset.sum_Icc_succ_top (by omega), ih]
          $step:tactic)]
  withAuditedEvidence "sum" do
    let some (proposition, proof) ← liftTermElabM <| firstProved "sum" statement proofs
      | throwErrorAt input "sum: the closed form proposed by {oracle.name}, \
          {(FullSimplify.Form.ofExpr [n.getId] closed).tidy.render}, is refused: the induction \
          from {n.getId} = {lower} could not be proved"
    let report ← liftTermElabM <| evidence
      #[(s!"Closed form for every {n.getId} ≥ {lower}", proposition, proof)]
    logReport input {
      domain := s!"{k.getId} ∈ [{lower}, {n.getId}], {n.getId} ≥ {lower}"
      input := surfaceText input.raw
      inputType := "summand"
      output := (FullSimplify.Form.ofExpr [n.getId] closed).tidy.render
      outputType := s!"closed form, checked by induction for {n.getId} ≥ {lower}"
    } #[report]

end CASOracle.Sum

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Algebra.Dense
public import CAS.Command.Systems
public import CAS.Command.FullSimplify
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Linear systems with a parameter

`#cas [solve x, y, …] (e₁ = f₁ ∧ …)` where the equations are linear in the unknowns with
coefficients polynomial in one further symbol `a` solves the system for every value of `a`, by
a case distinction:

* for `D (a) ≠ 0`, where `D` is the determinant, the unique solution `xᵢ = Nᵢ (a) / D (a)`
  (Cramer's rule), in lowest terms;
* for each rational root `r` of `D`, the system at `a = r`, solved exactly like a numeric
  system (unique solution, a family with free unknowns, or no solution).

The theorem is the conjunction of these statements. Real roots of `D` that are not rational are
reported and not treated. A square system whose determinant vanishes identically is refused. A
system that is not square, has no parameter or more than one, or is not linear in the unknowns
is left to the other elaborators of `#cas [solve x, y, …]`.

## Implementation notes

We compute `D` by cofactor expansion (`det`) and the numerators `Nᵢ` from the adjugate
(`adjugate`), over `ℚ[a]`, and cancel the gcd of `Nᵢ` and `D`. In the generic case
`linear_combination` with the cofactors gives `xᵢ D = Nᵢ` from the equations, and the common
factor cancels; back from the answer, `linear_combination` with `mul_inv_cancel₀` gives
`xᵢ D = Nᵢ` again, and each equation times `D` is a combination of these. The condition on `a` is
none for a constant `D`, `a ≠ rᵢ` when `D` splits into rational linear factors
(`FullSimplify.rationalRoots`), and `D (a) ≠ 0` otherwise. Each special value goes through
`solvedForm` of `CAS.Command.Systems`, and `linarith` proves the solved form (`solvedTactic`) or,
for a value where the system is inconsistent, its negation. The whole conjunction is one
kernel-checked proof.
-/

public meta section

namespace CAS.Command.ParamSystems

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.SpecialFunctions
open CAS.Command.Systems
open CAS.Command.Algebra (Dense)

/-- The determinant by cofactor expansion along the first row. -/
partial def det (m : Array (Array Dense)) : Dense :=
  if m.size == 0 then #[1]
  else if m.size == 1 then (m.getD 0 #[]).getD 0 #[]
  else (List.range m.size).foldl (fun total j ↦
    let minor := (m.extract 1 m.size).map fun row ↦
      (row.extract 0 j) ++ (row.extract (j + 1) row.size)
    let term := Dense.mul ((m.getD 0 #[]).getD j #[]) (det minor)
    if j % 2 == 0 then Dense.add total term else Dense.sub total term) #[]

/-- The adjugate: `adj i j = (-1) ^ (i + j) det (minor j i)`. -/
def adjugate (m : Array (Array Dense)) : Array (Array Dense) :=
  let n := m.size
  (Array.range n).map fun i ↦ (Array.range n).map fun j ↦
    let minor := ((m.extract 0 j) ++ (m.extract (j + 1) n)).map fun row ↦
      (row.extract 0 i) ++ (row.extract (i + 1) row.size)
    let d := det minor
    if (i + j) % 2 == 0 then d else Dense.scale (-1) d

/-- Function names of the calculator syntax, which are not parameters. -/
def functionNames : List Name :=
  [`sin, `cos, `tan, `exp, `log, `sqrt, `atan, `arctan, `asin, `arcsin, `acos, `arccos, `abs,
    `sinh, `cosh, `tanh, `pi, `π]

/-- The identifiers of a syntax tree. -/
partial def identifiers (stx : Syntax) : Array Name :=
  if stx.isIdent then #[stx.getId] else stx.getArgs.foldl (· ++ identifiers ·) #[]

/-- Run `#cas [solve x, y, …] system` with one parameter. -/
def logParamSystem (ref : Syntax) (unknowns : Array (TSyntax `ident)) (input : Syntax) :
    CommandElabM Unit := do
  let names := unknowns.map (·.getId)
  let n := names.size
  let params := (identifiers input).toList.eraseDups.filter fun id ↦
    !id.isAnonymous && !names.contains id && !functionNames.contains id
  let [param] := params | throwUnsupportedSyntax
  let equations := conjuncts input
  unless equations.length = n do throwUnsupportedSyntax
  -- Rows `[A | b]` with entries polynomial in the parameter.
  let mut rows : Array (Array Dense) := #[]
  let mut equationSyntax : Array (TSyntax `term) := #[]
  for equation in equations do
    let (lhs, rhs) ← match equation with
      | `($l:term = $r:term) => pure (l, r)
      | _ => throwUnsupportedSyntax
    let reified ← try parseExact (← `($lhs - $rhs)) (names.toList ++ [param])
      catch _ => throwUnsupportedSyntax
    let m := reified.names.length
    let some poly := Verified.Expr.Alg.mvPolyOf? (Verified.Expr.simplify reified.expr)
      | throwUnsupportedSyntax
    let mut row : Array Dense := Array.replicate (n + 1) #[]
    for (c, mono) in poly do
      let exponents := (List.finRange m).map mono
      let unknownDegree := (exponents.take n).foldl (· + ·) 0
      let paramDegree := exponents.getD n 0
      let monomial : Dense := (Array.replicate paramDegree 0).push c
      if unknownDegree = 0 then
        row := row.set! n (Dense.sub (row.getD n #[]) monomial)
      else if unknownDegree = 1 then
        let some j := (List.range n).find? (exponents.getD · 0 == 1) | throwUnsupportedSyntax
        row := row.set! j (Dense.add (row.getD j #[]) monomial)
      else throwUnsupportedSyntax
    rows := rows.push row
    equationSyntax := equationSyntax.push ⟨equation⟩
  let A := rows.map (·.extract 0 n)
  let b := rows.map (·.getD n #[])
  let D := det A
  if Dense.isZero D then
    throwErrorAt input "solve: the determinant vanishes for every value of {param}"
  let adj := adjugate A
  let numerators := (Array.range n).map fun i ↦
    (List.range n).foldl (fun total j ↦ Dense.add total (Dense.mul ((adj.getD i #[]).getD j #[])
      (b.getD j #[]))) #[]
  let paramIdent := mkIdent param
  let paramT : TSyntax `term := ⟨paramIdent.raw⟩
  let poly (p : Dense) : CommandElabM (TSyntax `term) := monomialSum paramIdent p.toList
  let DT ← poly D
  let system ← match equationSyntax.toList.reverse with
    | [] => throwUnsupportedSyntax
    | last :: rest => rest.foldlM (fun total e ↦ `($e ∧ $total)) last
  let hyps := (Array.range n).map fun j ↦ mkIdent (Name.mkSimple s!"h{j}")
  let hypTerms : Array (TSyntax `term) := hyps.map fun h ↦ ⟨h.raw⟩
  let pattern ← if n == 1 then pure hypTerms[0]! else `(⟨$hypTerms,*⟩)
  -- The generic case: `xᵢ = N'ᵢ / D'ᵢ` in lowest terms, `D = ℓ g D'`, `Nᵢ = ℓ g N'ᵢ`.
  let mut answers : Array (TSyntax `term) := #[]
  let mut forwards : Array (TSyntax `term) := #[]
  let mut backs : Array (TSyntax `term) := #[]
  let mut haves : Array (TSyntax `tactic) := #[]
  let mut reduced : Array (Dense × Dense) := #[]
  for i in [0:n] do
    let xi : TSyntax `term := ⟨mkIdent names[i]!⟩
    let N := numerators.getD i #[]
    let g := Dense.gcd N D
    let Dr := (Dense.divMod D g).1
    let Nr := (Dense.divMod N g).1
    let ℓ := Dense.lead Dr
    let D' := Dense.scale (1 / ℓ) Dr
    let N' := Dense.scale (1 / ℓ) Nr
    reduced := reduced.push (N', D')
    let factorT ← poly (Dense.scale ℓ g)
    let N'T ← poly N'
    let D'T ← poly D'
    let constantDenominator := D'.size ≤ 1
    answers := answers.push (← if constantDenominator then `($xi = $N'T)
      else `($xi = $N'T / $D'T))
    -- Forward: `xᵢ D = Nᵢ` from the cofactors, then cancel `ℓ g`.
    let mut combination : Option (TSyntax `term) := none
    for j in [0:n] do
      let c := (adj.getD i #[]).getD j #[]
      if Dense.isZero c then continue
      let hj : TSyntax `term := ⟨hyps[j]!.raw⟩
      let cT ← poly c
      let term ← `(($cT) * $hj)
      combination := some (← match combination with
        | none => pure term
        | some t => `($t + $term))
    let cancelled ← match combination with
      | none => `(by linear_combination)
      | some t => `(by linear_combination $t:term)
    let hfactor ← `((fun h ↦ hD (by linear_combination ($D'T) * h) : $factorT ≠ 0))
    let hden ← `((fun h ↦ hD (by linear_combination ($factorT) * h) : $D'T ≠ 0))
    forwards := forwards.push (← if constantDenominator then
        `(mul_right_cancel₀ $hfactor (show $xi * $factorT = $N'T * $factorT from $cancelled))
      else `(eq_div_of_mul_eq $hden (mul_right_cancel₀ $hfactor
        (show $xi * $D'T * $factorT = $N'T * $factorT from $cancelled))))
    -- Backward: `xᵢ D = Nᵢ` from the answer.
    let hx : TSyntax `ident := mkIdent (Name.mkSimple s!"hx{i}")
    let ha : TSyntax `term := ⟨(mkIdent (Name.mkSimple s!"ha{i}")).raw⟩
    let ℓgN' ← poly (Dense.mul (Dense.scale ℓ g) N')
    haves := haves.push (← if constantDenominator then
        `(tactic| have $hx : $xi * $DT = $(← poly N) := by linear_combination ($DT) * $ha)
      else `(tactic| have $hx : $xi * $DT = $(← poly N) := by
          linear_combination ($DT) * $ha + ($ℓgN') * (mul_inv_cancel₀ $hden)))
  let answer ← match answers.toList.reverse with
    | [] => throwUnsupportedSyntax
    | last :: rest => rest.foldlM (fun total e ↦ `($e ∧ $total)) last
  -- Each equation times `D` is a combination of `xⱼ D = Nⱼ`.
  for i in [0:n] do
    let mut combination : Option (TSyntax `term) := none
    for j in [0:n] do
      let c := (A.getD i #[]).getD j #[]
      if Dense.isZero c then continue
      let hxj : TSyntax `term := ⟨(mkIdent (Name.mkSimple s!"hx{j}")).raw⟩
      let term ← `(($(← poly c)) * $hxj)
      combination := some (← match combination with
        | none => pure term
        | some t => `($t + $term))
    let inner ← match combination with
      | none => `(by linear_combination)
      | some t => `(by linear_combination $t:term)
    backs := backs.push (← `(mul_right_cancel₀ hD $inner))
  let answerHyps : Array (TSyntax `term) := (Array.range n).map fun i ↦
    ⟨(mkIdent (Name.mkSimple s!"ha{i}")).raw⟩
  let answerPattern ← if n == 1 then pure answerHyps[0]! else `(⟨$answerHyps,*⟩)
  let mut substitute : TSyntax `tactic ← `(tactic| intro $answerPattern:term)
  for h in haves do
    substitute ← `(tactic| ($substitute:tactic; $h:tactic))
  -- The condition of the generic case: none for a constant determinant, `a ≠ rᵢ` when the
  -- determinant splits into rational linear factors, `D (a) ≠ 0` otherwise.
  let (roots, rest) := FullSimplify.rationalRoots D.toList
  let unresolved := rest.length > 1
  let core ← `(⟨fun $pattern ↦ ⟨$forwards,*⟩, by $substitute:tactic; exact ⟨$backs,*⟩⟩)
  let (generic, genericProof, conditionText) ← if (Dense.trim D).size ≤ 1 then do
      let statement ← `(∀ $paramIdent:ident $unknowns* : ℝ, ($system) ↔ $answer)
      let proofStx ← `(fun $paramIdent:ident $unknowns* ↦
        have hD : $DT ≠ 0 := (by norm_num); $core)
      pure (statement, proofStx, "")
    else if !unresolved then do
      -- `D = c ∏ (a - rᵢ) ^ mᵢ`.
      let c := (rest.head?).getD 1
      let cT ← `(($(← ratSyntax c) : ℝ))
      let mut hyps : Array (TSyntax `ident) := #[]
      let mut conditions : Array (TSyntax `term) := #[]
      let mut factors : Array (TSyntax `term) := #[]
      let mut nonzero : Array (TSyntax `term) := #[]
      for idx in [0:roots.length] do
        let (r, multiplicity) := roots.getD idx (0, 1)
        let rT ← `(($(← ratSyntax r) : ℝ))
        let h := mkIdent (Name.mkSimple s!"hne{idx}")
        let hT : TSyntax `term := ⟨h.raw⟩
        let mLit : TSyntax `num := Syntax.mkNumLit (toString multiplicity)
        hyps := hyps.push h
        conditions := conditions.push (← `($paramT ≠ $rT))
        factors := factors.push (← `(($paramT - $rT) ^ $mLit))
        nonzero := nonzero.push (← `(pow_ne_zero $mLit (sub_ne_zero.mpr $hT)))
      let product ← factors[1:].foldlM (fun total f ↦ `($total * $f)) factors[0]!
      let nonzeroProduct ← nonzero[1:].foldlM (fun total f ↦ `(mul_ne_zero $total $f))
        nonzero[0]!
      let mut statementBody ← `(($system) ↔ $answer)
      for condition in conditions.reverse do
        statementBody ← `($condition → $statementBody)
      let statement ← `(∀ $paramIdent:ident $unknowns* : ℝ, $statementBody)
      let hDProof ← `((by
          rw [show $DT = $cT * ($product) by ring]
          exact mul_ne_zero (by norm_num) $nonzeroProduct))
      let proofStx ← `(fun $paramIdent:ident $unknowns* $hyps* ↦
        have hD : $DT ≠ 0 := $hDProof; $core)
      let text := " ∧ ".intercalate (roots.map fun (r, _) ↦
        s!"{renderName param} ≠ {r}")
      pure (statement, proofStx, text)
    else do
      let statement ← `(∀ $paramIdent:ident $unknowns* : ℝ, $DT ≠ 0 → (($system) ↔ $answer))
      let proofStx ← `(fun $paramIdent:ident $unknowns* hD ↦ $core)
      pure (statement, proofStx, s!"{(renderPolynomial D.toList).replace "x"
        (renderName param)} ≠ 0")
  -- The special values: the rational roots of the determinant.
  let mut cases : Array (TSyntax `term × TSyntax `term) := #[]
  let mut renderedCases : Array String := #[]
  for (r, _) in roots do
    let numeric : Array (Array ℚ) := rows.map fun row ↦ row.map (Dense.eval · r)
    let rT ← `(($(← ratSyntax r) : ℝ))
    let tactic ← solvedTactic
    match ← solvedForm names numeric with
    | some (special, rendered, _) =>
        let statement ← `(∀ $paramIdent:ident $unknowns* : ℝ, $paramT = $rT →
          (($system) ↔ $special))
        let proofStx ← `(by
          intro $paramIdent:ident $unknowns* hparam
          subst hparam
          $tactic:tactic)
        cases := cases.push (statement, proofStx)
        renderedCases := renderedCases.push s!"{param} = {r}: {" ∧ ".intercalate rendered.toList}"
    | none =>
        let statement ← `(∀ $paramIdent:ident $unknowns* : ℝ, $paramT = $rT → ¬ ($system))
        let proofStx ← `(by
          intro $paramIdent:ident $unknowns* hparam hsystem
          subst hparam
          try casesm* _ ∧ _
          linarith)
        cases := cases.push (statement, proofStx)
        renderedCases := renderedCases.push s!"{param} = {r}: no solution"
  let proof ← liftTermElabM do
    let mut parts : Array Lean.Expr := #[← elabCheckedProof "solve" generic genericProof]
    for (statement, proofStx) in cases do
      parts := parts.push (← elabCheckedProof "solve" statement proofStx)
    let combined ← match parts.toList.reverse with
      | [] => throwError "solve: nothing to prove"
      | last :: rest => rest.foldlM (fun total p ↦ mkAppM ``And.intro #[p, total]) last
    let cleaned ← Digits.cleanProof combined (ratCastLemmas ++ [``one_mul, ``mul_one,
      ``zero_add, ``add_zero, ``pow_one]) (simprocs := true)
    let cleaned ← Digits.evaluateNumerals cleaned
    let named := Digits.restoreNames (← inferType combined) (← inferType cleaned)
    let cleaned ← mkExpectedTypeHint cleaned named
    CAS.Tactic.Explanation.kernelCheckedProof "solve" named cleaned
  let report ← liftTermElabM do
    evidenceReportMessage
      #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
        "The solution for every value of the parameter" proof]
  let paramName := renderName param
  let render (p : Dense) : String :=
    (renderPolynomial p.toList).replace "x" paramName
  let genericText := " ∧ ".intercalate ((List.range n).map fun i ↦
    let (N', D') := reduced.getD i (#[], #[1])
    s!"{renderName names[i]!} = " ++
      (if D'.size ≤ 1 then render N'
        else
          let top := if (Dense.trim N').size ≤ 1 then render N' else s!"({render N'})"
          s!"{top}/({render D'})"))
  let output := genericText ++ (if conditionText.isEmpty then "" else s!" for {conditionText}") ++
    (if renderedCases.isEmpty then "" else "; " ++ "; ".intercalate renderedCases.toList) ++
    (if unresolved then "; the determinant has a factor without rational roots, \
      whose real roots are not treated" else "")
  logReport ref {
    domain := s!"({renderNames names.toList}) ∈ ℝ^{n}, {param} ∈ ℝ"
    input := surfaceText input
    inputType := s!"linear system with the parameter {param}"
    output
    outputType := "solution by cases of the parameter"
  } #[report]

end CAS.Command.ParamSystems

namespace CAS.Command

open Lean Elab Command

elab_rules : command
  | `(#cas [solve $x:ident, $xs:ident,*] $system:term) =>
      ParamSystems.logParamSystem system (#[x] ++ xs.getElems) system

end CAS.Command

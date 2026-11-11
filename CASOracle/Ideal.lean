/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team

Asking the oracle for cofactors with respect to the original generators (not to a Gröbner
basis) follows the Macaulay2 route of DSLean (https://github.com/taterowney/DSLean, CC-BY-4.0);
see NOTICE.
-/

import CAS
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic.LinearCombination
import CASOracle.Integrate
import CASOracle.Sos

/-!
# Cofactor certificates: polynomial consequences, ideal membership, ideal bases

The oracle finds cofactors; Lean checks one ring identity.

* `cas [oracle := o]` on an equation `lhs = rhs` in a commutative ring, with hypotheses
  `hᵢ : aᵢ = bᵢ` of the same type in context: the oracle returns `cᵢ` and `k` with
  `(lhs - rhs) ^ k = ∑ cᵢ (aᵢ - bᵢ)`, and the goal is closed by
  `linear_combination (exp := k) ∑ cᵢ * hᵢ`, which suggests itself ("Try this"), so the proof
  no longer needs the oracle. It does the work of Mathlib's `polyrith`, whose Sage server is shut
  down, with a local oracle. It proves consequences in the ideal of the hypotheses, not every
  real implication: `x ^ 2 = 0 → x = 0` has no such certificate with `k = 1`.
* `cas [oracle := o]` on `f ∈ Ideal.span {g₁, …, gₘ}`: the oracle's `cᵢ` with
  `f = ∑ cᵢ gᵢ`, checked by the certificate checker of the bare `cas` on ideal goals
  (`CAS.Command.Ideal`).
* `#cas [groebner x, y, oracle := o] [f₁, …, fₘ]` for polynomials with rational coefficients:
  the oracle's basis `g₁, …, gₖ` with cofactors both ways, checked like the basis of
  `#cas [groebner x, y]`, and the theorem `Ideal.span {f₁, …} = Ideal.span {g₁, …}` in
  `MvPolynomial (Fin n) ℚ`, `X i` standing for the `i`-th declared variable. The Gröbner property
  of the `gⱼ` for `MonomialOrder.lex` is proved as well, from a division of every S-polynomial
  that the kernel checks (`CAS.Command.Ideal.basisGroebnerProperty`). Each `gⱼ` is scaled to
  coprime integer coefficients with a positive leading coefficient. Zero elements are accepted,
  and the empty basis of the zero ideal is printed `0` and written `{0}` in the theorems. That
  the basis is the reduced one is the oracle's claim, shown as a hint.
* `cas [oracle := o]` on an inequality between polynomials goes to `CASOracle.Sos`.

Cofactors are computed over `ℚ`. In a ring that is not a `ℚ`-algebra, a certificate with a
denominator is refused; nothing is cleared silently. A nonzero remainder from the oracle is never
read as non-membership.

The oracles with these tasks (`member`, `groebner`) are `sympy` and `sage`.

## Implementation notes

The cofactors are taken with respect to the original generators, not to a Gröbner basis, so
that the certificate is one identity in the hypotheses themselves. We follow the Macaulay2
route of DSLean here: it divides by a Gröbner basis and multiplies the quotients by the change
matrix that writes the basis in the generators. SymPy returns bases without cofactors, so the
`sympy` oracle runs a Buchberger algorithm of ours in lex order that tracks, for each new
element, its cofactors in the generators, and then divides `f ^ k` by the tracked basis for
`k = 1, 2, …` up to a bound. The `sage` oracle asks SageMath, which computes the basis and the
cofactors with Singular. Neither computation is trusted: the kernel checks the identity, and
for `groebner` the cofactors both ways and the division of every S-polynomial.

## References

* taterowney, *DSLean: A Bi-directional Interface Between Lean 4 and External Languages*,
  <https://github.com/taterowney/DSLean>, licensed under CC BY 4.0,
  <https://creativecommons.org/licenses/by/4.0/>. NOTICE gives the revision we pin, and
  `DSLean/LeanM2.lean` the Macaulay2 route.
-/

namespace CASOracle.Ideal

open Lean Elab Command Meta Term Tactic
open CAS CAS.Command CAS.Command.InfoView
open CASOracle.Accept CASOracle.Wire CASOracle.Integrate

/-! ## Cofactors from the oracle -/

/-- The cofactors of an oracle's `member` answer, with its power: `target ^ k` is proposed to be
the combination of the `generators` with the cofactors. -/
def cofactors (oracle : Oracle) {n : Nat} (target : Verified.Expr (Fin n))
    (generators : Array (Verified.Expr (Fin n))) (maxPower : Nat) :
    TermElabM (Nat × Array (Verified.Expr (Fin n))) := do
  let names := wireNames n
  let write := Translate.write (Translate.requestLanguage oracle) wireName
  let targetText ← write target
  let generatorTexts ← generators.mapM write
  let found ← askPython oracle "member" ["power", "cofactors"]
    s!"{pyRead targetText names}, [{", ".intercalate (generatorTexts.toList.map
      (pyRead · names))}], {pyVariables names}, {maxPower}"
  let powerText ← payload oracle found "power"
  let some power := smallNat? powerText
    | throwError "the oracle's power {powerText} is not a small natural number"
  unless 1 ≤ power ∧ power ≤ maxPower do throwError "the oracle's power {power} is out of range"
  let row := Translate.row (← payload oracle found "cofactors")
  unless row.length = generators.size do
    throwError "the oracle gave {row.length} cofactors for {generators.size} generators"
  return (power, ← row.toArray.mapM (Translate.readAnswer oracle wireName))

/-- The term of a cofactor, its atoms written by `atomTerms`; `none` for the zero cofactor. -/
def cofactorTerm {n : Nat} (atomTerms : Array Term) (c : Verified.Expr (Fin n)) :
    TermElabM (Option Term) := do
  if Translate.constantValue? c == some 0 then return none
  match Translate.ringTerm (fun i ↦ atomTerms[i.val]!) c with
  | .ok term => return some (← liftMacroM term)
  | .error reason => throwError "the oracle's cofactor is refused: {reason}"

/-! ## Polynomial consequences of hypotheses -/

/-- Close `lhs = rhs` from the equations of the context with `linear_combination` and the
oracle's cofactors; returns the suggested call. -/
def closeByCombination (oracle : Oracle) : TacticM (TSyntax `tactic) := do
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  let some (type, lhs, rhs) := target.consumeMData.eq?
    | throwError "cas [oracle]: the goal is not an equation"
  withMainContext do
    let mut hypotheses : Array (Lean.Expr × Lean.Expr × Lean.Expr) := #[]
    for declaration in ← getLCtx do
      if declaration.isImplementationDetail then continue
      let declType ← instantiateMVars declaration.type
      if let some (hType, a, b) := declType.consumeMData.eq? then
        if ← isDefEq hType type then
          hypotheses := hypotheses.push (declaration.toExpr, a, b)
    if hypotheses.isEmpty then
      throwError "cas [oracle]: no hypothesis is an equation in the type of the goal"
    if hypotheses.size > 64 then throwError "cas [oracle]: more than 64 equations in context"
    let ((target, generators), atoms) ← (do
        let target ← CAS.Command.Ideal.reifyPoly (← mkAppM ``HSub.hSub #[lhs, rhs])
        let generators ← hypotheses.mapM fun (_, a, b) ↦ do
          CAS.Command.Ideal.reifyPoly (← mkAppM ``HSub.hSub #[a, b])
        return (target, generators) : StateT (Array Lean.Expr) MetaM _).run #[]
    let (power, proposed) ← cofactors oracle (CAS.Command.Ideal.overAtoms atoms.size target)
      (generators.map (CAS.Command.Ideal.overAtoms atoms.size)) 4
    let atomTerms ← atoms.mapM fun a ↦ Term.exprToSyntax a
    let shownAtoms ← atoms.mapM fun a ↦ do return (← PrettyPrinter.delab a : Term)
    let hypothesisTerm (proof : Lean.Expr) (shown : Bool) : TacticM Term := do
      if let .fvar id := proof then
        let declaration ← id.getDecl
        let name := declaration.userName
        if !name.hasMacroScopes &&
            ((← getLCtx).findFromUserName? name).map (·.fvarId) == some id then
          return mkIdent name
      if shown then return ← `(‹_›)
      Term.exprToSyntax proof
    let combination (terms : Array Term) (shown : Bool) : TacticM Term := do
      let mut sum : Option Term := none
      for ((proof, _, _), cofactor) in hypotheses.zip proposed do
        let some c ← cofactorTerm terms cofactor | continue
        let h ← hypothesisTerm proof shown
        let summand ← if Translate.constantValue? cofactor == some 1 then pure h
          else `($c * $h)
        sum := some (← match sum with | none => pure summand | some s => `($s + $summand))
      return sum.getD (← `(0))
    let exponent : TSyntax `num := Syntax.mkNumLit (toString power)
    let combined ← combination atomTerms false
    let shownCombined ← combination shownAtoms true
    let tactic ← `(tactic| linear_combination (exp := $exponent) $combined:term)
    let suggestion ← if power = 1 then `(tactic| linear_combination $shownCombined:term)
      else `(tactic| linear_combination (exp := $exponent) $shownCombined:term)
    closeGoal s!"cas [oracle := {oracle.name}]" fun goal ↦ do
      try
        let remaining ← Tactic.run goal (evalTactic tactic)
        unless remaining.isEmpty do throwError "linear_combination left goals"
      catch error =>
        throwError m!"cas [oracle := {oracle.name}]: the cofactors proposed by {oracle.name} \
          are refused: linear_combination fails with them{indentD error.toMessageData}"
    return suggestion

/-! ## Ideal membership -/

/-- Close `f ∈ Ideal.span {g₁, …}` from the oracle's cofactors, checked like the certificates of
the bare `cas` on ideal goals. -/
def closeMembership (oracle : Oracle) : TacticM Unit := do
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  let (``Membership.mem, #[_, _, _, ideal, element]) := target.consumeMData.getAppFnArgs
    | throwError "cas [oracle]: the goal is not a membership"
  withMainContext do
    let some (ring, generators) ← CAS.Command.Ideal.spanGenerators? ideal
      | throwError "cas [oracle]: the goal is not a membership in `Ideal.span` of a set literal"
    let (exprs, atoms) ← ((#[element] ++ generators.map (·.1)).mapM
      CAS.Command.Ideal.reifyPoly).run #[]
    let typed := exprs.map (CAS.Command.Ideal.overAtoms atoms.size)
    let some polys := typed.mapM CAS.Command.Ideal.poly?
      | throwError "cas [oracle]: an element of the goal is not a polynomial in its atoms"
    let ctx ← CAS.Command.Ideal.Ctx.ofRing ring atoms
    let (_, proposed) ← cofactors oracle (typed[0]?.getD (.nat 0)) (typed.extract 1 typed.size) 1
    let some rows := proposed.mapM CAS.Command.Ideal.poly?
      | throwError "cas [oracle := {oracle.name}]: the cofactors proposed by {oracle.name} are \
          refused: one of them is not a polynomial with rational coefficients"
    let (_, facts) := CAS.Command.Ideal.generatorFacts generators (polys.extract 1 polys.size)
    let member : CAS.Command.Ideal.Input := { term := element, poly := polys[0]!, integral := true }
    closeGoal s!"cas [oracle := {oracle.name}]" fun goal ↦ do
      try
        let proof ← CAS.Command.Ideal.memberFrom ctx ideal member (facts.zip rows)
        unless ← isDefEq (← inferType proof) (← goal.getType) do
          throwError "the membership proof has another type"
        goal.assign proof
      catch error =>
        throwError m!"cas [oracle := {oracle.name}]: the cofactors proposed by {oracle.name} \
          are refused{indentD error.toMessageData}"

/-! ## The tactic -/

/-- The argument of `cas [oracle := o]`. -/
syntax (name := casOracle) "[" &"oracle" " := " ident "]" : casArgs

/-- `cas [oracle := o]` proves an interval-integral identity through the oracle's primitive, a
membership in `Ideal.span` of a set literal, an inequality between polynomials from a sum of
squares (`CASOracle.Sos`), or an equation from the equations in context, and checks the oracle's
certificate. -/
tactic_extension CAS.ExactTactic.tacticCas

/-- Elaborates `cas [oracle := o]`: dispatches on the goal (an interval integral, an ideal
membership, an inequality between polynomials or an equation from the hypotheses) and checks the
oracle's certificate. -/
@[tactic CAS.ExactTactic.tacticCas]
def evalOracleTactic : Tactic := fun stx ↦ do
  let `(tactic| cas [oracle := $o:ident]) := stx | throwUnsupportedSyntax
  let oracle ← liftM (oracleOf o)
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  let isOrder ← withMainContext do CASOracle.Sos.isOrderGoal target
  -- The tactic to record for `cas?` and the suggestion of `cas`, which for a sum of squares is
  -- the text that was parsed and run.
  let plain (tactic : TSyntax `tactic) :
      Option (TSyntax `tactic × Lean.Meta.Tactic.TryThis.Suggestion) :=
    some (tactic, { suggestion := .tsyntax tactic })
  let suggestion? ←
    if (integrandOf? target).isSome then
      plain <$> integrateByOracle oracle
    else if target.consumeMData.isAppOf ``Membership.mem then
      closeMembership oracle
      pure none
    else if isOrder then
      some <$> CASOracle.Sos.closeBySos oracle
    else
      plain <$> closeByCombination oracle
  -- Under `cas?` the suggestion is the replay of the recorded route.
  let replay ← (suggestion?.map (·.1)).getDM `(tactic| cas [oracle := $o])
  let recorded ← CAS.ExactTactic.recordRoute (.registered `oracle { replay })
  if let some (_, suggestion) := suggestion? then
    unless recorded do
      Lean.Meta.Tactic.TryThis.addSuggestion stx suggestion (origSpan? := stx)

/-! ## Ideal bases -/

/-- A polynomial as a checked expression for the oracle, the sum of its terms `c * x ^ k * …`. -/
def polyAsExpr {n : Nat} (p : CAS.Command.Groebner.Poly) : Verified.Expr (Fin n) :=
  let term (m : CAS.Command.Groebner.Mono) (c : ℚ) : Verified.Expr (Fin n) :=
    let powers := (List.finRange n).filterMap fun i ↦
      let e := m.getD i.val 0
      if e = 0 then none else if e = 1 then some (Verified.Expr.var i)
      else some (Verified.Expr.pow (.var i) e)
    match powers with
    | [] => ratExprIn c
    | x :: xs =>
        let monomial := xs.foldl .mul x
        if c = 1 then monomial else if c = -1 then .neg monomial
        else .mul (ratExprIn c) monomial
  match p with
  | [] => .nat 0
  | (m, c) :: rest => rest.foldl (fun acc (m, c) ↦ .add acc (term m c)) (term m c)

/-- `#cas [groebner x, y, oracle := o] [f₁, …]`. -/
syntax (name := casGroebnerOracleCommand)
  "#cas" "[" &"groebner" (atomic(ident ", "))+ &"oracle" " := " ident "]" "[" term,+ "]" :
    command

/-- Elaborates `#cas [groebner x, y, oracle := o] [f₁, …]`: the oracle's Gröbner basis, with its
cofactors and its Gröbner property checked as for `#cas [groebner x, y]`. -/
@[command_elab casGroebnerOracleCommand]
def elabGroebner : CommandElab := fun stx ↦ do
  let `(#cas [groebner $[$xs:ident, ]* oracle := $o:ident] [$ps:term,*]) := stx
    | throwUnsupportedSyntax
  let oracle ← liftCoreM (oracleOf o)
  let names := xs.map (·.getId)
  let n := names.size
  let shown := names.map renderName
  withAuditedEvidence "groebner" do
    let (gs, report) ← liftTermElabM <| CAS.Command.PolySystems.withProofBudget do
      let ctx ← CAS.Command.Ideal.Ctx.mvPolynomial n
      let inputs ← ps.getElems.mapM fun p ↦
        CAS.Command.Ideal.readPolynomial ctx "groebner" names p
      let texts ← inputs.mapM fun input ↦
        Translate.write (Translate.requestLanguage oracle) wireName (polyAsExpr (n := n) input.poly)
      let found ← askPython oracle "groebner" ["basis", "to_basis", "from_basis"]
        s!"[{", ".intercalate (texts.toList.map (pyRead · (wireNames n)))}], \
          {pyVariables (wireNames n)}"
      -- Pairs `basis g`, `to_basis` row, then one `from_basis` row per input.
      let keys := found.toList.map (·.key)
      let k := (keys.filter (· == "basis")).length
      unless keys == (List.replicate k ["basis", "to_basis"]).flatten ++
          List.replicate inputs.size "from_basis" do
        fail oracle (.failed "the answer's basis and cofactor rows do not match")
      let readPoly (record : String) : TermElabM CAS.Command.Groebner.Poly := do
        let answer : Verified.Expr (Fin n) ← Translate.readAnswer oracle wireName record
        let some p := CAS.Command.Ideal.poly? answer
          | throwError "the oracle's answer {record} is not a polynomial with rational \
              coefficients"
        return p
      let readRow (record : String) (size : Nat) :
          TermElabM (Array CAS.Command.Groebner.Poly) := do
        -- A row over the empty basis of the zero ideal is an empty record.
        let row := match Translate.row record with
          | [""] => []
          | row => row
        unless row.length = size do throwError "the oracle's cofactor row has the wrong size"
        row.toArray.mapM readPoly
      let records (key : String) := (found.filter (·.key == key)).map (·.payload)
      let basis ← (records "basis").mapM readPoly
      let toBasis ← (records "to_basis").mapM (readRow · inputs.size)
      let fromBasis ← (records "from_basis").mapM (readRow · k)
      -- Each basis element with coprime integer coefficients and a positive leading
      -- coefficient, its cofactor rows scaled to match.
      let scales := basis.map CAS.Command.Ideal.normalScale
      let gs := (basis.zip scales).map fun (g, s) ↦ CAS.Command.Groebner.scale s g
      let toBasis := (toBasis.zip scales).map fun (row, s) ↦
        row.map (CAS.Command.Groebner.scale s)
      let fromBasis := fromBasis.map fun row ↦
        (row.zip scales).map fun (c, s) ↦ CAS.Command.Groebner.scale (1 / s) c
      let proof ← try CAS.Command.Ideal.spanEqualityOfRows ctx inputs gs toBasis fromBasis
        catch error => throwErrorAt stx m!"groebner: the basis proposed by {oracle.name} is \
          refused: its cofactors do not prove that it spans the same ideal\
          {indentD error.toMessageData}"
      let groebner ← try CAS.Command.Ideal.basisGroebnerProperty "groebner" ctx gs
        catch error => throwErrorAt stx m!"groebner: the basis proposed by {oracle.name} is \
          refused: it is not shown to be a Gröbner basis{indentD error.toMessageData}"
      let report ← CAS.Command.Ideal.withMvPolynomialNames do
        evidence #[("The proposed basis spans the same ideal", ← inferType proof, proof),
          ("The proposed basis is a Gröbner basis", ← inferType groebner, groebner)]
      return (gs, report)
    let order := " > ".intercalate shown.toList
    CAS.Command.Ideal.logIdealReport stx {
      domain := CAS.Command.Ideal.domainText names
      input := ", ".intercalate (ps.getElems.toList.map fun p ↦ surfaceText p)
      inputType := "polynomials"
      output := if gs.isEmpty then "0"
        else ", ".intercalate (gs.toList.map (CAS.Command.Ideal.renderPoly shown))
      outputType := "Gröbner basis of the same ideal (checked)"
    } #[hintsNode oracle #[m!"the basis is the reduced one for the lexicographic order {order}, \
        each element scaled to coprime integer coefficients with a positive leading coefficient"],
      report]

end CASOracle.Ideal

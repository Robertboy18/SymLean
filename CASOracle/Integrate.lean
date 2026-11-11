/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import CAS.Command.Integration
import CAS.IntegrationTactic
import CASOracle.Accept
import CASOracle.Translate

/-!
# Antiderivatives proposed by an oracle

`#cas [integrate x, oracle := sympy] e` (or `[integrate, oracle := o]` for an expression in one
variable) asks the oracle for a primitive `F` of `e` and accepts it only through the residual
check of `#cas [integrate]`. The report is the one of `#cas [integrate x]`, with the oracle named
in its heading; the requirements of the certificate are its conditions. On an interval-integral
identity `∫ x in a..b, f x = r` (or `r = ∫ …`) the tactic `cas [oracle := o]` of
`CASOracle.Ideal` proves the goal through `cas [integrate primitive := F]` with the oracle's `F`,
and suggests that oracle-free call.

## Implementation notes

The oracle's `F` meets the check that our own primitives meet:
`IntegrationCheck.certifyCandidate?` must reach the literal zero for `∂ₓ F - e`, and the report
rebuilds the certificate's evidence in the kernel (the residual route is decided again, then
the derivative and fundamental-theorem statements follow from `AntiderivativeCert`). A
primitive that differs from SymLean's own by a constant is as good; one that fails the check is
refused with its residual. Since the proof of an interval identity needs only `F`, the
suggested call does not need the oracle again. The integrand's binder-independent subterms
travel to the oracle as parameters and come back as themselves.

The oracles with an `integrate` task are `sympy`, `sage` and `maxima`.
-/

namespace CASOracle.Integrate

open Lean Elab Command Meta Term Tactic
open CAS CAS.Command CAS.Command.InfoView
open CASOracle.Accept CASOracle.Wire

/-- Ask `oracle` for a primitive of `integrand` in coordinate `coordinate`. -/
def proposePrimitive (oracle : Oracle) {n : Nat} (coordinate : Fin n)
    (integrand : Verified.Expr (Fin n)) : TermElabM (Verified.Expr (Fin n)) := do
  let text ← Translate.write (Translate.requestLanguage oracle) wireName integrand
  let answer ← match oracle with
    | .maxima => askMaxima "integrate" "antiderivative" s!"integrate({text}, {wireName coordinate})"
    | _ =>
        let names := wireNames n
        let found ← askPython oracle "integrate" ["antiderivative"]
          s!"{pyRead text names}, {pyVariables names}[{coordinate.val}]"
        payload oracle found "antiderivative"
  -- Maxima writes an integral it cannot do as `integrate(…)` or `'integrate(…)`.
  if (answer.splitOn "integrate").length > 1 then
    throwError "integrate: {oracle.name} left the integral unevaluated"
  let primitive ← Translate.readAnswer oracle wireName answer
  -- The check differentiates the primitive; its derivative is admitted as the answer was.
  if let some why := Translate.admit (primitive.diff coordinate) n then
    throwError "the oracle's answer is refused: its derivative: {why}"
  return primitive

/-- `#cas [integrate x, oracle := o] e`. -/
syntax (name := casIntegrateOracleCommand)
  "#cas" "[" &"integrate" (ppSpace ident)? ", " &"oracle" " := " ident "]" term : command

/-- Elaborates `#cas [integrate x, oracle := o] e`: the oracle's primitive, checked by
differentiation in Lean before it is reported. -/
@[command_elab casIntegrateOracleCommand]
def elabIntegrateCommand : CommandElab := fun stx ↦ do
  let `(#cas [integrate $[$x?:ident]?, oracle := $o:ident] $input:term) := stx
    | throwUnsupportedSyntax
  let oracle ← liftCoreM (oracleOf o)
  let ⟨reified, coordinate⟩ ← scalarCoordinateInput input (x?.map (·.getId))
    "use [integrate x, oracle := …] to select the integration coordinate"
  let name := reified.names.get coordinate
  let candidate ← liftTermElabM <| proposePrimitive oracle coordinate reified.expr
  let certificate? :=
    (IntegrationCheck.certifyCandidate? coordinate reified.expr candidate.simplify).orElse
      fun _ ↦ IntegrationCheck.certifyCandidate? coordinate reified.expr candidate
  let some certificate := certificate?
    | let residual := IntegrationCheck.route coordinate reified.expr candidate.simplify
      throwErrorAt input "integrate: the primitive proposed by {oracle.name}, \
        {renderExpr reified candidate}, is refused: the derivative residual normalizes to \
        {renderExpr reified residual.rhs}, not 0"
  withAuditedEvidence "integrate" <|
    logIntegralCertificate input reified name coordinate certificate
      (extra := #[computationNode s!"Primitive proposed by {oracle.name} (checked below)"
        #[m!"{renderExpr reified candidate}"]])

/-! ## The tactic -/

/-- The integrand of an interval-integral equation, `∫ x in a..b, f x = r` or its mirror. -/
def integrandOf? (target : Lean.Expr) : Option Lean.Expr := do
  let some (_, lhs, rhs) := target.consumeMData.eq? | none
  let integral := if lhs.consumeMData.isAppOf ``intervalIntegral then lhs else rhs
  let integral := integral.consumeMData
  guard (integral.isAppOfArity ``intervalIntegral 7)
  return integral.getArg! 3

/-- Reify the body of `fun x ↦ body` with `x` as coordinate `0` and every binder-independent
subterm that is not a rational literal frozen as a parameter coordinate; returns the
parameters, coordinate `i + 1` being the `i`-th. -/
def reifyIntegrand (integrand : Lean.Expr) :
    MetaM (Σ n : Nat, Verified.Expr (Fin n) × Array Lean.Expr × Name) := do
  let integrand ← instantiateMVars integrand
  let .lam binderName binderType _ _ := integrand.consumeMData
    | throwError "the integrand is not a function literal"
  withLocalDeclD binderName binderType fun x ↦ do
    let body := (integrand.consumeMData.bindingBody!).instantiate1 x
    let reification ← CAS.Elaboration.RealExpression.reify {
      operation := "cas [oracle]"
      coordinates := #[x]
      opaque? := fun e ↦ do
        if CAS.Elaboration.RealExpression.dependsOn e x then return false
        return (← CAS.Tactic.Classify.rationalLiteral? e).isNone
      exponentAllowed := fun k ↦ pure (!CAS.Elaboration.RealExpression.dependsOn k x)
    } body
    let some expression ← reification.toVerifiedExpr?
      | throwError "the integrand has a symbolic exponent"
    -- Coordinate `0` is the bound variable; the others are parameters, free of it.
    let parameters := reification.coordinates.extract 1 reification.coordinates.size
    return ⟨reification.dimension, expression, parameters, binderName⟩

/-- Prove the interval-integral equation of the main goal from the oracle's primitive through
`cas [integrate primitive := F]`; returns that oracle-free call, for a suggestion. -/
def integrateByOracle (oracle : Oracle) : TacticM (TSyntax `tactic) := do
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  let some integrand := integrandOf? target
    | throwError "cas [oracle]: the goal is not an interval-integral equation"
  let (primitive, shown) ← withMainContext do
    let ⟨n, expression, parameters, binderName⟩ ← reifyIntegrand integrand
    let some zero := (List.finRange n).head?
      | throwError "cas [oracle]: the integrand has no variable"
    let candidate ← proposePrimitive oracle zero expression
    let x := mkIdent binderName
    let parameterTerms ← parameters.mapM fun c ↦ Term.exprToSyntax c
    let shownParameters ← parameters.mapM fun c ↦ do
      return (← PrettyPrinter.delab c : Term)
    let var (terms : Array Term) (i : Fin n) : Term :=
      if i.val = 0 then x else terms.getD (i.val - 1) x
    let body ← liftMacroM <| toTerm (var parameterTerms) candidate
    let shownBody ← liftMacroM <| toTerm (var shownParameters) candidate
    return (← `(fun ($x : ℝ) ↦ $body), ← `(fun ($x : ℝ) ↦ $shownBody))
  -- The suggestion is the elaborated primitive, printed back, so it reads as Lean source.
  let printed ← withMainContext do
    let primitive ← Term.elabTerm shown (some (← mkArrow (mkConst ``Real) (mkConst ``Real)))
    Term.synthesizeSyntheticMVarsNoPostponing
    PrettyPrinter.delab (← instantiateMVars primitive)
  closeGoal s!"cas [oracle := {oracle.name}]" fun goal ↦ do
    let saved ← getGoals
    setGoals [goal]
    try
      discard <| CAS.Tactic.Integration.close none (some primitive)
    catch error =>
      setGoals saved
      throwError m!"cas [oracle := {oracle.name}]: the primitive {printed} proposed \
        by {oracle.name} is refused{indentD error.toMessageData}"
    let rest ← getGoals
    setGoals saved
    unless rest.isEmpty do throwError "the primitive left goals"
  `(tactic| cas [integrate primitive := $printed])

end CASOracle.Integrate

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import CAS.Tactic.RealExpression
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Reflection for theorem-facing integration

Ordinary real `HasDerivAt` and interval-integral applications are recognized
(`hasDerivAtApplication?`, `intervalIntegralApplication?`) and their functions reflected into
checked expressions (`reflectFunction`). The temporary scalar binder becomes coordinate zero;
binder-independent real coefficients become frozen auxiliary coordinates.

## Implementation notes

The choice of what becomes a coordinate is that of `RealExpression.reflectBody` in
`CAS/Tactic/RealExpression.lean`, which keeps rational literal arithmetic and literal natural
powers visible to the planner. An integrand and a given primitive are reflected together by
`reflectPair` and quoted without simplification, so that the certificate keeps the domain
requirements of both. `endpointPrimitive?` reads a primitive off a goal value of the form
`F b - F a` by matching the two endpoint instances against each other, and accepts it only when
both are definitionally its values at the endpoints. Over the reals we accept only Mathlib's
Lebesgue measure (`ensureVolumeMeasure`), since the certificate theorems are stated for it.
-/

public meta section

namespace CAS.Tactic.Integration.Reflection

open Lean Elab Tactic Meta

/-- Explicit arguments of an ordinary scalar `HasDerivAt` proposition. -/
structure HasDerivAtApplication where
  private mk ::
  /-- Function whose derivative is asserted. -/
  function : Expr
  /-- Claimed derivative value at `point`. -/
  derivative : Expr
  /-- Point at which differentiability is asserted. -/
  point : Expr

/-- Explicit arguments of an ordinary real interval integral. -/
structure IntervalIntegralApplication where
  private mk ::
  /-- Integrand function. -/
  function : Expr
  /-- Lower integration endpoint. -/
  lower : Expr
  /-- Upper integration endpoint. -/
  upper : Expr
  /-- Measure supplied to `intervalIntegral`. -/
  measure : Expr

/--
An ordinary function after reflection, together with caller-local definitions
that were unfolded to expose its symbolic body.
-/
structure ReflectedFunction where
  private mk ::
  /-- Checked expression and frozen real parameters produced by reflection. -/
  reflection : RealExpression.Reflection
  /-- Caller-local definitions unfolded while exposing the function body. -/
  localDefinitions : Array Name

/-- Recognize the explicit data of a scalar `HasDerivAt` application. -/
def hasDerivAtApplication? (expression : Expr) :
    Option HasDerivAtApplication :=
  let expression := expression.consumeMData
  if !expression.isAppOfArity ``HasDerivAt 10 then
    none
  else
    let arguments := expression.getAppArgs
    some {
      function := arguments[7]!
      derivative := arguments[8]!
      point := arguments[9]!
    }

/-- Recognize the explicit data of a real interval-integral application. -/
def intervalIntegralApplication? (expression : Expr) :
    Option IntervalIntegralApplication :=
  let expression := expression.consumeMData
  if !expression.isAppOfArity ``intervalIntegral 7 then
    none
  else
    let arguments := expression.getAppArgs
    some {
      function := arguments[3]!
      lower := arguments[4]!
      upper := arguments[5]!
      measure := arguments[6]!
    }

/-- Reject a purported scalar-calculus value whose inferred type is not `Real`. -/
def ensureRealValue
    (description : String) (expression : Expr) : TacticM Unit := do
  unless ← Elaboration.RealExpression.hasType expression (mkConst ``Real) do
    let type ← inferType expression
    throwError
      "cas supports scalar calculus over ℝ; \
       {description} has type{indentExpr type}"

/--
Reflect one ordinary real function while its scalar binder is in scope.

The result no longer refers to the temporary scalar binder. Caller-local
parameters remain in scope when the integration planner consumes it.
-/
def reflectFunction (function : Expr) : TacticM ReflectedFunction := do
  let expectedType ← mkArrow (mkConst ``Real) (mkConst ``Real)
  unless ← Elaboration.RealExpression.hasType function expectedType do
    let type ← inferType function
    throwError
      "cas supports ordinary functions ℝ → ℝ; \
       the supplied function has type{indentExpr type}\n\
       Coefficients may come from any Lean type after conversion to ℝ. \
       Complex and vector-valued integration require separate certified backends."
  withLocalDeclD `t (mkConst ``Real) fun binder ↦ do
    let appliedFunction := mkApp function binder
    let localDefinitions ←
      RealExpression.collectDependentLocalDefinitions binder appliedFunction
    let body ← withTransparency .reducible <| whnf appliedFunction
    let localDefinitions ←
      RealExpression.collectDependentLocalDefinitions
        binder body localDefinitions
    unless ← Elaboration.RealExpression.hasType body (mkConst ``Real) do
      let codomain ← inferType body
      throwError
        "cas supports real-valued scalar functions; \
         the function body has type{indentExpr codomain}"
    let reflection ←
      RealExpression.reflectBody "cas" binder body
    return { reflection, localDefinitions }

/-- An integrand and primitive quoted over the same coordinate and frozen parameters. -/
structure ReflectedPair where
  /-- The original integrand, without cancellation of its domain requirements. -/
  integrand : Expr
  /-- The proposed primitive, without cancellation of its domain requirements. -/
  candidate : Expr
  /-- The common affine origin, with zero at the integration coordinate. -/
  origin : Expr
  /-- The integration coordinate in the common finite index type. -/
  coordinate : Expr
  /-- Caller-local definitions unfolded in either ordinary function. -/
  localDefinitions : Array Name

/-- Freeze only binder-independent coefficients, retaining literal rational arithmetic and
natural powers for the checked expression backend. -/
private def coefficient? (binder expression : Expr) : MetaM Bool := do
  if CAS.Elaboration.RealExpression.dependsOn expression binder then
    return false
  let expression := expression.consumeMData
  let head := expression.getAppFn
  if head.isConstOf ``OfScientific.ofScientific ||
      head.isConstOf ``Int.cast || head.isConstOf ``Rat.cast then
    return true
  if expression.isAppOfArity ``HPow.hPow 6 &&
      expression.getAppArgs[1]!.isConstOf ``Nat then
    let exponent := expression.appArg!.consumeMData
    if (exponent.nat? <|> exponent.rawNatLit?).isSome then
      return false
  return (← Classify.rationalLiteral? expression).isNone

/-- Reflect both functions before quoting either one, so a coefficient has the same
coordinate even when its first occurrence differs between integrand and primitive. -/
def reflectPair (integrand primitive : Expr) : TacticM ReflectedPair := do
  let expectedType ← mkArrow (mkConst ``Real) (mkConst ``Real)
  for function in #[integrand, primitive] do
    unless ← Elaboration.RealExpression.hasType function expectedType do
      throwError "cas expects an integrand and primitive of type ℝ → ℝ"
  withLocalDeclD `t (mkConst ``Real) fun binder ↦ do
    let mut table := #[binder]
    let mut reifications := #[]
    let mut localDefinitions := #[]
    for function in #[integrand, primitive] do
      let application := mkApp function binder
      localDefinitions ←
        RealExpression.collectDependentLocalDefinitions binder application localDefinitions
      let body ← instantiateMVars (← withTransparency .reducible <| whnf application)
      localDefinitions ←
        RealExpression.collectDependentLocalDefinitions binder body localDefinitions
      let reification ← CAS.Elaboration.RealExpression.reify {
        operation := "cas"
        coordinates := table
        opaque? := coefficient? binder
        exponentAllowed := fun exponent ↦
          pure (!CAS.Elaboration.RealExpression.dependsOn exponent binder)
        unfoldLimit := RealExpression.localUnfoldLimit
      } body
      table := reification.coordinates
      reifications := reifications.push reification
    let dimension := table.size
    let index := mkApp (mkConst ``Fin) (Lean.toExpr dimension)
    let quoteCoordinate := fun position ↦ RealExpression.finLiteral position dimension
    let coordinate ← quoteCoordinate 0
    let zero ← mkAppOptM ``OfNat.ofNat
      #[some (mkConst ``Real), some (mkRawNatLit 0), none]
    let mut origin ← mkAppM ``EuclideanSpace.single #[coordinate, zero]
    for position in [1:dimension] do
      let entry ← mkAppM ``EuclideanSpace.single #[← quoteCoordinate position, table[position]!]
      origin ← mkAppM ``HAdd.hAdd #[origin, entry]
    let #[integrandReification, candidateReification] := reifications
      | throwError "cas internal error: paired reflection lost a function"
    return {
      integrand := ← integrandReification.quoteWith index quoteCoordinate
      candidate := ← candidateReification.quoteWith index quoteCoordinate
      origin
      coordinate
      localDefinitions
    }

private def commonEndpointBody
    (binder lower upper : Expr) : Nat → Expr → Expr → Option Expr
  | 0, _, _ => none
  | fuel + 1, atLower, atUpper =>
      let atLower := atLower.consumeMData
      let atUpper := atUpper.consumeMData
      if atLower == atUpper then
        some atUpper
      else if atLower == lower && atUpper == upper then
        some binder
      else
        match atLower, atUpper with
        | .app lowerFunction lowerArgument, .app upperFunction upperArgument => do
            let function ← commonEndpointBody binder lower upper fuel lowerFunction upperFunction
            let argument ← commonEndpointBody binder lower upper fuel lowerArgument upperArgument
            return mkApp function argument
        | _, _ => none

/-- Reconstruct a primitive from a common endpoint expression, checking both instances.
Subterms shared by the two endpoints remain coefficients, even when equal to an endpoint.
Coincident endpoints leave candidate selection to the explicit form or search. -/
def endpointPrimitive? (value lower upper : Expr) : TacticM (Option Expr) := do
  let value := value.consumeMData
  unless value.isAppOfArity ``HSub.hSub 6 do
    return none
  if ← isDefEqGuarded lower upper then
    return none
  let atUpper := value.getAppArgs[4]!
  let atLower := value.getAppArgs[5]!
  withLocalDeclD `t (mkConst ``Real) fun binder ↦ do
    let fuel := atLower.sizeWithoutSharing + atUpper.sizeWithoutSharing + 1
    let some body := commonEndpointBody binder lower upper fuel atLower atUpper
      | return none
    unless CAS.Elaboration.RealExpression.dependsOn body binder do
      return none
    let primitive ← mkLambdaFVars #[binder] body
    unless ← isDefEqGuarded (mkApp primitive lower) atLower do
      return none
    unless ← isDefEqGuarded (mkApp primitive upper) atUpper do
      return none
    return some primitive

/-- Require Mathlib's default Lebesgue measure, allowing definitionally equal aliases. -/
def ensureVolumeMeasure (measure : Expr) : TacticM Unit := do
  -- Fix the instance explicitly: a caller-local `MeasureSpace ℝ` may have a different volume.
  let volume ← mkAppOptM ``MeasureTheory.MeasureSpace.volume
    #[some (mkConst ``Real), some (mkConst ``Real.measureSpace)]
  unless ← isDefEq measure volume do
    throwError
      "cas proves interval integrals with Mathlib's default Lebesgue measure on ℝ only; a \
       different measure was supplied"

end CAS.Tactic.Integration.Reflection

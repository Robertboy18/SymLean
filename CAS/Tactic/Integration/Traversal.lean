/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import CAS.Expr.Syntax
public meta import CAS.Tactic.Integration.Basic

/-!
# Traversal of checked integration targets

The low-level integration route accepts goals that already mention
`Verified.Expr.eval`. From such a target we extract the unique coordinate line
and the single checked integrand. Both searches use one outermost-match
traversal that visits parents before children.
-/

public meta section

namespace CAS.Tactic.Integration.Traversal

open Lean Meta

private def collectOutermost {α : Type}
    (extract? : Expr → Option α) (expression : Expr)
    (results : Array α := #[]) : Array α :=
  match expression with
  | .mdata _ body =>
      collectOutermost extract? body results
  | expression =>
      match extract? expression with
      | some result =>
          results.push result
      | none =>
          match expression with
          | .app function argument =>
              collectOutermost extract? argument <|
                collectOutermost extract? function results
          | .lam _ type body _
          | .forallE _ type body _ =>
              collectOutermost extract? body <|
                collectOutermost extract? type results
          | .letE _ type value body _ =>
              collectOutermost extract? body <|
                collectOutermost extract? value <|
                  collectOutermost extract? type results
          | .proj _ _ body =>
              collectOutermost extract? body results
          | _ =>
              results

private def symbolicEvaluation? (expression : Expr) : Option Expr :=
  if expression.isAppOfArity ``Verified.Expr.eval 3 then
    some expression.getAppArgs[2]!
  else
    none

private def coordinateOfSingle? (expression : Expr) : Option Expr :=
  if expression.isAppOfArity ``EuclideanSpace.single 6 then
    some expression.getAppArgs[4]!
  else
    none

/-- Extract the unique coordinate used by every coordinate-line term in a target. -/
def uniqueCoordinate (target : Expr) : MetaM Expr := do
  let coordinates := collectOutermost coordinateOfSingle? target
  let some coordinate := coordinates[0]?
    | throwError
        "cas expected a coordinate line containing \
         EuclideanSpace.single"
  for other in coordinates[1:] do
    unless ← isDefEq coordinate other do
      throwError
        "cas found multiple coordinate directions in the target"
  return coordinate

/--
Recognize a checked-expression derivative or interval-integral target and
return its analytic projection together with its unique integrand.
-/
def projectionAndIntegrand (target : Expr) : MetaM (Projection × Expr) := do
  let target := target.consumeMData
  if target.isAppOfArity ``HasDerivAt 10 then
    let derivativeValue := target.getAppArgs[8]!
    let some integrand := symbolicEvaluation? derivativeValue
      | throwError
          "cas expected the derivative value to be the evaluation \
           of one Verified.Expr"
    return (.hasDerivAt, integrand)
  if target.isAppOfArity ``Eq 3 then
    let lhs := target.getAppArgs[1]!.consumeMData
    if lhs.isAppOfArity ``intervalIntegral 7 then
      let integrandFunction := lhs.getAppArgs[3]!
      let integrands :=
        collectOutermost symbolicEvaluation? integrandFunction
      let some integrand := integrands[0]?
        | throwError
            "cas expected an interval integrand evaluating one \
             Verified.Expr"
      unless integrands.size == 1 do
        throwError
          "cas found an ambiguous symbolic interval integrand"
      return (.intervalIntegral, integrand)
  throwError
    "cas expected a coordinate-line HasDerivAt goal or a \
     coordinate-line interval-integral identity"

end CAS.Tactic.Integration.Traversal

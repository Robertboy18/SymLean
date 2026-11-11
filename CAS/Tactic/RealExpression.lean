/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Elaboration.RealExpression
public meta import CAS.Elaboration.RealExpression
public import CAS.Tactic.Classify
public meta import CAS.Tactic.Classify
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Positivity.Finset

/-!
# Reflection of ordinary real expressions

A theorem-facing bridge between ordinary Mathlib functions `ℝ → ℝ` and the checked expression
language `Verified.Expr`. The elaborated-term traversal itself is
`CAS.Elaboration.RealExpression.reify`; the code here records caller-local definitions and
chooses the coordinates of the reflection for the integration tactic, the derivative tactics and
the checked identity proofs. Reflection does not prove an analytic claim: callers apply a theorem
about the quoted `Verified.Expr` and then convert that theorem back to the original goal.

## Main definitions

* `collectDependentLocalDefinitions`: the definitions of the current module whose applications
  depend on the reflected binder.
* `reflectBody` and `Reflection`: a function of one real variable on the affine coordinate line
  of the integration tactic.
* `reflectEmbedded` and `EmbeddedReflection`: a body over several differentiated coordinates, in
  the parameter-embedding convention of the derivative tactics.
* `reifyOverAtoms`: closed real terms over one shared table of atoms, for the checked identity
  proofs, the comparison of a computed derivative with a stated one, and the equation hint of
  the arithmetic route.
* `isAtomHead`, `vectorLiteral`, `parameterVector`, `finLiteral` and `embeddedCoordinate`: the
  atom test and the literals of the quotations.

## Implementation notes

We choose the coordinates; the traversal is that of `CAS/Elaboration/RealExpression.lean`. In
`reflectBody` the function argument occupies coordinate zero and binder-independent real
subterms are frozen as further coordinates, so coefficients may be computed from arbitrary Lean
types, while rational arithmetic and literal natural powers stay visible for antiderivative
pattern matching. `reflectEmbedded` freezes every binder-independent subterm, so that the
validity conditions of a derivative theorem impose nothing on constants. Derivative and integral
reflection reject unsupported operations that depend on the reflected binder. `reifyOverAtoms`
keeps every unknown real subterm as an atom, so that an identity between arbitrary real terms is
normalized over its atoms.

We prove nothing here. A caller identifies the evaluation of each quotation with the term it
started from before it applies the checked theorem of its route: by `rfl` or the lowering lemmas
of `DerivativeBridge.loweringBridgeSyntax` (`CAS/Tactic/DerivativeBridge.lean`) in the
derivative tactics and identity proofs, and by `Integration.Conversion.close`
(`CAS/Tactic/Integration/Conversion.lean`) in the integration tactic, which first unfolds the
local definitions recorded here.
-/

public meta section

namespace CAS.Tactic.RealExpression

open Lean Meta
open CAS.Elaboration.RealExpression (traversalFuel makeFin realNumeral)

/-- Default bound on consecutive unfoldings of caller-local definitions during reflection. -/
def localUnfoldLimit : Nat := 16

/--
A reflected expression together with the affine coordinate line on which
it represents the original ordinary function.
-/
structure Reflection where
  private mk ::
  /-- The quoted `Verified.Expr` representing the ordinary real expression. -/
  expression : Lean.Expr
  /-- The coordinate vector storing frozen parameters and zero in the function coordinate. -/
  origin : Lean.Expr
  /-- The `Fin` index of the reflected function argument. -/
  coordinate : Lean.Expr
  /-- The unit coordinate vector along which the original function is evaluated. -/
  direction : Lean.Expr

/--
Collect definitions from the caller's current module whose applications depend
on the reflected binder.

Reflection unfolds these definitions to discover their mathematical expression.
Callers retain the names so the final checked theorem can be converted back to
the user's original presentation without unfolding imported analytic APIs.
The fuel bounds recursive definitions and chains of local definitions.
-/
private def collectDependentLocalDefinitionsAux
    (binder expression : Lean.Expr)
    (definitions : Array Name) (unfoldFuel traversalFuel : Nat) :
    MetaM (Array Name) :=
  match traversalFuel with
  | 0 =>
      throwError
        "reflection exceeded its traversal limit while collecting local definitions"
  | traversalFuel + 1 => do
      let expression := expression.consumeMData
      if !CAS.Elaboration.RealExpression.dependsOn expression binder then
        return definitions
      let mut definitions := definitions
      let head := expression.getAppFn.consumeMData
      if let .const name _ := head then
        let env ← getEnv
        if !env.isImportedConst name then
          if let some (.defnInfo _) := env.find? name then
            unless definitions.contains name do
              definitions := definitions.push name
            if let unfoldFuel + 1 := unfoldFuel then
              let candidate ←
                withTransparency .all <| unfoldDefinition? expression true
              if let some unfolded := candidate then
                if unfolded != expression then
                  return ←
                    collectDependentLocalDefinitionsAux
                      binder unfolded definitions unfoldFuel traversalFuel
      match expression with
      | .app function argument =>
          let functionDefinitions ←
            collectDependentLocalDefinitionsAux
              binder function definitions unfoldFuel traversalFuel
          collectDependentLocalDefinitionsAux
            binder argument functionDefinitions unfoldFuel traversalFuel
      | .lam _ domain body _
      | .forallE _ domain body _ =>
          let domainDefinitions ←
            collectDependentLocalDefinitionsAux
              binder domain definitions unfoldFuel traversalFuel
          collectDependentLocalDefinitionsAux
            binder body domainDefinitions unfoldFuel traversalFuel
      | .letE _ type value body _ =>
          let typeDefinitions ←
            collectDependentLocalDefinitionsAux
              binder type definitions unfoldFuel traversalFuel
          let valueDefinitions ←
            collectDependentLocalDefinitionsAux
              binder value typeDefinitions unfoldFuel traversalFuel
          collectDependentLocalDefinitionsAux
            binder body valueDefinitions unfoldFuel traversalFuel
      | .mdata _ body
      | .proj _ _ body =>
          collectDependentLocalDefinitionsAux
            binder body definitions unfoldFuel traversalFuel
      | _ =>
          return definitions

/--
Collect caller-local definitions that conceal dependence on `binder`.

`fuel` bounds consecutive local-definition unfoldings. The separate traversal
budget exists only to make the metaprogram total and fails closed on exhaustion.
-/
def collectDependentLocalDefinitions
    (binder expression : Lean.Expr)
    (definitions : Array Name := #[]) (fuel : Nat := localUnfoldLimit) :
    MetaM (Array Name) :=
  collectDependentLocalDefinitionsAux
    binder expression definitions fuel (traversalFuel expression fuel)

private def coordinateVector
    (dimension index : Nat) : MetaM Lean.Expr := do
  let coordinate ← makeFin index dimension
  mkAppM ``EuclideanSpace.single #[coordinate, ← realNumeral 1]

/--
Place frozen parameters in coordinates `1, ..., n - 1`.

Coordinate zero remains zero, so adding `t • e₀` makes evaluation of the
reflected expression definitionally represent the original scalar function at
`t` after simplification.
-/
private def parameterOrigin
    (coordinates : Array Lean.Expr) : MetaM Lean.Expr := do
  let dimension := coordinates.size
  let zeroCoordinate ← makeFin 0 dimension
  let mut origin ←
    mkAppM ``EuclideanSpace.single #[zeroCoordinate, ← realNumeral 0]
  for coordinateIndex in [1:coordinates.size] do
    let coordinate ← makeFin coordinateIndex dimension
    let parameterVector ←
      mkAppM ``EuclideanSpace.single #[coordinate, coordinates[coordinateIndex]!]
    origin ← mkAppM ``HAdd.hAdd #[origin, parameterVector]
  return origin

/-- Whether a term is a power `a ^ k` with a literal natural exponent. -/
private def isLiteralNaturalPower (expression : Lean.Expr) : Bool :=
  let expression := expression.consumeMData
  expression.isAppOfArity ``HPow.hPow 6 ∧
    expression.getAppArgs[1]!.isConstOf ``Nat ∧
    let exponent := expression.appArg!.consumeMData
    (exponent.nat? <|> exponent.rawNatLit?).isSome

/--
Reflect a real expression depending on one local real binder.

The temporary binder does not occur in the result. Caller-local coefficients
and natural exponents may remain, so the result must stay in their enclosing
context.

Binder-independent terms become parameter coordinates, except rational
arithmetic on natural literals and powers with literal natural exponents.
Exposing this syntax lets the planner recognize `1 / (1 + t ^ 2)`,
`1 / √(1 - t ^ 2)`, and `1 / (a ^ 2 + t ^ 2)`. Scientific literals and
integer or rational casts remain parameters because the shared reifier does
not read those numeral forms.
-/
def reflectBody
    (operation : String) (binder body : Lean.Expr) : MetaM Reflection := do
  let reification ←
    CAS.Elaboration.RealExpression.reify {
      operation
      coordinates := #[binder]
      opaque? := fun expression ↦ do
        if CAS.Elaboration.RealExpression.dependsOn expression binder then
          return false
        let head := expression.consumeMData.getAppFn
        if head.isConstOf ``OfScientific.ofScientific ||
            head.isConstOf ``Int.cast || head.isConstOf ``Rat.cast then
          return true
        if isLiteralNaturalPower expression then
          return false
        return (← Classify.rationalLiteral? expression).isNone
      exponentAllowed := fun exponent ↦
        pure (!CAS.Elaboration.RealExpression.dependsOn exponent binder)
      unfoldLimit := localUnfoldLimit
    } body
  return {
    expression := ← reification.quote
    origin := ← parameterOrigin reification.coordinates
    coordinate := ← makeFin 0 reification.dimension
    direction := ← coordinateVector reification.dimension 0
  }

end CAS.Tactic.RealExpression

namespace CAS.Tactic.RealExpression

open Lean Meta

/-!
## Embedded reflection

The derivative tactics place the `n` differentiated coordinates at the
`Fin.castAdd` positions and every frozen parameter at a `Fin.natAdd` position
of `Fin (n + k)`. Together with the parameter vector `![c₀, …, c_{k-1}]` this
is exactly the convention of `Verified.Expr.paramEmbed`, so the reflected
function `fun q ↦ expr.eval (paramEmbed c q)` is definitionally the original
one whenever reflection only used definitional lowerings.
-/

/-- A reflected real expression in the parameter-embedding convention. -/
structure EmbeddedReflection where
  private mk ::
  /-- The quoted `Verified.Expr (Fin (n + k))` representing the differentiated body. -/
  expression : Lean.Expr
  /-- The parameter vector `![c₀, …, c_{k-1}] : Fin k → ℝ`. -/
  parameters : Lean.Expr
  /-- The number `n` of differentiated coordinates. -/
  dimension : Nat
  /-- The number `k` of frozen parameters. -/
  parameterCount : Nat
  /-- The complete coordinate table: `n` coordinates followed by the `k` frozen parameters. -/
  coordinates : Array Lean.Expr

/-- Whether a real term is an atom for the checked normalizer: its head is not one of the
operations the reifier understands. A cast of a natural number is not an atom head: the
reifier reflects the arithmetic of the natural number and freezes its own atoms. -/
def isAtomHead (expression : Lean.Expr) : Bool :=
  let head := expression.consumeMData.getAppFn.consumeMData
  match head with
  | .const name _ =>
      !(name == ``HAdd.hAdd || name == ``HSub.hSub || name == ``HMul.hMul ||
        name == ``HDiv.hDiv || name == ``Neg.neg || name == ``Inv.inv ||
        name == ``HPow.hPow || name == ``abs || name == ``OfNat.ofNat ||
        name == ``Real.pi || name == ``Real.sin || name == ``Real.cos ||
        name == ``Real.tan || name == ``Real.sinh || name == ``Real.cosh ||
        name == ``Real.tanh || name == ``Real.arctan || name == ``Real.arcsin ||
        name == ``Real.arccos || name == ``Real.exp || name == ``Real.log ||
        name == ``Real.sqrt || name == ``Nat.cast)
  | _ => true

/-- Build the vector literal `![c₀, …, c_{k-1}]` of the given element type. -/
def vectorLiteral (type : Lean.Expr) (entries : Array Lean.Expr) : MetaM Lean.Expr := do
  let mut vector ← mkAppOptM ``Matrix.vecEmpty #[some type]
  for entry in entries.reverse do
    vector ← mkAppM ``Matrix.vecCons #[entry, vector]
  return vector

/-- Build the vector literal `![c₀, …, c_{k-1}] : Fin k → ℝ`. -/
def parameterVector (parameters : Array Lean.Expr) : MetaM Lean.Expr :=
  vectorLiteral (mkConst ``Real) parameters

/-- The numeric literal `(value : Fin bound)`. -/
def finLiteral (value bound : Nat) : MetaM Lean.Expr :=
  mkAppOptM ``OfNat.ofNat
    #[some (mkApp (mkConst ``Fin) (Lean.toExpr bound)), some (mkRawNatLit value), none]

/-- Quote a coordinate position of `Fin (n + k)` as `Fin.castAdd k (i : Fin n)` for a
differentiated coordinate and as `Fin.natAdd n (i - n : Fin k)` for a parameter, using
numeric literals so that the unfolded coordinates print as the user's `q i`. -/
def embeddedCoordinate (dimension parameterCount position : Nat) : MetaM Lean.Expr := do
  if position < dimension then
    mkAppOptM ``Fin.castAdd
      #[some (Lean.toExpr dimension), some (Lean.toExpr parameterCount),
        some (← finLiteral position dimension)]
  else
    mkAppOptM ``Fin.natAdd
      #[some (Lean.toExpr parameterCount), some (Lean.toExpr dimension),
        some (← finLiteral (position - dimension) parameterCount)]

/--
Reflect `body` over the differentiated coordinate terms `coordinates` (terms
depending on the local binders `binders`), freezing every binder-independent
real subterm as a parameter.

Freezing whole binder-independent subterms keeps the analytic validity conditions
of the derivative theorem free of conditions on constants: a constant `Real.log a`
is a fixed real number and needs no `a ≠ 0` for differentiation.
-/
def reflectEmbedded
    (operation : String) (binders : Array Lean.Expr) (coordinates : Array Lean.Expr)
    (body : Lean.Expr) : MetaM EmbeddedReflection := do
  let dependsOnBinder (expression : Lean.Expr) : Bool :=
    binders.any fun binder ↦
      CAS.Elaboration.RealExpression.dependsOn expression binder
  let dimension := coordinates.size
  let config : CAS.Elaboration.RealExpression.Config := {
    operation
    coordinates
    opaque? := fun expression ↦ pure (!dependsOnBinder expression)
    exponentAllowed := fun exponent ↦ pure (!dependsOnBinder exponent)
    unfoldLimit := localUnfoldLimit
  }
  let reification ← CAS.Elaboration.RealExpression.reify config body
  let table := reification.coordinates
  let parameterCount := table.size - dimension
  let index ← inferType (← embeddedCoordinate dimension parameterCount 0)
  return {
    expression := ← reification.quoteWith index (embeddedCoordinate dimension parameterCount)
    parameters := ← parameterVector (table.extract dimension table.size)
    dimension
    parameterCount
    coordinates := table
  }

/--
Reflect closed real terms over one shared atom table that starts with `initial`.

Every maximal subterm whose head is not a reifier operation becomes an atom, a natural
or integer power with a symbolic exponent `k` is read as the real power with the cast `↑k`
as exponent, and a cast of a natural-number expression is reflected through its arithmetic
(with `omega` deciding that a subtraction is not truncated), so that the reflected terms can
be evaluated in the kernel and exponent arithmetic is visible to the normalizer. The quotations use
plain numeric literals of `Fin m`, where `m` is the size of the final table, so that the
checked normalizer sees the supported algebraic operations, with opaque subterms left as
atoms. Returns the quotations and the final atom table. Callers must justify their evaluation
against the original terms before applying a normalization theorem.
-/
def reifyOverAtoms
    (operation : String) (initial : Array Lean.Expr) (terms : Array Lean.Expr) :
    MetaM (Array Lean.Expr × Array Lean.Expr) := do
  let mut table := initial
  let mut reifications := #[]
  for term in terms do
    let config : CAS.Elaboration.RealExpression.Config := {
      operation
      coordinates := table
      opaque? := fun expression ↦ pure (isAtomHead expression)
      exponentAllowed := fun _ ↦ pure true
      symbolicExponentsAsRealPowers := true
      unfoldLimit := localUnfoldLimit
    }
    let reification ← CAS.Elaboration.RealExpression.reify config term
    table := reification.coordinates
    reifications := reifications.push reification
  let size := table.size
  let index := mkApp (mkConst ``Fin) (Lean.toExpr size)
  let quotations ← reifications.mapM fun reification ↦
    reification.quoteWith index (finLiteral · size)
  return (quotations, table)

end CAS.Tactic.RealExpression

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Elaboration.RealExpression.Syntax
public meta import CAS.Elaboration.RealExpression.Syntax

/-!
# Reification of elaborated real expressions

The common low-level traversal from elaborated `Lean.Expr` terms to the checked real-expression
language `Verified.Expr`. Frontends choose the initial real coordinates, which subterms become
opaque coordinates, which local constants receive distinguished symbolic values, and which power
exponents they accept. The traversal is independent of commands, tactics, symbolic calculus,
CEGA and PDE models, and it produces syntax, not a proof.

## Main definitions

* `Config`: the choices of one traversal.
* `reify`: the traversal; it returns a `Reification`, the reflected expression together with its
  table of real coordinates.
* `Reification.quote` and `Reification.quoteWith`: the reification as a kernel term of type
  `Verified.Expr (Fin dimension)`, or over coordinate terms the caller chooses.
* `Reification.toVerifiedExpr?`: the executable `Verified.Expr` value, when every exponent
  reduces to a natural number.

## Implementation notes

Turning a goal into syntax that a certified procedure then decides is proof by reflection
[Boutin1997]; this is the first half, shared by the frontends. We read the term from the top. A
subterm is first matched against the coordinate table and the distinguished constants by guarded
definitional equality (`isDefEqGuarded`), so a definitionally equal occurrence reuses its
coordinate. With `rationalLiterals`, a decimal literal is then read as the exact rational it
denotes. What remains is offered to `opaque?`, which may freeze it as a new coordinate; otherwise,
unless `unfoldLocal` is off, a definition of the current module at its head is unfolded, at most
`unfoldLimit` in a chain, and `traversalFuel` bounds the whole traversal. Literal integer powers
are normalized to natural powers and division during traversal; a power whose exponent has type
`ℝ`, written either with `^` or as `Real.rpow`, becomes the checked real power `rpow`.

Frontends that evaluate the reflected expression in the kernel enable
`symbolicExponentsAsRealPowers`. For them a natural or integer power with a symbolic exponent is
the real power of the cast exponent, and a cast `((k : ℕ) : ℝ)` of a natural-number expression
is reflected through its arithmetic: sums, products, numerals, and literal powers become the
corresponding real operations (`Nat.cast_add`, `Nat.cast_mul`, `Nat.cast_ofNat`,
`Nat.cast_pow`), a subtraction becomes a real subtraction when `omega` proves it non-truncating
from the local context (`Nat.cast_sub`), and every remaining natural atom is frozen as the cast
`↑k`. The exponent `2 + k * 2 - 1` therefore reflects to `2 + k * 2 - 1` over the atom `↑k`,
which the polynomial normalizer identifies with `2 * k + 1`.

Nothing here is trusted. A caller applies the checked semantic theorem or certificate of its
route, and proves that the evaluation of the quoted term is the term it started from, as
`DerivativeBridge.loweringBridgeSyntax` (`CAS/Tactic/DerivativeBridge.lean`) does by `rfl` or by
rewriting with the lowering and cast lemmas.

## References

* [Boutin1997] Samuel Boutin, "Using reflection to build efficient and certified decision
  procedures", in *Theoretical Aspects of Computer Software*, Lecture Notes in Computer Science,
  Springer, 1997, pp. 515-529, <https://doi.org/10.1007/BFb0014565>.
-/

public meta section

namespace CAS.Elaboration.RealExpression

open Lean Meta

/-- Associate an elaborated real term with a distinguished symbolic constant. -/
structure ConstantBinding where
  /-- Elaborated real term recognized by guarded definitional equality. -/
  source : Lean.Expr
  /-- Checked nullary constant represented by `source`. -/
  value : Constant

/-- Configuration for one elaborated real-expression traversal. -/
structure Config where
  /-- Name used to identify the requesting operation in diagnostics. -/
  operation : String
  /-- Real terms assigned coordinates before traversal begins. -/
  coordinates : Array Lean.Expr := #[]
  /-- Additional nullary real constants recognized before opaque-term handling. -/
  constants : Array ConstantBinding := #[]
  /-- Whether a real subterm should be frozen as a new opaque coordinate. -/
  opaque? : Lean.Expr → MetaM Bool := fun _ ↦ pure false
  /-- Whether a natural exponent is admitted by this frontend. -/
  exponentAllowed : Lean.Expr → MetaM Bool := fun _ ↦ pure true
  /-- Whether a natural or integer power with a non-literal exponent `k` is reflected as the
  real power `rpow base (↑k)` (`Real.rpow_natCast`, `Real.rpow_intCast`), instead of a natural
  power with a symbolic exponent, and whether a cast `((k : ℕ) : ℝ)` is reflected through the
  arithmetic of `k` with the natural atoms frozen as casts. Frontends that evaluate the
  reflected expression in the kernel need this, since a symbolic natural exponent cannot be
  reduced. -/
  symbolicExponentsAsRealPowers : Bool := false
  /-- Whether a decimal literal `OfScientific.ofScientific` of `ℝ` is read as the exact rational
  it denotes (`ReflectedExpr.decimalLiteral`), before `opaque?` is asked, instead of being left
  to `opaque?`. -/
  rationalLiterals : Bool := false
  /-- Whether definitions from the current module may be unfolded. -/
  unfoldLocal : Bool := true
  /-- Maximum length of a chain of caller-local definition unfoldings. -/
  unfoldLimit : Nat := 16

/-- A reflected expression together with its complete real coordinate table. -/
structure Reification where
  private mk ::
  /-- Meta-level checked-expression syntax. -/
  reflected : ReflectedExpr Nat Lean.Expr
  /-- Elaborated real terms denoted by the expression coordinates. -/
  coordinates : Array Lean.Expr

namespace Reification

/-- Dimension of the reflected expression's real coordinate space. -/
def dimension (result : Reification) : Nat :=
  result.coordinates.size

end Reification

/-- Whether an expression contains the supplied local variable. -/
def dependsOn (expression target : Lean.Expr) : Bool :=
  expression.hasAnyFVar fun fvarId ↦ fvarId == target.fvarId!

/-- Check an inferred type by guarded definitional equality. -/
def hasType (expression type : Lean.Expr) : MetaM Bool := do
  isDefEqGuarded (← inferType expression) type

/-- Traversal budget for an expression when at most `unfoldLimit` definitions are unfolded. -/
def traversalFuel (expression : Lean.Expr) (unfoldLimit : Nat) : Nat :=
  max 1024 ((expression.sizeWithoutSharing + 1) * (unfoldLimit + 1))

private def lastArgument? (expression : Lean.Expr) : Option Lean.Expr :=
  let arguments := expression.getAppArgs
  if h : 0 < arguments.size then
    some arguments[arguments.size - 1]
  else
    none

private def lastTwoArguments?
    (expression : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  let arguments := expression.getAppArgs
  if h : 2 ≤ arguments.size then
    some (arguments[arguments.size - 2], arguments[arguments.size - 1])
  else
    none

private def unaryArgument?
    (expression : Lean.Expr) (functionName : Name) : Option Lean.Expr :=
  if expression.getAppFn.consumeMData.isConstOf functionName then
    lastArgument? expression
  else
    none

private def binaryArguments?
    (expression : Lean.Expr) (functionName : Name) :
    Option (Lean.Expr × Lean.Expr) :=
  if expression.getAppFn.consumeMData.isConstOf functionName then
    lastTwoArguments? expression
  else
    none

private def unaryOperationApplication?
    (expression : Lean.Expr) : Option (UnaryOperation × Lean.Expr) := do
  let .const name _ := expression.getAppFn.consumeMData
    | none
  let operation ← UnaryOperation.ofConstantName? name
  let argument ← lastArgument? expression
  return (operation, argument)

private def desugaredFunctionApplication?
    (expression : Lean.Expr) : Option (DesugaredFunction × Lean.Expr) := do
  let .const name _ := expression.getAppFn.consumeMData
    | none
  let function ← DesugaredFunction.ofConstantName? name
  let argument ← lastArgument? expression
  return (function, argument)

private def unfoldLocalDefinitions
    (expression : Lean.Expr) : Nat → MetaM Lean.Expr
  | 0 =>
      return expression
  | fuel + 1 => do
      let head := expression.getAppFn.consumeMData
      let .const name _ := head
        | return expression
      if (← getEnv).isImportedConst name then
        return expression
      match ← withTransparency .all <| unfoldDefinition? expression true with
      | some unfolded =>
          if unfolded == expression then
            return expression
          unfoldLocalDefinitions unfolded fuel
      | none =>
          return expression

private def coordinateIndex?
    (expression : Lean.Expr) (coordinates : Array Lean.Expr) :
    MetaM (Option Nat) := do
  for index in [0:coordinates.size] do
    if ← isDefEqGuarded expression coordinates[index]! then
      return some index
  return none

private def constantValue?
    (expression : Lean.Expr) (constants : Array ConstantBinding) :
    MetaM (Option Constant) := do
  for binding in constants do
    if ← isDefEqGuarded expression binding.source then
      return some binding.value
  return none

private def realNatLiteral? (expression : Lean.Expr) : MetaM (Option Nat) := do
  unless expression.getAppFn.consumeMData.isConstOf ``OfNat.ofNat do
    return none
  unless ← hasType expression (mkConst ``Real) do
    return none
  let arguments := expression.getAppArgs
  if h : 2 ≤ arguments.size then
    getNatValue? arguments[arguments.size - 2]
  else
    return none

/-- The argument `k` of a real cast `((k : ℕ) : ℝ)`. -/
private def natCastArgument? (expression : Lean.Expr) : Option Lean.Expr :=
  if expression.isAppOfArity ``Nat.cast 3 ∧ expression.appFn!.appFn!.appArg!.isConstOf ``Real then
    some expression.appArg!
  else
    none

/-- The real numeral `(n : ℝ)`, as `OfNat.ofNat` of a raw literal. -/
def realNumeral (n : ℕ) : MetaM Lean.Expr :=
  mkAppOptM ``OfNat.ofNat #[some (mkConst ``Real), some (mkRawNatLit n), none]

/-- The real cast `((k : ℕ) : ℝ)`. -/
def realNatCast (k : Lean.Expr) : MetaM Lean.Expr :=
  mkAppOptM ``Nat.cast #[some (mkConst ``Real), none, some k]

/-- Whether `omega` proves `b ≤ a` for natural-number terms from the local context, so that the
natural subtraction `a - b` is not truncated. The proof itself is not kept: the theorem that
identifies the reflection with the original term rediscovers it with the same tactic as the
discharger of `Nat.cast_sub`. -/
private def natLeProvable (b a : Lean.Expr) : MetaM Bool := do
  withoutModifyingState do
    try
      let goal ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[b, a])
      let some contradiction ← goal.mvarId!.falseOrByContra | return true
      contradiction.withContext do
        let hypotheses := (← getLocalHyps).toList
        Lean.Elab.Tactic.Omega.omega hypotheses contradiction {}
      return true
    catch _ =>
      return false

private def checkInitialData (config : Config) : MetaM Unit := do
  for coordinate in config.coordinates do
    unless ← hasType coordinate (mkConst ``Real) do
      let type ← inferType coordinate
      throwError
        "{config.operation} received a non-real symbolic coordinate of type\
         {indentExpr type}"
  for binding in config.constants do
    unless ← hasType binding.source (mkConst ``Real) do
      let type ← inferType binding.source
      throwError
        "{config.operation} received a non-real symbolic constant of type\
         {indentExpr type}"

/-- The decimal literal `@OfScientific.ofScientific ℝ _ m s e` with literal mantissa and power of
ten as an exact constant, refused when the power of ten is over `maxDecimalExponent`; `none` for
any other term. -/
private def decimalLiteral? (expression : Lean.Expr) :
    MetaM (Option (ReflectedExpr Nat Lean.Expr)) := do
  unless expression.isAppOfArity ``OfScientific.ofScientific 5 do
    return none
  let arguments := expression.getAppArgs
  unless ← isDefEqGuarded arguments[0]! (mkConst ``Real) do
    return none
  let literal (term : Lean.Expr) : Option Nat :=
    term.consumeMData.rawNatLit? <|> term.consumeMData.nat?
  let some mantissa := literal arguments[2]! | return none
  let some exponent := literal arguments[4]! | return none
  -- The Boolean in `OfScientific` signs the exponent, not the mantissa.
  let sign := arguments[3]!.consumeMData
  let negativeExponent ←
    if sign.isConstOf ``Bool.true then pure true
    else if sign.isConstOf ``Bool.false then pure false
    else return none
  checkDecimalExponent .missing exponent
  return some (ReflectedExpr.decimalLiteral mantissa negativeExponent exponent)

/-- Freeze a real term as a coordinate, reusing an existing definitionally equal coordinate. -/
private def freezeAtom (expression : Lean.Expr) (coordinates : Array Lean.Expr) :
    MetaM (ReflectedExpr Nat Lean.Expr × Array Lean.Expr) := do
  if let some index ← coordinateIndex? expression coordinates then
    return (.coordinate index, coordinates)
  return (.coordinate coordinates.size, coordinates.push expression)

/--
Reflect the real cast `cast = ((natural : ℕ) : ℝ)` through the arithmetic of `natural`: numerals,
sums, products, literal powers, and subtractions that `omega` proves non-truncating are reflected
as the corresponding real operations, a symbolic power `a ^ b` becomes the real power of the two
casts, and any other natural term is frozen as its cast.
-/
private def reifyNatCast
    (config : Config) (natural cast : Lean.Expr) (coordinates : Array Lean.Expr) :
    Nat → MetaM (ReflectedExpr Nat Lean.Expr × Array Lean.Expr)
  | 0 =>
      throwError "{config.operation} exceeded the reflection traversal limit"
  | fuel + 1 => do
      let natural := natural.consumeMData
      if let some value ← getNatValue? natural then
        return (.nat value, coordinates)
      let recurse (term : Lean.Expr) (coordinates : Array Lean.Expr) := do
        reifyNatCast config term (← realNatCast term) coordinates fuel
      if let some (lhs, rhs) := binaryArguments? natural ``HAdd.hAdd then
        let (lhsExpression, coordinates) ← recurse lhs coordinates
        let (rhsExpression, coordinates) ← recurse rhs coordinates
        return (.add lhsExpression rhsExpression, coordinates)
      if let some (lhs, rhs) := binaryArguments? natural ``HMul.hMul then
        let (lhsExpression, coordinates) ← recurse lhs coordinates
        let (rhsExpression, coordinates) ← recurse rhs coordinates
        return (.mul lhsExpression rhsExpression, coordinates)
      if let some (lhs, rhs) := binaryArguments? natural ``HSub.hSub then
        if ← natLeProvable rhs lhs then
          let (lhsExpression, coordinates) ← recurse lhs coordinates
          let (rhsExpression, coordinates) ← recurse rhs coordinates
          return (.sub lhsExpression rhsExpression, coordinates)
        return ← freezeAtom cast coordinates
      if let some (base, exponent) := binaryArguments? natural ``HPow.hPow then
        let (baseExpression, coordinates) ← recurse base coordinates
        match ← getNatValue? exponent with
        | some value => return (.pow baseExpression (mkNatLit value), coordinates)
        | none =>
            let (exponentExpression, coordinates) ← recurse exponent coordinates
            return (.rpow baseExpression exponentExpression, coordinates)
      freezeAtom cast coordinates

private def reifyAux
    (config : Config) (expression : Lean.Expr)
    (coordinates : Array Lean.Expr) (fuel : Nat) :
    MetaM (ReflectedExpr Nat Lean.Expr × Array Lean.Expr) :=
  match fuel with
  | 0 =>
      throwError "{config.operation} exceeded the reflection traversal limit"
  | fuel + 1 => do
      let expression := expression.consumeMData
      if let some index ← coordinateIndex? expression coordinates then
        return (.coordinate index, coordinates)
      if let some value ← constantValue? expression config.constants then
        return (.constant value, coordinates)
      if config.rationalLiterals then
        if let some literal ← decimalLiteral? expression then
          return (literal, coordinates)
      if ← config.opaque? expression then
        unless ← hasType expression (mkConst ``Real) do
          let type ← inferType expression
          throwError
            "{config.operation} attempted to freeze a non-real term of type\
             {indentExpr type}"
        return (.coordinate coordinates.size, coordinates.push expression)
      let expression ←
        if config.unfoldLocal then
          unfoldLocalDefinitions expression config.unfoldLimit
        else
          pure expression
      let expression := expression.consumeMData
      if let .letE _ _ value body _ := expression then
        return ← reifyAux config (body.instantiate1 value) coordinates fuel
      if let some value ← realNatLiteral? expression then
        return (.nat value, coordinates)
      if expression.getAppFn.consumeMData.isConstOf ``Real.pi then
        return (.constant .pi, coordinates)
      if let some natural := natCastArgument? expression then
        if config.symbolicExponentsAsRealPowers then
          return ← reifyNatCast config natural expression coordinates fuel
        return ← freezeAtom expression coordinates
      if let some (lhs, rhs) := binaryArguments? expression ``HAdd.hAdd then
        let (lhsExpression, coordinates) ← reifyAux config lhs coordinates fuel
        let (rhsExpression, coordinates) ← reifyAux config rhs coordinates fuel
        return (.add lhsExpression rhsExpression, coordinates)
      if let some (lhs, rhs) := binaryArguments? expression ``HSub.hSub then
        let (lhsExpression, coordinates) ← reifyAux config lhs coordinates fuel
        let (rhsExpression, coordinates) ← reifyAux config rhs coordinates fuel
        return (.sub lhsExpression rhsExpression, coordinates)
      if let some (lhs, rhs) := binaryArguments? expression ``HMul.hMul then
        let (lhsExpression, coordinates) ← reifyAux config lhs coordinates fuel
        let (rhsExpression, coordinates) ← reifyAux config rhs coordinates fuel
        return (.mul lhsExpression rhsExpression, coordinates)
      if let some (lhs, rhs) := binaryArguments? expression ``HDiv.hDiv then
        let (lhsExpression, coordinates) ← reifyAux config lhs coordinates fuel
        let (rhsExpression, coordinates) ← reifyAux config rhs coordinates fuel
        return (.div lhsExpression rhsExpression, coordinates)
      if let some argument := unaryArgument? expression ``Neg.neg then
        let (argumentExpression, coordinates) ←
          reifyAux config argument coordinates fuel
        return (.neg argumentExpression, coordinates)
      if let some argument := unaryArgument? expression ``Inv.inv then
        let (argumentExpression, coordinates) ←
          reifyAux config argument coordinates fuel
        return (.div (.nat 1) argumentExpression, coordinates)
      if let some (base, exponent) :=
          binaryArguments? expression ``HPow.hPow then
        let exponentType ← inferType exponent
        if ← isDefEqGuarded exponentType (mkConst ``Nat) then
          if config.symbolicExponentsAsRealPowers ∧ (← getNatValue? exponent).isNone then
            let castExponent ←
              mkAppOptM ``Nat.cast #[some (mkConst ``Real), none, some exponent]
            let (baseExpression, coordinates) ← reifyAux config base coordinates fuel
            let (exponentExpression, coordinates) ←
              reifyAux config castExponent coordinates fuel
            return (.rpow baseExpression exponentExpression, coordinates)
          unless ← config.exponentAllowed exponent do
            throwError
              "{config.operation} does not accept this natural-number exponent:\
               {indentExpr exponent}"
          let (baseExpression, coordinates) ← reifyAux config base coordinates fuel
          return (.pow baseExpression exponent, coordinates)
        else if ← isDefEqGuarded exponentType (mkConst ``Int) then
          if config.symbolicExponentsAsRealPowers ∧ (← getIntValue? exponent).isNone then
            let castExponent ←
              mkAppOptM ``Int.cast #[some (mkConst ``Real), none, some exponent]
            let (baseExpression, coordinates) ← reifyAux config base coordinates fuel
            let (exponentExpression, coordinates) ←
              reifyAux config castExponent coordinates fuel
            return (.rpow baseExpression exponentExpression, coordinates)
          let some value ← getIntValue? exponent
            | throwError
                "{config.operation} supports integer powers only when the exponent \
                 is a literal; received{indentExpr exponent}"
          let naturalExponent := mkNatLit value.natAbs
          unless ← config.exponentAllowed naturalExponent do
            throwError
              "{config.operation} does not accept this integer exponent:\
               {indentExpr exponent}"
          let (baseExpression, coordinates) ← reifyAux config base coordinates fuel
          if value < 0 then
            return (
              .div (.nat 1) (.pow baseExpression naturalExponent),
              coordinates)
          else
            return (.pow baseExpression naturalExponent, coordinates)
        else if ← isDefEqGuarded exponentType (mkConst ``Real) then
          let (baseExpression, coordinates) ← reifyAux config base coordinates fuel
          let (exponentExpression, coordinates) ←
            reifyAux config exponent coordinates fuel
          return (.rpow baseExpression exponentExpression, coordinates)
        else
          throwError
            "{config.operation} supports natural powers, literal integer powers, and real \
             powers; the exponent has type{indentExpr exponentType}"
      if let some (base, exponent) := binaryArguments? expression ``Real.rpow then
        let (baseExpression, coordinates) ← reifyAux config base coordinates fuel
        let (exponentExpression, coordinates) ←
          reifyAux config exponent coordinates fuel
        return (.rpow baseExpression exponentExpression, coordinates)
      if let some (function, argument) := desugaredFunctionApplication? expression then
        let (argumentExpression, coordinates) ←
          reifyAux config argument coordinates fuel
        return (.apply function argumentExpression, coordinates)
      if let some (operation, argument) :=
          unaryOperationApplication? expression then
        let (argumentExpression, coordinates) ←
          reifyAux config argument coordinates fuel
        return (.unary operation argumentExpression, coordinates)
      throwError
        "{config.operation} cannot reflect this real expression:\
         {indentExpr expression}\n\
         Supported operations are +, -, *, /, natural powers, literal integer powers, \
         real powers, abs, sin, cos, tan, sinh, cosh, tanh, atan/arctan, asin/arcsin, \
         acos/arccos, exp, log, or sqrt."

/--
Reify one elaborated real expression according to `config`.

Predefined coordinates are matched by guarded definitional equality. When
`opaque?` accepts a real subterm, it is appended to the coordinate table once
and subsequent definitionally equal occurrences reuse that coordinate.
-/
def reify (config : Config) (expression : Lean.Expr) : MetaM Reification := do
  checkInitialData config
  unless ← hasType expression (mkConst ``Real) do
    let type ← inferType expression
    throwError
      "{config.operation} supports real-valued expressions; the input has type\
       {indentExpr type}"
  let (reflected, coordinates) ←
    reifyAux config expression config.coordinates
      (traversalFuel expression config.unfoldLimit)
  return .mk reflected coordinates

/-- The expression `⟨value, proof⟩ : Fin bound`, with the bound checked by `decide`. -/
def makeFin (value bound : Nat) : MetaM Lean.Expr := do
  let inequality ← mkAppM ``LT.lt #[Lean.toExpr value, Lean.toExpr bound]
  let proof ← mkDecideProof inequality
  mkAppM ``Fin.mk #[Lean.toExpr value, proof]

/-- Quote `form`, an expression in one variable, with the quoted `argument` for the variable. With
`form = function.desugar (.var ())` this quotes the form of `function` at the argument, the term
that the operations of the form would quote to. -/
private def quoteForm (index argument : Lean.Expr) : Verified.Expr Unit → MetaM Lean.Expr
  | .var () => pure argument
  | .nat value => mkAppOptM ``Verified.Expr.nat #[some index, some (Lean.toExpr value)]
  | .add lhs rhs => do
      mkAppM ``Verified.Expr.add
        #[← quoteForm index argument lhs, ← quoteForm index argument rhs]
  | .sub lhs rhs => do
      mkAppM ``Verified.Expr.sub
        #[← quoteForm index argument lhs, ← quoteForm index argument rhs]
  | .div lhs rhs => do
      mkAppM ``Verified.Expr.div
        #[← quoteForm index argument lhs, ← quoteForm index argument rhs]
  | .neg arg => do mkAppM ``Verified.Expr.neg #[← quoteForm index argument arg]
  | .pow base exponent => do
      mkAppM ``Verified.Expr.pow #[← quoteForm index argument base, mkNatLit exponent]
  | .sin arg => do mkAppM ``Verified.Expr.sin #[← quoteForm index argument arg]
  | .cos arg => do mkAppM ``Verified.Expr.cos #[← quoteForm index argument arg]
  | .exp arg => do mkAppM ``Verified.Expr.exp #[← quoteForm index argument arg]
  | .sqrt arg => do mkAppM ``Verified.Expr.sqrt #[← quoteForm index argument arg]
  | _ => throwError "a desugared function uses an operation that its quotation does not cover"

private def quoteReflectedWith
    (index : Lean.Expr) (coordinate : Nat → MetaM Lean.Expr) :
    ReflectedExpr Nat Lean.Expr → MetaM Lean.Expr
  | .nat value =>
      mkAppOptM ``Verified.Expr.nat #[some index, some (Lean.toExpr value)]
  | .rat num den =>
      mkAppOptM ``Verified.Expr.rat #[some index, some (Lean.toExpr num), some (Lean.toExpr den)]
  | .constant .pi =>
      mkAppOptM ``Verified.Expr.pi #[some index]
  | .constant .e =>
      mkAppOptM ``Verified.Expr.e #[some index]
  | .coordinate position => do
      mkAppM ``Verified.Expr.var #[← coordinate position]
  | .add lhs rhs => do
      mkAppM ``Verified.Expr.add #[
        ← quoteReflectedWith index coordinate lhs,
        ← quoteReflectedWith index coordinate rhs
      ]
  | .mul lhs rhs => do
      mkAppM ``Verified.Expr.mul #[
        ← quoteReflectedWith index coordinate lhs,
        ← quoteReflectedWith index coordinate rhs
      ]
  | .sub lhs rhs => do
      mkAppM ``Verified.Expr.sub #[
        ← quoteReflectedWith index coordinate lhs,
        ← quoteReflectedWith index coordinate rhs
      ]
  | .div lhs rhs => do
      mkAppM ``Verified.Expr.div #[
        ← quoteReflectedWith index coordinate lhs,
        ← quoteReflectedWith index coordinate rhs
      ]
  | .neg arg => do
      mkAppM ``Verified.Expr.neg #[← quoteReflectedWith index coordinate arg]
  | .pow base exponent => do
      mkAppM ``Verified.Expr.pow #[← quoteReflectedWith index coordinate base, exponent]
  | .unary operation arg => do
      mkAppM operation.constructorName #[← quoteReflectedWith index coordinate arg]
  | .apply function arg => do
      quoteForm index (← quoteReflectedWith index coordinate arg) (function.desugar (.var ()))
  | .rpow base exponent => do
      mkAppM ``Verified.Expr.rpow #[
        ← quoteReflectedWith index coordinate base,
        ← quoteReflectedWith index coordinate exponent
      ]

private def quoteReflected
    (dimension : Nat) (reflected : ReflectedExpr Nat Lean.Expr) : MetaM Lean.Expr :=
  quoteReflectedWith
    (mkApp (mkConst ``Fin) (Lean.toExpr dimension))
    (fun position ↦ makeFin position dimension)
    reflected

/--
Quote a reification over a variable type in any universe, choosing the kernel term
denoting each coordinate position. Here `index` is an elaborated Lean term representing
the label type; each returned coordinate term must have that type. Constructor quotation
infers the label universe from these terms.

Derivative tactics use this to place coordinates and frozen parameters at
`Fin.castAdd`/`Fin.natAdd` positions of `Fin (n + k)`, so that the standard
`Fin.append` simp lemmas recover the original real terms.
-/
def Reification.quoteWith
    (result : Reification) (index : Lean.Expr)
    (coordinate : Nat → MetaM Lean.Expr) : MetaM Lean.Expr :=
  quoteReflectedWith index coordinate result.reflected

/-- Quote a reification as a kernel term of type `Verified.Expr (Fin dimension)`. -/
def Reification.quote (result : Reification) : MetaM Lean.Expr :=
  quoteReflected result.dimension result.reflected

/--
Lower a reification to executable checked syntax when every exponent reduces to
a natural number. Quotation remains available when an exponent is a local
natural parameter and therefore cannot be evaluated during elaboration.
-/
def Reification.toVerifiedExpr?
    (result : Reification) : MetaM (Option (Verified.Expr (Fin result.dimension))) :=
  result.reflected.toVerifiedExprM?
    (fun index ↦
      pure <| if h : index < result.dimension then some ⟨index, h⟩ else none)
    getNatValue?

end CAS.Elaboration.RealExpression

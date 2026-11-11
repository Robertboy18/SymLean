/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Elaboration.RealExpression.Syntax
public meta import CAS.Elaboration.RealExpression.Syntax
public meta import CAS.Expr.Rendering
public meta import CAS.Command.FunctionTable

/-!
# Input syntax for the checked symbolic calculator

`parseExpr` reads the expression of a `#cas` command from ordinary Lean notation into the
frontend-neutral `ReflectedExpr` shared with theorem elaboration, without asking Lean to
elaborate identifiers such as `x` or `y`. `reifyInferred`, `reifyWithLeading` and `reifyExact`
replace those names by the coordinates of a `Verified.Expr (Fin n)`, kept with its table of
names as a `ReifiedExpr`, and the checked engines receive that expression. The other definitions
are what the modes share about their input: its text as typed (`surfaceText`), the quotation of
a checked expression as a Lean term (`quoteVerifiedExpr`), exact rational literals
(`parseRationalLiteral`), and the options `cas.verbose` and `cas.maxDigits`.

## Main definitions

* `CAS.Command.parseExpr`: the expression of a command as a `ReflectedExpr` over names.
* `CAS.Command.ReifiedExpr`: a checked expression with its ordered coordinate names and the input
  as written (`SurfaceForm`).
* `CAS.Command.parseInferred`, `CAS.Command.parseWithLeading`, `CAS.Command.parseExact`: parse
  and reify, with the variables in first-occurrence order, with the declared variables first, or
  in exactly the declared variables.
* `CAS.Command.parseScalarInput`: a scalar input, whose coordinate a lambda `fun x ↦ e` selects.
* `CAS.Command.quoteVerifiedExpr`: a checked expression as a closed Lean term, for proof terms.
* `CAS.Command.parseRationalLiteral`: an exact rational literal, such as an interval endpoint.
* `CAS.Command.parseDigitsOption`: the count `d` of `(digits := d)`, from `1` to `cas.maxDigits`.

## Implementation notes

The parser is fail-closed and reads syntax only. Arbitrary Lean applications are rejected rather
than interpreted as symbolic functions, and an ascription other than `ℝ` or `Real` is refused
rather than dropped, with a message of its own for `ℂ`. The constants are `pi`, `π` (a name, or
Mathlib's notation for `Real.pi` under `open Real`), `Real.pi` and `e`. A decimal literal is the
exact rational it denotes, refused when its power of ten is over `maxDecimalExponent`. Natural
powers are represented directly; negative integer literals are lowered to reciprocals of natural
powers; any other exponent is parsed as a real expression and becomes the checked real power
`rpow`, whose base must be positive. The functions of `DesugaredFunction`, such as `tan` and
`|a|`, stay applications in the reflected input (`SurfaceForm`), so a statement can name them
where the user wrote them. The name-indexed
expression is an internal reflection format: command users write ordinary Lean notation and never
construct it themselves. A coordinate is a `Fin names.length` found by `coordinateIndex?`, so
reification cannot produce an index out of range.
-/

public meta section

namespace CAS

/-- Show the complete checked-evidence tree below `cas?` and `cega?` suggestions, and the
symbolic derivation trees in `#cas` reports. -/
register_option cas.verbose : Bool := {
  defValue := false
  descr := "show the complete checked-evidence and planner-metadata report for cas? and cega?, \
    and the derivation trees of #cas reports"
}

end CAS

namespace CAS.Command

open Lean Elab Command Meta
open CAS.Elaboration.RealExpression

/-- Render a command-level symbolic name as Lean prints it: with the escapes `«…»` only when a
component is not an identifier, so that a variable named `«n-m»` is not printed as `n-m`. -/
def renderName (name : Name) : String :=
  name.toString

/-- The source text of `stx` as typed, without the whitespace and comments that follow it in the
file. Reports print their input with it. -/
def surfaceText (stx : Syntax) : String :=
  (stx.unsetTrailing.reprint.getD "").trimAscii.toString

/-- `count` followed by `noun`, plural unless `count = 1`: `1 cell`, `3 cells`. -/
def countText (count : Nat) (noun : String) (plural : String := noun ++ "s") : String :=
  s!"{count} {if count = 1 then noun else plural}"

/--
Find a variable's coordinate together with the proof that it lies in the name table.

Returning `Fin names.length` keeps the coordinate bound attached to the lookup, so reification
cannot manufacture an out-of-range variable index.
-/
def coordinateIndex? (names : List Name) (target : Name) : Option (Fin names.length) :=
  match names with
  | [] => none
  | name :: rest =>
      if name = target then
        some 0
      else
        (coordinateIndex? rest target).map Fin.succ

private def appendVariable (names : List Name) (name : Name) : List Name :=
  if name ∈ names then names else names ++ [name]

/--
Collect expression variables in first-occurrence order.

This order is the default coordinate order for modes such as `simplify`.
Modes with declared variables may replace or extend it explicitly.
-/
private def freeNames : ReflectedExpr Name Nat → List Name
  | .nat _ | .rat .. | .constant _ => []
  | .coordinate name => [name]
  | .add lhs rhs | .mul lhs rhs | .sub lhs rhs | .div lhs rhs =>
      (freeNames rhs).foldl appendVariable (freeNames lhs)
  | .neg arg | .pow arg _ | .unary _ arg | .apply _ arg =>
      freeNames arg
  | .rpow base exponent =>
      (freeNames exponent).foldl appendVariable (freeNames base)

/-- What a reified expression in `n` coordinates keeps of the input as the user wrote it. -/
structure SurfaceForm (n : Nat) where
  /-- The text of the input, kept only for the input line of reports. -/
  text? : Option String := none
  /-- The input as reflected syntax with its coordinates resolved, so that a statement can name
  each function of `DesugaredFunction` exactly where the user applied it. -/
  tree? : Option (ReflectedExpr (Fin n) Nat) := none

/-- A checked expression paired with its complete ordered coordinate-name table. -/
structure ReifiedExpr where
  /-- Coordinate names in the order used by the checked expression. -/
  names : List Name
  /-- The checked expression indexed by positions in `names`. -/
  expr : Verified.Expr (Fin names.length)
  /-- The input as the user wrote it. -/
  surface : SurfaceForm names.length := {}

namespace ReifiedExpr

/-- Display name of a coordinate in a reified expression. -/
def coordinateName (reified : ReifiedExpr) (i : Fin reified.names.length) : String :=
  renderName (reified.names.get i)

/-- Render a reified expression using the names written in the command. -/
def render (reified : ReifiedExpr) : String :=
  reified.surface.text?.getD <| reified.expr.renderWith reified.coordinateName

/-- The functions of `DesugaredFunction` that `tree` applies, with repetitions. -/
private def appliedFunctions {ι κ : Type} : ReflectedExpr ι κ → List DesugaredFunction
  | .apply function arg => function :: appliedFunctions arg
  | .add lhs rhs | .mul lhs rhs | .sub lhs rhs | .div lhs rhs | .rpow lhs rhs =>
      appliedFunctions lhs ++ appliedFunctions rhs
  | .neg arg | .pow arg _ | .unary _ arg => appliedFunctions arg
  | .nat _ | .rat .. | .constant _ | .coordinate _ => []

/-- The functions of `DesugaredFunction` that the input applies somewhere. The statements and the
display lines of a report name these functions and no others. -/
def inputFunctions (reified : ReifiedExpr) : List DesugaredFunction :=
  ((reified.surface.tree?.map appliedFunctions).getD []).eraseDups

end ReifiedExpr

/-- The index type `Fin n` of a quoted expression in `n` variables. -/
def quotedVariableType (n : Nat) : Lean.Expr :=
  .app (.const ``Fin []) (Lean.toExpr n)

private def quoteConstant (n : Nat) (constructor : Name)
    (args : Array Lean.Expr) : Lean.Expr :=
  mkAppN (.const constructor [Level.zero]) (#[quotedVariableType n] ++ args)

/--
Quote a checked expression as a closed Lean syntax-tree term.

Commands quote through this function when constructing proof terms whose
propositions mention the expression displayed in the InfoView. The
dimension is supplied to nullary constructors explicitly, preventing an
unresolved variable-type metavariable from escaping into evidence validation.
-/
def quoteVerifiedExpr {n : Nat} :
    Verified.Expr (Fin n) → MetaM Lean.Expr
  | .nat value =>
      pure <| quoteConstant n ``Verified.Expr.nat #[Lean.toExpr value]
  | .int value =>
      pure <| quoteConstant n ``Verified.Expr.int #[Lean.toExpr value]
  | .rat numerator denominator =>
      pure <| quoteConstant n ``Verified.Expr.rat
        #[Lean.toExpr numerator, Lean.toExpr denominator]
  | .pi =>
      pure <| quoteConstant n ``Verified.Expr.pi #[]
  | .e =>
      pure <| quoteConstant n ``Verified.Expr.e #[]
  | .var coordinate =>
      mkAppM ``Verified.Expr.var #[Lean.toExpr coordinate]
  | .add lhs rhs => do
      mkAppM ``Verified.Expr.add #[← quoteVerifiedExpr lhs, ← quoteVerifiedExpr rhs]
  | .mul lhs rhs => do
      mkAppM ``Verified.Expr.mul #[← quoteVerifiedExpr lhs, ← quoteVerifiedExpr rhs]
  | .sub lhs rhs => do
      mkAppM ``Verified.Expr.sub #[← quoteVerifiedExpr lhs, ← quoteVerifiedExpr rhs]
  | .div lhs rhs => do
      mkAppM ``Verified.Expr.div #[← quoteVerifiedExpr lhs, ← quoteVerifiedExpr rhs]
  | .neg arg => do
      mkAppM ``Verified.Expr.neg #[← quoteVerifiedExpr arg]
  | .pow base exponent => do
      mkAppM ``Verified.Expr.pow #[← quoteVerifiedExpr base, Lean.toExpr exponent]
  | .sin arg => do
      mkAppM ``Verified.Expr.sin #[← quoteVerifiedExpr arg]
  | .cos arg => do
      mkAppM ``Verified.Expr.cos #[← quoteVerifiedExpr arg]
  | .atan arg => do
      mkAppM ``Verified.Expr.atan #[← quoteVerifiedExpr arg]
  | .asin arg => do
      mkAppM ``Verified.Expr.asin #[← quoteVerifiedExpr arg]
  | .acos arg => do
      mkAppM ``Verified.Expr.acos #[← quoteVerifiedExpr arg]
  | .exp arg => do
      mkAppM ``Verified.Expr.exp #[← quoteVerifiedExpr arg]
  | .log arg => do
      mkAppM ``Verified.Expr.log #[← quoteVerifiedExpr arg]
  | .sqrt arg => do
      mkAppM ``Verified.Expr.sqrt #[← quoteVerifiedExpr arg]
  | .rpow base exponent => do
      mkAppM ``Verified.Expr.rpow #[← quoteVerifiedExpr base, ← quoteVerifiedExpr exponent]

private def isReservedFunction (name : Name) : Bool :=
  (UnaryOperation.ofSurfaceName? name).isSome || (DesugaredFunction.ofSurfaceName? name).isSome

private def supportedFunctionNames : String :=
  "abs, sin, cos, tan, sinh, cosh, tanh, atan/arctan, asin/arcsin, \
   acos/arccos, exp, log, or sqrt"

/-- The last sentence of the refusal of an application of `name`: for a function of the call
table, the commands that evaluate it, and otherwise how to write a product. -/
private def applicationHint (name : Name) : String :=
  (FunctionTable.callHint? name.toString).getD
    "If multiplication was intended, write it explicitly with `*`"

private inductive ScalarTypeAnnotation where
  | real
  | complex
  | unsupported

/--
Classify only the scalar annotations whose semantics are fixed by `#cas`.

The classification is syntactic. Elaborating an arbitrary type and then
discarding it would make a command appear polymorphic, while every checked
backend denotes a real-valued expression.
-/
private def classifyScalarTypeAnnotation (type : Syntax) : ScalarTypeAnnotation :=
  if type.isOfKind ``termℝ then
    .real
  else if type.isOfKind ``termℂ then
    .complex
  else if type.isIdent then
    match type.getId with
    | `Real => .real
    | `Complex => .complex
    | _ => .unsupported
  else
    .unsupported

private def checkScalarTypeAnnotation {m : Type → Type} [Monad m] [MonadError m]
    (type : Syntax) : m Unit := do
  match classifyScalarTypeAnnotation type with
  | .real => pure ()
  | .complex =>
      throwErrorAt type
        "#cas supports real scalar expressions only; use ℝ or Real, or omit the annotation"
  | .unsupported =>
      throwErrorAt type
        "#cas does not support this scalar type; use ℝ or Real, or omit the annotation"

/--
Return one more than the number of nodes in a syntax tree.

The parser uses this as a structural recursion budget. Lean's standard
top-down traversal avoids depending on the compiler-internal `SizeOf Syntax`
instance, which is unavailable to generated code.
-/
private def syntaxTraversalFuel (stx : Syntax) : Nat := Id.run do
  let mut fuel := 1
  for _ in stx.topDown do
    fuel := fuel + 1
  return fuel

private def isIntegerTypeAnnotation (type : Syntax) : Bool :=
  type.isOfKind ``termℤ || (type.isIdent && type.getId = `Int)

/-- Recognize a possibly parenthesized integer literal used as a power. -/
private def integerPowerLiteralWithFuel : Nat → Syntax → Option Int
  | 0, _ => none
  | fuel + 1, stx =>
      if let some value := stx.isNatLit? then
        some value
      else
        match stx with
        | `(- $arg:term) =>
            (integerPowerLiteralWithFuel fuel arg).map (-·)
        | `(($arg:term)) =>
            integerPowerLiteralWithFuel fuel arg
        | `(($arg:term : $type:term)) =>
            if isIntegerTypeAnnotation type then
              integerPowerLiteralWithFuel fuel arg
            else
              none
        | _ => none

private def integerPowerLiteral? (stx : Syntax) : Option Int :=
  integerPowerLiteralWithFuel (syntaxTraversalFuel stx) stx

private def parseExprWithFuel {m : Type → Type} [Monad m] [MonadError m]
    (boundName? : Option Name) :
    Nat → Syntax → m (ReflectedExpr Name Nat)
  | 0, stx =>
      throwErrorAt stx "symbolic expression exceeds the parser's structural recursion bound"
  | fuel + 1, stx => do
      if let some value := stx.isNatLit? then
        return .nat value
      -- A decimal `m.dE±e` is the exact rational `m / 10 ^ k` or the natural `m * 10 ^ k`.
      if let some (mantissa, negativeExponent, exponent) := stx.isScientificLit? then
        checkDecimalExponent stx exponent
        return ReflectedExpr.decimalLiteral mantissa negativeExponent exponent
      if stx.isIdent then
        let name := stx.getId
        if boundName? == some name then
          return .coordinate name
        if name = `pi ∨ name = `Real.pi ∨ name = `π then
          return .constant .pi
        if name = `e then
          return .constant .e
        if isReservedFunction name then
          throwErrorAt stx "symbolic function '{name}' requires exactly one argument"
        return .coordinate name
      -- `π` under `open Real` is Mathlib's notation for `Real.pi`, a node with the one atom `π`.
      if let .node _ _ #[.atom _ "π"] := stx then
        return .constant .pi
      match stx with
      | `(($arg:term : $type:term)) =>
          checkScalarTypeAnnotation type
          parseExprWithFuel boundName? fuel arg
      | `(($arg:term)) =>
          parseExprWithFuel boundName? fuel arg
      | `(|$arg:term|) =>
          return .apply .abs (← parseExprWithFuel boundName? fuel arg)
      | `(- $arg:term) =>
          return .neg (← parseExprWithFuel boundName? fuel arg)
      | `($lhs:term + $rhs:term) =>
          return .add
            (← parseExprWithFuel boundName? fuel lhs) (← parseExprWithFuel boundName? fuel rhs)
      | `($lhs:term - $rhs:term) =>
          return .sub
            (← parseExprWithFuel boundName? fuel lhs) (← parseExprWithFuel boundName? fuel rhs)
      | `($lhs:term * $rhs:term) =>
          return .mul
            (← parseExprWithFuel boundName? fuel lhs) (← parseExprWithFuel boundName? fuel rhs)
      | `($lhs:term / $rhs:term) =>
          return .div
            (← parseExprWithFuel boundName? fuel lhs) (← parseExprWithFuel boundName? fuel rhs)
      | `($base:term ^ $exponent:term) =>
          let some value := integerPowerLiteral? exponent
            | do
              let base ← parseExprWithFuel boundName? fuel base
              let exponent ← parseExprWithFuel boundName? fuel exponent
              return .rpow base exponent
          let base ← parseExprWithFuel boundName? fuel base
          if value < 0 then
            return .div (.nat 1) (.pow base value.natAbs)
          else
            return .pow base value.toNat
      | `($function:ident $arg:term) =>
          if boundName? == some function.getId then
            throwErrorAt function
              "the real parameter '{function.getId}' cannot be applied as a function"
          let argument ← parseExprWithFuel boundName? fuel arg
          if let some desugared := DesugaredFunction.ofSurfaceName? function.getId then
            return .apply desugared argument
          let some operation := UnaryOperation.ofSurfaceName? function.getId
            | throwErrorAt function
                "unsupported symbolic function '{function.getId}'; expected \
                  {supportedFunctionNames}. {applicationHint function.getId}"
          return .unary operation argument
      | _ =>
          if stx.isOfKind ``Lean.Parser.Term.app then
            throwErrorAt stx
              "unsupported symbolic application; supported functions take one argument and are: \
                {supportedFunctionNames}. {applicationHint stx[0].getId}"
          else
            throwErrorAt stx
              "unsupported #cas expression; use variables, integer literals, arithmetic, integer \
                literal powers, abs, sin, cos, tan, sinh, cosh, tanh, atan, asin, arccos, \
                exp, log, sqrt, pi, or e"

/--
Parse one calculator expression from ordinary Lean mathematical notation.

The accepted functions are `abs`, `sin`, `cos`, `tan`, `sinh`, `cosh`, `tanh`,
`atan`, `asin`, `arccos`, `exp`, `log`, and `sqrt`, with their `Real.*`
spellings also accepted. An application with the wrong arity, such as
`sin x y`, receives an explicit diagnostic. Since this
expression language has fixed scalar-real semantics, `ℝ` and `Real`
ascriptions are accepted as explicit documentation. Other ascriptions are
rejected rather than silently discarded.

The recursion bound is derived from the input syntax tree. Every recursive
call consumes one unit while descending to a child syntax node.
-/
def parseExpr {m : Type → Type} [Monad m] [MonadError m]
    (stx : Syntax) : m (ReflectedExpr Name Nat) :=
  parseExprWithFuel none (syntaxTraversalFuel stx) stx

private def parseRationalLiteralWithFuel
    {m : Type → Type} [Monad m] [MonadError m] :
    Nat → Syntax → m ℚ
  | 0, stx =>
      throwErrorAt stx "rational literal exceeds the parser's structural recursion bound"
  | fuel + 1, stx => do
      if let some value := stx.isNatLit? then
        return value
      if let some (mantissa, negativeExponent, exponent) := stx.isScientificLit? then
        checkDecimalExponent stx exponent
        return if negativeExponent then mkRat mantissa (10 ^ exponent)
          else (mantissa * 10 ^ exponent : Nat)
      match stx with
      | `(($value:term)) =>
          parseRationalLiteralWithFuel fuel value
      | `(- $value:term) =>
          return -(← parseRationalLiteralWithFuel fuel value)
      | `($numerator:term / $denominator:term) =>
          let numeratorValue ← parseRationalLiteralWithFuel fuel numerator
          let denominatorValue ← parseRationalLiteralWithFuel fuel denominator
          if denominatorValue = 0 then
            throwErrorAt denominator "a rational interval endpoint cannot divide by zero"
          return numeratorValue / denominatorValue
      | _ =>
          throwErrorAt stx
            "interval endpoints must be exact rational literals, such as -1, 3/2, -1/10, or 0.1"

/--
Parse an exact rational endpoint without invoking floating-point evaluation.

The accepted grammar consists of natural and decimal literals (`1.1` is `11/10`), unary
negation, parentheses, and quotients. Arbitrary Lean terms are rejected, so the
endpoints of an interval in a `#cas` command have exact rational values that
can be read off their syntax.
-/
def parseRationalLiteral {m : Type → Type} [Monad m] [MonadError m]
    (stx : Syntax) : m ℚ :=
  parseRationalLiteralWithFuel (syntaxTraversalFuel stx) stx

/-- `parseRationalLiteral` for an argument of `command` that is not an interval endpoint: when
`stx` is not an exact rational literal, the error is `"{command}: {requirement}"`, so it names
the mode and what it accepts. -/
def parseRationalLiteralFor {m : Type → Type} [Monad m] [MonadError m]
    (command requirement : String) (stx : Syntax) : m ℚ :=
  tryCatchThe Exception (parseRationalLiteral stx) fun _ ↦
    throwErrorAt stx "{command}: {requirement}"

private def firstDuplicate? : List Name → Option Name
  | [] => none
  | name :: names => if name ∈ names then some name else firstDuplicate? names

private def lowerIn (names : List Name) (named : ReflectedExpr Name Nat) :
    Option (Verified.Expr (Fin names.length)) :=
  Id.run <| named.toVerifiedExprM?
    (fun name ↦ pure (coordinateIndex? names name)) (fun exponent ↦ pure (some exponent))

/-- `named` with its coordinates resolved in `names`. -/
private def resolveIn (names : List Name) :
    ReflectedExpr Name Nat → Option (ReflectedExpr (Fin names.length) Nat)
  | .nat value => some (.nat value)
  | .rat num den => some (.rat num den)
  | .constant value => some (.constant value)
  | .coordinate name => (coordinateIndex? names name).map ReflectedExpr.coordinate
  | .add lhs rhs => do return .add (← resolveIn names lhs) (← resolveIn names rhs)
  | .mul lhs rhs => do return .mul (← resolveIn names lhs) (← resolveIn names rhs)
  | .sub lhs rhs => do return .sub (← resolveIn names lhs) (← resolveIn names rhs)
  | .div lhs rhs => do return .div (← resolveIn names lhs) (← resolveIn names rhs)
  | .neg arg => do return .neg (← resolveIn names arg)
  | .pow base exponent => do return .pow (← resolveIn names base) exponent
  | .unary operation arg => do return .unary operation (← resolveIn names arg)
  | .apply function arg => do return .apply function (← resolveIn names arg)
  | .rpow base exponent => do
      return .rpow (← resolveIn names base) (← resolveIn names exponent)

private def lowerWithNames (named : ReflectedExpr Name Nat) (names : List Name) :
    Except String ReifiedExpr :=
  match lowerIn names named with
  | some expr =>
      .ok { names := names, expr := expr, surface := { tree? := resolveIn names named } }
  | none => .error "internal #cas reification error: the coordinate table is incomplete"

/-- Reify an expression using first-occurrence variable order. -/
def reifyInferred (named : ReflectedExpr Name Nat) : Except String ReifiedExpr :=
  lowerWithNames named (freeNames named)

/--
Reify an expression with declared variables first, followed by undeclared
variables in first-occurrence order.

This is used by scalar modes such as `derive x` and `integrate x`, where other
coordinates remain parameters.
-/
def reifyWithLeading (declared : List Name) (named : ReflectedExpr Name Nat) :
    Except String ReifiedExpr := do
  if let some duplicate := firstDuplicate? declared then
    throw s!"duplicate coordinate '{renderName duplicate}'"
  let names := (freeNames named).foldl appendVariable declared
  lowerWithNames named names

/--
Reify an expression in exactly the declared coordinate space.

Gradient-like operators use this form so their output dimension and component
order are explicit. Variables appearing in the expression but absent from the
declaration are rejected.
-/
def reifyExact (declared : List Name) (named : ReflectedExpr Name Nat) :
    Except String ReifiedExpr := do
  if declared.isEmpty then
    throw "at least one coordinate must be declared"
  if let some duplicate := firstDuplicate? declared then
    throw s!"duplicate coordinate '{renderName duplicate}'"
  let undeclared := (freeNames named).filter fun name ↦ name ∉ declared
  if !undeclared.isEmpty then
    let names := ", ".intercalate <|
      undeclared.map renderName
    throw s!"expression contains undeclared variables: {names}"
  lowerWithNames named declared

/-- Parse and reify a term with inferred variable order. -/
def parseInferred {m : Type → Type} [Monad m] [MonadError m]
    (stx : Syntax) : m ReifiedExpr := do
  let named ← parseExpr stx
  match reifyInferred named with
  | .ok reified => return { reified with surface.text? := some (surfaceText stx) }
  | .error message => throwErrorAt stx message

/-- Parse and reify a term with the declared variables placed first. -/
def parseWithLeading {m : Type → Type} [Monad m] [MonadError m]
    (stx : Syntax) (declared : List Name) : m ReifiedExpr := do
  let named ← parseExpr stx
  match reifyWithLeading declared named with
  | .ok reified => return { reified with surface.text? := some (surfaceText stx) }
  | .error message => throwErrorAt stx message

private def scalarFunctionBodyWithFuel {m : Type → Type} [Monad m] [MonadError m] :
    Nat → Syntax → m (Option (Name × Syntax))
  | 0, stx =>
      throwErrorAt stx "symbolic function exceeds the parser's structural recursion bound"
  | fuel + 1, stx => do
      match stx with
      | `(($body:term)) => scalarFunctionBodyWithFuel fuel body
      | `(fun $name:ident ↦ $body:term) => return some (name.getId, body)
      | `(fun ($name:ident : $type:term) ↦ $body:term)
      | `(fun $name:ident : $type:term ↦ $body:term) =>
          checkScalarTypeAnnotation type
          return some (name.getId, body)
      | _ =>
          if stx.isOfKind ``Lean.Parser.Term.fun then
            throwErrorAt stx
              "#cas expects one named real parameter, such as `fun x : ℝ ↦ 2 * x`; \
                for several coordinates, write an expression and select a coordinate explicitly"
          return none

/--
Parse a scalar calculation, using a function's parameter when the input is a lambda.

The function body has the same checked real-expression grammar as a bare expression.
Its binder selects the coordinate even when the body is constant or contains parameters.
An explicit coordinate must agree with that binder. Bound names shadow calculator constants
and function names, as in ordinary Lean notation.
-/
def parseScalarInput {m : Type → Type} [Monad m] [MonadError m]
    (stx : Syntax) (coordinate? : Option Name) : m (ReifiedExpr × Option Name) := do
  match ← scalarFunctionBodyWithFuel (syntaxTraversalFuel stx) stx with
  | none =>
      match coordinate? with
      | none => return (← parseInferred stx, none)
      | some name => return (← parseWithLeading stx [name], some name)
  | some (name, body) =>
      if let some coordinate := coordinate? then
        if coordinate != name then
          throwErrorAt stx
            "coordinate '{renderName coordinate}' does not match the function parameter \
              '{renderName name}'; use the parameter name or omit the coordinate"
      let named ← parseExprWithFuel (some name) (syntaxTraversalFuel body) body
      match reifyWithLeading [name] named with
      | .ok reified => return ({ reified with surface.text? := some (surfaceText body) }, some name)
      | .error message => throwErrorAt stx message

/-- Parse and reify a term in exactly the declared coordinate space. -/
def parseExact {m : Type → Type} [Monad m] [MonadError m]
    (stx : Syntax) (declared : List Name) : m ReifiedExpr := do
  let named ← parseExpr stx
  match reifyExact declared named with
  | .ok reified => return { reified with surface.text? := some (surfaceText stx) }
  | .error message => throwErrorAt stx message

/-! ## Options -/

/-- Flatten an `optConfig` node, such as `(digits := 8) (depth := 3)`, into its configuration
items. The fuel bounds the descent by the depth of the syntax tree, so the traversal is total; a
configuration group is at most a few levels deep. -/
def configItems : Nat → Syntax → Array Syntax
  | 0, stx => #[stx]
  | fuel + 1, stx =>
    if stx.isOfKind ``Lean.Parser.Term.optConfig ∨ stx.isOfKind nullKind ∨
        stx.isOfKind ``Lean.Parser.Term.configItem then
      stx.getArgs.flatMap (configItems fuel)
    else
      #[stx]

/-- The name and value of a configuration item `(name := value)`, or `none` for another shape. -/
def valueConfigItem? (item : Syntax) : Option (Name × Syntax) :=
  if item.isOfKind ``Lean.Parser.Term.valConfigItem ∧ item.getNumArgs = 5 then
    some (item[1].getId.eraseMacroScopes, item[3])
  else
    none

/-- The largest number of decimal digits that a `#cas` command or a CEGA query may request; a
request outside `1 ≤ digits ≤ cas.maxDigits` is refused. -/
register_option cas.maxDigits : Nat := {
  defValue := 2000
  descr := "maximum number of decimal digits requested from a #cas command or a CEGA query"
}

/-- Refuse a request for `digits` decimal digits unless `1 ≤ digits ≤ cas.maxDigits`, at `ref`
and naming `command`. -/
def checkDigitCount {m : Type → Type} [Monad m] [MonadError m] [MonadOptions m]
    (ref : Syntax) (command : String) (digits : Nat) : m Unit := do
  let limit := cas.maxDigits.get (← getOptions)
  unless 1 ≤ digits ∧ digits ≤ limit do
    throwErrorAt ref "{command} accepts between 1 and {limit} digits"

/-- The digit count that the configuration `optConfig` of the `#cas` mode `command` requests with
its one option `(digits := d)`, or `default` when the group is empty. A requested count lies
between `1` and `cas.maxDigits`. -/
def parseDigitsOption {m : Type → Type} [Monad m] [MonadError m] [MonadOptions m]
    (command : String) (optConfig : Syntax) (default : Nat) : m Nat := do
  let mut digits := default
  for item in configItems 16 optConfig do
    match valueConfigItem? item with
    | some (`digits, value) =>
        let some d := value.isNatLit?
          | throwErrorAt value "`(digits := d)` takes a natural-number literal"
        checkDigitCount value command d
        digits := d
    | _ => throwErrorAt item "{command} takes the one option `(digits := d)`"
  return digits

end CAS.Command

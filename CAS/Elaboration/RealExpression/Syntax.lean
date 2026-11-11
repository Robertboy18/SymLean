/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Elaboration.RealExpression.Operation

/-!
# Frontend-neutral reflected real expressions

The syntax tree shared by the symbolic commands and the theorem elaborators. The coordinate and
exponent types are parameters because raw commands initially identify coordinates by names and
exponents by literal natural numbers, whereas theorem elaboration identifies coordinates by array
positions and retains elaborated natural exponents for quotation.

The syntax carries no theorem. `ReflectedExpr.toVerifiedExprM?` lowers it into
the executable checked expression language and fails on anything it cannot
translate. `ReflectedExpr.decimalLiteral` reads a decimal literal as the exact natural number or
reduced fraction it denotes, and `checkDecimalExponent` refuses a power of ten above
`maxDecimalExponent`.
-/

@[expose] public section

namespace CAS.Elaboration.RealExpression

/-- A distinguished nullary constant in the checked expression language. -/
inductive Constant where
  | pi
  | e
deriving DecidableEq, Repr

/--
Frontend-neutral syntax for a reflected real expression.

The parameters identify coordinates and natural-number exponents before a
frontend lowers them into `Verified.Expr`.
-/
inductive ReflectedExpr (ι κ : Type*) where
  | nat (value : Nat)
  /-- An exact rational constant `num / den`, as a decimal literal reads; `den` is positive and
  coprime to `num`. -/
  | rat (num : Int) (den : Nat)
  | constant (value : Constant)
  | coordinate (index : ι)
  | add (lhs rhs : ReflectedExpr ι κ)
  | mul (lhs rhs : ReflectedExpr ι κ)
  | sub (lhs rhs : ReflectedExpr ι κ)
  | div (lhs rhs : ReflectedExpr ι κ)
  | neg (arg : ReflectedExpr ι κ)
  | pow (base : ReflectedExpr ι κ) (exponent : κ)
  | unary (operation : UnaryOperation) (arg : ReflectedExpr ι κ)
  /-- A function of the `DesugaredFunction` table, lowered to its form `function.desugar`. -/
  | apply (function : DesugaredFunction) (arg : ReflectedExpr ι κ)
  /-- A real power with a reflected real exponent, lowered to `Verified.Expr.rpow`. -/
  | rpow (base exponent : ReflectedExpr ι κ)

namespace ReflectedExpr

/--
Lower reflected syntax into the executable checked language.

Both coordinate resolution and exponent evaluation may fail. Keeping those
operations explicit prevents either frontend from inventing an out-of-range
coordinate or treating an unevaluated exponent as a natural literal.
-/
def toVerifiedExprM? {ι κ : Type*} {ι' : Type} {m : Type → Type} [Monad m]
    (coordinate? : ι → m (Option ι')) (exponent? : κ → m (Option Nat)) :
    ReflectedExpr ι κ → m (Option (Verified.Expr ι'))
  | .nat value =>
      return some (.nat value)
  | .rat num den =>
      return some (.rat num den)
  | .constant .pi =>
      return some .pi
  | .constant .e =>
      return some .e
  | .coordinate index =>
      return (← coordinate? index).map .var
  | .add lhs rhs => do
      let some lhs ← lhs.toVerifiedExprM? coordinate? exponent? | return none
      let some rhs ← rhs.toVerifiedExprM? coordinate? exponent? | return none
      return some (.add lhs rhs)
  | .mul lhs rhs => do
      let some lhs ← lhs.toVerifiedExprM? coordinate? exponent? | return none
      let some rhs ← rhs.toVerifiedExprM? coordinate? exponent? | return none
      return some (.mul lhs rhs)
  | .sub lhs rhs => do
      let some lhs ← lhs.toVerifiedExprM? coordinate? exponent? | return none
      let some rhs ← rhs.toVerifiedExprM? coordinate? exponent? | return none
      return some (.sub lhs rhs)
  | .div lhs rhs => do
      let some lhs ← lhs.toVerifiedExprM? coordinate? exponent? | return none
      let some rhs ← rhs.toVerifiedExprM? coordinate? exponent? | return none
      return some (.div lhs rhs)
  | .neg arg => do
      let some arg ← arg.toVerifiedExprM? coordinate? exponent? | return none
      return some (.neg arg)
  | .pow base exponent => do
      let some base ← base.toVerifiedExprM? coordinate? exponent? | return none
      let some exponent ← exponent? exponent | return none
      return some (.pow base exponent)
  | .unary operation arg => do
      let some arg ← arg.toVerifiedExprM? coordinate? exponent? | return none
      return some (operation.apply arg)
  | .apply function arg => do
      let some arg ← arg.toVerifiedExprM? coordinate? exponent? | return none
      return some (function.desugar arg)
  | .rpow base power => do
      let some base ← base.toVerifiedExprM? coordinate? exponent? | return none
      let some power ← power.toVerifiedExprM? coordinate? exponent? | return none
      return some (.rpow base power)

/-- The decimal literal `m.dE±e` with mantissa `mantissa` and power of ten `exponent`, negative
when `negativeExponent`, as an exact constant: `.nat` when its value is a natural number, and
otherwise `.rat` of the reduced fraction. -/
def decimalLiteral {ι κ : Type*} (mantissa : Nat) (negativeExponent : Bool) (exponent : Nat) :
    ReflectedExpr ι κ :=
  if negativeExponent then
    let value := mkRat mantissa (10 ^ exponent)
    if value.den = 1 then .nat value.num.toNat else .rat value.num value.den
  else
    .nat (mantissa * 10 ^ exponent)

end ReflectedExpr

/-- Largest power of ten a decimal literal may carry, so that reading `1e100000000` as an exact
rational cannot allocate an enormous numeral before any query budget is checked. -/
def maxDecimalExponent : Nat := 1000

/-- Refuse a decimal literal whose power of ten exceeds `maxDecimalExponent`, at `stx`. -/
def checkDecimalExponent {m : Type → Type} [Monad m] [Lean.MonadError m]
    (stx : Lean.Syntax) (exponent : Nat) : m Unit := do
  if maxDecimalExponent < exponent then
    Lean.throwErrorAt stx m!"the decimal literal has a power of ten {exponent}, over the limit \
      {maxDecimalExponent}; write it as an exact rational"

end CAS.Elaboration.RealExpression

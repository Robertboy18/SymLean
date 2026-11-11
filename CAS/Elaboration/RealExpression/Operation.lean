/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Syntax

/-!
# Unary operations in elaborated real expressions

The unary operations shared by the real-expression elaborators: for each, the
accepted source spellings, the elaborated Lean constant, the checked-expression
constructor, and the quotation name. The functions without a constructor of
their own, `|a|`, `tan`, `sinh`, `cosh` and `tanh`, are a second table,
`DesugaredFunction`: for each, its spellings, its Mathlib constant, the form in
the checked language that the parsers write for it, and the Mathlib lemmas
rewriting the function to that form. `DesugaredFunction.match?` reads such a form back, so that
a statement can name the function the user wrote. Nothing here depends on a particular command
or tactic.
-/

@[expose] public section

namespace CAS.Elaboration.RealExpression

open Lean

/-- Unary real operations represented by the checked expression language. -/
inductive UnaryOperation where
  | sin
  | cos
  | atan
  | asin
  | acos
  | exp
  | log
  | sqrt
deriving DecidableEq, Repr

namespace UnaryOperation

/-- Recognize a supported surface spelling. -/
def ofSurfaceName? : Name → Option UnaryOperation
  | `sin | `Real.sin => some .sin
  | `cos | `Real.cos => some .cos
  | `atan | `arctan | `Real.arctan => some .atan
  | `asin | `arcsin | `Real.arcsin => some .asin
  | `acos | `arccos | `Real.arccos => some .acos
  | `exp | `Real.exp => some .exp
  | `log | `Real.log => some .log
  | `sqrt | `Real.sqrt => some .sqrt
  | _ => none

/-- Recognize the head constant of an elaborated unary application. -/
def ofConstantName? : Name → Option UnaryOperation
  | ``Real.sin => some .sin
  | ``Real.cos => some .cos
  | ``Real.arctan => some .atan
  | ``Real.arcsin => some .asin
  | ``Real.arccos => some .acos
  | ``Real.exp => some .exp
  | ``Real.log => some .log
  | ``Real.sqrt => some .sqrt
  | _ => none

/-- Apply an operation in the checked expression language. -/
def apply {ι : Type*} : UnaryOperation → Verified.Expr ι → Verified.Expr ι
  | .sin => .sin
  | .cos => .cos
  | .atan => .atan
  | .asin => .asin
  | .acos => .acos
  | .exp => .exp
  | .log => .log
  | .sqrt => .sqrt

/-- Constructor name used when quoting a checked expression. -/
def constructorName : UnaryOperation → Name
  | .sin => ``Verified.Expr.sin
  | .cos => ``Verified.Expr.cos
  | .atan => ``Verified.Expr.atan
  | .asin => ``Verified.Expr.asin
  | .acos => ``Verified.Expr.acos
  | .exp => ``Verified.Expr.exp
  | .log => ``Verified.Expr.log
  | .sqrt => ``Verified.Expr.sqrt

end UnaryOperation

/-- The real functions that the parsers write in the checked language through other operations,
since the language has no constructor for them. -/
inductive DesugaredFunction where
  /-- `|a|`, written `√(a ^ 2)`. -/
  | abs
  /-- `tan a`, written `sin a / cos a`. -/
  | tan
  /-- `sinh a`, written `(exp a - exp (-a)) / 2`. -/
  | sinh
  /-- `cosh a`, written `(exp a + exp (-a)) / 2`. -/
  | cosh
  /-- `tanh a`, written as the quotient of the forms of `sinh a` and `cosh a`. -/
  | tanh
deriving DecidableEq, Repr

namespace DesugaredFunction

/-- Recognize a supported surface spelling. -/
def ofSurfaceName? : Name → Option DesugaredFunction
  | `abs => some .abs
  | `tan | `Real.tan => some .tan
  | `sinh | `Real.sinh => some .sinh
  | `cosh | `Real.cosh => some .cosh
  | `tanh | `Real.tanh => some .tanh
  | _ => none

/-- Recognize the head constant of an elaborated application. -/
def ofConstantName? : Name → Option DesugaredFunction
  | ``_root_.abs => some .abs
  | ``Real.tan => some .tan
  | ``Real.sinh => some .sinh
  | ``Real.cosh => some .cosh
  | ``Real.tanh => some .tanh
  | _ => none

/-- The Mathlib constant of the function. -/
def constantName : DesugaredFunction → Name
  | .abs => ``_root_.abs
  | .tan => ``Real.tan
  | .sinh => ``Real.sinh
  | .cosh => ``Real.cosh
  | .tanh => ``Real.tanh

/-- The functions of the table. -/
def all : List DesugaredFunction := [.abs, .tan, .sinh, .cosh, .tanh]

/-- The Mathlib lemmas identifying the function with the operations of `desugar` and of the forms
that `match?` reads, up to the casts of the numerals: `√(a ^ 2) = |a|` and `√(a * a) = |a|`,
`tan a = sin a / cos a`, `sinh a = (exp a - exp (-a)) / 2`, `cosh a = (exp a + exp (-a)) / 2`,
`tanh a = sinh a / cosh a` and `tanh a = (exp a - exp (-a)) / (exp a + exp (-a))`. -/
def rewriteLemmas : DesugaredFunction → List Name
  | .abs => [``Real.sqrt_sq_eq_abs, ``Real.sqrt_mul_self_eq_abs]
  | .tan => [``Real.tan_eq_sin_div_cos]
  | .sinh => [``Real.sinh_eq]
  | .cosh => [``Real.cosh_eq]
  | .tanh => [``Real.tanh_eq_sinh_div_cosh, ``Real.tanh_eq]

/-- The name of the function in the calculator's output. -/
def displayName : DesugaredFunction → String
  | .abs => "abs"
  | .tan => "tan"
  | .sinh => "sinh"
  | .cosh => "cosh"
  | .tanh => "tanh"

/-- The function applied to `a` in the checked language. -/
def desugar {ι : Type*} : DesugaredFunction → Verified.Expr ι → Verified.Expr ι
  | .abs, a => .sqrt (.pow a 2)
  | .tan, a => .div (.sin a) (.cos a)
  | .sinh, a => .div (.sub (.exp a) (.exp (.neg a))) (.nat 2)
  | .cosh, a => .div (.add (.exp a) (.exp (.neg a))) (.nat 2)
  | .tanh, a => .div (.div (.sub (.exp a) (.exp (.neg a))) (.nat 2))
      (.div (.add (.exp a) (.exp (.neg a))) (.nat 2))

/-- The argument `a` when the expression is a form of `sinh a` in the checked language:
`(exp a - exp (-a)) / 2`, `1/2*(exp a + -exp (-a))` or `1/2*(exp a - exp (-a))`. -/
def sinhArgument? {ι : Type*} [DecidableEq ι] :
    Verified.Expr ι → Option (Verified.Expr ι)
  | .div (.sub (.exp a) (.exp (.neg b))) (.nat 2)
  | .mul (.rat 1 2) (.add (.exp a) (.neg (.exp (.neg b))))
  | .mul (.rat 1 2) (.sub (.exp a) (.exp (.neg b))) => if a = b then some a else none
  | _ => none

/-- The argument `a` when the expression is a form of `cosh a` in the checked language:
`(exp a + exp (-a)) / 2` or `1/2*(exp a + exp (-a))`. -/
def coshArgument? {ι : Type*} [DecidableEq ι] :
    Verified.Expr ι → Option (Verified.Expr ι)
  | .div (.add (.exp a) (.exp (.neg b))) (.nat 2)
  | .mul (.rat 1 2) (.add (.exp a) (.exp (.neg b))) => if a = b then some a else none
  | _ => none

/-- The function and its argument when `expr` is the form of `desugar`, or a form of it that the
display normal form or the simplifier writes (`√(a * a)`, `1/2*(exp a - exp (-a))`, the quotient
of such forms of `sinh a` and `cosh a`, and `(exp a - exp (-a)) / (exp a + exp (-a))`), each equal
to the function by its `rewriteLemmas` and ring arithmetic. -/
def match? {ι : Type*} [DecidableEq ι] (expr : Verified.Expr ι) :
    Option (DesugaredFunction × Verified.Expr ι) :=
  let hyperbolic : Option (DesugaredFunction × Verified.Expr ι) :=
    match sinhArgument? expr, coshArgument? expr with
    | some a, _ => some (.sinh, a)
    | _, some a => some (.cosh, a)
    | _, _ => none
  match expr with
  | .sqrt (.pow a 2) => some (.abs, a)
  | .sqrt (.mul a b) => if a = b then some (.abs, a) else none
  | .div (.sin a) (.cos b) => if a = b then some (.tan, a) else none
  | .div (.sub (.exp a) (.exp (.neg b))) (.add (.exp c) (.exp (.neg d))) =>
      if a = b ∧ a = c ∧ a = d then some (.tanh, a) else none
  | .div numerator denominator =>
      match sinhArgument? numerator, coshArgument? denominator with
      | some a, some b => if a = b then some (.tanh, a) else hyperbolic
      | _, _ => hyperbolic
  | _ => hyperbolic

/-- `match?` for the functions of `functions` only. The statements and the display lines of a
report read their expressions with the functions that the input applies, so that they name a
function only when the input applies it somewhere. -/
def matchAmong? {ι : Type*} [DecidableEq ι] (functions : List DesugaredFunction)
    (expr : Verified.Expr ι) : Option (DesugaredFunction × Verified.Expr ι) :=
  (match? expr).filter fun (function, _) ↦ function ∈ functions

end DesugaredFunction

end CAS.Elaboration.RealExpression

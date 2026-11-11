/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Syntax

/-!
# Rendering verified expressions

Human-readable rendering for the reflected expression language. Variable names are presentation
metadata only: evaluation and certificate soundness use the typed variable index carried by the
syntax tree.

For conventional display, a caller can first apply `displayNormalForm`. It
flattens sums and differences, writes `a * a` as `a ^ 2`, and moves a leading minus
sign out of a quotient and out of a later term of a sum. `renderWith` prints the
supplied tree with the usual precedence of `+`, `*`, unary minus and `^`,
inserting parentheses where needed.
It does not apply `displayNormalForm`; neither do `render`, `ToString`, or `Repr`.
The normalization changes syntax for display alone; no soundness theorem depends
on it.

## Main definitions

* `VarNames`: a class supplying display names for a variable type, with the default
  Euclidean names `x, y, z, w, x4, …` for `Fin n` and identity for `String`.
* `displayNormalForm`: presentation-only normalization.
* `renderWith`, `render`: precedence-aware string rendering, also exposed through the
  `ToString` and `Repr` instances on `Verified.Expr ι`.
-/

@[expose] public section

namespace CAS

namespace Verified.Expr

/-- Variable-name provider used by the symbolic pretty-printer. -/
class VarNames (ι : Type*) where
  /-- Return the display name for a symbolic variable. -/
  name : ι → String

/-- String-indexed variables display as themselves. -/
instance : VarNames String where
  name := id

/-- Default coordinate names for Euclidean symbolic expressions. -/
instance {n : Nat} : VarNames (Fin n) where
  name i :=
    match i.val with
    | 0 => "x"
    | 1 => "y"
    | 2 => "z"
    | 3 => "w"
    | k => "x" ++ toString k

/-- Wrap `s` in parentheses when `needsParens` is `true`; otherwise return `s` unchanged. -/
def parenIf (needsParens : Bool) (s : String) : String :=
  if needsParens then "(" ++ s ++ ")" else s

/-- Collect the signed terms of an already display-normalized additive expression. -/
def signedDisplayTerms {ι : Type*} (negative : Bool) :
    Verified.Expr ι → List (Bool × Verified.Expr ι)
  | .add left right =>
      signedDisplayTerms negative left ++ signedDisplayTerms negative right
  | .sub left right =>
      signedDisplayTerms negative left ++ signedDisplayTerms (!negative) right
  | .neg arg => signedDisplayTerms (!negative) arg
  | .int (.negSucc n) => [(!negative, .nat (n + 1))]
  | .rat (.negSucc n) den => [(!negative, .rat (.ofNat (n + 1)) den)]
  | expr => [(negative, expr)]

/-- Separate a displayed leading minus sign from its unsigned expression. -/
def splitDisplaySign {ι : Type*} :
    Verified.Expr ι → Bool × Verified.Expr ι
  | .neg a => (true, a)
  | .int (.negSucc n) => (true, .nat (n + 1))
  | .rat (.negSucc n) den => (true, .rat (.ofNat (n + 1)) den)
  | a => (false, a)

/-- Separate a displayed leading minus sign from a term, also when it leads the left factor of a
product or the numerator of a quotient: `-2*x` gives `2*x` with the sign. -/
def splitLeadingSign {ι : Type*} : Verified.Expr ι → Bool × Verified.Expr ι
  | .mul a b =>
      match splitLeadingSign a with
      | (true, a') => (true, .mul a' b)
      | (false, _) => (false, .mul a b)
  | .div a b =>
      match splitLeadingSign a with
      | (true, a') => (true, .div a' b)
      | (false, _) => (false, .div a b)
  | a => splitDisplaySign a

/-- Rebuild signed terms as a left-associated conventional sum or difference. A later term with
a leading minus sign, such as `-2*x`, is subtracted without it, so that no `+ -` is displayed. -/
def rebuildDisplaySum {ι : Type*} :
    List (Bool × Verified.Expr ι) → Verified.Expr ι
  | [] => .nat 0
  | (negative, first) :: rest =>
      rest.foldl
        (fun sum signedTerm ↦
          let (leading, term) := splitLeadingSign signedTerm.2
          if signedTerm.1 != leading then .sub sum term else .add sum term)
        (if negative then .neg first else first)

/--
Normalize an expression for conventional mathematical display.

This function is presentation-only: certificate generation, evaluation, and
proof reconstruction continue to use the original expression. It flattens
additive normal forms into conventional sums and differences and writes a
repeated product as a square.
-/
def displayNormalForm {ι : Type*} [DecidableEq ι] : Verified.Expr ι → Verified.Expr ι
  | .nat k => .nat k
  | .int k => .int k
  | .rat num den => .rat num den
  | .pi => .pi
  | .e => .e
  | .var i => .var i
  | .add a b =>
      let a' := displayNormalForm a
      let b' := displayNormalForm b
      rebuildDisplaySum (signedDisplayTerms false a' ++ signedDisplayTerms false b')
  | .mul a b =>
      let a' := displayNormalForm a
      let b' := displayNormalForm b
      if a' = b' then .pow a' 2 else .mul a' b'
  | .sub a b =>
      let a' := displayNormalForm a
      let b' := displayNormalForm b
      rebuildDisplaySum (signedDisplayTerms false a' ++ signedDisplayTerms true b')
  | .div a b =>
      let (negativeA, a') := splitDisplaySign (displayNormalForm a)
      let (negativeB, b') := splitDisplaySign (displayNormalForm b)
      let quotient := Verified.Expr.div a' b'
      if negativeA != negativeB then .neg quotient else quotient
  | .neg a =>
      let (negative, a') := splitDisplaySign (displayNormalForm a)
      if negative then a' else .neg a'
  | .pow a k => .pow (displayNormalForm a) k
  | .sin a => .sin (displayNormalForm a)
  | .cos a => .cos (displayNormalForm a)
  | .atan a => .atan (displayNormalForm a)
  | .asin a => .asin (displayNormalForm a)
  | .acos a => .acos (displayNormalForm a)
  | .exp a => .exp (displayNormalForm a)
  | .log a => .log (displayNormalForm a)
  | .sqrt a => .sqrt (displayNormalForm a)
  | .rpow a b => .rpow (displayNormalForm a) (displayNormalForm b)

/-- Binding precedence of an expression's head symbol for rendering: sums and differences bind
weakest, then products, quotients, and rational literals, then negation and negative integer
literals, then powers; every other expression is atomic and binds tightest. -/
def precedence {ι : Type*} : Verified.Expr ι → Nat
  | .add _ _ | .sub _ _ => 50
  | .mul _ _ | .div _ _ | .rat _ _ => 60
  | .neg _ | .int (.negSucc _) => 70
  | .pow _ _ => 80
  | .rpow _ _ => 80
  | _ => 100

/-- Internal precedence-aware worker for `renderWith`. -/
def renderWithAux {ι : Type*}
    (varName : ι → String) (expression : Verified.Expr ι) (context : Nat) : String :=
  let rendered :=
    match expression with
    | .nat k => toString k
    | .int k => toString k
    | .rat num den => toString num ++ "/" ++ toString den
    | .pi => "pi"
    | .e => "e"
    | .var i => varName i
    | .add a b => renderWithAux varName a 50 ++ " + " ++ renderWithAux varName b 50
    | .mul a b => renderWithAux varName a 60 ++ "*" ++ renderWithAux varName b 60
    | .sub a b => renderWithAux varName a 50 ++ " - " ++ renderWithAux varName b 51
    | .div a b => renderWithAux varName a 60 ++ "/" ++ renderWithAux varName b 61
    | .neg a => "-" ++ renderWithAux varName a 71
    | .pow a k => renderWithAux varName a 81 ++ "^" ++ toString k
    | .sin a => "sin(" ++ renderWithAux varName a 0 ++ ")"
    | .cos a => "cos(" ++ renderWithAux varName a 0 ++ ")"
    | .atan a => "atan(" ++ renderWithAux varName a 0 ++ ")"
    | .asin a => "asin(" ++ renderWithAux varName a 0 ++ ")"
    | .acos a => "acos(" ++ renderWithAux varName a 0 ++ ")"
    | .exp a => "exp(" ++ renderWithAux varName a 0 ++ ")"
    | .log a => "log(" ++ renderWithAux varName a 0 ++ ")"
    | .sqrt a => "sqrt(" ++ renderWithAux varName a 0 ++ ")"
    | .rpow a b => renderWithAux varName a 81 ++ "^" ++ renderWithAux varName b 81
  parenIf (decide (precedence expression < context)) rendered

/-- Render a symbolic expression using a custom variable-name function. -/
def renderWith {ι : Type*} (varName : ι → String) (expr : Verified.Expr ι) : String :=
  renderWithAux varName expr 0

/-- Render a symbolic expression with the default names for its variable type. -/
def render {ι : Type*} [VarNames ι] (expr : Verified.Expr ι) : String :=
  renderWith VarNames.name expr

/-- `ToString` for symbolic expressions: `render`, with the default variable names of `ι`. -/
instance {ι : Type*} [VarNames ι] : ToString (Verified.Expr ι) where
  toString := render

/-- `Repr` for symbolic expressions: the text of `render` at every precedence, with the default
variable names of `ι`. -/
instance {ι : Type*} [VarNames ι] : Repr (Verified.Expr ι) where
  reprPrec expr _ := Std.Format.text (render expr)

end Verified.Expr

end CAS

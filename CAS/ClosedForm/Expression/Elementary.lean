/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.NamedVariables -- shake: keep

/-!
# Elementary symbolic functions

The namespace `Verified.Expr.Sym` writes the elementary functions that are not constructors of
`Verified.Expr`, and the Gaussian profile, as expressions in its core. Each one unfolds to the
verified expression language, so differentiation and evaluation use the soundness theorems of
that language rather than an external function table.

The core of `Verified.Expr` has arithmetic, `sin`, `cos`, `atan`, `asin`, `acos`, `exp`, `log`,
`sqrt`, and the real power `rpow`. Everything here is an encoding in that core: `tan = sin / cos`,
`abs x = sqrt (x^2)`, the hyperbolic functions through `exp`, `max` and `min` through `abs`. The
price of an encoding is that its validity conditions (for evaluation to match the intended
function, and for the symbolic derivative to be the true derivative) are those of the encoding,
not of the named function. The docstrings of `abs`, `max`, and `min` record the result: the
symbolic derivative of `abs x` is certified only where `x ≠ 0`, and those of `max a b` and
`min a b` only where `a ≠ b`. The quotients `tan`, `sec`, `tanh`, and `sech` require their
denominators to be nonzero.

## Main definitions

All names in this list live in the namespace `Verified.Expr.Sym`.

* `tan`, `sec`: trigonometric encodings.
* `sinh`, `cosh`, `tanh`, `sech`: hyperbolic encodings.
* `abs`, `max`, `min`: the absolute value and the order operations.
* `Special.gaussian`: the Gaussian profile `exp (-(x ^ 2))`.
-/

@[expose] public section

namespace CAS

open scoped BigOperators

namespace Verified.Expr

namespace Sym

/-- Symbolic absolute value, represented as `sqrt(x^2)`.

The derivative certificate uses the existing `sqrt` rule, so classical derivative claims inherit
the corresponding `ValidAt` condition, namely that the inner square is strictly positive.  For
`abs x`, this means away from `x = 0`. -/
def abs {ι : Type*} (expr : Verified.Expr ι) : Verified.Expr ι :=
  .sqrt (expr ^ 2)

/-- Symbolic tangent, represented as `sin(x) / cos(x)`. -/
def tan {ι : Type*} (expr : Verified.Expr ι) : Verified.Expr ι :=
  .sin expr / .cos expr

/-- Symbolic secant, represented as `1 / cos(x)`. -/
def sec {ι : Type*} (expr : Verified.Expr ι) : Verified.Expr ι :=
  1 / .cos expr

/-- Symbolic hyperbolic sine, represented as `(exp(x) - exp(-x)) / 2`. -/
def sinh {ι : Type*} (expr : Verified.Expr ι) : Verified.Expr ι :=
  (.exp expr - .exp (-expr)) / 2

/-- Symbolic hyperbolic cosine, represented as `(exp(x) + exp(-x)) / 2`. -/
def cosh {ι : Type*} (expr : Verified.Expr ι) : Verified.Expr ι :=
  (.exp expr + .exp (-expr)) / 2

/-- Symbolic hyperbolic tangent, represented as `sinh(x) / cosh(x)`. -/
def tanh {ι : Type*} (expr : Verified.Expr ι) : Verified.Expr ι :=
  sinh expr / cosh expr

/-- Symbolic hyperbolic secant, represented as `1 / cosh(x)`. -/
def sech {ι : Type*} (expr : Verified.Expr ι) : Verified.Expr ι :=
  1 / cosh expr

/-- Symbolic maximum, represented by `(a + b + abs(a - b)) / 2`.

The derivative is valid away from the switching surface `a = b`, inherited from `abs`. -/
def max {ι : Type*} (a b : Verified.Expr ι) : Verified.Expr ι :=
  (a + b + abs (a - b)) / 2

/-- Symbolic minimum, represented by `(a + b - abs(a - b)) / 2`.

The derivative is valid away from the switching surface `a = b`, inherited from `abs`. -/
def min {ι : Type*} (a b : Verified.Expr ι) : Verified.Expr ι :=
  (a + b - abs (a - b)) / 2

/-! ### PDE-oriented encoded special functions

`Special.gaussian` unfolds to `exp`, negation, and a square in the core language, so
differentiation, simplification, and domain reporting reuse the same checked machinery as
ordinary closed forms.
-/

namespace Special

/-- Standard Gaussian profile `exp(-x^2)`. -/
def gaussian {ι : Type*} (x : Verified.Expr ι) : Verified.Expr ι :=
  .exp (-(x ^ 2))

end Special

end Sym

end Verified.Expr

end CAS

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Laplace

/-!
# Input admission for `#cas [ndsolve]`, `#cas [inverseLaplace]` and `#cas [N d] (erf q)`

`checkExpr` refuses an input of these modes whose powers, degrees or constants are too large,
before the exact reader expands it. `boundedRational` reads a closed rational number of the input
with capped arithmetic, and `polyOf?` gives `#cas [ndsolve]` its field as a polynomial computed
without gcds.

## Main definitions

* `CAS.Command.Admission.checkExpr`: the size checks of an expression (powers, degrees,
  constants).
* `CAS.Command.Admission.degreeBounds`, `CAS.Command.Admission.bitBounds`: saturating bounds of
  the degrees and of the bits of the coefficients that the reader builds.
* `CAS.Command.Admission.polyOf?`: the polynomial of an expression with no quotient by an
  expression with a variable.
* `CAS.Command.Admission.boundedRational`: a closed rational number of the input.

## Implementation notes

The rational reader of `CAS.Command.Algebra` expands powers and products of polynomials exactly,
so a short input such as `(1 + y) ^ 1000000` or `2 ^ 1000000000` costs time and memory before any
limit on the result applies. These checks run on the expression read by the shared reader, before
any expansion or rational evaluation, after the syntactic pre-scan of `#cas [laplace]`
(`hasLongAtom`, `hasLargeDecimal`, `inputSize`): every natural power has an exponent of at most
`maxPower`; for every subexpression, also the base of a power `^ 0` (which the reader evaluates),
the degrees of the numerator and of the denominator that the reader builds are at most a given
bound (`degreeBounds`, following `RatFun.add`, `mul`, `div` and `pow`); and the bits of the
coefficients stay below `maxBits` (`bitBounds`: an operation adds the bits of its operands and a
slack for the number of terms, a power multiplies them by the exponent). The bounds saturate, so
the checks are linear in the size of the expression. They bound the expansions of the reader, not
the intermediate results of the gcds with which `RatFun.reduce` normalizes every step: `#cas
[ndsolve]`, whose field is a polynomial in two variables, refuses quotients by expressions with a
variable (`hasQuotient`) and reads the field with `polyOf?`, which has no gcd; for one variable
(`#cas [inverseLaplace]`) the remainder sequence of polynomials of degree at most the cap, made
monic after each step, stays polynomial in the degree and the bits. A closed
rational number (an interval end, an initial value, an output time, the point of `erf`) is
evaluated by `Laplace.ratOf?`, which caps every operand at 1024 bits.
-/

public meta section

namespace CAS.Command.Admission

open Lean Elab Command
open CAS.Command.Laplace
open CAS.Verified.Expr.Alg

/-- The largest exponent of a natural power in an admitted input. -/
def maxPower : Nat := 64

/-- The largest number of bits of the constants of an admitted input. -/
def maxBits : Nat := 4096

/-- Upper bounds `(n, d)` of the total degrees of the numerator and of the denominator of the
rational function that the reader of `CAS.Command.Algebra` builds for an expression, following
its operations (`RatFun.add` multiplies the denominators), saturating at `cap + 1`, and whether
the bounds of every subexpression (also the base of a power `^ 0`, which the reader evaluates)
stay at most `cap`. Other functions count as constants. -/
def degreeBounds {n : Nat} (cap : Nat) : Verified.Expr (Fin n) → Nat × Nat × Bool
  | .var _ => (1, 0, 1 ≤ cap)
  | .add a b | .sub a b =>
      let (na, da, oa) := degreeBounds cap a
      let (nb, db, ob) := degreeBounds cap b
      let num := min (cap + 1) (max (na + db) (nb + da))
      let den := min (cap + 1) (da + db)
      (num, den, oa && ob && num ≤ cap && den ≤ cap)
  | .mul a b =>
      let (na, da, oa) := degreeBounds cap a
      let (nb, db, ob) := degreeBounds cap b
      let num := min (cap + 1) (na + nb)
      let den := min (cap + 1) (da + db)
      (num, den, oa && ob && num ≤ cap && den ≤ cap)
  | .div a b =>
      let (na, da, oa) := degreeBounds cap a
      let (nb, db, ob) := degreeBounds cap b
      let num := min (cap + 1) (na + db)
      let den := min (cap + 1) (da + nb)
      (num, den, oa && ob && num ≤ cap && den ≤ cap)
  | .neg a => degreeBounds cap a
  | .pow a k =>
      let (na, da, oa) := degreeBounds cap a
      let num := min (cap + 1) (na * min k (cap + 1))
      let den := min (cap + 1) (da * min k (cap + 1))
      (num, den, oa && num ≤ cap && den ≤ cap)
  | _ => (0, 0, true)

/-- The slack of `bitBounds` per operation: the bits of the number of terms that a coefficient
of a sum or product of polynomials of the admitted degrees adds up (at most `2 ^ 16` terms). -/
def termBits : Nat := 16

/-- An upper bound of the bits of the numerators and denominators of the coefficients that the
reader builds (an operation adds the bits of its operands and `termBits`, a power multiplies
them), saturating at `maxBits + 1`, and whether the bound of every subexpression stays at most
`maxBits`. -/
def bitBounds {n : Nat} : Verified.Expr (Fin n) → Nat × Bool
  | .nat k => let b := min (maxBits + 1) (k.log2 + 1); (b, b ≤ maxBits)
  | .int k => let b := min (maxBits + 1) (k.natAbs.log2 + 1); (b, b ≤ maxBits)
  | .rat p q => let b := min (maxBits + 1) (p.natAbs.log2 + q.log2 + 2); (b, b ≤ maxBits)
  | .add a b | .sub a b | .mul a b | .div a b =>
      let (ba, oa) := bitBounds a
      let (bb, ob) := bitBounds b
      let r := min (maxBits + 1) (ba + bb + termBits)
      (r, oa && ob && r ≤ maxBits)
  | .neg a => bitBounds a
  | .pow a k =>
      let (ba, oa) := bitBounds a
      let r := min (maxBits + 1) ((ba + termBits) * min k (maxBits + 1))
      (r, oa && r ≤ maxBits)
  | _ => (1, true)

/-- Whether every natural power has an exponent of at most `maxPower`. -/
def powersBounded {n : Nat} : Verified.Expr (Fin n) → Bool
  | .add a b | .sub a b | .mul a b | .div a b | .rpow a b => powersBounded a && powersBounded b
  | .neg a | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a | .sqrt a =>
      powersBounded a
  | .pow a k => k ≤ maxPower && powersBounded a
  | _ => true

/-- Whether an expression mentions a variable. -/
def hasVar {n : Nat} : Verified.Expr (Fin n) → Bool
  | .var _ => true
  | .add a b | .sub a b | .mul a b | .div a b | .rpow a b => hasVar a || hasVar b
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a
  | .sqrt a => hasVar a
  | _ => false

/-- Whether an expression has a quotient by an expression with a variable (a quotient by a
constant, such as a decimal literal, needs no cancellation and no polynomial gcd). -/
def hasQuotient {n : Nat} : Verified.Expr (Fin n) → Bool
  | .div a b => hasVar b || hasQuotient a || hasQuotient b
  | .add a b | .sub a b | .mul a b | .rpow a b => hasQuotient a || hasQuotient b
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a
  | .sqrt a => hasQuotient a
  | _ => false

/-- The polynomial of an expression with no quotient by an expression with a variable, by the
core polynomial arithmetic of `CAS.Polynomial.Sparse` (`mvAdd`, `mvMulPoly`, `mvPowPoly`) without
the gcds with which the rational reader `RatFun.reduce` normalizes every step; a quotient by a
constant divides by its value from `Laplace.ratOf?` (capped). `none` for other functions and for a
divisor with a variable or of value `0`. Under the bounds of `checkExpr` its work is that of the
expansions. -/
def polyOf? {n : Nat} : Verified.Expr (Fin n) → Option (MvPoly n)
  | .nat k => some (Algebra.constPoly n k)
  | .int k => some (Algebra.constPoly n k)
  | .rat p q => if q = 0 then none else some (Algebra.constPoly n ((p : ℚ) / q))
  | .var i => some (Algebra.varPoly i)
  | .add a b => return mvAdd (← polyOf? a) (← polyOf? b)
  | .sub a b => return mvSub (← polyOf? a) (← polyOf? b)
  | .neg a => return mvNeg (← polyOf? a)
  | .mul a b => return mvMulPoly (← polyOf? a) (← polyOf? b)
  | .pow a k => return mvPowPoly (← polyOf? a) k
  | .div a b => do
      let c ← ratOf? b
      if c = 0 then none
      return Algebra.scalePoly (1 / c) (← polyOf? a)
  | _ => none

/-- The syntactic pre-scan of `#cas [laplace]`, with the name of the command in the messages. -/
def prescan (command : String) (stx : Syntax) : CommandElabM Unit := do
  if hasLongAtom stx then
    throwErrorAt stx "{command}: a literal has more than {maxLiteral} characters"
  if hasLargeDecimal stx then
    throwErrorAt stx "{command}: a decimal literal has a power of ten over {maxExponent}"
  if inputSize stx > maxSize then
    throwErrorAt stx "{command}: the input is too large (more than {maxSize} syntax nodes)"

/-- The size checks of an expression read from the input: powers, degrees and constants. -/
def checkExpr {n : Nat} (command : String) (stx : Syntax) (maxDegree : Nat)
    (expr : Verified.Expr (Fin n)) : CommandElabM Unit := do
  unless powersBounded expr do
    throwErrorAt stx "{command}: a power has an exponent over {maxPower}"
  unless (degreeBounds maxDegree expr).2.2 do
    throwErrorAt stx "{command}: the input has degree over {maxDegree} before simplification \
      (in a numerator or a denominator of a subexpression)"
  unless (bitBounds expr).2 do
    throwErrorAt stx "{command}: the constants of the input may need more than {maxBits} bits"

/-- A closed rational number of the input, evaluated with capped arithmetic. -/
def boundedRational (command : String) (stx : Syntax) : CommandElabM ℚ := do
  prescan command stx
  -- The shared reader needs a coordinate; this one is unused, so a free symbol is refused.
  let reified ← try parseExact stx [`_admissionCoordinate] catch _ =>
    throwErrorAt stx "{command}: expected a rational number"
  checkExpr command stx 0 reified.expr
  match ratOf? reified.expr with
  | some q => return q
  | none => throwErrorAt stx "{command}: expected a rational number of at most \
      {Laplace.maxBits} bits"

end CAS.Command.Admission

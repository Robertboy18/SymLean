/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public meta import Lean.Meta.Basic
public meta import Lean.Util.Recognizers

/-!
# Goal shapes of the Mathematica-style commands

`isAlgebraStatement` recognizes, by head symbols alone, the goals whose proofs the `command` route
of bare `cas` builds with the algebra, matrix and number theory commands
(`CAS.Command.AlgebraGoals`): equalities with a side headed by `gcd`, `lcm`, `Polynomial.coeff`,
`Polynomial.natDegree`, `Inv.inv`, `Matrix.rank`, `Matrix.charpoly`, `Matrix.transpose`,
`Matrix.trace`, `Matrix.mulVec`, `Real.Gamma`, `jacobiSym`, a finite sum or product, a modular
power `a ^ b % m`, or a quotient or remainder `p / q`, `p % q` of polynomials, also under
universal quantifiers. `ExactTactic` tries that route for these shapes in its `algebraStatement`
stage, after the determinant stage and the routes of higher priority but before its arithmetic
routes would expand, for example, a modular power with a huge exponent. A refutation by that
route (`refutedTag`) ends the search.
-/

public meta section

namespace CAS.Tactic.CommandShapes

open Lean Meta

/-- The heads of equality sides that the algebra route treats. -/
def algebraHeads : List Name :=
  [`GCDMonoid.gcd, `GCDMonoid.lcm, `Polynomial.coeff, `Polynomial.natDegree, `Inv.inv,
   `Matrix.rank, `Matrix.charpoly, `Matrix.transpose, `Matrix.trace, `Matrix.mulVec,
   `Finset.sum, `Finset.prod, `Real.Gamma, `jacobiSym]

/-- Whether `e` is `a ^ b % m`. -/
def isModularPower (e : Expr) : Bool :=
  e.isAppOfArity `HMod.hMod 6 && (e.getArg! 4).consumeMData.isAppOfArity `HPow.hPow 6

/-- Whether `e` is `p.coeff n`, which elaborates to a coercion of `Polynomial.coeff p`. -/
def isPolynomialCoeff (e : Expr) : Bool :=
  e.isAppOfArity `DFunLike.coe 6 && (e.getArg! 4).consumeMData.isAppOf `Polynomial.coeff

/-- Whether `e` is `p / q` or `p % q` in a polynomial ring. -/
def isPolynomialDivision (e : Expr) : Bool :=
  (e.isAppOfArity `HDiv.hDiv 6 || e.isAppOfArity `HMod.hMod 6) &&
    (e.getArg! 0).consumeMData.isAppOf `Polynomial

/-- Whether `e`, a side of an equality, is headed by one of `algebraHeads` (under binders of a
universally quantified statement). -/
def isAlgebraSide (e : Expr) : Bool :=
  let e := e.consumeMData
  algebraHeads.any (e.isAppOf ·) || isModularPower e || isPolynomialCoeff e ||
    isPolynomialDivision e

/-- Whether the proposition is a goal of the algebra route: an equation with a side headed by
one of `algebraHeads`, or such an equation under universal quantifiers (the finite sums and
products over `Finset.range (n + c)` or `Finset.Icc 1 n`). -/
partial def isAlgebraStatement (target : Expr) : Bool :=
  let target := target.consumeMData
  if let .forallE _ _ body _ := target then
    isAlgebraStatement body
  else match target.eq? with
    | some (_, lhs, rhs) => isAlgebraSide lhs || isAlgebraSide rhs
    | none => false

/-- The tag of a refutation by the algebra route: the goal is in its fragment and the computed
value differs from the stated one, so no other route is tried. -/
def refutedTag : Name := `CAS.Command.AlgebraGoals.refuted

/-- Whether an exception is a refutation by the algebra route (see `refutedTag`). -/
def isRefutation : Exception → Bool
  | .error _ (.tagged tag _) => tag == refutedTag
  | _ => false

end CAS.Tactic.CommandShapes

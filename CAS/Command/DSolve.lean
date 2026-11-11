/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.DSolveOrder
public import CAS.Command.DSolveRoot
public import CAS.Command.DSolveParam
public import CAS.Command.RootSplit
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Linear differential equations: `#cas [dsolve y x]`

`#cas [dsolve y x] (y'' + p * y' + q * y = f)` solves a linear equation in `y` of the variable
`x` and proves that the displayed family is exactly the set of solutions. `dispatch` reads the
equation, takes its order from the derivatives `y'`, `y''`, … that it mentions, and passes it to
one of three routes.

* Rational constant coefficients, of any order, with a right side made of terms
  `xᵏ e ^ (a x) cos (b x)` and `xᵏ e ^ (a x) sin (b x)`: `CAS.Command.RootSplit` splits the
  characteristic polynomial; `CAS.Command.DSolveOrder` gives the general solution, or the single
  solution of an initial-value problem, when every root is known exactly, and
  `CAS.Command.DSolveRoot` the general solution when some roots are known only by enclosures.
* A first-order equation `y' + p(x) y = q(x)` with a coefficient depending on `x`: the
  integrating factor of `CAS.Command.DSolveOrder`.
* A first-order equation whose coefficients mention parameters: `CAS.Command.DSolveParam`.

## Implementation notes

`dispatch` only chooses the route. It reads `lhs - rhs` as an expression `E` in `x`, `y`, `y'`,
…, takes the coefficient of `y⁽ᵏ⁾` to be the partial derivative of `E` in that variable
(`Verified.Expr.diff`, then `Verified.Expr.simplify`), and calls the equation linear when no
coefficient mentions `y` or its derivatives; the leading coefficient must be a nonzero rational
constant. Identifiers other than `x`, `y`, its derivatives and the names of functions and
constants are parameters (`DSolveParam.parameters`) and send the equation to
`DSolveParam.logParam`. The coefficients that `dispatch` reads are not trusted: each route proves
that the equation as written is equivalent to the normal form of its theorem with these
coefficients (`simp`, `push_cast`, `linear_combination`). The theorems are in
`CAS/Calculus/LinearODEOrder.lean`, `CAS/Calculus/LinearODERoots.lean` and
`CAS/Calculus/LinearODEVariable.lean`. Initial values are refused when some roots are known only
by enclosures.
-/

public meta section

namespace CAS.Command.DSolve

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.SpecialFunctions
open CAS.Command.RootSplit
open CAS.Command.ExpPolynomials
open CAS.Verified.Expr

/-- Run `#cas [dsolve y x, conditions] equation`: read the order and the coefficients of the
equation and pass it to `DSolveParam.logParam`, `DSolveOrder.logOrder`, `DSolveRoot.logRoot` or
`DSolveOrder.logVariable`. -/
def dispatch (ref : Syntax) (y x : TSyntax `ident) (conditions : Array (TSyntax `term))
    (input : Syntax) : CommandElabM Unit := do
  let (lhs, rhs) ← match unparen input with
    | `($l:term = $r:term) => pure (l, r)
    | _ => throwErrorAt input "dsolve: expected an equation lhs = rhs"
  let yName := y.getId
  let ids := ExpPolynomials.identifiers input
  let longest := ids.foldl (fun m n ↦ max m (n.toString (escape := false)).length) 0
  let order := (List.range (longest + 1)).foldl (fun acc k ↦
    if k ≥ 1 && ids.contains (DSolveOrder.primed yName k) then k else acc) 0
  if order = 0 then throwErrorAt input "dsolve: the equation has no derivative of {yName}"
  if !(DSolveParam.parameters yName x.getId order input).isEmpty then
    DSolveParam.logParam ref y x conditions input order
    return
  let names := x.getId :: (List.range (order + 1)).map (DSolveOrder.primed yName)
  let reified ← parseExact (← `($lhs - $rhs)) names
  let N := reified.names.length
  let E := reified.expr
  let isConstant (c : Verified.Expr (Fin N)) : Bool :=
    !(List.finRange N).any (fun i ↦ c.containsVar i)
  let linear (c : Verified.Expr (Fin N)) : Bool :=
    !(List.finRange N).any (fun i ↦ i.val ≠ 0 && c.containsVar i)
  let mut coefficients : Array (Verified.Expr (Fin N)) := #[]
  for k in [0:order + 1] do
    let some c := (if h : k + 1 < N then some (Verified.Expr.simplify (E.diff ⟨k + 1, h⟩))
      else none) | throwErrorAt input "dsolve: the equation could not be read"
    unless linear c do
      throwErrorAt input "dsolve: the equation is not linear in {yName} and its derivatives"
    coefficients := coefficients.push c
  let top := coefficients.getD order (.nat 0)
  let some topValue := (if isConstant top then exactValue? (fun _ ↦ (0 : ℚ)) top else none)
    | throwErrorAt input "dsolve: the leading coefficient must be a rational constant"
  if topValue = 0 then throwErrorAt input "dsolve: the leading coefficient vanishes"
  let constants := coefficients.map fun c ↦
    if isConstant c then exactValue? (fun _ ↦ (0 : ℚ)) c else none
  if constants.all (·.isSome) then
    let cs := constants.map (·.getD 0)
    match ← RootSplit.rootsHere cs with
    | .error msg => throwErrorAt input "dsolve: {msg}"
    | .ok roots =>
      if roots.split.enclosed.isEmpty then
        DSolveOrder.logOrder ref y x conditions input order E cs roots.split.exact roots.prec
      else
        unless conditions.isEmpty do
          throwErrorAt input "dsolve: initial values are not treated when some characteristic \
            roots are known only by enclosures"
        DSolveRoot.logRoot ref y x input order E cs roots
  else if order = 1 then
    let toX : Verified.Expr (Fin N) → Verified.Expr (Fin 1) := fun c ↦ c.mapVars fun i ↦
      if i.val = 0 then (.var 0 : Verified.Expr (Fin 1)) else .nat 0
    DSolveOrder.logVariable ref y x conditions input E topValue
      (toX (coefficients.getD 0 (.nat 0)))
  else
    let k := (List.range (order + 1)).find? (fun k ↦ (constants.getD k none).isNone) |>.getD 0
    throwErrorAt input "dsolve: the coefficient of the derivative of order {k} is not a \
      rational constant"

end CAS.Command.DSolve

namespace CAS.Command

open Lean Elab Command

/-- `#cas [dsolve y x] eq` solves the linear differential equation `eq` for the function `y` of `x`,
and `#cas [dsolve y x, y 0 = v₀, y' 0 = v₁, …] eq` gives the solution of the initial-value
problem.

## Theorem
For an equation of order `n` and the printed family `F`, the report proves that `F` is exactly
the set of solutions: for every `y : ℝ → ℝ` with `∀ k < n, Differentiable ℝ (iteratedDeriv k y)`,
`(∀ x, eq) ↔ ∃ c₁ … cₙ, ∀ x, y x = F`, where `eq` is written with `deriv y x` and
`iteratedDeriv k y x`. With initial values the equivalence is
`(∀ x, eq) ∧ y 0 = v₀ ∧ deriv y 0 = v₁ ↔ ∀ x, y x = Y` for the single solution `Y`.

## Conditions and limits
The equation is linear in `y` and its derivatives `y'`, `y''` and so on. With rational constant
coefficients it may have any order, and its right side is a sum of terms
`x ^ k * exp (a * x) * cos (b * x)` and `x ^ k * exp (a * x) * sin (b * x)`. The characteristic
roots are rational, roots of rational quadratic factors, roots of the factors that Hex finds when
`CASHex.Factor` is imported, or named by certified enclosures; with enclosed roots only the
general solution is given. A first-order equation `y' + p * y = q` whose coefficients depend on
`x` is solved by an integrating factor when the checked integrator finds both primitives without
domain conditions, and first-order equations may have parameters. The initial values are given
at one point.

## Options
None.

## Examples
```lean
#cas [dsolve y x] (y'' + y = 0)
```
```output
Output (order 2, characteristic roots: ±i): y(x) = c₁*cos(x) + c₂*sin(x)
```
```lean
#cas [dsolve y x] (y' + 2*y = x)
```
```output
Output (order 1, characteristic roots: -2): y(x) = -(1/4) + 1/2*x + c₁*exp(-(2*x))
```
```lean
#cas [dsolve y x, y 0 = 1, y' 0 = 0] (y'' + y = 0)
```
```output
Output (order 2, characteristic roots: ±i): y(x) = cos(x)
```

## In a proof
```lean
theorem dsolve_solution (c₁ x : ℝ) :
    HasDerivAt (fun x ↦ -(1 / 4) + 1 / 2 * x + c₁ * Real.exp (-(2 * x)))
      (x - 2 * (-(1 / 4) + 1 / 2 * x + c₁ * Real.exp (-(2 * x)))) x := by
  cas
```
The tactic `cas` does not prove the equivalence of `dsolve`; it proves that a member of the
printed family satisfies `y' = x - 2 * y`, as here.

## See also
Mathematica `DSolve`, SymPy `dsolve`. Hex `Hex.ZPoly.factorize` (through `CASHex.Factor`)
splits the characteristic polynomial. The modes `ndsolve`, `laplace`, `rsolve` and `derive`.
Oracle route: `#cas [dsolve y x, oracle := sympy] eq`, which proves that the oracle's family
solves the equation, while its completeness is the oracle's claim.

## Possible issues
```lean
#cas [dsolve y x] (y' * y = 1)
```
```output
dsolve: the equation is not linear in y and its derivatives
```
The oracle route checks a family that SymPy or Sage proposes for a nonlinear equation.
```lean
#cas [dsolve y x] (z'' + z = 0)
```
```output
dsolve: the equation has no derivative of y
```
Name the unknown function of the equation: `#cas [dsolve z x]`.
```lean
#cas [dsolve y x, y 0 = 1, y 1 = 2] (y'' + y = 0)
```
```output
dsolve: the initial values must be given at one point
```
Boundary-value problems are not solved; fit the constants of the general solution instead.
-/
syntax (name := casDSolveCommand) "#cas" "[" &"dsolve" ident ident (", " term)* "]" term :
  command

elab_rules : command
  | `(#cas [dsolve $y:ident $x:ident $[, $conditions]*] $equation:term) =>
      DSolve.dispatch equation y x conditions equation

end CAS.Command

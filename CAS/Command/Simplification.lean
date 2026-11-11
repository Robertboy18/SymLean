/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Common
public import CAS.Command.Headline
public import CAS.ClosedForm.Pipeline.Configured

/-!
# Exact simplification reports for `#cas`

The command `#cas [simplify] e` runs the side-conditioned exact simplification route
`simplifyFinDisplayRoute` on `e`, validates its semantic theorem in the kernel, and logs an
InfoView report with the simplified expression and the nonvanishing conditions under which it
equals `e`. Pipeline diagnostics are kept separate from the kernel-checked evidence.

## Main results

* `eq_of_simplifyFinDisplayRoute`: when the display route of `E` ends at `D` with the conditions
  `N`, the values of `E` and `D` are equal wherever `N` holds.

## Implementation notes

The simplification is `simplifyFinDisplayRoute` of `CAS/ClosedForm/Pipeline/Configured.lean`:
the side-conditioned pipeline of checked passes, followed by the rational canonical form in one
variable or `Alg.canonical` in several, keeping cosines unless the Pythagorean elimination gives
a smaller result. Every pass is proved sound in that library, so the route carries its own
theorem, `SideClaimRoute.sound`, and we search for no certificate. We run the route in compiled
code to print the result, and the kernel evaluates it once more on the same input
(`decideByKernel`) to fix the result and the conditions that the report states.

The first checked step states the identity about the real terms themselves,
`∀ x : ℝ, conditions → e = result`. We transport it from the route's statement about the
internal expressions by `eq_of_simplifyFinDisplayRoute`, so that the user reads a theorem about
Mathlib's real functions rather than about the expression syntax.
-/

public meta section

namespace CAS.Command

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Tactic.Explanation

private def simplifyEvidence {n : Nat}
    (input : Verified.Expr (Fin n)) : MetaM UncheckedExplanationStep := do
  let inputTerm ← quoteVerifiedExpr input
  let routeTerm ←
    mkAppM ``Verified.Expr.simplifyFinDisplayRoute #[inputTerm]
  let proof ←
    mkAppM ``Verified.Expr.SideClaimRoute.sound #[routeTerm]
  proofStep "Simplification under generated rewrite assumptions"
    ``Verified.Expr.SideClaimRoute.sound proof

/-- `simplifyFinDisplayRoute` as an identity of real terms: when the route of `E` ends at `D` with
the recorded conditions `N`, `E` and `D` evaluate to `a` and `b` at `ρ`, and the conditions hold
there (`Alg.SideHolds ρ N`), then `a = b`. -/
theorem eq_of_simplifyFinDisplayRoute {n : Nat} {E D : Verified.Expr (Fin n)}
    {N : List (Verified.Expr (Fin n))}
    (hroute : (Verified.Expr.simplifyFinDisplayRoute E).rhs = D ∧
      (Verified.Expr.simplifyFinDisplayRoute E).nonzero = N)
    (ρ : Fin n → ℝ) {a b : ℝ} (ha : E.eval ρ = a) (hb : D.eval ρ = b)
    (hside : Verified.Expr.Alg.SideHolds ρ N) : a = b :=
  (Verified.Expr.simplifyFinDisplayRoute E).eq_of_eval
    (Verified.Expr.simplifyFinDisplayRoute_lhs E) hroute ρ ha hb hside

/-- The headline of a simplification report, `∀ x… : ℝ, conditions → input = result` about the
printed real terms. The route is fixed by one kernel decision of its result and conditions, and
`eq_of_simplifyFinDisplayRoute` transports its soundness theorem to the printed terms. -/
private def simplifyHeadline (reified : ReifiedExpr)
    (route : Verified.Expr.SideClaimRoute (Fin reified.names.length)) :
    TermElabM UncheckedExplanationStep := do
  let n := reified.names.length
  let (idents, vars) := coordinateIdents reified
  let conditions ← conditionTerms vars { nonzero := route.nonzero, positive := [] }
  let statement ← realForallStatement idents conditions
    (← `(($(← reified.inputTerm vars) : ℝ) =
      $(← exprTerm vars route.rhs reified.resultFunction?)))
  headlineStep "Identity with the simplified form" ``eq_of_simplifyFinDisplayRoute
      statement (n + conditions.size) fun locals conclusion ↦ do
    let some (_, lhs, rhs) := conclusion.eq?
      | throwError "the simplification headline is not an equation"
    let ρ ← Tactic.RealExpression.parameterVector (locals.extract 0 n)
    let input ← quoteVerifiedExpr reified.expr
    let result ← quoteVerifiedExpr route.rhs
    let nonzero ← quoteVerifiedList n route.nonzero
    let routeTerm ← mkAppM ``Verified.Expr.simplifyFinDisplayRoute #[input]
    let fields := mkAnd
      (← mkEq (← mkAppM ``Verified.Expr.SideClaimRoute.rhs #[routeTerm]) result)
      (← mkEq (← mkAppM ``Verified.Expr.SideClaimRoute.nonzero #[routeTerm]) nonzero)
    let hroute ← Tactic.KernelReadBack.decideByKernel "#cas [simplify]" fields
    let hside ← headlineConditions "#cas [simplify]"
      (← mkAppM ``Verified.Expr.Alg.SideHolds #[ρ, nonzero])
    mkAppOptM ``eq_of_simplifyFinDisplayRoute
      #[none, some input, none, none, some hroute, some ρ, none, none,
        some (← headlineBridge ρ input lhs), some (← headlineBridge ρ result rhs), some hside]

/-- Log the `#cas [simplify]` report of the reified input: the result and the conditions of
`simplifyFinDisplayRoute`, the headline identity (when it is proved within its budget) and the
route's soundness theorem as checked steps, and the passes of the route as planner metadata. Under
`cas.suggest` the headline is also offered as an `example`. -/
def logSimplify (ref : Syntax) (reified : ReifiedExpr) : CommandElabM Unit := do
  let route := Verified.Expr.simplifyFinDisplayRoute reified.expr
  let requirements : Verified.Expr.ValidityRequirements (Fin reified.names.length) :=
    { nonzero := route.nonzero, positive := [] }
  let (report, statement?) ← liftTermElabM <|
    withHeadlines #[simplifyHeadline reified route] fun headlines ↦ do
      evidenceReportMessage #[← simplifyEvidence reified.expr]
        (route.steps.toArray.map passMetadata) headlines
  let computation := computationNode "Checked symbolic computation" #[
    m!"Raw checked nonzero requirements: {renderExprList reified requirements.nonzero}",
    m!"Guarantee: these assumptions justify conditional rewrites and preserve real evaluation"
  ]
  logReport ref {
    domain := renderRealDomain reified.names
    input := reified.render
    inputType := "scalar ℝ"
    output := renderExpr reified route.rhs
    outputType := "scalar ℝ"
    conditions? := renderConditions reified requirements
  } #[
    m!"Variables: {renderNames reified.names}",
    computation,
    report
  ]
  offerExample statement?

end CAS.Command

namespace CAS.Command

open Lean Elab Command

/-- `#cas [simplify] e` simplifies the real expression `e` by checked exact rewrites and prints the
result with the conditions under which it equals `e`.

## Theorem
For the variables `x₁, …, xₙ` of `e`, the printed result `e'` and the checked conditions
`c₁, …, cₖ`, which the `Conditions` line prints in its display form, the first checked step
proves `∀ x₁ … xₙ : ℝ, c₁ → … → cₖ → e = e'` about Mathlib's real functions, such as
`∀ (x : ℝ), x + x = 2 * x` for `#cas [simplify] (x + x)`. The lemma
`CAS.Command.eq_of_simplifyFinDisplayRoute` transports it from the statement for the internal
expression syntax (`CAS.Verified.Expr.SideClaimRoute.sound`), which follows it among the checked
steps. The first step is shown when its proof succeeds within its own budget of `maxHeartbeats`
heartbeats; otherwise the report keeps only the internal statement. The tactic `cas` proves the
same identity.

## Conditions and limits
The variables of `e` are real. The functions are `abs`, `sin`, `cos`, `tan`, `sinh`, `cosh`,
`tanh`, `atan`, `asin`, `acos`, `exp`, `log` and `sqrt`, with `+`, `-`, `*`, `/` and powers; a
power with a variable exponent is a real power. Cancelling a divisor `d` adds the condition
`d ≠ 0`, and combining real powers of `a` adds the condition `a > 0`.

## Options
Under `set_option cas.suggest true` the report also offers the first checked step above as an
`example` to paste in place of the command, when the binders and the type of that example,
elaborated where the command is with the variables of its section, are the proposition of the step
up to unfolding instances, and the whole example elaborates there without errors to a declaration
of that proposition with no `sorry` (`cas.suggest`).

## Examples
```lean
#cas [simplify] ((x ^ 4 - 1) / (x ^ 2 - 1))
```
```output
Output (scalar ℝ): x^2 + 1
Conditions: x^2 - 1 ≠ 0
```
```lean
#cas [simplify] (exp ((x^2 - y^2)/(x - y)))
```
```output
Output (scalar ℝ): exp(x + y)
Conditions: x - y ≠ 0
```
```lean
#cas [simplify] (a ^ p * a * sqrt a / a ^ q)
```
```output
Output (scalar ℝ): a^(p - q + 3/2)
Conditions: a > 0
```

## In a proof
```lean
theorem simplify_quotient (x : ℝ) (h : x ^ 2 - 1 ≠ 0) :
    (x ^ 4 - 1) / (x ^ 2 - 1) = x ^ 2 + 1 := by
  cas
```

## See also
Mathematica `Simplify`, SymPy `simplify`. The modes `fullSimplify`, `together`, `cancel` and
`factor`, and the tactic `cas`.

## Possible issues
```lean
#cas [simplify] (x y)
```
```output
unsupported symbolic function 'x'; expected abs, sin, cos, tan, sinh, cosh, tanh, atan/arctan,
asin/arcsin, acos/arccos, exp, log, or sqrt. If multiplication was intended, write it explicitly
with `*`
```
An identifier applied to an argument is read as a function. Write a product as `x * y`.

```lean
#cas [simplify] ((1 / (1/x + 1/(1-x)) - 1) / (1 / (1/x + 1/(1-x)) - 1))
```
```output
Output (scalar ℝ): 1
Conditions: 1/(1/x + 1/(1 - x)) - 1 ≠ 0
```
A condition is written as a polynomial in descending powers only when it equals that polynomial
for every value of its variables. The divisor here equals `-(x^2 - x + 1)` only for `x ≠ 0` and
`x ≠ 1` (at `x = 0` it is `0`, since `1/0 = 0`), so the condition keeps the form of the input.
-/
syntax (name := casSimplifyCommand) "#cas" "[" &"simplify" "]" term : command

elab_rules : command
  | `(#cas [simplify] $expr:term) => do
      logSimplify expr (← parseInferred expr)

end CAS.Command

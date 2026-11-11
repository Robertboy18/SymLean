/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Differential
public meta import CAS.Integration
public import CAS.Calculus.Antiderivative
public meta import CAS.Tactic.RouteRegistry
public import CAS.Command.FullSimplify
public import CAS.Tactic.Integration.Limits
public meta import CAS.Tactic.Integration.Projection
public import CAS.IntegrationTactic

/-!
# Checked integration reports for `#cas`

The commands `#cas [integrate x] e` and `#cas [integrate] e` (for an expression with one
free variable or a unary lambda) print an antiderivative `F` of `e` with its domain conditions.
The report shows the primitive, the normalization of its derivative residual, the domain
requirements, and kernel-checked evidence linking the `AntiderivativeCert` to its analytic
coordinate-line theorems; planner metadata is shown separately from the evidence. The evidence
opens with the fundamental theorem of calculus for the printed integrand and primitive,
`∀ a b : ℝ, (∀ x ∈ Set.uIcc a b, conditions) → ∫ x in a..b, e = F b - F a`.
`logIntegralCertificate` prints this report for a checked antiderivative from any search; the
oracle route of `CASOracle/Integrate.lean` uses it too. The command
`#cas [integrate x in [a, b]] e` evaluates a definite integral, where an endpoint is a real term,
`∞` or `-∞`, and proves `∫ x in a..b, e = v` or, over `Set.Ioi a`, `Set.Iic b` or the whole line,
that `e` is integrable there and its integral is `v`.

## Implementation notes

The commands `#cas [integrate x]` and `#cas [integrate]` first run the backends registered with
`@[cas_route integrate]`, such as the Gaussian integrals of `CAS/Command/GaussianIntegral.lean`;
the definite integral runs none. When every backend declines,
`integrate?` (`CAS/Integration.lean`) searches with the untrusted planner of
`CAS/Integration/Planner.lean`: the table of `CAS/Integration/Elementary.lean`, Bioche's rules
and trigonometric polynomials (`CAS/Integration/Bioche.lean`), substitution, the
exponential-trigonometric recurrence (`CAS/Integration/ExponentialTrig.lean`), the tangent
half-angle substitution, integration by parts, and, for a rational integrand, the Euclidean
division of `CAS/Integration/Rational.lean`, Hermite reduction (`CAS/Integration/Hermite.lean`)
and the closed square-free primitives of `CAS/Integration/RationalElementary.lean`. There is no
resultant (Rothstein-Trager) step; Hex's factorizer (`CASHex.Factor`), when it is imported,
splits a square-free denominator factor of degree three or more over `ℚ`.

The certificate is an `IntegrationCheck.AntiderivativeCert` (`CAS/Integration/Check.lean`): the
residual `F' - e` reaches literal zero along a checked normalization route. We decide that
equation and the requirement lists in one kernel decision (`integrationCertificate`), the one
expensive reflection step of the report, and the certificate steps of the evidence and the
headline refer to the resulting constant. The headline comes from
`AntiderivativeCert.intervalIntegral_eq_sub_of_line` (`CAS/Calculus/Antiderivative.lean`), which
rests on Mathlib's `intervalIntegral.integral_eq_sub_of_hasDerivAt`. For a definite integral we
evaluate `F` at the endpoints, take its limit at an infinite endpoint with
`Tactic.Integration.Limits.limitAtTopOfBody`, and write out the values of elementary functions at
special points (`endpointValues`). The statement is then proved by `cas` or `cas using h`, and on
a bounded interval also by `cas [integrate primitive := F]` (`tryProve`); the printed value is the
first one whose statement was proved. Conditions of `F` that contain parameters but not `x`
become hypotheses of that statement. On a bounded interval the other conditions of `F` are first
proved on the interval by the requirement prover of `cas` (`Projection.proveRequirements`), and
the command refuses when it fails or runs out of heartbeats. The other attempts need the same
conditions, for `F` or for the primitive that the same planner finds in `cas`, and prove them only
after certifying the primitive in the kernel, which can cost more than the declaration's
heartbeats. The primitive of `1 / (2 + cos x)` jumps at `π`, where `1 + cos x ≠ 0` fails, so its
value on `[0, 4]` is refused at once. When the integrand has no parameters, the proved conditions
are kept as a theorem `h`, and the attempt with the primitive is
`cas [integrate primitive := F using h]`, which does not prove them again. The kernel checks of
an attempt get a quarter of `maxHeartbeats`, and the first attempt that runs out of heartbeats
ends the search with a refusal: on `[0, 1]`, where the conditions hold, the kernel check of the
certificate of that primitive needs more than that quarter.
-/

public meta section

namespace CAS.Command

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Tactic.Explanation

/-- The certificate of a checked primitive as a term, with the proof that its requirements are
the lists `requirements` the command computed. -/
private def integrationCertificate {n : Nat} (coordinate : Fin n)
    (integrand candidate : Verified.Expr (Fin n))
    (requirements : Verified.Expr.ValidityRequirements (Fin n)) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let integrandTerm ← quoteVerifiedExpr integrand
  let candidateTerm ← quoteVerifiedExpr candidate
  let coordinateTerm := Lean.toExpr coordinate
  let routeTerm ←
    mkAppM ``IntegrationCheck.route
      #[coordinateTerm, integrandTerm, candidateTerm]
  let routeRhs ←
    mkAppM ``Verified.Expr.SideClaimRoute.rhs #[routeTerm]
  let zeroTerm ← quoteVerifiedExpr (0 : Verified.Expr (Fin n))
  let routeZeroProposition ← mkEq routeRhs zeroTerm
  let requirementsTerm ←
    mkAppM ``IntegrationCheck.AntiderivativeCert.candidateRequirements
      #[coordinateTerm, integrandTerm, candidateTerm]
  let requirementsLiteral ← mkAppM ``Verified.Expr.ValidityRequirements.mk
    #[← quoteVerifiedList n requirements.nonzero, ← quoteVerifiedList n requirements.positive]
  let proposition := mkAnd routeZeroProposition (← mkEq requirementsTerm requirementsLiteral)
  -- The residual normalization is the one expensive reflection step in this
  -- report. The kernel evaluates it once here, together with the requirements; the steps
  -- built from the certificate, in the evidence and in the headline, then refer to the
  -- resulting constant instead of repeating the evaluation.
  let proof ← kernelCheckedProof "the checked residual route"
    proposition (← mkDecideProof proposition)
  let certificateTerm ←
    mkAppM ``IntegrationCheck.AntiderivativeCert.mk
      #[candidateTerm, ← mkAppM ``And.left #[proof]]
  let requirementsProof ← mkEqTrans
    (← mkAppM ``IntegrationCheck.AntiderivativeCert.requirements_eq_candidateRequirements
      #[certificateTerm])
    (← mkAppM ``And.right #[proof])
  return (certificateTerm, requirementsProof)

private def integrationEvidence {n : Nat}
    (coordinateName : String) (coordinate : Fin n)
    (candidate : Verified.Expr (Fin n)) (certificateTerm : Lean.Expr) :
    MetaM (Array UncheckedExplanationStep) := do
  let certificateRouteZero ←
    mkAppM ``IntegrationCheck.AntiderivativeCert.routeZero #[certificateTerm]
  let evalDiffProof ←
    mkAppM ``IntegrationCheck.AntiderivativeCert.eval_diff_eq #[certificateTerm]
  let hasDerivAtProof ←
    mkAppM
      ``IntegrationCheck.AntiderivativeCert.hasDerivAt_eval_add_smul_single
      #[certificateTerm]
  let intervalIntegralProof ←
    mkAppM
      ``IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_eval_add_smul_single
      #[certificateTerm]
  let derivativeSteps ←
    derivativeEvidence s!"Primitive derivative in {coordinateName}"
      coordinate candidate
  return derivativeSteps ++ #[
    ← proofStep "Residual route reaches zero"
      ``IntegrationCheck.AntiderivativeCert.routeZero certificateRouteZero,
    ← proofStep "Symbolic antiderivative identity under the displayed requirements"
      ``IntegrationCheck.AntiderivativeCert.eval_diff_eq evalDiffProof,
    ← proofStep "Coordinate-line derivative theorem"
      ``IntegrationCheck.AntiderivativeCert.hasDerivAt_eval_add_smul_single
      hasDerivAtProof,
    ← proofStep "Coordinate-line fundamental theorem of calculus"
      ``IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_eval_add_smul_single
      intervalIntegralProof
  ]

/-- A name for a limit of integration: the first of `base`, `base1`, …, `base9` that is not one of
the variables, and `base'` when all ten are. -/
private def limitIdent (names : List Name) (base : String) : TSyntax `ident :=
  let candidates := (List.range 10).map fun k ↦
    if k = 0 then Name.mkSimple base else Name.mkSimple s!"{base}{k}"
  mkIdent ((candidates.find? (!names.contains ·)).getD (Name.mkSimple s!"{base}'"))

/-- The headline of an integration report, the fundamental theorem of calculus for the printed
integrand and primitive, `∀ y… a b : ℝ, (∀ x ∈ Set.uIcc a b, conditions) →
∫ x in a..b, f = F b - F a`. It is transported from the certificate by
`AntiderivativeCert.intervalIntegral_eq_sub_of_line`, whose requirements the kernel decision of
the certificate has evaluated. -/
private def integrationHeadline (reified : ReifiedExpr) (coordinate : Fin reified.names.length)
    (candidate : Verified.Expr (Fin reified.names.length))
    (requirements : Verified.Expr.ValidityRequirements (Fin reified.names.length))
    (certificateTerm requirementsProof : Lean.Expr) : TermElabM UncheckedExplanationStep := do
  let n := reified.names.length
  let (idents, vars) := coordinateIdents reified
  let x := idents[coordinate.val]!
  let a := limitIdent reified.names "a"
  let b := limitIdent reified.names "b"
  let atLimit (limit : TSyntax `term) (j : Fin n) : TSyntax `term :=
    if j = coordinate then limit else vars j
  let conditions ← conditionTerms vars requirements
  let hypotheses : Array (TSyntax `term) ← if conditions.isEmpty then pure #[] else do
    let conjunction ← conditions.pop.foldrM (fun condition rest ↦ `($condition ∧ $rest))
      conditions.back!
    pure #[← `(∀ $x:ident ∈ Set.uIcc $a $b, $conjunction)]
  let primitive (limit : TSyntax `term) :=
    exprTerm (atLimit limit) candidate reified.resultFunction?
  let body ← `(intervalIntegral
      (fun ($x : ℝ) ↦ ($(← reified.inputTerm vars) : ℝ)) $a $b
      MeasureTheory.volume =
    ($(← primitive b) : ℝ) - $(← primitive a))
  let statement ← realForallStatement ((idents.eraseIdx! coordinate.val).push a |>.push b)
    hypotheses body
  headlineStep "Integral of the input"
      ``IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_of_line statement
      (n + 1 + hypotheses.size) fun locals conclusion ↦ do
    let some (_, integral, difference) := conclusion.eq?
      | throwError "the integration headline is not an equation"
    let integralArguments := integral.getAppArgs
    unless integral.isAppOf ``intervalIntegral && integralArguments.size ≥ 4 &&
        difference.isAppOfArity ``HSub.hSub 6 do
      throwError "the integration headline is not a fundamental theorem of calculus"
    let f := integralArguments[integralArguments.size - 4]!
    let lower := locals[n - 1]!
    let upper := locals[n]!
    let integrandTerm ← quoteVerifiedExpr reified.expr
    let candidateTerm ← quoteVerifiedExpr candidate
    let line ← withLocalDeclD `s (mkConst ``Real) fun s ↦ do
      mkLambdaFVars #[s] (← Tactic.RealExpression.parameterVector
        ((locals.extract 0 (n - 1)).insertIdx! coordinate.val s))
    let hline ← headlineLine line (Lean.toExpr coordinate) (← mkNumeral (mkConst ``Real) 0)
    let hf ← withLocalDeclD `s (mkConst ``Real) fun s ↦ do
      mkLambdaFVars #[s] (← headlineBridge (line.beta #[s]) integrandTerm (f.beta #[s]))
    let partialProof ← mkAppOptM
      ``IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_of_line
      #[none, none, none, some certificateTerm, none, none, some requirementsProof, some line,
        some hline, none, some hf, some lower, some upper, none, none,
        some (← headlineBridge (line.beta #[lower]) candidateTerm (difference.getArg! 5)),
        some (← headlineBridge (line.beta #[upper]) candidateTerm (difference.getArg! 4))]
    let .forallE _ holdsType _ _ ← whnf (← inferType partialProof)
      | throwError "the integration lemma has an unexpected type"
    let holds ← forallBoundedTelescope holdsType (some 2) fun point goal ↦ do
      let facts ← match locals[n + 1]? with
        | some hypothesis => headlineConjuncts (mkAppN hypothesis point)
        | none => pure #[]
      mkLambdaFVars point (← headlineConditionsWith "#cas [integrate]" goal facts)
    return mkApp partialProof holds

/-- Emit the analytic certificate report of a checked antiderivative, whichever search proposed
its primitive; `extra` adds nodes before the evidence. The evidence is rebuilt from the
certificate (the residual route is decided again in the kernel), so a proposal contributes only
the primitive. -/
def logIntegralCertificate (ref : Syntax) (reified : ReifiedExpr)
    (name : Name) (coordinate : Fin reified.names.length)
    (certificate : IntegrationCheck.AntiderivativeCert coordinate reified.expr)
    (extra : Array MessageData := #[]) :
    CommandElabM Unit := do
  let derivation :=
    Verified.Expr.DiffDerivation.build coordinate certificate.candidate
  -- `AntiderivativeCert.requirements` is the compacted requirement bundle, not
  -- `AntiderivativeCert.rawRequirements`; the report labels below say "compacted" for that.
  let requirements := certificate.requirements
  let rawResidual :=
    IntegrationCheck.residual coordinate reified.expr certificate.candidate
  let residualRoute := IntegrationCheck.route coordinate reified.expr certificate.candidate
  let verbose := cas.verbose.get (← getOptions)
  let computation := computationNode "Checked antiderivative computation" #[
    computationNode "1. Differentiate the proposed primitive" <|
      #[m!"Raw derivative: {renderExpr reified derivation.rawDerivative}"] ++
        (if verbose then #[derivationMessage reified derivation.pack] else #[]),
    computationNode "2. Form the derivative residual" #[
      m!"Raw residual: {renderExpr reified rawResidual}",
      m!"Definition: {MessageData.ofConstName ``IntegrationCheck.residual}"
    ],
    computationNode "3. Check the residual normal form" #[
      m!"Checked residual normal form: {renderExpr reified residualRoute.rhs}",
      m!"Certificate condition: checked residual normal form = 0"
    ],
    computationNode "4. Record analytic domain requirements" #[
      m!"Certificate nonzero requirements (compacted): \
        {renderExprList reified requirements.nonzero}",
      m!"Certificate positivity requirements (compacted): \
        {renderExprList reified requirements.positive}"
    ]
  ]
  let (report, statement?) ← liftTermElabM do
    let (certificateTerm, requirementsProof) ←
      integrationCertificate coordinate reified.expr certificate.candidate requirements
    withHeadlines #[integrationHeadline reified coordinate certificate.candidate requirements
        certificateTerm requirementsProof] fun headlines ↦
      -- The kernel decision above also evaluates the requirements, which only the headline
      -- uses. The evidence is checked with a heartbeat budget of its own, so the heartbeats of
      -- that decision do not reduce it.
      withCurrHeartbeats do
        let evidence ← integrationEvidence
          (renderName name) coordinate certificate.candidate certificateTerm
        evidenceReportMessage evidence (residualRoute.steps.toArray.map passMetadata) headlines
  logReport ref {
    domain := renderRealDomain reified.names
    input := reified.render
    inputType := "scalar ℝ"
    output := renderExpr reified certificate.candidate
    outputType := "scalar ℝ; antiderivative"
    conditions? := renderConditions reified requirements
  } (#[m!"Variables: {renderNames reified.names}", computation] ++ extra ++ #[report])
  offerExample statement?

/-- The note that ends a refusal when the integrand has a denominator factor of degree three or
more and no factor provider is registered, and `""` otherwise. -/
private def factorProviderHint {n : Nat} (hasProvider : Bool) (coordinate : Fin n)
    (expr : Verified.Expr (Fin n)) : String :=
  if !hasProvider && CAS.IntegrationPlanner.Rational.needsFactorProvider coordinate expr then
    ". The denominator has a factor of degree three or more, which is not factored \
      without Hex: `import CASHex.Factor` (built with `lake -R -Khex=on build CASHex`) \
      factors it"
  else ""

/-- The factor provider of the route registry, if one is registered, in the form `integrate?`
takes. -/
private def integrationFactorProvider? : CommandElabM
    (Option CAS.Polynomial.Sparse.Univariate.RationalFactorization.Provider) := do
  return (← liftCoreM Tactic.RouteRegistry.factorProvider?).map
    CAS.Polynomial.Sparse.Univariate.RationalFactorization.ofDense

private def logIntegralCore (ref : Syntax) (reified : ReifiedExpr)
    (name : Name) (coordinate : Fin reified.names.length) : CommandElabM Unit := do
  let provider? ← integrationFactorProvider?
  let some certificate := integrate? coordinate reified.expr provider?
    | let hint := factorProviderHint provider?.isSome coordinate reified.expr
      throwErrorAt ref
        "the checked integrator found no supported antiderivative in coordinate \
          '{renderName name}'. Try an equivalent supported form. For a `HasDerivAt` identity, \
          use `cas` or `cas using h`. To check a known primitive `F` of an ordinary \
          interval-integral identity, use `cas [integrate primitive := F]` or \
          `cas [integrate primitive := F using h]`; the domain conditions must hold throughout \
          the interval `Set.uIcc a b`{hint}"
  logIntegralCertificate ref reified name coordinate certificate

/-- Search a checked antiderivative with `integrate?`, with the factor provider of the route
registry, and log its report by `logIntegralCertificate`; fail when the search finds none. -/
def logIntegral (ref : Syntax) (reified : ReifiedExpr)
    (name : Name) (coordinate : Fin reified.names.length) : CommandElabM Unit :=
  logIntegralCore ref reified name coordinate

end CAS.Command

namespace CAS.Command

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Tactic.Explanation

/-- `#cas [integrate x] e` finds an antiderivative of `e` with respect to `x`, checks it by
differentiation, and prints it with the conditions under which it holds.

## Theorem
For the printed antiderivative `F` and the checked conditions `c₁, …, cₖ`, which the `Conditions`
line prints in its display form, the first checked step proves the fundamental theorem of
calculus about Mathlib's real functions,
`∀ a b : ℝ, (∀ x ∈ Set.uIcc a b, c₁ ∧ … ∧ cₖ) → ∫ x in a..b, e = F b - F a`, for every value of
the other variables, such as
`∀ (a b : ℝ), ∫ (x : ℝ) in a..b, x * Real.exp x = Real.exp b * (b - 1) - Real.exp a * (a - 1)`
for `#cas [integrate x] (x * exp x)`. The lemma
`CAS.IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_of_line` transports it from the
checked certificate, whose statements for the internal expression syntax follow it
(`CAS.IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_eval_add_smul_single`). The
first step is shown when its proof succeeds within its own budget of `maxHeartbeats` heartbeats;
otherwise the report keeps only the internal statements. The limits get other names when a
variable is called `a` or `b`. The tactic `cas` proves
`HasDerivAt (fun x ↦ F) e x`, `∫ x in a..b, e = v` and, over a half-line `D`,
`IntegrableOn (fun x ↦ e) D ∧ ∫ x in D, e = v`.

## Conditions and limits
`e` uses the functions of `#cas [derive x]`, and the other variables are parameters. The search
covers polynomials and the table of elementary antiderivatives, substitution, rational functions,
integration by parts, polynomials times exponential and trigonometric phases, and rational
functions of `sin` and `cos`; the backends registered with `@[cas_route integrate]`, such as the
Gaussian integrals, run first. The search is bounded, and a candidate is printed only after its
derivative is checked. Without Hex, a rational function is refused when its denominator keeps a
factor of degree three or more after the powers of `x` are split off.

## Options
Under `set_option cas.verbose true` the first computation step also shows the tree of
differentiation rules of the antiderivative, each rule with its input and its raw derivative.
Under `set_option cas.suggest true` the report also offers the first checked step above as an
`example` to paste in place of the command, when the binders and the type of that example,
elaborated where the command is with the variables of its section, are the proposition of the step
up to unfolding instances, and the whole example elaborates there without errors to a declaration
of that proposition with no `sorry` (`cas.suggest`).

## Examples
```lean
#cas [integrate x] (x * sin (x ^ 2))
```
```output
Output (scalar ℝ; antiderivative): -(1/2*cos(x^2))
```
```lean
#cas [integrate x] (1 / (x * log x))
```
```output
Output (scalar ℝ; antiderivative): log(log(x))
Conditions: x ≠ 0; log(x) ≠ 0
```
```lean
#cas [integrate x in [0, 1]] (x * exp x)
```
```output
Output (scalar ℝ; definite integral): 1
```

## In a proof
```lean
theorem integrate_by_parts : ∫ x in (0 : ℝ)..1, x * Real.exp x = 1 := by
  cas
```

## See also
Mathematica `Integrate`, SymPy `integrate`. Hex `Hex.ZPoly.factorize` (through `CASHex.Factor`)
splits the denominators of rational integrands. The modes `derive`, `nintegrate`, `apart` and
`laplace`, and the tactic `cas [integrate primitive := F]`, which checks a given primitive. Oracle
route: `#cas [integrate x, oracle := sympy] e`, which checks the oracle's primitive as its own.

## Possible issues
```lean
#cas [integrate x] (exp (x ^ 2))
```
```output
the checked integrator found no supported antiderivative in coordinate 'x'. Try an equivalent
supported form.
```
`exp (x ^ 2)` has no elementary antiderivative. `#cas [nintegrate x in [a, b]]` gives a certified
value of a definite integral.
```lean
#cas [integrate x] (1/(x^3 - 1))
```
```output
The denominator has a factor of degree three or more, which is not factored without Hex:
`import CASHex.Factor` (built with `lake -R -Khex=on build CASHex`) factors it
```
With Hex the same command prints
`-1/6*log(x^2 + x + 1) - atan((2*x + 1)/sqrt(3))/sqrt(3) + 1/3*log(x - 1)`.
```lean
#cas [integrate x in [1, ∞]] (1 / x)
```
```output
#cas [integrate] could not determine the limit at +∞ of the primitive: no decay shape applies to
```
The integral diverges: the primitive `log x` has no limit at `∞`.
-/
syntax (name := casIntegralCommand) "#cas" "[" &"integrate" ident "]" term : command

/-- `#cas [integrate] e` integrates an expression with exactly one variable, or a lambda
`fun x ↦ e`, in that variable; see `#cas [integrate x]`.
-/
syntax (name := casUnivariateIntegralCommand) "#cas" "[" &"integrate" "]" term : command

/-- An endpoint of `#cas [integrate x in [a, b]]`: a real term, `∞` or `-∞`. -/
declare_syntax_cat casIntegralEndpoint

/-- The endpoint `∞`. -/
syntax "∞" : casIntegralEndpoint

/-- The endpoint `-∞`. -/
syntax "-" "∞" : casIntegralEndpoint

/-- A real endpoint. -/
syntax (priority := low) term : casIntegralEndpoint

/-- `#cas [integrate x in [a, b]] e` evaluates the definite integral of `e` from `a` to `b` as
`F b - F a` for the antiderivative `F` that `integrate?` finds (the search of `#cas [integrate x]`
without its backends), where an endpoint is a real term, `∞` or `-∞` and `F` is replaced by its
limit at an infinite endpoint. It proves the printed theorem `∫ x in a..b, e = v` with `cas`, or,
over `Set.Ioi a`, `Set.Iic b` or the whole line, the integrability of `e` there together with the
value of its integral, such as `IntegrableOn (fun x ↦ e) (Set.Ioi a) ∧ ∫ x in Set.Ioi a, e = v`.
-/
syntax (name := casDefiniteIntegralCommand) "#cas" "[" &"integrate" ident " in " "["
  casIntegralEndpoint ", " casIntegralEndpoint "]" "]" term : command

/-- An endpoint of a definite integral, read in the coordinates of the integrand. -/
private inductive Endpoint (n : Nat) where
  /-- A real endpoint. -/
  | finite (value : Verified.Expr (Fin n))
  /-- The endpoint `∞`. -/
  | top
  /-- The endpoint `-∞`. -/
  | bot

/-- The term of a real endpoint, and `none` for `∞` and `-∞`. -/
private def endpointTerm? (endpoint : TSyntax `casIntegralEndpoint) : Option Term :=
  match endpoint with
  | `(casIntegralEndpoint| ∞) => none
  | `(casIntegralEndpoint| -∞) => none
  | `(casIntegralEndpoint| $value:term) => some value
  | _ => none

/-- An endpoint read in the coordinates of `reified`. -/
private def readEndpoint (reified : ReifiedExpr) (endpoint : TSyntax `casIntegralEndpoint) :
    CommandElabM (Endpoint reified.names.length) := do
  match endpointTerm? endpoint with
  | some value =>
      let point ← parseExact value reified.names
      if h : point.names.length = reified.names.length then
        return .finite (point.expr.mapVars fun j ↦ .var (j.cast h))
      else
        throwErrorAt value "internal #cas error: an endpoint was read in other coordinates"
  | none =>
      match endpoint with
      | `(casIntegralEndpoint| -∞) => return .bot
      | _ => return .top

/-- `expr` with the coordinate `i` replaced by `value`. -/
private def substituteCoordinate {n : Nat} (i : Fin n) (value expr : Verified.Expr (Fin n)) :
    Verified.Expr (Fin n) :=
  expr.mapVars fun j ↦ if j = i then value else .var j

/-- The rational `q` when `expr` is `q π`, also when it is written as a quotient by a rational. -/
private def piCoefficient? {n : Nat} : Verified.Expr (Fin n) → Option ℚ
  | .div a b => do
      let q ← piCoefficient? a
      let d ← IntegrationPlanner.Bioche.rationalValue? b
      if d = 0 then none else some (q / d)
  | expr =>
      match Verified.Expr.Alg.polyOf expr with
      | [] => some 0
      | [(q, [.pi])] => some q
      | _ => none

/-- `q π` as an expression. -/
private def piTimes {n : Nat} (q : ℚ) : Verified.Expr (Fin n) :=
  if q = 0 then 0 else Verified.Expr.mkMul (Verified.Expr.mkRatConst q) .pi

/-- `sin (m π / 12)` for `m` divisible by 2 or 3, which is `0`, `1/2`, `√2/2`, `√3/2` or `1` up to
its sign. -/
private def sinTwelfths {n : Nat} (m : Nat) : Verified.Expr (Fin n) :=
  let r := min (m % 12) (12 - m % 12)
  let value : Verified.Expr (Fin n) :=
    if r = 0 then 0
    else if r = 2 then Verified.Expr.mkRatConst (1 / 2)
    else if r = 3 then .div (.sqrt 2) 2
    else if r = 4 then .div (.sqrt 3) 2
    else 1
  if m % 24 < 12 then value else Verified.Expr.mkNeg value

/-- `sin a` (when `isSin`) or `cos a`, evaluated when `a` is `k π / 12` for an integer `k`
divisible by 2 or 3. -/
private def trigValue {n : Nat} (isSin : Bool) (a : Verified.Expr (Fin n)) :
    Verified.Expr (Fin n) :=
  let unevaluated : Verified.Expr (Fin n) := if isSin then .sin a else .cos a
  match piCoefficient? (Verified.Expr.Alg.normalize a) with
  | some q =>
      let k := 12 * q
      if k.den = 1 && (k.num % 2 = 0 || k.num % 3 = 0) then
        let m := (k.num % 24).toNat
        sinTwelfths (if isSin then m else m + 6)
      else unevaluated
  | none => unevaluated

/-- The value at `-1`, `0` or `1` of `atan`, `asin` or `acos`, given as three rational multiples
of `π`, and `none` at another argument. -/
private def inverseTrigValue? {n : Nat} (values : ℚ × ℚ × ℚ)
    (argument : Verified.Expr (Fin n)) : Option (Verified.Expr (Fin n)) := do
  let q ← IntegrationPlanner.Bioche.rationalValue? (Verified.Expr.Alg.normalize argument)
  if q = -1 then some (piTimes values.1)
  else if q = 0 then some (piTimes values.2.1)
  else if q = 1 then some (piTimes values.2.2)
  else none

/-- `exp a`, with `exp (log c) = c` for a positive rational `c`. -/
private def expValue {n : Nat} (a : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  match a with
  | .log c =>
      match IntegrationPlanner.Bioche.rationalValue? (Verified.Expr.Alg.normalize c) with
      | some q => if 0 < q then Verified.Expr.mkRatConst q else .exp a
      | none => .exp a
  | _ => .exp a

/-- `log c` for a rational `c`, written as `log |c|` when `c < 0`, which is its value in Lean
(`Real.log_neg_eq_log`), and `log a` for any other `a`. -/
private def logValue {n : Nat} (a : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  match IntegrationPlanner.Bioche.rationalValue? (Verified.Expr.Alg.normalize a) with
  | some q => if q < 0 then .log (Verified.Expr.mkRatConst (-q)) else .log a
  | none => .log a

/-- `expr` with the values of elementary functions at special points written out: `sin` and `cos`
at `k π / 12` for `k` divisible by 2 or 3, `atan`, `asin` and `acos` at `-1`, `0` and `1`,
`exp (log c)` for a positive rational `c`, and `log c` for a negative one. A primitive evaluated
at the endpoints is simplified this way. -/
private def endpointValues {n : Nat} : Verified.Expr (Fin n) → Verified.Expr (Fin n)
  | .add a b => .add (endpointValues a) (endpointValues b)
  | .sub a b => .sub (endpointValues a) (endpointValues b)
  | .mul a b => .mul (endpointValues a) (endpointValues b)
  | .div a b => .div (endpointValues a) (endpointValues b)
  | .neg a => .neg (endpointValues a)
  | .pow a k => .pow (endpointValues a) k
  | .sin a => trigValue true (endpointValues a)
  | .cos a => trigValue false (endpointValues a)
  | .atan a =>
      let value := endpointValues a
      (inverseTrigValue? (-1 / 4, 0, 1 / 4) value).getD (.atan value)
  | .asin a =>
      let value := endpointValues a
      (inverseTrigValue? (-1 / 2, 0, 1 / 2) value).getD (.asin value)
  | .acos a =>
      let value := endpointValues a
      (inverseTrigValue? (1, 1 / 2, 0) value).getD (.acos value)
  | .exp (.log c) => expValue (.log (endpointValues c))
  | .exp a => expValue (endpointValues a)
  | .log a => logValue (endpointValues a)
  | .sqrt a => .sqrt (endpointValues a)
  | .rpow a b => .rpow (endpointValues a) (endpointValues b)
  | expr => expr

/-- The term of an expression in the coordinates `names`, as `FullSimplify` states it. -/
private def termOf {n : Nat} (names : List Name) (expr : Verified.Expr (Fin n)) :
    CommandElabM Term :=
  (FullSimplify.Form.ofExpr names expr).toSyntax

/-- The limit of the primitive at `∞`, or at `-∞` when `atBot`, found by
`Limits.limitAtTopOfBody` on `t ↦ F t` (or on `t ↦ F (-t)`) and read back in the coordinates of
`reified`, whose only coordinate is the integration coordinate. -/
private def primitiveLimitValue (reified : ReifiedExpr) (coordinate : Fin reified.names.length)
    (primitive : Verified.Expr (Fin reified.names.length)) (atBot : Bool) :
    CommandElabM (Verified.Expr (Fin reified.names.length)) := do
  let oriented :=
    if atBot then
      Verified.Expr.Alg.normalize
        (substituteCoordinate coordinate (.neg (.var coordinate)) primitive)
    else primitive
  let body ← termOf reified.names oriented
  let x := mkIdent (reified.names.get coordinate)
  let limit ← liftTermElabM do
    let function ← Term.elabTerm (← `(fun $x:ident : ℝ ↦ $body)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let function ← instantiateMVars function
    withLocalDeclD `t (mkConst ``Real) fun t ↦ do
      let (limitExpr, _) ← Tactic.Integration.Limits.limitAtTopOfBody "#cas [integrate]" t
        (function.beta #[t])
      PrettyPrinter.delab limitExpr
  let value ← parseExact limit reified.names
  if h : value.names.length = reified.names.length then
    return value.expr.mapVars fun j ↦ .var (j.cast h)
  else
    throwError "internal #cas error: the limit was read in other coordinates"

/-- The primitive at an endpoint: its value at a real endpoint and its limit at `∞` or `-∞`. -/
private def primitiveAt (reified : ReifiedExpr) (coordinate : Fin reified.names.length)
    (primitive : Verified.Expr (Fin reified.names.length)) :
    Endpoint reified.names.length → CommandElabM (Verified.Expr (Fin reified.names.length))
  | .finite point => pure (substituteCoordinate coordinate point primitive)
  | .top => primitiveLimitValue reified coordinate primitive false
  | .bot => primitiveLimitValue reified coordinate primitive true

/-- `∀ p₁ … pₖ : ℝ, h₁ → … → hₘ → ∫ x in a..b, integrand = value` for finite endpoints `lower?`
and `upper?`, and, when an endpoint is infinite (`none`), the conjunction of the integrability of
the integrand on `Set.Ioi a`, on `Set.Iic b` or on the whole line with the value of its integral
there. -/
private def definiteStatement (x : Ident) (parameters : List Ident) (hypotheses : List Term)
    (lower? upper? : Option Term) (integrand value : Term) : CommandElabM Term := do
  let equation ← match lower?, upper? with
    | some a, some b => `(∫ $x:ident in ($a : ℝ)..$b, $integrand = $value)
    | some a, none =>
        `(MeasureTheory.IntegrableOn (fun $x:ident : ℝ ↦ $integrand) (Set.Ioi ($a : ℝ)) ∧
          ∫ $x:ident in Set.Ioi ($a : ℝ), $integrand = $value)
    | none, some b =>
        `(MeasureTheory.IntegrableOn (fun $x:ident : ℝ ↦ $integrand) (Set.Iic ($b : ℝ)) ∧
          ∫ $x:ident in Set.Iic ($b : ℝ), $integrand = $value)
    | none, none =>
        `(MeasureTheory.Integrable (fun $x:ident : ℝ ↦ $integrand) ∧
          ∫ $x:ident : ℝ, $integrand = $value)
  let body ← hypotheses.foldrM (fun h statement ↦ `($h → $statement)) equation
  parameters.foldrM (fun p statement ↦ `(∀ $p:ident : ℝ, $statement)) body

/-- Elaborate `statement` and run `tactic` on it without error recovery, restoring the state when
the tactic fails. A kernel check inside the tactic gets at most `kernelBudget` thousand heartbeats,
through the option `maxHeartbeats` that the kernel checks of `cas` read
(`ProofCarrier.withRemainingKernelBudget`); the elaboration keeps the declaration's budget. The
answer is the statement and its proof, or the error and whether a budget ran out. -/
private def tryProve (statement : Term) (tactic : TSyntax `tactic) (kernelBudget : Nat) :
    TermElabM (Except (MessageData × Bool) (Lean.Expr × Lean.Expr)) := do
  let saved ← Term.saveState
  tryCatchRuntimeEx
    (withOptions (maxHeartbeats.set · kernelBudget) do
        let type ← Term.elabType statement
        Term.synthesizeSyntheticMVarsNoPostponing
        let type ← instantiateMVars type
        let goal ← mkFreshExprMVar type
        let remaining ← Lean.Elab.Tactic.run goal.mvarId!
          (Lean.Elab.Tactic.withoutRecover (Lean.Elab.Tactic.evalTactic tactic))
        unless remaining.isEmpty do throwError "{tactic} left {remaining.length} goals open"
        let proof ← instantiateMVars goal
        if proof.hasSorry || proof.hasExprMVar then throwError "{tactic} did not close the goal"
        return .ok (type, proof))
    fun error ↦ do
      if error.isInterrupt then throw error
      saved.restore
      return .error (error.toMessageData, error.isRuntime)

/-- What the requirement prover of `cas` makes of the conditions of a primitive on an interval. -/
private inductive ConditionsCheck where
  /-- The statement of the conditions does not elaborate. -/
  | skipped
  /-- The conditions are proved, as the theorem `name?` when their statement has no binders. -/
  | proved (name? : Option Name)
  /-- The prover failed, or ran out of heartbeats. -/
  | failed (timedOut : Bool)

/-- Prove `statement`, the conditions of a primitive on an interval under the parameters and
hypotheses that `binders` introduce, with the requirement prover of `cas`. A heartbeat exception
is caught too, so that it becomes the command's refusal. The state is restored unless the
conditions are proved without binders: their proof is then kept as a theorem, which the attempts
pass to `cas [integrate primitive := F using h]`. -/
private def checkConditions (statement : Term) (binders : Array Term) :
    TermElabM ConditionsCheck := do
  let saved ← Term.saveState
  let type? ←
    try
      let type ← Term.elabType statement
      Term.synthesizeSyntheticMVarsNoPostponing
      pure (some (← instantiateMVars type))
    catch _ =>
      pure none
  let some type := type? | do saved.restore; return .skipped
  let goal ← mkFreshExprMVar type
  let outcome ← tryCatchRuntimeEx
    (do
      discard <| Lean.Elab.Tactic.run goal.mvarId! <| Lean.Elab.Tactic.withoutRecover do
        unless binders.isEmpty do
          Lean.Elab.Tactic.evalTactic (← `(tactic| intro $binders*))
        discard <| Tactic.Integration.Projection.proveRequirements
          (.mvar (← Lean.Elab.Tactic.getMainGoal)) none
      unless binders.isEmpty do return .proved none
      let proof ← Tactic.ProofCarrier.cacheClosedProof
        "the conditions of the primitive on the interval" (← instantiateMVars goal)
      return .proved proof.constName?)
    fun error ↦ do
      if error.isInterrupt then throw error
      pure (.failed error.isRuntime)
  unless outcome matches .proved (some _) do saved.restore
  return outcome

/-- `#cas [integrate x in [a, b]] f`: the primitive `F` from `integrate?`, the value `F b - F a`
(a limit at an infinite endpoint), and `∫ x in a..b, f = v`,
`IntegrableOn (fun x ↦ f) (Set.Ioi a) ∧ ∫ x in Set.Ioi a, f = v`, the same over `Set.Iic b`, or
`Integrable (fun x ↦ f) ∧ ∫ x, f = v`, proved by `cas`. The conditions of the primitive that
do not contain `x` but contain a parameter become hypotheses of the theorem. An infinite endpoint
needs an integrand without parameters. -/
def logDefiniteIntegral (ref : Syntax) (x : TSyntax `ident)
    (lower upper : TSyntax `casIntegralEndpoint) (input : TSyntax `term) : CommandElabM Unit := do
  let ⟨reified₀, _⟩ ← scalarCoordinateInput input (some x.getId) ""
  let mut names := reified₀.names
  for endpoint in [lower, upper] do
    if let some value := endpointTerm? endpoint then
      names := (← parseWithLeading value names).names
  let reified ←
    if names == reified₀.names then pure reified₀
    else do
      let reparsed ← parseWithLeading input names
      pure { reparsed with surface.text? := reified₀.surface.text? }
  let coordinate ← coordinateAt input reified x.getId
  let a ← readEndpoint reified lower
  let b ← readEndpoint reified upper
  if (a matches .top) || (b matches .bot) then
    throwErrorAt ref "the lower endpoint is `∞` or the upper endpoint is `-∞`; write the \
      endpoints in increasing order, as in `[a, ∞]`, `[-∞, b]` or `[-∞, ∞]`"
  for endpoint in [a, b] do
    if let .finite point := endpoint then
      if Verified.Expr.containsVar coordinate point then
        throwErrorAt ref "an endpoint contains the integration coordinate '{renderName x.getId}'"
  let bounded := (a matches .finite _) && (b matches .finite _)
  let parameters := reified.names.filter (· != x.getId)
  unless bounded || parameters.isEmpty do
    throwErrorAt ref "an infinite endpoint needs an integrand in '{renderName x.getId}' alone, \
      without the parameters {renderNames parameters}"
  let rational := fun (endpoint : Endpoint reified.names.length) ↦
    match endpoint with
    | .finite value =>
        (IntegrationPlanner.Bioche.rationalValue? (Verified.Expr.Alg.normalize value)).isSome
    | _ => false
  let numeric :=
    if rational a && rational b then
      s!" For a numerical value use `#cas [nintegrate {renderName x.getId} in \
        [{surfaceText lower}, {surfaceText upper}]] {surfaceText input}`."
    else ""
  let provider? ← integrationFactorProvider?
  let some certificate := integrate? coordinate reified.expr provider?
    | let hint := factorProviderHint provider?.isSome coordinate reified.expr
      throwErrorAt ref "the checked integrator found no supported antiderivative in \
        coordinate '{renderName x.getId}', so the integral has no exact value here{hint}.\
        {numeric}"
  let primitive := certificate.candidate
  let raw := Verified.Expr.Alg.normalize
    (.sub (← primitiveAt reified coordinate primitive b)
      (← primitiveAt reified coordinate primitive a))
  let simplified := Verified.Expr.Alg.normalize (endpointValues raw)
  let values := if simplified == raw then [raw] else [simplified, raw]
  let requirements := certificate.requirements
  let parametric := fun (condition : Verified.Expr (Fin reified.names.length)) ↦
    !Verified.Expr.containsVar coordinate condition &&
      (List.finRange reified.names.length).any fun j ↦ Verified.Expr.containsVar j condition
  let assumed : Verified.Expr.ValidityRequirements (Fin reified.names.length) :=
    { nonzero := requirements.nonzero.filter parametric
      positive := requirements.positive.filter parametric }
  let mut hypotheses : List Term := []
  for condition in assumed.nonzero do
    hypotheses := hypotheses ++
      [← (FullSimplify.Condition.nonzero
        (FullSimplify.Form.ofExpr reified.names condition)).toSyntax]
  for condition in assumed.positive do
    hypotheses := hypotheses ++
      [← (FullSimplify.Condition.positive
        (FullSimplify.Form.ofExpr reified.names condition)).toSyntax]
  let xIdent := mkIdent x.getId
  let parameterNames := parameters.map mkIdent
  let hypothesisNames : List Ident :=
    (List.range hypotheses.length).map fun k ↦ mkIdent (Name.mkSimple s!"hcas{k}")
  let evidenceTerms : Array Term := hypothesisNames.toArray.map fun h ↦ ⟨h.raw⟩
  let mut closers : Array (TSyntax `tactic) := #[]
  match evidenceTerms.toList with
  | [] => closers := closers.push (← `(tactic| cas))
  | [h] => closers := closers.push (← `(tactic| cas using $h))
  | _ => closers := closers.push (← `(tactic| cas using [$evidenceTerms,*]))
  if bounded && evidenceTerms.size ≤ 1 then
    let function ← `(fun $xIdent:ident : ℝ ↦ $(← termOf reified.names primitive))
    match evidenceTerms.toList with
    | [h] => closers := closers.push (← `(tactic| cas [integrate primitive := $function using $h]))
    | _ => closers := closers.push (← `(tactic| cas [integrate primitive := $function]))
  let binders : Array Term := (parameterNames ++ hypothesisNames).toArray.map fun b ↦ ⟨b.raw⟩
  let endpointSyntax : Endpoint reified.names.length → CommandElabM (Option Term) := fun
    | .finite point => some <$> termOf reified.names point
    | _ => pure none
  let lowerTerm? ← endpointSyntax a
  let upperTerm? ← endpointSyntax b
  let integrand ← termOf reified.names reified.expr
  -- The attempts below prove these conditions only after certifying the primitive in the kernel,
  -- which can cost more than the declaration's heartbeats, so a failure on them comes first.
  if let (some lowerTerm, some upperTerm) := (lowerTerm?, upperTerm?) then
    let checked : Verified.Expr.ValidityRequirements (Fin reified.names.length) :=
      { nonzero := requirements.nonzero.filter (!parametric ·)
        positive := requirements.positive.filter (!parametric ·) }
    let mut conditions : List Term := []
    for condition in checked.nonzero do
      conditions := conditions ++
        [← (FullSimplify.Condition.nonzero
          (FullSimplify.Form.ofExpr reified.names condition)).toSyntax]
    for condition in checked.positive do
      conditions := conditions ++
        [← (FullSimplify.Condition.positive
          (FullSimplify.Form.ofExpr reified.names condition)).toSyntax]
    if let some last := conditions.getLast? then
      let conjunction ← conditions.dropLast.foldrM (fun c rest ↦ `($c ∧ $rest)) last
      let onInterval ←
        `(∀ $xIdent:ident ∈ Set.uIcc ($lowerTerm : ℝ) $upperTerm, $conjunction)
      let body ← hypotheses.foldrM (fun h statement ↦ `($h → $statement)) onInterval
      let statement ← parameterNames.foldrM (fun p statement ↦ `(∀ $p:ident : ℝ, $statement))
        body
      match ← liftTermElabM (checkConditions statement binders) with
      | .proved (some name) =>
          -- The attempt with the primitive need not prove the conditions again.
          let function ← `(fun $xIdent:ident : ℝ ↦ $(← termOf reified.names primitive))
          closers := closers.pop.push
            (← `(tactic| cas [integrate primitive := $function using $(mkIdent name)]))
      | .failed timedOut =>
        let shown := (renderConditions reified checked).getD "its conditions"
        let timedOut := if timedOut then " (the check ran out of heartbeats)" else ""
        throwErrorAt ref "`cas` did not prove the value {renderExpr reified simplified} of the \
          integral: it could not prove that the conditions of the primitive \
          {renderExpr reified primitive} hold on the interval ({shown}){timedOut}. Where they \
          fail, the difference of the primitive's values at the endpoints need not be the \
          integral.{numeric}"
      | _ => pure ()
  let mut attempts : Array (Verified.Expr (Fin reified.names.length) × Term × TSyntax `tactic) :=
    #[]
  for value in values do
    let valueTerm ← (FullSimplify.Form.ofExpr reified.names value).tidy.toSyntax
    let statement ← definiteStatement xIdent parameterNames hypotheses lowerTerm? upperTerm?
      integrand valueTerm
    for closer in closers do
      let tactic ← if binders.isEmpty then pure closer else `(tactic| (intro $binders*; $closer))
      attempts := attempts.push (value, statement, tactic)
  -- The kernel checks of an attempt get a quarter of `maxHeartbeats`, so that a proof whose kernel
  -- check is too large, such as that of the certificate of the primitive of `1 / (2 + cos x)`,
  -- ends in a refusal sooner; the first attempt that runs out of heartbeats ends the search.
  let budget := maxHeartbeats.get (← getOptions)
  let kernelBudget := if budget == 0 then 0 else max 1 (budget / 4)
  let outcome : Except (MessageData × Bool)
      (Verified.Expr (Fin reified.names.length) × String × MessageData) ← liftTermElabM do
    let mut failure : MessageData × Bool := (m!"no proof was attempted", false)
    for (value, statement, tactic) in attempts do
      match ← tryProve statement tactic kernelBudget with
      | .ok (type, proof) =>
          let step ← UncheckedExplanationStep.ofProof "Definite integral, proved by `cas`"
            (← mkExpectedTypeHint proof type)
          return .ok (value, toString (← ppExpr type), ← evidenceReportMessage #[step])
      | .error (message, timedOut) =>
          failure := (message, timedOut)
          if timedOut then break
    return .error failure
  match outcome with
  | .ok (value, statementText, evidence) =>
      logReport ref {
        domain := renderRealDomain reified.names
        input := reified.render
        inputType := "scalar ℝ"
        output := renderExpr reified value
        outputType := "scalar ℝ; definite integral"
        furtherResults :=
          #[("Theorem", statementText), ("Primitive", renderExpr reified primitive)]
        conditions? := renderConditions reified assumed
      } #[m!"Variables: {renderNames reified.names}", evidence]
  | .error (_, true) =>
      throwErrorAt ref "`cas` did not prove the value {renderExpr reified simplified} of the \
        integral: its proof ran out of heartbeats, `maxHeartbeats` ({budget} thousand) for the \
        elaboration of an attempt and a quarter of it for each kernel check; `set_option \
        maxHeartbeats` raises both.{numeric}"
  | .error (failure, false) =>
      throwErrorAt ref "`cas` did not prove the value {renderExpr reified simplified} of the \
        integral.{numeric} The last attempt failed with{indentD failure}"

elab_rules : command
  | `(#cas [integrate] $expr:term) => do
      unless ← Tactic.RouteRegistry.runCommandBackends `integrate (← getRef) do
        let ⟨reified, coordinate⟩ ← scalarCoordinateInput expr none
          "use [integrate x] to select the integration coordinate"
        logIntegral expr reified (reified.names.get coordinate) coordinate
  | `(#cas [integrate $name:ident] $expr:term) => do
      unless ← Tactic.RouteRegistry.runCommandBackends `integrate (← getRef) do
        let ⟨reified, coordinate⟩ ← scalarCoordinateInput expr (some name.getId) ""
        logIntegral expr reified name.getId coordinate
  | `(#cas [integrate $x:ident in [$a:casIntegralEndpoint, $b:casIntegralEndpoint]]
        $expr:term) =>
      logDefiniteIntegral expr x a b expr

end CAS.Command

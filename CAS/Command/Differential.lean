/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.Derivation
public meta import CAS.Calculus.Derivation
public import CAS.Calculus.Gradient
public meta import CAS.Calculus.Gradient
public import CAS.Command.Common
public import CAS.Command.Headline
public import CAS.ClosedForm.Pipeline.Configured

/-!
# Differential reports for `#cas`

`#cas [derive] e` (for an expression with one free variable or a unary lambda) and
`#cas [derive x] e` print a partial derivative with its domain conditions, and
`#cas [grad x, y, ...] e` prints the gradient; each logs an InfoView report. The report of a
partial derivative opens with the theorem about the printed terms,
`∀ x… : ℝ, conditions → HasDerivAt (fun x ↦ f) f' x`, and the gradient report with
`HasGradientAt` for the printed terms. The theorems behind the displayed derivative are
`displayDerivativeRoute_sound`, `fderiv_apply_single_eq_eval_displayDerivative` and
`hasDerivAt_of_displayRoute`.

## Implementation notes

The derivative is `Verified.Expr.diff`, recorded as the indexed rule tree `DiffDerivation` of
`CAS/Calculus/Derivation.lean`, which `DiffDerivation.build` constructs for every expression, so
no search is involved. The evidence has four steps: the tree computes `Expr.diff`
(`DiffDerivation.rawDerivative_eq_diff`), its unconditional normal form keeps the value
(`DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative`), a side-conditioned cleanup gives
the displayed form (`displayDerivativeRoute_sound`), and the displayed expression is the
derivative of the evaluation in the coordinate direction
(`fderiv_apply_single_eq_eval_displayDerivative`). `displayDerivativeRoute` takes the rational
canonical form `Alg.canonical` when it is the shortest and its obligations follow from the
validity requirements of the input, otherwise the cleanup `simplifySideClaimRoute` when it is
shorter, otherwise the simplified derivative itself; the conditions recorded by the chosen route
join the printed conditions.

The headline is transported by `hasDerivAt_of_displayRoute`, which rests on
`Verified.Expr.hasDerivAt_eval_add_smul_single`, with one kernel decision
(`Tactic.KernelReadBack.decideByKernel`) of the result and the conditions of the route. That
decision is about the chosen route itself (`displayRouteTerm`), so the kernel does not replay the
choice. The gradient reuses the scalar computation for each coordinate, adds the vector assembly
`closedGradient_eval_eq_gradient`, and transports its headline by
`hasGradientAt_of_closedGradient` of `CAS/Calculus/Gradient.lean` after one kernel decision of
the components.
-/

public meta section

namespace CAS.Command

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Tactic.Explanation

/-!
## Displayed derivatives

The printed derivative is the end of `displayDerivativeRoute`, a checked route that starts at the
unconditional normal form `DiffDerivation.simplifiedDerivative`.
-/

/-- Whether the obligation `d ≠ 0` is one of the validity requirements, follows from one (a
positivity requirement `0 < d`, or `0 < a` for `d = sqrt a`), or holds automatically. -/
def coveredByRequirements {ι : Type*} [DecidableEq ι]
    (requirements : Verified.Expr.ValidityRequirements ι) (d : Verified.Expr ι) : Bool :=
  requirements.nonzero.contains d || requirements.positive.contains d ||
    Verified.Expr.AutomaticSign.nonzero d ||
    match d with
    | .sqrt a => requirements.positive.contains a
    | _ => false

/-- The displayed derivative: the rational canonical form `Alg.canonical` when it is the
shortest and each of its recorded obligations is covered by the input's validity requirements,
so that it holds wherever the input is valid; otherwise the side-conditioned cleanup when it
shortens the derivative; otherwise the identity claim on the derivative. It needs `[Ord ι]`,
which orders the variables in the terms of `Alg.canonical`. -/
def displayDerivativeRoute {ι : Type*} [DecidableEq ι] [Ord ι]
    {coordinate : ι} {input output : Verified.Expr ι}
    (derivation : Verified.Expr.DiffDerivation coordinate input output) :
    Verified.Expr.SideClaimRoute ι :=
  let candidate :=
    Verified.Expr.simplifySideClaimRoute derivation.simplifiedDerivative
  let rational := Verified.Expr.Alg.canonical derivation.simplifiedDerivative
  if rational.rhs.nodeCount < candidate.rhs.nodeCount &&
      rational.rhs.nodeCount < derivation.simplifiedDerivative.nodeCount &&
      rational.nonzero.all (coveredByRequirements input.validityRequirements) then
    rational
  else if candidate.rhs.nodeCount < derivation.simplifiedDerivative.nodeCount then
    candidate
  else
    Verified.Expr.SideClaimRoute.exact derivation.simplifiedDerivative
      derivation.simplifiedDerivative fun _ ↦ rfl

/-- The display route starts at the simplified derivative of `derivation`. Like
`displayDerivativeRoute`, it needs `[Ord ι]`, which orders the variables. -/
theorem displayDerivativeRoute_lhs {ι : Type*} [DecidableEq ι] [Ord ι]
    {coordinate : ι} {input output : Verified.Expr ι}
    (derivation : Verified.Expr.DiffDerivation coordinate input output) :
    (displayDerivativeRoute derivation).lhs = derivation.simplifiedDerivative := by
  simp only [displayDerivativeRoute]
  split
  · rfl
  · split <;> rfl

/-- The displayed derivative has the value of the simplified derivative wherever the conditions
recorded by the display route hold. Like `displayDerivativeRoute`, it needs `[Ord ι]`, which
orders the variables. -/
theorem displayDerivativeRoute_sound {ι : Type*} [DecidableEq ι] [Ord ι]
    {coordinate : ι} {input output : Verified.Expr ι}
    (derivation : Verified.Expr.DiffDerivation coordinate input output) :
    ∀ ρ : ι → ℝ,
      Verified.Expr.Alg.SideHolds ρ (displayDerivativeRoute derivation).nonzero →
        (displayDerivativeRoute derivation).rhs.eval ρ =
          derivation.simplifiedDerivative.eval ρ := fun ρ hside ↦
  displayDerivativeRoute_lhs derivation ▸ (displayDerivativeRoute derivation).sound ρ hside

/-- The displayed expression equals the derivative of the input in the coordinate direction at a
point where the input is valid (`ValidAt`) and the conditions recorded by the display route
hold. -/
theorem fderiv_apply_single_eq_eval_displayDerivative {n : Nat}
    {coordinate : Fin n} {input output : Verified.Expr (Fin n)}
    (derivation : Verified.Expr.DiffDerivation coordinate input output) :
    ∀ (x : ℝ^n), input.ValidAt x →
      Verified.Expr.Alg.SideHolds x.ofLp (displayDerivativeRoute derivation).nonzero →
        fderiv ℝ (fun y : ℝ^n ↦ input.eval y.ofLp) x (EuclideanSpace.single coordinate 1) =
          (displayDerivativeRoute derivation).rhs.eval x.ofLp := fun x hvalid hside ↦
  (derivation.fderiv_apply_single_eq_eval_simplifiedDerivative x hvalid).trans
    (displayDerivativeRoute_sound derivation x.ofLp hside).symm

/-- A derivative of real terms from a checked derivation. Let `σ s` be the point whose
`coordinate` is `s` and whose other coordinates are fixed, `f s` the value of the input there and
`f'` the value at `σ t` of the result `D` of a route that starts at the simplified derivative
and records the conditions `N`. When the input is valid at `σ t` and the conditions hold there,
`f` has derivative `f'` at `t`. -/
theorem hasDerivAt_of_displayRoute {n : Nat} {coordinate : Fin n}
    {input output : Verified.Expr (Fin n)}
    (derivation : Verified.Expr.DiffDerivation coordinate input output)
    (route : Verified.Expr.SideClaimRoute (Fin n))
    (hlhs : route.lhs = derivation.simplifiedDerivative)
    {D : Verified.Expr (Fin n)} {N : List (Verified.Expr (Fin n))}
    (hroute : route.rhs = D ∧ route.nonzero = N)
    (σ : ℝ → Fin n → ℝ) (t : ℝ) (hσ : ∀ s, σ s = Function.update (σ t) coordinate s)
    {f : ℝ → ℝ} {f' : ℝ} (hf : ∀ s, input.eval (σ s) = f s) (hf' : D.eval (σ t) = f')
    (hvalid : input.ValidAt (σ t)) (hside : Verified.Expr.Alg.SideHolds (σ t) N) :
    HasDerivAt f f' t := by
  obtain ⟨x, hx⟩ : ∃ x : ℝ^n, x = WithLp.toLp 2 (Function.update (σ t) coordinate 0) :=
    ⟨_, rfl⟩
  have hline : ∀ s : ℝ,
      WithLp.ofLp (x + s • EuclideanSpace.single coordinate (1 : ℝ)) = σ s := by
    intro s
    funext j
    rw [hσ s, hx]
    by_cases hj : j = coordinate
    · rw [hj]
      simp
    · simp [hj]
  have hderiv : (input.diff coordinate).eval (σ t) = f' := by
    rw [← derivation.rawDerivative_eq_diff,
      ← derivation.eval_simplifiedDerivative_eq_rawDerivative, ← hlhs,
      ← route.sound (σ t) (by rw [hroute.2]; exact hside), hroute.1]
    exact hf'
  have key := Verified.Expr.hasDerivAt_eval_add_smul_single input x coordinate t
    (by simpa only [hline] using hvalid)
  simpa only [hline, hf, hderiv] using key

private def displayDerivativeRequirements {n : Nat}
    {coordinate : Fin n} {input output : Verified.Expr (Fin n)}
    (derivation : Verified.Expr.DiffDerivation coordinate input output) :
    Verified.Expr.ValidityRequirements (Fin n) :=
  let analytic := input.validityRequirements
  {
    nonzero := analytic.nonzero ++ (displayDerivativeRoute derivation).nonzero
    positive := analytic.positive
  }

/--
The four evidence steps, not yet validated, behind one displayed derivative: the rule tree
computes `Expr.diff` (`DiffDerivation.rawDerivative_eq_diff`), the unconditional normal form
keeps its value (`DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative`), the display route
keeps it under its conditions (`displayDerivativeRoute_sound`), and the displayed expression is
the derivative of the evaluation in the coordinate direction
(`fderiv_apply_single_eq_eval_displayDerivative`).
-/
def derivativeEvidence {n : Nat}
    (label : String) (coordinate : Fin n)
    (input : Verified.Expr (Fin n)) :
    MetaM (Array UncheckedExplanationStep) := do
  let inputTerm ← quoteVerifiedExpr input
  let coordinateTerm := Lean.toExpr coordinate
  let derivationTerm ←
    mkAppM ``Verified.Expr.DiffDerivation.build #[coordinateTerm, inputTerm]
  let rawProof ←
    mkAppM ``Verified.Expr.DiffDerivation.rawDerivative_eq_diff #[derivationTerm]
  let normalizationProof ←
    mkAppM ``Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      #[derivationTerm]
  let displayRouteProof ←
    mkAppM ``displayDerivativeRoute_sound #[derivationTerm]
  let semanticProof ←
    mkAppM ``fderiv_apply_single_eq_eval_displayDerivative #[derivationTerm]
  return #[
    ← proofStep s!"{label}: indexed rules compute Expr.diff"
      ``Verified.Expr.DiffDerivation.rawDerivative_eq_diff rawProof,
    ← proofStep s!"{label}: normalization preserves evaluation"
      ``Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      normalizationProof,
    ← proofStep s!"{label}: side-conditioned display normalization"
      ``displayDerivativeRoute_sound displayRouteProof,
    ← proofStep s!"{label}: analytic semantics of the displayed result"
      ``fderiv_apply_single_eq_eval_displayDerivative
      semanticProof
  ]

private def gradientAssemblyEvidence {n : Nat}
    (input : Verified.Expr (Fin n)) : MetaM UncheckedExplanationStep := do
  let inputTerm ← quoteVerifiedExpr input
  let proof :=
    mkAppN (.const ``Verified.Expr.closedGradient_eval_eq_gradient [])
      #[Lean.toExpr n, inputTerm]
  proofStep "Analytic gradient assembly"
    ``Verified.Expr.closedGradient_eval_eq_gradient proof

private def derivationMessageCore (reified : ReifiedExpr)
    {coordinate : Fin reified.names.length}
    {input output : Verified.Expr (Fin reified.names.length)}
    (derivation : Verified.Expr.DiffDerivation coordinate input output) : MessageData :=
  let ruleData := #[
    m!"input: {renderExpr reified input}",
    m!"raw derivative: {renderExpr reified output}",
    m!"representation: indexed DiffDerivation node"
  ]
  let children : Array MessageData :=
    match derivation with
    | .add left right | .mul left right | .sub left right | .div left right =>
        #[derivationMessageCore reified left, derivationMessageCore reified right]
    | .neg inner | .pow _ inner | .sin inner | .cos inner | .atan inner | .asin inner |
        .acos inner |
        .exp inner | .log inner | .sqrt inner =>
        #[derivationMessageCore reified inner]
    | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ =>
        #[]
    | .rpow base exponent =>
        #[derivationMessageCore reified base, derivationMessageCore reified exponent]
  computationNode derivation.ruleLabel (ruleData ++ children)

/--
Render the rule tree of a derivation from `node` down: each rule with its input, its raw
derivative and the trees of its operands.

The tree rendered is the indexed `DiffDerivation` itself, not a reconstruction from diagnostic
text; the evidence report checks its root theorem separately.
-/
def derivationMessage (reified : ReifiedExpr)
    {coordinate : Fin reified.names.length}
    (node : Verified.Expr.DiffDerivation.Packed coordinate) : MessageData :=
  derivationMessageCore reified node.derivation

/--
Render the computation of one partial derivative: the raw result of the rules, its unconditional
normal form, and the displayed result with the conditions the display route adds.

The rule tree of the differentiation (`derivationMessage`) is shown only when `verbose` is set,
as the commands do under the option `cas.verbose`.
-/
def derivativeComputation (reified : ReifiedExpr) (name : Name)
    {coordinate : Fin reified.names.length}
    {input : Verified.Expr (Fin reified.names.length)}
    (derivation :
      Verified.Expr.DiffDerivation coordinate input (input.diff coordinate))
    (verbose : Bool := false) :
    MessageData :=
  computationNode s!"Partial derivative in {renderName name}" #[
    computationNode "1. Apply symbolic differentiation rules" <|
      #[m!"raw result: {renderExpr reified derivation.rawDerivative}"] ++
        (if verbose then #[derivationMessage reified derivation.pack] else #[]),
    computationNode "2. Normalize the symbolic derivative unconditionally" #[
      m!"normalized result: {renderExpr reified derivation.simplifiedDerivative}"
    ],
    computationNode "3. Apply checked side-conditioned cleanup" #[
      m!"displayed result: {renderExpr reified (displayDerivativeRoute derivation).rhs}",
      m!"additional nonzero requirements: \
        {renderExprList reified (displayDerivativeRoute derivation).nonzero}"
    ]
  ]

/-- The route that `displayDerivativeRoute` selects, as a term the kernel evaluates, with the proof
that it starts at the simplified derivative. `displayDerivativeRoute` is a `meta` definition, so a
kernel decision names an exposed route with the same result and conditions, the cheapest first:
the identity claim, the side-conditioned cleanup, or the canonical form. -/
private def displayRouteTerm {n : Nat} {coordinate : Fin n}
    {input output : Verified.Expr (Fin n)}
    (derivation : Verified.Expr.DiffDerivation coordinate input output)
    (derivationTerm : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let route := displayDerivativeRoute derivation
  let simplified ← mkAppM ``Verified.Expr.DiffDerivation.simplifiedDerivative #[derivationTerm]
  if route.rhs == derivation.simplifiedDerivative && route.nonzero.isEmpty then
    let point ← mkArrow (quotedVariableType n) (mkConst ``Real)
    let proof ← withLocalDeclD `ρ point fun ρ ↦ do
      mkLambdaFVars #[ρ] (← mkEqRefl (← mkAppM ``Verified.Expr.eval #[ρ, simplified]))
    let steps := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Verified.Expr.PassInfo)
    let arguments := #[none, some simplified, some simplified, some proof, some steps]
    return (← mkAppOptM ``Verified.Expr.SideClaimRoute.exact arguments,
      ← mkAppOptM ``Verified.Expr.SideClaimRoute.exact_lhs arguments)
  let candidate := Verified.Expr.simplifySideClaimRoute derivation.simplifiedDerivative
  if route.rhs == candidate.rhs && route.nonzero == candidate.nonzero then
    return (← mkAppM ``Verified.Expr.simplifySideClaimRoute #[simplified],
      ← mkAppM ``Verified.Expr.simplifySideClaimRoute_lhs #[simplified])
  return (← mkAppM ``Verified.Expr.Alg.canonical #[simplified],
    ← mkAppM ``Verified.Expr.Alg.canonical_lhs #[simplified])

/-- The headline of a derivative report, `∀ x… : ℝ, conditions → HasDerivAt (fun x ↦ f) f' x`
about the printed input and displayed derivative, transported from the derivation by
`hasDerivAt_of_displayRoute` with one kernel decision of the displayed route. -/
private def derivativeHeadline (reified : ReifiedExpr) (coordinate : Fin reified.names.length) :
    TermElabM UncheckedExplanationStep := do
  let n := reified.names.length
  let derivation := Verified.Expr.DiffDerivation.build coordinate reified.expr
  let route := displayDerivativeRoute derivation
  let (idents, vars) := coordinateIdents reified
  let conditions ← conditionTerms vars (displayDerivativeRequirements derivation)
  let x := idents[coordinate.val]!
  let body ← `(HasDerivAt
    (fun ($x : ℝ) ↦ ($(← reified.inputTerm vars) : ℝ))
    ($(← exprTerm vars route.rhs reified.resultFunction?) : ℝ) $x)
  let statement ← realForallStatement idents conditions body
  headlineStep "Derivative of the input" ``hasDerivAt_of_displayRoute statement
      (n + conditions.size) fun locals conclusion ↦ do
    let arguments := conclusion.getAppArgs
    unless conclusion.isAppOf ``HasDerivAt && arguments.size ≥ 3 do
      throwError "the derivative headline is not a HasDerivAt statement"
    let f := arguments[arguments.size - 3]!
    let f' := arguments[arguments.size - 2]!
    let points := locals.extract 0 n
    let t := points[coordinate.val]!
    let input ← quoteVerifiedExpr reified.expr
    let derivationTerm ←
      mkAppM ``Verified.Expr.DiffDerivation.build #[Lean.toExpr coordinate, input]
    let (routeTerm, hlhs) ← displayRouteTerm derivation derivationTerm
    let result ← quoteVerifiedExpr route.rhs
    let nonzero ← quoteVerifiedList n route.nonzero
    let hroute ← Tactic.KernelReadBack.decideByKernel "#cas [derive]" (mkAnd
      (← mkEq (← mkAppM ``Verified.Expr.SideClaimRoute.rhs #[routeTerm]) result)
      (← mkEq (← mkAppM ``Verified.Expr.SideClaimRoute.nonzero #[routeTerm]) nonzero))
    let ρ ← Tactic.RealExpression.parameterVector points
    let line ← withLocalDeclD `s (mkConst ``Real) fun s ↦ do
      mkLambdaFVars #[s]
        (← Tactic.RealExpression.parameterVector (points.set! coordinate.val s))
    let hline ← headlineLine line (Lean.toExpr coordinate) t
    let hf ← withLocalDeclD `s (mkConst ``Real) fun s ↦ do
      mkLambdaFVars #[s] (← headlineBridge (line.beta #[s]) input (f.beta #[s]))
    let hvalid ← headlineConditions "#cas [derive]"
      (← mkAppM ``Verified.Expr.ValidAt #[ρ, input])
    let hside ← headlineConditions "#cas [derive]"
      (← mkAppM ``Verified.Expr.Alg.SideHolds #[ρ, nonzero])
    mkAppOptM ``hasDerivAt_of_displayRoute
      #[none, none, none, none, some derivationTerm, some routeTerm, some hlhs, none, none,
        some hroute, some line, some t, some hline, some f, some f',
        some hf, some (← headlineBridge ρ result f'), some hvalid, some hside]

/-- Log the report of one partial derivative: the displayed derivative with its conditions, the
computation, and the headline (when it is proved within its budget) followed by the evidence of
`derivativeEvidence`. Under `cas.suggest` the headline is also offered as an `example`. -/
def logDerivative (ref : Syntax) (reified : ReifiedExpr)
    (name : Name) (coordinate : Fin reified.names.length) : CommandElabM Unit := do
  let derivation := Verified.Expr.DiffDerivation.build coordinate reified.expr
  let route := displayDerivativeRoute derivation
  let result := route.rhs
  let requirements := displayDerivativeRequirements derivation
  let (report, statement?) ← liftTermElabM <|
    withHeadlines #[derivativeHeadline reified coordinate] fun headlines ↦ do
      evidenceReportMessage
        (← derivativeEvidence s!"Partial derivative in {renderName name}"
          coordinate reified.expr)
        (route.steps.map passMetadata).toArray headlines
  logReport ref {
    domain := renderRealDomain reified.names
    input := reified.render
    inputType := "scalar ℝ"
    output := renderExpr reified result
    outputType := "scalar ℝ"
    conditions? := renderConditions reified requirements
  } #[
    m!"Variables: {renderNames reified.names}",
    requirementsComputation reified "Analytic domain conditions" requirements,
    derivativeComputation reified name derivation (cas.verbose.get (← getOptions)),
    report
  ]
  offerExample statement?

/-- The headline of a gradient report, `∀ x… : ℝ, conditions → HasGradientAt (fun p ↦ f) g x`
about the printed input in the coordinates `p 0, p 1, …` of `EuclideanSpace ℝ (Fin n)` and the
printed components `g` at the point `x` of the variables, transported by
`Verified.Expr.hasGradientAt_of_closedGradient` with one kernel decision of the components. -/
private def gradientHeadline (reified : ReifiedExpr) : TermElabM UncheckedExplanationStep := do
  let n := reified.names.length
  let components := reified.expr.closedGradientList
  let (idents, vars) := coordinateIdents reified
  let conditions ← conditionTerms vars reified.expr.validityRequirements
  let p := mkIdent `p
  let numeral (k : Nat) : TSyntax `term := ⟨Syntax.mkNumLit (toString k)⟩
  let coordinates ← (List.finRange n).toArray.mapM fun i ↦ `($p $(numeral i.val))
  let input ← reified.inputTerm fun i ↦ coordinates[i.val]!
  let gradient ← components.toArray.mapM (exprTerm vars · reified.resultFunction?)
  let point : Array (TSyntax `term) := idents.map fun ident ↦ ⟨ident.raw⟩
  let body ← `(HasGradientAt (fun ($p : EuclideanSpace ℝ (Fin $(numeral n))) ↦ ($input : ℝ))
    (WithLp.toLp 2 ![$gradient,*]) (WithLp.toLp 2 ![$point,*]))
  let statement ← realForallStatement idents conditions body
  headlineStep "Gradient of the input" ``Verified.Expr.hasGradientAt_of_closedGradient statement
      (n + conditions.size) fun locals conclusion ↦ do
    let arguments := conclusion.getAppArgs
    unless conclusion.isAppOf ``HasGradientAt && arguments.size ≥ 3 do
      throwError "the gradient headline is not a HasGradientAt statement"
    let f := arguments[arguments.size - 3]!
    let g := arguments[arguments.size - 2]!.appArg!
    let ρ ← Tactic.RealExpression.parameterVector (locals.extract 0 n)
    let input ← quoteVerifiedExpr reified.expr
    let G ← Tactic.RealExpression.vectorLiteral
      (mkApp (mkConst ``Verified.Expr [Level.zero]) (quotedVariableType n))
      (← components.toArray.mapM fun component ↦ quoteVerifiedExpr component)
    let hG ← Tactic.KernelReadBack.decideByKernel "#cas [grad]" (←
      withLocalDeclD `i (quotedVariableType n) fun i ↦ do
        mkForallFVars #[i]
          (← mkEq (← mkAppM ``Verified.Expr.closedGradient #[input, i]) (mkApp G i)))
    let hf ← withLocalDeclD `y (← inferType f).bindingDomain! fun y ↦ do
      mkLambdaFVars #[y] (← headlineBridge (← mkAppM ``WithLp.ofLp #[y]) input (f.beta #[y]))
    let hvalid ← headlineConditions "#cas [grad]"
      (← mkAppM ``Verified.Expr.ValidAt #[ρ, input])
    mkAppOptM ``Verified.Expr.hasGradientAt_of_closedGradient
      #[none, some input, some G, some hG, some f, some hf, some ρ, some g,
        some (← headlineBridgeEntries n ρ G g), some hvalid]

/-- Log the report of the gradient in the order of the variables: the components with their
computations, and the headline (when it is proved within its budget) followed by the evidence of
each component and the assembly `closedGradient_eval_eq_gradient`. Under `cas.suggest` the
headline is also offered as an `example`. -/
def logGradient (ref : Syntax) (reified : ReifiedExpr) : CommandElabM Unit := do
  let coordinates := List.finRange reified.names.length
  let result := reified.expr.closedGradientList
  let verbose := cas.verbose.get (← getOptions)
  let components := coordinates.map fun coordinate ↦
    let name := reified.names.get coordinate
    let derivation := Verified.Expr.DiffDerivation.build coordinate reified.expr
    computationNode s!"Gradient component ∂_{renderName name}" #[
      m!"Output: {renderExpr reified derivation.simplifiedDerivative}",
      derivativeComputation reified name derivation verbose
    ]
  let (report, statement?) ← liftTermElabM <|
    withHeadlines #[gradientHeadline reified] fun headlines ↦ do
      let mut steps := #[]
      for coordinate in coordinates do
        let name := reified.names.get coordinate
        steps := steps ++
          (← derivativeEvidence s!"Gradient component ∂_{renderName name}"
            coordinate reified.expr)
      steps := steps.push (← gradientAssemblyEvidence reified.expr)
      evidenceReportMessage steps (validated := headlines)
  let requirements := reified.expr.validityRequirements
  logReport ref {
    domain := renderRealDomain reified.names
    input := reified.render
    inputType := "scalar ℝ"
    output := s!"({renderExprList reified result})"
    outputType :=
      s!"vector ℝ^{reified.names.length}; order {renderNames reified.names}"
    conditions? := renderConditions reified requirements
  } #[
    m!"Variables and component order: {renderNames reified.names}",
    requirementsComputation reified "Analytic domain conditions" requirements,
    computationNode "Checked gradient computation" components.toArray,
    report
  ]
  offerExample statement?

end CAS.Command

namespace CAS.Command

open Lean Elab Command

/-- `#cas [derive] e` differentiates an expression with exactly one variable, or a lambda
`fun x ↦ e`, in that variable; see `#cas [derive x]`. An expression with several variables is
refused with a pointer to `#cas [derive x]` and `#cas [grad x, y]`.
-/
syntax (name := casUnivariateDerivativeCommand) "#cas" "[" &"derive" "]" term : command

/-- `#cas [derive x] e` differentiates `e` with respect to `x` and prints the derivative with the
conditions under which it holds; the other variables of `e` are parameters.

## Theorem
For the variables `x₁, …, xₙ` of `e`, the printed derivative `e'` and the checked conditions
`c₁, …, cₖ`, which the `Conditions` line prints in its display form, the first checked step
proves `∀ x₁ … xₙ : ℝ, c₁ → … → cₖ → HasDerivAt (fun x ↦ e) e' x` about Mathlib's real functions,
such as `∀ (x : ℝ), 0 < 2 * x + 2 → HasDerivAt (fun x ↦ √(2 * x + 2)) (1 / √(2 * x + 2)) x` for
`#cas [derive x] (sqrt (2 * x + 2))`, whose `Conditions` line reads `x + 1 > 0`. A square root
contributes `0 < a` and a quotient `d ≠ 0` to the conditions. The lemma
`CAS.Command.hasDerivAt_of_displayRoute` transports it from the checked derivation; the statement
for the internal expression syntax,
`fderiv ℝ (fun y ↦ eval y e) p (EuclideanSpace.single i 1) = eval p e'`
(`CAS.Command.fderiv_apply_single_eq_eval_displayDerivative`), follows it. The first step is shown
when its proof succeeds within its own budget of `maxHeartbeats` heartbeats; otherwise the report
keeps only the internal statement. The tactic `cas` proves the same `HasDerivAt` goals.

## Conditions and limits
The functions are `abs`, `sin`, `cos`, `tan`, `sinh`, `cosh`, `tanh`, `atan`, `asin`, `acos`,
`exp`, `log` and `sqrt`, with `+`, `-`, `*`, `/` and powers; a power with a variable exponent is
a real power. The validity conditions of `e`, such as `x + 1 > 0` for `sqrt (2 * x + 2)`, and the
conditions recorded by the simplification of the derivative are printed as conditions. A lambda
`fun t ↦ e` is differentiated in its parameter, which must be the named variable.

## Options
Under `set_option cas.verbose true` the details also show the tree of differentiation
rules, each rule with its input and its raw derivative.
Under `set_option cas.suggest true` the report also offers the first checked step above as an
`example` to paste in place of the command, when the binders and the type of that example,
elaborated where the command is with the variables of its section, are the proposition of the step
up to unfolding instances, and the whole example elaborates there without errors to a declaration
of that proposition with no `sorry` (`cas.suggest`).

## Examples
```lean
#cas [derive x] (x ^ 2 * sin x)
```
```output
Output (scalar ℝ): x*(2*sin(x) + x*cos(x))
```
```lean
#cas [derive x] (sqrt (2 * x + 2))
```
```output
Output (scalar ℝ): 1/sqrt(2*x + 2)
Conditions: x + 1 > 0
```
```lean
#cas [derive x] (sin (x * y))
```
```output
Output (scalar ℝ): cos(x*y)*y
```

## In a proof
```lean
theorem derive_product (x : ℝ) :
    HasDerivAt (fun x ↦ x ^ 2 * Real.sin x) (2 * x * Real.sin x + x ^ 2 * Real.cos x) x := by
  cas
```

## See also
Mathematica `D`, SymPy `diff`. The modes `grad`, `integrate` and `series`, and the tactic `cas`,
which proves `HasDerivAt` goals.

## Possible issues
```lean
#cas [derive x] (gamma x)
```
```output
unsupported symbolic function 'gamma'; expected abs, sin, cos, tan, sinh, cosh, tanh,
atan/arctan, asin/arcsin, acos/arccos, exp, log, or sqrt
```
Only the listed functions are differentiated.
```lean
#cas [derive x] (fun t : ℝ ↦ t ^ 2)
```
```output
coordinate 'x' does not match the function parameter 't'; use the parameter name or omit the
coordinate
```
Name the parameter of the lambda, `#cas [derive t]`, or write `#cas [derive]`.
-/
syntax (name := casDerivativeCommand) "#cas" "[" &"derive" ident "]" term : command

/-- `#cas [grad x, y, …] e` computes the gradient of `e` in the listed variables, in that order, and
prints it as a vector.

## Theorem
For the variables `x₁, …, xₙ` of `e`, the printed components `g₁, …, gₙ` and the checked
conditions `c₁, …, cₖ`, which the `Conditions` line prints in its display form, the first checked
step proves
`∀ x₁ … xₙ : ℝ, c₁ → … → cₖ → HasGradientAt (fun p ↦ e) !₂[g₁, …, gₙ] !₂[x₁, …, xₙ]` about
Mathlib's real functions, with `e` written in the coordinates `p.ofLp 0, …` of
`EuclideanSpace ℝ (Fin n)`, such as
`∀ (x y : ℝ), HasGradientAt (fun p ↦ p.ofLp 0 * p.ofLp 1) !₂[y, x] !₂[x, y]` for
`#cas [grad x, y] (x * y)`. The lemma `CAS.Verified.Expr.hasGradientAt_of_closedGradient`
transports it from the symbolic gradient, fixed by one kernel decision. The first step is shown
when its proof succeeds within its own budget of `maxHeartbeats` heartbeats. Each component is
also proved as by `#cas [derive x]`, and the vector of the components is
`gradient (fun y ↦ eval y e) p`, Mathlib's gradient of the evaluation of `e` in the internal
expression syntax, at every point `p` of `ℝ^n` where `e` satisfies `CAS.Verified.Expr.ValidAt`:
every divisor and every argument of `log` is nonzero, every argument of `sqrt` and every base of
a real power is positive, and no argument of `asin` or `acos` is `1` or `-1`
(`CAS.Verified.Expr.closedGradient_eval_eq_gradient`).

## Conditions and limits
Every variable of `e` must be listed. The functions are those of `#cas [derive x]`, and the
conditions are the validity conditions of `e`.

## Options
Under `set_option cas.verbose true` the details of each component also show the tree of
differentiation rules, as for `#cas [derive x]`.

## Examples
```lean
#cas [grad x, y] (x ^ 2 * y + y ^ 3)
```
```output
Output (vector ℝ^2; order x, y): (2*x*y, x^2 + 3*y^2)
```
```lean
#cas [grad x, y] (sin (x * y))
```
```output
Output (vector ℝ^2; order x, y): (cos(x*y)*y, cos(x*y)*x)
```

## In a proof
```lean
theorem grad_first_component (x y : ℝ) :
    HasDerivAt (fun x ↦ x ^ 2 * y + y ^ 3) (2 * x * y) x := by
  cas
```

## See also
Mathematica `Grad`, SymPy `derive_by_array`. The modes `derive` and `minimize`.

## Possible issues
```lean
#cas [grad x] (x * y)
```
```output
expression contains undeclared variables: y
```
List every variable of `e`; a variable that should stay a parameter needs `#cas [derive x]`.
-/
syntax (name := casGradientCommand) "#cas" "[" &"grad" ident,* "]" term : command

elab_rules : command
  | `(#cas [derive] $expr:term) => do
      let ⟨reified, coordinate⟩ ← scalarCoordinateInput expr none
        "use [derive x] for a partial derivative or [grad x, y] for a gradient"
      logDerivative expr reified (reified.names.get coordinate) coordinate
  | `(#cas [derive $name:ident] $expr:term) => do
      let ⟨reified, coordinate⟩ ← scalarCoordinateInput expr (some name.getId) ""
      logDerivative expr reified name.getId coordinate
  | `(#cas [grad $names:ident,*] $expr:term) => do
      let declared := names.getElems.toList.map TSyntax.getId
      let reified ← parseExact expr declared
      logGradient expr reified

end CAS.Command

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.CEGA.ExpressionSyntax
public meta import CAS.CEGA.ExpressionSyntax

public import CAS.CEGA.Elaboration
public meta import CAS.CEGA.Elaboration
public import CAS.Command.Explanation
public import CAS.Command.Headline
public import CAS.Command.Report
public import CAS.Tactic.BoxInequality

/-!
# The `enclose` mode of the `#cas` command

`#cas (cfg) [enclose x in [a, b], ...] e` certifies an interval with exact rational endpoints
that contains every value of `e` on the box of its bindings, and `#cas (cfg) [enclose] e` one
that contains the value of a closed real expression. The report also reads three bounds off the
interval: the upper bound, the bound on the absolute value, and the midpoint with its radius. Each
of the four is a kernel-checked proposition with its own projection theorem. With
`(depth := n)` in the configuration, the query first refines the box by checked subdivision to
depth `n`.

## Implementation notes

The query is the one the `cega` tactics run with `CEGA.Elaboration.runBoxQuery`, here through
`CEGA.Elaboration.runEncloseViews` (see `CAS/CEGA/Elaboration.lean`); when no route succeeds, the
error is a search diagnostic. The kernel checks one theorem, the conjunction of the four views, so
the interval is evaluated once, and the proof of each view is a projection of that theorem,
validated as evidence with the projection theorem of its mode (`BoxQueryMode.soundTheorem`). The
route steps of the local enclosures are listed as planner metadata, not as proof.

The checked evidence opens with the four views stated about the input as the report prints it,
with the bounds of the preview: `∀ x ∈ Set.Icc a b, lo ≤ f ∧ f ≤ hi`, then `f ≤ u`, `|f| ≤ m` and
`|f - c| ≤ r`, where the radius `r` also covers the rounding of the center `c`. Each is
transported from the checked proof of its view by a lemma of `CAS.Tactic.BoxInequality`
(`mem_of_enclosedOn_box`, `le_of_boundOn_box`, `abs_le_of_boundOn_abs_box` and
`abs_sub_le_of_approxOn_box`), as the `cega` tactic transports a certificate to an ordinary
inequality, so these theorems add no kernel evaluation to the report.
-/

public meta section

namespace CAS.Command.CEGA

open CAS.Verified
open CAS.Certificate
open CAS.Continuum
open CAS.CEGA
open CAS.CEGA.Elaboration
open CAS.Continuum.RationalInterval
open CAS.Tactic.Explanation
open CAS.Command.InfoView

open Lean Elab Command Meta
open CAS

private def routeStepLabel (step : Lean.Expr) : MetaM String := do
  let reduced ← kernelWhnf step
  match reduced with
  | .const ``RouteStep.exactNormalization _ => return "exact normalization"
  | .const ``RouteStep.affineArithmetic _ => return "affine arithmetic"
  | .const ``RouteStep.boxSubdivision _ => return "checked box subdivision"
  | .const ``RouteStep.monotoneIncreasingRange _ =>
      return "increasing endpoint range"
  | .const ``RouteStep.monotoneDecreasingRange _ =>
      return "decreasing endpoint range"
  | .const ``RouteStep.centeredForm _ => return "centered mean-value form"
  | .const ``RouteStep.variableLowerBound _ => return "variable lower bound"
  | .const ``RouteStep.productLowerBound _ => return "product lower bound"
  | .const ``RouteStep.squareLowerBound _ => return "square lower bound"
  | .const ``RouteStep.powerLowerBound _ => return "power lower bound"
  | .const ``RouteStep.intervalLowerBound _ => return "interval lower bound"
  | .const ``RouteStep.sqrtRange _ => return "square-root range"
  | .const ``RouteStep.atanRange _ => return "arctangent range"
  | .const ``RouteStep.asinRange _ => return "arcsine range"
  | .const ``RouteStep.acosRange _ => return "arccosine range"
  | .const ``RouteStep.logRange _ => return "logarithm range"
  | .const ``RouteStep.expRange _ => return "exponential range"
  | .const ``RouteStep.hyperbolicRange _ => return "correlated hyperbolic range"
  | .const ``RouteStep.reciprocalPositiveRange _ =>
      return "positive reciprocal range"
  | .const ``RouteStep.reciprocalNegativeRange _ =>
      return "negative reciprocal range"
  | _ => return "unknown route step"

private def routeStepLabelsWithFuel :
    Nat → Lean.Expr → MetaM (Array String)
  | 0, _ =>
      return #["route-step report exceeded its structural recursion bound"]
  | fuel + 1, steps => do
      let reduced ← kernelWhnf steps
      if reduced.isAppOfArity ``List.nil 1 then
        return #[]
      if reduced.isAppOfArity ``List.cons 3 then
        let arguments := reduced.getAppArgs
        let label ← routeStepLabel arguments[1]!
        return #[label] ++ (← routeStepLabelsWithFuel fuel arguments[2]!)
      return #["unknown route step"]

/-- The labels of the route steps in `steps`, the step list of a CEGA query, read by kernel
weak-head reduction for the planner metadata of the report. At most 1024 steps are read; at that
bound the list ends with a label saying so. -/
private def routeStepLabels (steps : Lean.Expr) : MetaM (Array String) :=
  routeStepLabelsWithFuel 1024 steps

private def viewLabel : BoxQueryMode → String
  | .enclose => "Certified enclosure"
  | .bound => "Certified upper bound"
  | .absBound => "Certified absolute bound"
  | .approx => "Certified center and radius"

private def validateViewEvidence (view : EncloseView) : MetaM CheckedExplanationStep := do
  let proposition ← inferType view.proof
  UncheckedExplanationStep.validate {
    label := viewLabel view.mode
    proposition
    proof := view.proof
    theoremName? := some view.mode.soundTheorem
  }

private def plannerMetadata
    (steps : Array String) : Array PlannerExplanationStep :=
  let labels := steps.foldl
    (fun labels step ↦ if labels.contains step then labels else labels.push step) #[]
  labels.map fun label ↦
    let count := steps.foldl (fun count step ↦ if step = label then count + 1 else count) 0
    { label
      status := .succeeded
      detail := if count = 1 then "" else s!"used by {count} local enclosure routes" }

private def renderInterval (binding : BoxBinding) : String :=
  s!"[{renderRational binding.interval.lo}, {renderRational binding.interval.hi}]"

private def renderBinding (binding : BoxBinding) : String :=
  s!"{renderName binding.coordinate} ∈ {renderInterval binding}"

private def renderBox (bindings : List BoxBinding) : String :=
  ", ".intercalate (bindings.map renderBinding)

private def renderCoordinates (bindings : List BoxBinding) : String :=
  ", ".intercalate <| bindings.map fun binding ↦
    renderName binding.coordinate

private def renderAmbientSpace (dimension : Nat) : String :=
  if dimension = 1 then "ℝ" else s!"ℝ^{dimension}"

/-- Decimal places of the preview, `6` unless a digit count is requested. -/
private def previewPlaces (precision : Precision) : Nat := precision.digits.getD 6

private def renderScaledDecimal (places : Nat) (scaled : Int) : String :=
  let scale := 10 ^ places
  let magnitude := scaled.natAbs
  let whole := magnitude / scale
  let fractional := toString (magnitude % scale)
  let padding := String.ofList <| List.replicate (places - fractional.length) '0'
  let sign := if scaled < 0 then "-" else ""
  s!"{sign}{whole}.{padding}{fractional}"

private def exactEndpointIsCompact (value : ℚ) : Bool :=
  (renderRational value).length ≤ 24

private def renderLowerPreview (places : Nat) (value : ℚ) : String :=
  if exactEndpointIsCompact value then
    renderRational value
  else
    renderScaledDecimal places <| Rat.floor (value * ((10 ^ places : ℕ) : ℚ))

private def renderUpperPreview (places : Nat) (value : ℚ) : String :=
  if exactEndpointIsCompact value then
    renderRational value
  else
    renderScaledDecimal places <| Rat.ceil (value * ((10 ^ places : ℕ) : ℚ))

private def renderCenterPreview (places : Nat) (value : ℚ) : String :=
  if exactEndpointIsCompact value then
    renderRational value
  else
    "≈" ++ renderScaledDecimal places (Rat.floor (value * ((10 ^ places : ℕ) : ℚ)))

/-- The center of a center-and-radius view as the report states it: the center itself when it is
compact, and otherwise the center rounded down to `places` decimals, as the preview prints it. -/
private def statedCenter (places : Nat) (center : ℚ) : ℚ :=
  if exactEndpointIsCompact center then center
  else (Rat.floor (center * ((10 ^ places : ℕ) : ℚ)) : ℚ) / ((10 ^ places : ℕ) : ℚ)

/-- The radius of a center-and-radius view widened by the rounding of its center, so that
`|e - c| ≤ r` holds for the stated center `c` and this radius `r`. The headline states this radius
as `statedValue` states a value, exactly when it is compact and otherwise rounded up to `places`
decimals. The preview (`renderView`) prints it the same way when the center is compact; when the
center is rounded, it prints the radius rounded up to `places` decimals even when the radius is
compact, so the headline can state `1/3` where the preview prints `0.333334`. -/
private def widenedRadius (places : Nat) (center radius : ℚ) : ℚ :=
  radius + (center - statedCenter places center)

/-- The label, the decimal preview and the exact text of one view. The preview of a center and a
radius prints the radius widened by the rounding of the center (`widenedRadius`). When the center
is rounded, the radius is printed to the same decimal places and rounded up, as in
`≈0.997502 ± 0.002498`. -/
private def renderView (places : Nat) : BoxQueryDisplay ℚ → String × String × String
  | .enclosure lo hi =>
      ("Output", s!"[{renderLowerPreview places lo}, {renderUpperPreview places hi}]",
        s!"[{renderRational lo}, {renderRational hi}]")
  | .upperBound upper =>
      ("Upper bound", renderUpperPreview places upper, renderRational upper)
  | .absoluteBound upper =>
      ("Absolute bound", renderUpperPreview places upper, renderRational upper)
  | .midpointApprox center radius =>
      let widened := widenedRadius places center radius
      let shownRadius :=
        if exactEndpointIsCompact center then renderUpperPreview places widened
        else renderScaledDecimal places <| Rat.ceil (widened * ((10 ^ places : ℕ) : ℚ))
      ("Center and radius", s!"{renderCenterPreview places center} ± {shownRadius}",
        s!"{renderRational center} ± {renderRational radius}")

/-! ## Headline theorems -/

/-- The rational `q` as real term syntax: `n`, `-n`, `n / d` or `-n / d`. -/
private def exactSyntax (q : ℚ) : TermElabM (TSyntax `term) := do
  let numerator : TSyntax `term := ⟨Syntax.mkNumLit (toString q.num.natAbs)⟩
  let signed ← if q.num < 0 then `(-$numerator) else pure numerator
  if q.den = 1 then
    return signed
  let denominator : TSyntax `term := ⟨Syntax.mkNumLit (toString q.den)⟩
  `($signed / $denominator)

/-- A value of a view as a headline states it: the exact rational when it is compact, and
otherwise the rational rounded to `places` decimals, down when `down` and up otherwise, as a
decimal literal such as `0.544012`: the value that the preview prints. -/
private def statedValue (places : Nat) (down : Bool) (q : ℚ) : TermElabM (TSyntax `term) := do
  if exactEndpointIsCompact q then
    return ← exactSyntax q
  let scale : ℚ := ((10 ^ places : ℕ) : ℚ)
  let scaled := if down then Rat.floor (q * scale) else Rat.ceil (q * scale)
  let literal : TSyntax `term :=
    ⟨Syntax.mkScientificLit (renderScaledDecimal places scaled.natAbs)⟩
  if scaled < 0 then `(-$literal) else pure literal

/-- A proof of the closed comparison `goal` by `norm_num`: a stated value against a certified one,
or an endpoint written in a headline against the endpoint of the box. -/
private def comparisonProof (goal : Lean.Expr) : MetaM Lean.Expr := do
  let proof ← mkFreshExprSyntheticOpaqueMVar goal
  let remaining ← Tactic.KernelReadBack.withSuppressedMessagesMeta <|
    Tactic.KernelReadBack.runTacticOnGoal proof.mvarId! (← `(tactic| norm_num))
  unless remaining.isEmpty do
    throwError "the stated value does not follow from the certified one{indentExpr goal}"
  instantiateMVars proof

/-- From the hypothesis `x ∈ Set.Icc a b` of a headline, the membership
`((lo : ℚ) : ℝ) ≤ x ∧ x ≤ ((hi : ℚ) : ℝ)` of `x` in the interval of the box, with the written
endpoints compared with those of the interval by `norm_num`. -/
private def coordinateFact (interval : RationalInterval) (coordinate hypothesis : Lean.Expr) :
    MetaM Lean.Expr := do
  let type := (← instantiateMVars (← inferType hypothesis)).consumeMData
  let some set := type.getAppArgs.find? (·.isAppOfArity ``Set.Icc 4)
    | throwError "the headline hypothesis{indentExpr type}\nis not a membership in `Set.Icc`"
  let (lower, upper) := (set.getArg! 2, set.getArg! 3)
  let written ← mkExpectedTypeHint hypothesis
    (mkAnd (← mkAppM ``LE.le #[lower, coordinate]) (← mkAppM ``LE.le #[coordinate, upper]))
  let castLower ← mkAppOptM ``Rat.cast
    #[some (mkConst ``Real), none, some (Lean.toExpr interval.lo)]
  let castUpper ← mkAppOptM ``Rat.cast
    #[some (mkConst ``Real), none, some (Lean.toExpr interval.hi)]
  let lowerProof ← mkAppM ``le_trans #[← comparisonProof (← mkAppM ``LE.le #[castLower, lower]),
    ← mkAppM ``And.left #[written]]
  let upperProof ← mkAppM ``le_trans #[← mkAppM ``And.right #[written],
    ← comparisonProof (← mkAppM ``LE.le #[upper, castUpper])]
  mkAppM ``And.intro #[lowerProof, upperProof]

/-- A proof of `goal`, the membership `∀ i, (box i).MemReal (ρ i)` of the variables of a headline
in the box of the query, from the facts `coordinateFact` about each variable, by the script of the
`cega` tactic route. -/
private def boxMembership (goal : Lean.Expr) (facts : Array Lean.Expr) : MetaM Lean.Expr := do
  let proof ← mkFreshExprSyntheticOpaqueMVar goal
  let mut hypotheses : Array Hypothesis := #[]
  for fact in facts do
    hypotheses := hypotheses.push {
      userName := Name.mkSimple s!"hcasBox{hypotheses.size}"
      type := ← inferType fact
      value := fact
    }
  let (_, membership) ← proof.mvarId!.assertHypotheses hypotheses
  let remaining ← Tactic.KernelReadBack.withSuppressedMessagesMeta <|
    Tactic.KernelReadBack.runTacticOnGoal membership (← `(tactic|
      (intro i
       fin_cases i <;>
         first
           | assumption
           | (simp only [CAS.Continuum.RationalInterval.MemReal,
                CAS.Continuum.RationalInterval.ofBounds, List.get,
                Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
                Matrix.head_cons, Matrix.cons_val_succ, Fin.isValue, Fin.zero_eta,
                Fin.mk_one, Fin.reduceFinMk] at *
              assumption))))
  unless remaining.isEmpty do
    throwError "the variables of the headline were not placed in the box of the query"
  instantiateMVars proof

/-- Prove `conclusion`, the conclusion of a headline about the variables `coordinates` with the
hypotheses `hypotheses : xₖ ∈ Set.Icc aₖ bₖ`, by the transport lemma `lemmaName` from the checked
proof `certificate` of a view on `box`, as the `cega` tactic route closes an ordinary inequality:
the conclusion of the lemma is unified with the headline's, the evaluation of the reflected input
is `headlineBridge`, and the comparisons of the stated values with the certified ones are proved
by `norm_num`. -/
private def transportView (lemmaName : Name) (certificate : Lean.Expr)
    (box : List RationalInterval) (coordinates hypotheses : Array Lean.Expr)
    (conclusion : Lean.Expr) : MetaM Lean.Expr := do
  let lemmaConstant ← mkConstWithFreshMVarLevels lemmaName
  let (arguments, binderInfos, lemmaConclusion) ←
    forallMetaTelescopeReducing (← inferType lemmaConstant)
  let explicitArguments := (arguments.zip binderInfos).filterMap fun (argument, info) ↦
    if info.isExplicit then some argument else none
  let #[certificateArgument, vectorArgument, membership, evaluation] :=
      explicitArguments.extract 0 4
    | throwError "{lemmaName} is not a transport lemma of a box query"
  let ρ ← Tactic.RealExpression.parameterVector coordinates
  unless ← isDefEq certificateArgument certificate do
    throwError "the checked view does not have the shape of {lemmaName}"
  unless ← isDefEq vectorArgument ρ do
    throwError "the variables of the headline do not fit {lemmaName}"
  unless ← isDefEq lemmaConclusion conclusion do
    throwError "{lemmaName} does not conclude the headline{indentExpr conclusion}"
  let facts ← (box.toArray.zip (coordinates.zip hypotheses)).mapM
    fun (interval, coordinate, hypothesis) ↦ coordinateFact interval coordinate hypothesis
  let membershipProof ← boxMembership (← instantiateMVars (← inferType membership)) facts
  let some (_, value, term) := (← instantiateMVars (← inferType evaluation)).eq?
    | throwError "{lemmaName} has no evaluation hypothesis"
  let evaluationProof ← headlineBridge ρ value.appArg! term
  unless (← isDefEq membership membershipProof) && (← isDefEq evaluation evaluationProof) do
    throwError "the box membership or the evaluation does not fit {lemmaName}"
  for comparison in explicitArguments.extract 4 explicitArguments.size do
    let proof ← comparisonProof (← instantiateMVars (← inferType comparison))
    unless ← isDefEq comparison proof do
      throwError "a comparison with the certified value does not fit {lemmaName}"
  instantiateMVars (mkAppN lemmaConstant arguments)

/-- The label, the transport lemma and the conclusion of the headline of a view about the input
term `input`, with the values of the view as `statedValue` states them. -/
private def viewStatement (places : Nat) (input : TSyntax `term) :
    BoxQueryDisplay ℚ → TermElabM (String × Name × TSyntax `term)
  | .enclosure lo hi => do
      let lower ← statedValue places true lo
      let upper ← statedValue places false hi
      return ("Enclosure of the input", ``CAS.Tactic.BoxInequality.mem_of_enclosedOn_box,
        ← `(($lower : ℝ) ≤ ($input : ℝ) ∧ ($input : ℝ) ≤ ($upper : ℝ)))
  | .upperBound upper => do
      let upper ← statedValue places false upper
      return ("Upper bound of the input", ``CAS.Tactic.BoxInequality.le_of_boundOn_box,
        ← `(($input : ℝ) ≤ ($upper : ℝ)))
  | .absoluteBound bound => do
      let bound ← statedValue places false bound
      return ("Absolute bound of the input", ``CAS.Tactic.BoxInequality.abs_le_of_boundOn_abs_box,
        ← `(_root_.abs ($input : ℝ) ≤ ($bound : ℝ)))
  | .midpointApprox center radius => do
      let centerTerm ← statedValue places true center
      let radiusTerm ← statedValue places false (widenedRadius places center radius)
      return ("Center and radius of the input",
        ``CAS.Tactic.BoxInequality.abs_sub_le_of_approxOn_box,
        ← `(_root_.abs (($input : ℝ) - ($centerTerm : ℝ)) ≤ ($radiusTerm : ℝ)))

/-- The headline of one view of an enclosure: the theorem about the printed input on the box of
the bindings, `∀ x ∈ Set.Icc a b, …`, transported from the checked proof of the view. -/
private def viewHeadline (places : Nat) (bindings : List BoxBinding) (reified : ReifiedExpr)
    (view : EncloseView) : TermElabM UncheckedExplanationStep := do
  let (_, vars) := coordinateIdents reified
  let (label, lemmaName, conclusion) ←
    viewStatement places (← reified.inputTerm vars) view.display
  let statement ← bindings.foldrM (init := conclusion) fun binding statement ↦ do
    let lower ← exactSyntax binding.interval.lo
    let upper ← exactSyntax binding.interval.hi
    `(∀ $(mkIdent binding.coordinate):ident ∈ Set.Icc ($lower : ℝ) ($upper : ℝ), $statement)
  headlineStep label lemmaName statement (2 * bindings.length) fun locals conclusion ↦ do
    let coordinates := (List.range bindings.length).toArray.map fun k ↦ locals[2 * k]!
    let hypotheses := (List.range bindings.length).toArray.map fun k ↦ locals[2 * k + 1]!
    transportView lemmaName view.proof (bindings.map (·.interval)) coordinates hypotheses
      conclusion

private def logEnclosure
    (ref : Syntax) (method : EnclosureMethod) (precision : Precision) (config : String)
    (bindings : List BoxBinding) (reified : ReifiedExpr) : CommandElabM Unit := do
  let closedValue := bindings.isEmpty
  let box := bindings.map BoxBinding.interval
  let some result ←
      liftTermElabM <| runEncloseViews method precision box reified.expr
    | throwErrorAt ref (if closedValue then
          "no checked interval route could enclose this closed expression; simplify it or \
            raise the precision, as in `(prec := 40)`"
        else
          boxQueryFailureMessage method reified.expr)
  let boxDisplay := renderBox bindings
  let ambientSpace := renderAmbientSpace bindings.length
  let domain := if closedValue then "closed real expression" else
    s!"{boxDisplay} ⊆ {ambientSpace}"
  let places := previewPlaces precision
  let rendered := result.views.map (renderView places ·.display)
  let some (_, output, exactOutput) := rendered[0]?
    | throwError "internal CEGA numerical error: no enclosure view"
  let exactOutputDetails : Array MessageData :=
    if output = exactOutput then
      #[]
    else
      #[m!"Decimal preview: outward-rounded to {places} places where it is a bound",
        m!"Exact certified output: {exactOutput}"]
  let precisionDetails : Array MessageData :=
    if precision = {} then #[] else #[m!"Precision policy: {renderPrecision precision}"]
  let guarantee := if closedValue then "the real value lies in the output interval" else
    "the input lies in the output interval throughout the box"
  -- Under `cas.suggest`, an enclosure computed with a configuration is also offered with `cega`
  -- and that configuration, when `cas` does not prove its statement.
  let tactics := if config.isEmpty then #["cas"] else #["cas", s!"cega {config}"]
  let views := result.views.map (viewHeadline places bindings reified)
  let ((evidence, routeSteps), statement?) ← liftTermElabM <|
    withHeadlines views fun headlines ↦ do
      let evidence ←
        profileitM Exception "CEGA command evidence validation" (← getOptions) do
          return headlines ++ (← result.views.mapM fun view ↦ validateViewEvidence view)
      let routeSteps ← profileitM Exception "CEGA route rendering" (← getOptions) do
        routeStepLabels result.routeSteps
      return (evidence, routeSteps)
  let reportMessage ← liftTermElabM do
    let report : ExplanationReport := {
      checkedEvidence := evidence
      plannerMetadata := plannerMetadata routeSteps
    }
    CAS.Command.Explanation.render report
  logReport ref {
    domain
    input := reified.render
    inputType := if closedValue then "scalar ℝ" else s!"scalar map {ambientSpace} → ℝ"
    output
    outputType := "certified interval in ℝ"
    furtherResults := (rendered.extract 1).map fun (label, preview, _) ↦ (label, preview)
  } #[
    m!"Coordinates: {if closedValue then "none" else renderCoordinates bindings}",
    m!"Certified domain: {domain}",
    computationNode "Certified numerical guarantee"
      (#[m!"Guarantee: {guarantee}"] ++ exactOutputDetails ++ precisionDetails),
    reportMessage
  ]
  offerExample statement? tactics

/-- `#cas [enclose x in [a, b], y in [c, d]] e` computes an interval with rational endpoints that
contains every value of `e` on the box of the bindings, proves it, and derives an upper bound, an
absolute bound and a center with a radius.

## Theorem
For the printed interval `[lo, hi]` the first checked step proves
`∀ x ∈ Set.Icc a b, lo ≤ e ∧ e ≤ hi` about Mathlib's real functions, with one `∀ y ∈ Set.Icc c d`
for each further binding, such as
`∀ x ∈ Set.Icc 0 1, -1 / 4 ≤ x ^ 2 - x ∧ x ^ 2 - x ≤ 0` for
`#cas [enclose x in [0, 1]] (x ^ 2 - x)`. The next steps prove `e ≤ u` for the upper bound,
`|e| ≤ m` for the absolute bound and `|e - c| ≤ r` for the center `c` and the radius `r`, which
also covers the rounding of the center; decimal endpoints are rounded outward. The lemmas
`mem_of_enclosedOn_box`, `le_of_boundOn_box`, `abs_le_of_boundOn_abs_box` and
`abs_sub_le_of_approxOn_box` of `CAS.Tactic.BoxInequality` transport these statements from the
checked certificate `CAS.Certificate.EnclosedOn f box lo hi` of the reflected form `f` of `e`
(`CAS.Continuum.RationalInterval.EnclosureAttempt.enclosedOn_of_interval_eq`), as the tactic
`cega` does. Each of these steps is shown when its proof succeeds within its own budget of
`maxHeartbeats` heartbeats; otherwise the report keeps only the certificate of that view about
`f`. Without bindings, `#cas [enclose] e` encloses a closed expression `e`.

## Conditions and limits
Each binding `x in [a, b]` has rational literal endpoints with `a ≤ b`, such as `-1`, `3/2` or
`0.1`, and a box has at most 8 coordinates (`cega.maxDimension`). `e` uses the calculator
grammar of `#cas [N d]` and `|x|`, and every subexpression must be defined on the whole box, so
denominators exclude zero and the arguments of `log` stay positive. The enclosure is valid but
not always tight. The Output line prints an endpoint exactly when its rational has at most 24
characters and otherwise rounds it outward to 6 decimal places; the details print the exact
rationals. A center rounded this way is rounded down, and the printed radius is widened by that
rounding.

## Options
- `(prec := n)` sets `n` Taylor terms for `exp`, `n` series terms for `log` and `n` binary
  digits for square roots; `(expOrder := n)`, `(logTerms := n)` and `(sqrtDigits := n)` set
  them one at a time, with defaults 8, 10 and 12.
- `(depth := n)` first refines the box by checked bisection to depth `n`.
- `(digits := d)` first tries the digit evaluator of `#cas [N d]` at a matching precision and
  prints `d` decimal places.
- `set_option cega.maxPrecision` (default 256) and `cega.maxRefinementWork` (default 4096) cap
  the precision and the work of a subdivision.
- Under `set_option cas.suggest true` the report also offers the first checked step above as an
  `example` to paste in place of the command, when the binders and the type of that example,
  elaborated where the command is with the variables of its section, are the proposition of the
  step up to unfolding instances, and the whole example elaborates there without errors to a
  declaration of that proposition with no `sorry` (`cas.suggest`).

## Examples
```lean
#cas [enclose x in [0, 1]] (x ^ 2 + x)
```
```output
Output (certified interval in ℝ): [0, 2]
Upper bound: 2
Absolute bound: 2
Center and radius: 1 ± 1
```
```lean
#cas [enclose x in [0, 1], y in [0, 1]] (x * y + sin y)
```
```output
Output (certified interval in ℝ): [0, 1.841471]
```
```lean
#cas [enclose x in [-2, 2]] (x / (1 + x ^ 2))
```
```output
Output (certified interval in ℝ): [-2, 2]
```
```lean
#cas (depth := 2) [enclose x in [-2, 2]] (x / (1 + x ^ 2))
```
```output
Output (certified interval in ℝ): [-1/2, 1/2]
```
Bisection to depth `2` cuts `[-2, 2]` at `0` and at the turning points `±1`, so
`x / (1 + x ^ 2)` is monotone on each piece and the enclosure is its exact range.
```lean
#cas [enclose] (1 / 1000000000000000000000000)
```
```output
Output (certified interval in ℝ): [0.000000, 0.000001]
Upper bound: 0.000001
Absolute bound: 0.000001
Center and radius: ≈0.000000 ± 0.000001
```
The exact value `1/1000000000000000000000000` is longer than 24 characters, so the bounds are
rounded outward to 6 decimal places. The center is rounded down and marked `≈`, and the radius
covers that rounding, as in the theorem `|e - 0.000000| ≤ 0.000001`.

## In a proof
```lean
theorem enclose_bound (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : x ^ 2 + x ≤ 2 := by
  cas
```
The tactics `cas` and `cega` take the box from the hypotheses on `x`.

## See also
Mathematica `Interval`, SymPy `AccumBounds`. The modes `N`, `minimize` and `maximize`, and the
tactic `cega [enclose ...]`, which proves a goal from the same query. Oracle route:
`#cas [enclose x in [a, b], oracle := sympy] e`, which proves an enclosure around the oracle's
estimate.

## Possible issues
```lean
#cas [enclose x in [-1, 1]] (1 / x)
```
```output
no checked interval route succeeded on this box. Possible domain obstruction: check whether
denominator intervals exclude zero.
```
`1 / x` is unbounded near `0`, so no interval holds its values on `[-1, 1]`. Enclose it on boxes
that exclude zero, such as `[1/10, 1]`.
```lean
#cas [enclose x in [0, pi]] (sin x)
```
```output
interval endpoints must be exact rational literals, such as -1, 3/2, -1/10, or 0.1
```
Use a rational interval that contains the one you mean, such as `[0, 315/100]` for `[0, π]`.
```lean
#cas [enclose x in [1, 0]] (x)
```
```output
interval endpoints are reversed: 1 > 0
```
Write the smaller endpoint first.
-/
syntax (name := casEncloseCommand)
  "#cas" optConfig "[" &"enclose" cegaIntervalBinding,* "]" term : command

elab_rules : command
  | `(#cas $cfg:optConfig [enclose $bindings:cegaIntervalBinding,*] $expr:term) => do
      let precision ← parsePrecision cfg
      let method := requestedMethod cfg
      let bindings ← parseBindings bindings.getElems
      if method = .subdivided ∧ bindings.isEmpty then
        throwErrorAt cfg "`(depth := n)` subdivides the box of the bindings `x in [a, b]`, and \
          a closed expression has none"
      let reified ← CAS.CEGA.parseExpression expr (bindings.map BoxBinding.coordinate)
      logEnclosure expr method precision (surfaceText cfg) bindings reified

end CAS.Command.CEGA

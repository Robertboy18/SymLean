/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Tactic.Algebra
public import CAS.Tactic.DerivativeRewrite
public import CAS.Tactic.Exact
public import CAS.Tactic.Identity
public import CAS.Tactic.RealNormalization
public meta import CAS.Tactic.RealNormalization
public import CAS.Calculus.FDeriv
public meta import CAS.Calculus.FDeriv
public meta import CAS.Tactic.PolynomialEquations
public import CAS.Tactic.RealDeriv
public import CAS.Tactic.Regularity
public meta import CAS.Tactic.RouteRegistry
public import CAS.Tactic.Syntax
public import CAS.Tactic.RouteRegistry
public import CAS.Tactic.Determinant
public meta import CAS.Tactic.Determinant
public import CAS.Tactic.Fallback
public meta import CAS.Tactic.Fallback
public import CAS.Tactic.ElementaryRewrites
public meta import CAS.Tactic.ElementaryRewrites
public meta import CAS.Tactic.CommandShapes

/-!
# Exact computer algebra tactics for theorem proofs

The exact import for theorem authors, without the integration planner. It defines the routes
of `cas` and the checked normalization `cas_nf`. The forms `cas using h` and `cas_nf using h`
take explicit evidence, `cas using [h₁, h₂]` takes complete proofs as local facts, and
`cas [f, g]` adds local simp lemmas such as definitions to unfold.
Ordinary scalar goals are written in standard Lean and Mathlib syntax; users do not
construct `Verified.Expr` values for them. Symbolic integration is in `CAS.IntegrationTactic`.

## Main definitions

* `evalCas`: the elaborator of `cas`, `cas using h`, `cas using [h₁, h₂]` and `cas [l₁, l₂]`.
* `closeCore`: the stages of `cas` on the main goal; `close` runs them after validating the
  `using` evidence once.
* `closeWithFacts`: `cas using [h₁, h₂]`. The facts join the local context, and the equations
  among them over the goal's coefficient type go to polynomial consequence search first.
* `closeDerivative`: the derivative stage.
* `routeOrder`: the stages of `cas` in the current environment, with their priorities.
* `SelectedRoute`, `recordRoute` and `runRecordingRoute`: the route that closed the goal, as
  `cas?` reads it.
* `cas_nf`, `cas_nf using h` and their `conv` forms `convCasNF` and `convCasNFUsing`, which
  rewrite with `Tactic.RealNormalization` (`CAS/Tactic/RealNormalization.lean`).

## Implementation notes

Each stage of `cas` only proposes a proof. We accept it through
`ProofCarrier.attemptClosingMainGoal` (`CAS/Tactic/ProofCarrier.lean`), and only when the proof
assigned to the original goal is complete, type-correct and definitionally equal to that goal;
a refused route, like an unsupported target, leaves the proof state as it was. A route that
exhausts Lean's recursion depth fails like any other, so that the remaining routes run and the
failure is reported by `cas` rather than as Lean's runtime error; heartbeat exhaustion
propagates.

The stages differ in what does the mathematics. On the checked stages we reflect the goal into
the deep embedding `Verified.Expr` and let the kernel run a verified normalizer. An ordinary
real equality is reflected by `CAS.Elaboration.RealExpression.reify`
(`CAS/Elaboration/RealExpression.lean`), both sides over one table of atoms
(`Tactic.RealExpression.reifyOverAtoms`, `CAS/Tactic/RealExpression.lean`); a semantic target or
a reflected equality already contains its `Verified.Expr` terms. The kernel runs the
side-conditioned pipeline `Verified.Expr.sideConditionPipeline`
(`CAS/ClosedForm/Pipeline/Configured.lean`) on the difference of the two sides, or the
multivariate canonical form `Verified.Expr.Alg.canonicalForm` (`CAS/ClosedForm/Canonical.lean`)
when the pipeline leaves a residual, and one `decide +kernel` (`KernelReadBack.decideByKernel`,
`CAS/Tactic/KernelReadBack.lean`) certifies that the run ends in zero and which essential
conditions it recorded (`Verified.Expr.essentialSide`: those the structural sign checker does
not prove). `Verified.Expr.eval_eq_of_sideConditionPipeline_run_essential` and
`Verified.Expr.Alg.eval_eq_of_canonicalForm_sub_eq` give the equality under those conditions
(nonzero denominators and cancelled factors, positive bases of real powers and square roots),
which `symbolic_assumptions` or `DerivativeBridge.closeValidity`
(`CAS/Tactic/DerivativeBridge.lean`) prove from the local context or the `using` evidence;
`DerivativeBridge.loweringBridgeSyntax` identifies each reflection with the term it came from.
The derivative, integral, box and command stages call library modules with checked theorems
of their own, named in the route order; the remaining stages call Mathlib and core tactics,
whose proofs are ordinary Lean proofs. Proof by reflection is the classical technique (the
reference is in `CAS/Elaboration/RealExpression.lean`); the normalizers, their soundness
theorems and the order of the stages are ours.

We chose the order stage by stage. Determinants are evaluated first, since left in place they
send `rfl` and `simp` into a row-by-row expansion. The statements of the algebra, matrix and
number theory commands come before `algebraicEquality`, which would try to evaluate a modular
power directly. `norm_num` and `grind` come last, so that a goal an earlier route proves keeps
that route's proof.

CEGA certificate projection lives in `CAS.CEGA`, and the optional `cas?` and `cega?` InfoView
reports live in `CAS.Reporting`. Keeping those layers separate lets exact proofs avoid
numerical-query and presentation imports.

## Route order

`closeCore` runs the stages in order of priority, together with the routes that other modules
register with `@[cas_route]` in `Tactic.RouteRegistry` (`CAS/Tactic/RouteRegistry.lean`), each at
its own priority (1000 by default) and after the built-in stages of equal priority; `routeOrder`
lists them. A stage either closes the goal, or records its failure for the report and passes the
goal on, or ends the search with its failure when no later stage applies to the goal. The
built-in stages, with their priorities:

* `determinant` (2000): determinants of matrix literals `!![...]` in a relation are evaluated
  with Mathlib's `norm_det` (`Tactic.Determinant.evaluate`, `CAS/Tactic/Determinant.lean`), and
  the later stages see the numeral or polynomial that remains.
* `algebraStatement` (1900): the statements of the algebra, matrix and number theory commands
  (`CommandShapes.isAlgebraStatement`, `CAS/Tactic/CommandShapes.lean`) go to the route that
  `CAS` registers under `command` (`CAS/Command/Goals.lean`), which proves the theorem the
  corresponding `#cas` command proves and transports it to the goal. A computed algebraic value
  that differs from the stated one ends the search.
* `algebraicEquality` (1800): an equality that `assumption`, `rfl`, `ring1` or `ac_rfl` proves
  is closed at once (`Tactic.Arithmetic.closeAlgebraicEquality`, `CAS/Tactic/Arithmetic.lean`).
* `commandStatement` (1700): limits `Filter.Tendsto f l l'` at a rational point or at `atTop` or
  `atBot` with `l'` one of `𝓝 L`, `atTop` and `atBot`, and counts of real roots
  `Fintype.card (p.rootSet ℝ) = n`, go to the same route; when it fails, the later stages still
  run.
* `derivative` (1600): evaluated checked-expression constants inside an ordinary relation are
  first exposed as ordinary real syntax (`Tactic.DerivativeBridge.exposeCheckedExpressions`).
  `Tactic.RealDeriv.close` (`CAS/Tactic/RealDeriv.lean`) proves `deriv f x₀ = rhs`,
  `HasDerivAt f f' x₀`, `HasDerivWithinAt f f' s x₀` and `DifferentiableAt ℝ f x₀` for ordinary
  functions `ℝ → ℝ` with analytic theorem rules before real-valued reflection, including nested
  derivatives such as `deriv (fun x ↦ deriv g x) x₀`, and `iteratedDeriv n f x₀ = rhs` and
  `iteratedDerivWithin n f s x₀ = rhs` of a literal order `n`, which become nested derivatives.
  An inner derivative of a function that is not valid everywhere is replaced by its symbolic
  derivative near `x₀`, so its conditions are needed at `x₀` only. Arithmetic and chain rules
  also handle complex scalar functions; `@[cas_deriv]` theorems and local derivative families
  extend the analytic route to other ordinary functions. The regularity goals `Differentiable`,
  `DifferentiableOn`, `ContDiffAt`, `ContDiffOn`, `ContDiff`, `ContinuousAt`, `ContinuousOn`,
  `Continuous`, `AnalyticAt` and `AnalyticOnNhd` follow from the checked derivative and
  smoothness theorems of the reflected body (`Tactic.Regularity.close`,
  `CAS/Tactic/Regularity.lean`). A derivative backend registered with `@[cas_derivative_backend]`
  in `CAS/Tactic/DerivativeRegistry.lean` adds Euclidean shapes for ordinary functions
  `ℝ^n → ℝ` with a literal dimension, such as `fderiv ℝ f p (EuclideanSpace.single i 1) = rhs`;
  the backend has to be imported, since operator definitions alone install none. The function
  body is reflected, the analytic derivative is read off the executable symbolic derivative
  through the bridge theorems, and the stated derivative is matched by a fixed Mathlib script
  with the checked side-conditioned normalizer as fallback. Analytic domain conditions are
  proved by `symbolic_assumptions` or by the `using` evidence. The reflected derivative theorems
  `Verified.Expr.deriv_eval_add_smul_single_eq_diff_eval` (`CAS/Calculus/Euclidean.lean`) and
  `Verified.Expr.fderiv_eval_apply_eq_sum_closedPartial` (`CAS/Calculus/FDeriv.lean`) are used
  directly only when the goal already mentions the checked evaluator. When the derivative
  routes fail on an equality, the arithmetic script runs on it with the derivatives as atoms.
* `integral` (1500): a goal with an interval integral goes to the route that
  `CAS.IntegrationTactic` registers under `integral` (`CAS/IntegrationTactic.lean`), so that the
  antiderivative planner is loaded only with that import; with it, improper integrals such as
  `∫ t in Set.Ioi 0, f t` go there too. When the route fails on a relation with an interval
  integral, the arithmetic script runs with the integrals as atoms.
* `semantic` (1400): semantic targets (`Set.EqOn`, a zero-error `ApproxOn` and a zero
  `ResidualBound`) go to `Tactic.Exact.closeSemanticTarget` (`CAS/Tactic/Exact.lean`). It builds
  the configured pipeline's route `Exact.SymbolicClaimRoute.withSideConditions`
  (`CAS/Exact/ScalarRoutes.lean`), or
  `Verified.Expr.Alg.canonical` when the pipeline leaves a residual, certifies its zero target
  and its essential conditions by one `decide +kernel`, and applies
  `Exact.eqOn_of_symbolicApproxRoute` or `Exact.approxOn_zero_of_symbolicApproxRoute`
  (`CAS/Exact/ApproximationRoutes.lean`), or
  `Exact.SymbolicClaimRoute.eqOn_zero` or `Exact.SymbolicClaimRoute.residualBound_zero`
  (`CAS/Exact/ZeroResidual.lean`), with the vector and tensor forms of
  `CAS/Exact/VectorResidual.lean` and `CAS/Exact/TensorResidual.lean`. Without `using` evidence
  a route without essential conditions is tried first, then the inferred side-condition route,
  which proves the emitted conditions with `symbolic_assumptions`. These are the routes whose
  side conditions the `#cas [simplify]` report describes. `Set.EqOn f g s` and
  `ApproxOn f g s 0` between ordinary functions are proved pointwise
  (`CAS.Certificate.approxOn_of_eqOn` for the second): the stages of `cas` prove `f x = g x`
  for `x ∈ s`.
* `reflectedEquality` (1300): an equality mentioning `Verified.Expr.eval` goes to the tactics
  `symbolic_eq` and `symbolic_alg_zero_side` of `CAS/ClosedForm/Tactic/Algebra.lean`, which
  certify with `decide +kernel` that the polynomial normalizer, the fraction normal form or the
  canonical form takes the difference to zero
  (`Verified.Expr.Alg.eval_eq_of_normalize_sub_eq_zero`,
  `Verified.Expr.Alg.ZeroCheck.eval_eq_of_zeroCheck_sub_eq_zero`,
  `Verified.Expr.Alg.eval_eq_of_canonicalForm_sub_eq_zero`), then to
  `Tactic.Identity.closeReflectedEquality` (`CAS/Tactic/Identity.lean`), which runs the
  side-conditioned pipeline on the difference in the goal's own environment. A reflected
  equality that neither proves goes on to the routes of ordinary equalities, with its
  evaluations as atoms; the lemmas of `cas [l₁, l₂]` can unfold them there.
* `arithmetic` (1200): ordinary Lean equalities, disequalities and order relations, written in
  plain Mathlib syntax, go to `Tactic.Arithmetic.close` (`CAS/Tactic/Arithmetic.lean`), a fixed
  script of Mathlib tactics (target simplification with a small set of exp/log/tan/sqrt
  rewrites, `field_simp`, `ring`, `norm_num`, `positivity`, `linarith`, `nlinarith`), after
  every derivative subterm of an explicit function is rewritten to its checked closed form
  (`Tactic.DerivativeRewrite.prepareIdentity`, `CAS/Tactic/DerivativeRewrite.lean`). The script
  is retried once with the real-valued definitions of the current module unfolded.
* `equationHint` (1150) and `polynomialEquations` (1100): an equation `h` of `cas using h` over
  the goal's coefficient type closes a real goal as a polynomial multiple of `h` after clearing
  denominators (`Tactic.Arithmetic.closeWithEquation`, certified by `linear_combination`).
  Remaining commutative-ring equalities are offered to core `grobner`, which proves polynomial
  consequences of the local equations, or closed by guarded denominator clearing
  (`Tactic.PolynomialEquations.attempt`, `CAS/Tactic/PolynomialEquations.lean`).
  `cas using [h₁, h₂]` supplies separately elaborated proposition proofs as local facts.
  Inequalities and nonvanishing facts are available to arithmetic and domain discharge; only
  equations over the target's coefficient type are passed to the polynomial route. Rational
  equations retain their nonzero-denominator obligations.
* `checkedIdentity` (1050): an ordinary real equality that these routes do not close goes to
  `Tactic.Identity.closeRealIdentity` (`CAS/Tactic/Identity.lean`), the reflection described in
  the implementation notes. This is how real-power identities such as
  `a ^ (s / 2) * a ^ ((t - s) / 2) = a ^ (t / 2)` under `0 < a` and exponential recombinations
  such as `exp a * exp b = exp (a + b)` are proved. The route takes equalities only; the domain
  hint printed when the arithmetic script fails is heuristic guidance read off the goal's syntax
  (`Classify.analyticSideConditionHint?`).
* `box` (900): an order goal, or a goal outside the relation language, on real variables
  bounded by rational literal hypotheses (`x * (1 - x) ≤ 1 / 4` under `0 ≤ x` and `x ≤ 1`, also
  `c ≤ f x`, `|f x| ≤ c`, `a ≤ f x ∧ f x ≤ b`, `f x ∈ Set.Icc a b`, `f x ≤ g x`, and their
  strict forms) goes to the checked CEGA box query when `CAS.CEGA` is imported: `CAS/CEGA.lean`
  registers the route of `CAS.Tactic.BoxInequality` (`CAS/Tactic/BoxInequality.lean`) under
  `box`. The certificate is transported by the soundness lemmas of `CAS.Tactic.BoxInequality`,
  and the route reports the explicit `cega [enclose ...]` call it ran.
* `command` (800): polynomial sign conditions `∀ x : ℝ, p x ≤ q x` (and the relation in one free
  variable that no hypothesis bounds) and the existence of a root in an interval go to the
  `command` route.
* `elementary` (700): on an ordinary real identity, the elementary rewrites of
  `Tactic.ElementaryRewrites` (`CAS/Tactic/ElementaryRewrites.lean`: multiple angles,
  exponentials of multiples of logarithms, products of real powers, each under its hypothesis)
  are applied and the arithmetic routes run again.
* `normNum` (600) and `grind` (500): `norm_num` on a proposition outside the relation language
  without variables whose closed natural-number and integer subterms are at most `10 ^ 12` in
  absolute value (`Tactic.Fallback.closeClosedByNormNum`), and core `grind` on any ordinary
  relation or proposition outside that language (`Tactic.Fallback.closeByGrind`), each under the
  heartbeat budget `cas.grindHeartbeats` (`CAS/Tactic/Fallback.lean`).
-/

public meta section

namespace CAS

open Lean Elab Tactic Meta
open Parser.Tactic

namespace ExactTactic

/-! ## Frontend implementation API -/

/--
Diagnostic classification of the exact route selected by `cas`.

`CAS.Reporting` reads this value. The assigned proof, not this tag,
is the mathematical evidence.
-/
inductive SelectedRoute where
  /-- A checked exact semantic route closed the goal. -/
  | semantic
  /-- A checked semantic route closed the goal after inferring side conditions. -/
  | inferredSide
  /-- The reflected symbolic equality fallback closed the goal. -/
  | rawSymbolic
  /-- Ordinary Lean simplification or arithmetic closed the goal. -/
  | arithmetic
  /-- Core `grobner` proved a consequence of the equation hypotheses. -/
  | polynomialEquations
  /-- The checked normalizer closed an ordinary real identity after reflection over atoms. -/
  | checkedIdentity
  /-- Checked symbolic differentiation closed the goal. -/
  | derivative
  /-- The integration frontend closed the goal and retained its replay and explanation. -/
  | integral (result : Tactic.RouteRegistry.Result)
  /-- The checked CEGA box query closed an ordinary inequality on bounded real variables;
  `query` is the explicit `cega [...]` call that runs the same query. -/
  | boxInequality (query : TSyntax `tactic)
  /-- The theorem a `#cas` command proves (a limit, a root count, a sign condition) closed the
  goal through the route that `CAS` registers. -/
  | command (result : Tactic.RouteRegistry.Result)
  /-- The arithmetic routes closed an ordinary real equality after the elementary rewrites
  (multiple angles, exponentials of multiples of logarithms, products of real powers). -/
  | elementary
  /-- Core `grind`, run under the budget `cas.grindHeartbeats`, closed the goal. -/
  | grind
  /-- `norm_num` closed a proposition without local variables. -/
  | normNum
  /-- A route registered with `@[cas_route]` under the name `route`, or a frontend's form of `cas`
  that records itself under that name, closed the goal and returned `result`. -/
  | registered (route : Name) (result : Tactic.RouteRegistry.Result)
  /-- `Set.EqOn f g s` or `ApproxOn f g s 0` between ordinary functions followed from the
  equality `f x = g x` for `x ∈ s`, which `route` proved. -/
  | pointwise (route : SelectedRoute)

namespace SelectedRoute

/-- Stable diagnostic label used by the optional reporting layer. -/
def label : SelectedRoute → String
  | .semantic => "exact semantic"
  | .inferredSide => "exact semantic with inferred side conditions"
  | .rawSymbolic => "raw symbolic equality"
  | .arithmetic => "ordinary Lean simplification/arithmetic"
  | .polynomialEquations => "polynomial consequences of equation hypotheses"
  | .checkedIdentity => "checked symbolic identity"
  | .derivative => "checked symbolic derivative"
  | .integral _ => "checked integration"
  | .boxInequality _ => "checked CEGA box enclosure of an ordinary inequality"
  | .command _ => "theorem of a #cas command"
  | .elementary => "elementary rewrites, then ordinary arithmetic"
  | .grind => "bounded grind"
  | .normNum => "norm_num on a closed proposition"
  | .registered route _ => route.toString
  | .pointwise route => s!"pointwise, {route.label}"

/-- Rewrite the replay syntax that the route carries. -/
def mapReplays (f : TSyntax `tactic → TacticM (TSyntax `tactic)) :
    SelectedRoute → TacticM SelectedRoute
  | .integral result => return .integral { result with replay := ← f result.replay }
  | .command result => return .command { result with replay := ← f result.replay }
  | .registered route result =>
      return .registered route { result with replay := ← f result.replay }
  | .boxInequality query => .boxInequality <$> f query
  | .pointwise route => .pointwise <$> mapReplays f route
  | route => pure route

end SelectedRoute

/-- With `set_option trace.cas.fallback true`, a failure report of `cas` shows the complete
diagnostics of its `grind` and `norm_num` fallbacks instead of their first lines. -/
initialize registerTraceClass `cas.fallback

/-- The failure of a `grind` or `norm_num` fallback in a report of `cas`: its first line, which
says what failed or which budget ran out, or its whole message under `trace.cas.fallback`. -/
private def fallbackSummary (error : Exception) : CoreM MessageData := do
  if ← isTracingEnabledFor `cas.fallback then
    return error.toMessageData
  let text ← error.toMessageData.toString
  match text.splitOn "\n" with
  | [] | [_] => return error.toMessageData
  | first :: _ =>
      return m!"{first} (`set_option trace.cas.fallback true` shows its diagnostics)"

/--
`ProofCarrier.attemptClosingMainGoal` for the routes of `cas`. A route that exhausts Lean's
recursion depth fails like any other route, with a message that says so, and the remaining routes
still run; `ProofCarrier` itself propagates that exception, which is right for its other callers.
Heartbeat exhaustion still propagates: it is the budget of the whole declaration.
-/
private def attemptRoute {α : Type} (description : String) (action : TacticM α) :
    TacticM (Except Exception (ProofCarrier.ClosedMainGoal α)) := do
  tryCatchRuntimeEx (ProofCarrier.attemptClosingMainGoal description action) fun error ↦ do
    unless error.isMaxRecDepth do
      throw error
    let depth := maxRecDepth.get (← getOptions)
    return .error <| .error (← getRef)
      m!"{description} exceeded Lean's maximum recursion depth (the option maxRecDepth is \
        {depth}) and was abandoned; a larger setting may help: write \
        `set_option maxRecDepth {4 * depth} in` before the tactic"

/-- Try the installed box inequality route: `none` when `CAS.CEGA` is not imported,
otherwise the route's result or its refusal, with the tactic state restored on refusal. -/
private def attemptBoxInequalityRoute : TacticM (Option (Except Exception (TSyntax `tactic))) := do
  match ← Tactic.RouteRegistry.closer? `box with
  | none => return none
  | some closer =>
      match ← attemptRoute "CAS box inequality route" (closer none) with
      | .ok closed => return some (.ok closed.value.replay)
      | .error error => return some (.error error)

/-- Close the main goal with core `grind` under the budget `cas.grindHeartbeats`, validated
like every route; an exhausted budget is an ordinary failure. -/
private def attemptGrind : TacticM (Except Exception (ProofCarrier.ClosedMainGoal Unit)) :=
  Tactic.Fallback.attemptWithinBudget "grind"
    (attemptRoute "CAS grind fallback" Tactic.Fallback.closeByGrind)

/-- Try the installed route that closes goals with the theorems of the `#cas` commands: `none`
when `CAS` is not imported, otherwise the route's result or its refusal, with the
tactic state restored on refusal. -/
private def attemptCommandRoute (side? : Option (TSyntax `term)) :
    TacticM (Option (Except Exception Tactic.RouteRegistry.Result)) := do
  match ← Tactic.RouteRegistry.closer? `command with
  | none => return none
  | some closer =>
      match ← attemptRoute "CAS command theorem route" (closer side?) with
      | .ok closed => return some (.ok closed.value)
      | .error error => return some (.error error)

/-- Whether the goal is a limit `Filter.Tendsto f l l'` or a count of real roots
`Fintype.card (p.rootSet ℝ) = n`, statements of `#cas [limit]` and `#cas [roots]` that no
arithmetic route proves. Only the head shapes are read. -/
private def isCommandStatement : TacticM Bool := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  if target.isAppOf ``Filter.Tendsto then
    return true
  let some (_, lhs, _) := target.eq? | return false
  let lhs := lhs.consumeMData
  return lhs.isAppOf ``Fintype.card &&
    (lhs.getAppArgs[0]?.any fun set ↦ set.consumeMData.isAppOf ``Set.Elem &&
      (set.consumeMData.getAppArgs[1]?.any (·.consumeMData.isAppOf ``Polynomial.rootSet)))

private def runRawSymbolic
    (side? : Option (TSyntax `term))
    (defs? : Option (Array (TSyntax ``Lean.Parser.Tactic.simpLemma))) : TacticM Unit := do
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    unless target.consumeMData.getAppFn.consumeMData.isConstOf ``Eq do
      throwError "cas raw symbolic fallback expected an equality goal"
  let tactic ←
    match defs? with
    | none => `(tactic| first | symbolic_eq | symbolic_alg_zero_side)
    | some defs => `(tactic| first | symbolic_eq [$defs,*] | symbolic_alg_zero_side [$defs,*])
  -- The normalizer certificates are `decide +kernel` steps inside the tactic script; running
  -- it without error recovery makes a failed certificate a failure instead of a placeholder.
  let saved ← saveState
  try
    let goal ← getMainGoal
    let remaining ← Tactic.KernelReadBack.runTacticOnGoal goal tactic
    replaceMainGoal remaining
  catch rawError =>
    saved.restore
    -- The unconditional normalizer and the fraction normal form did not reach zero; the full
    -- side-conditioned pipeline is run in the goal's own environment.
    try
      Tactic.Identity.closeReflectedEquality "cas" side?
    catch identityError =>
      throwError
        "raw normalizer route:{indentD rawError.toMessageData}\n\
         side-conditioned normalizer route:{indentD identityError.toMessageData}"

private def throwSemanticFailure {α : Type}
    (semanticError : Exception)
    (inferredSideError? : Option Exception)
    (pointwiseError? : Option Exception := none) : TacticM α :=
  let inferredSide := match inferredSideError? with
    | some error => m!"\ninferred side-condition route:{indentD error.toMessageData}"
    | none => m!""
  let pointwise := match pointwiseError? with
    | some error => m!"\npointwise route:{indentD error.toMessageData}"
    | none => m!""
  throwError
    "cas failed on a checked semantic target.\n\
     exact semantic route:{indentD semanticError.toMessageData}{inferredSide}{pointwise}"

private def attemptArithmeticRoute
    (defs? : Option (Array (TSyntax ``Lean.Parser.Tactic.simpLemma))) :
    TacticM (Except Exception SelectedRoute) := do
  match ← attemptRoute "CAS arithmetic route"
      (Tactic.Arithmetic.close defs?) with
  | .ok _ => return .ok .arithmetic
  | .error error => return .error error

private def attemptCheckedIdentityRoute
    (side? : Option (TSyntax `term))
    (defs? : Option (Array (TSyntax ``Lean.Parser.Tactic.simpLemma))) :
    TacticM (Except Exception SelectedRoute) := do
  let route : TacticM Unit := do
    if let some defs := defs? then
      evalTactic (← `(tactic| try simp only [$defs,*]))
    Tactic.Identity.closeRealIdentity "cas" side?
  match ← attemptRoute "CAS checked identity route" route with
  | .ok _ => return .ok .checkedIdentity
  | .error error => return .error error

/-- Whether the `using` term is an equation over the goal's coefficient type. -/
private def isEquationOver (side : TSyntax `term) (carrier : Lean.Expr) :
    TacticM Bool := withMainContext do
  let saved ← saveState
  tryCatchRuntimeEx (do
    let evidence ← Term.withoutErrToSorry <| Term.elabTerm side none
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← whnf (← instantiateMVars (← inferType evidence))
    let result ←
      match type.consumeMData.eq? with
      | some (hintCarrier, _, _) => isDefEq hintCarrier carrier
      | none => pure false
    saved.restore
    return result) fun error ↦ do
    saved.restore
    if error.isRuntime then
      throw error
    return false

run_cmd Lean.modifyEnv fun env ↦
  Lean.Parser.addSyntaxNodeKind env `CAS.ExactTactic.validatedUsingEvidence

/--
Elaborate an internal single-hint node in the expected type of the route using it, and record
that it was validated. The marker lives in the metavariable context, so it survives when a bridge
runs a fresh term elaborator; reader-scoped `elabToSyntax` callbacks would not.
-/
@[term_elab CAS.ExactTactic.validatedUsingEvidence]
def elabValidatedUsingEvidence : Term.TermElab := fun stx expected? ↦ do
  let evidence ← Term.withoutErrToSorry <| Term.elabTerm stx[1] expected?
  let evidence ← (ProofCarrier.checkCompletedProof "CAS using hint" evidence).run
    { elaborator := `CAS.ExactTactic.elabValidatedUsingEvidence, recover := false }
    |>.run' { goals := [] }
  let checked : MVarId := ⟨stx[0].getId⟩
  unless ← checked.isAssigned do
    checked.assign (mkConst ``True.intro)
  return evidence

/--
Interpret an unparenthesized application as separate proof hints only when it fails as
a single proof and every component is independently complete. Parentheses retain the
single-term interpretation; applied equations and expected-type evidence are left intact.
-/
private def conjoinUsingProofs (side : TSyntax `term) : TacticM (TSyntax `term) := do
  unless side.raw.isOfKind ``Parser.Term.app do
    return side
  let isCompleteProof (term : TSyntax `term) : TacticM Bool := withMainContext do
    let saved ← saveState
    tryCatchRuntimeEx (do
      let proof ← Term.withoutErrToSorry <| Term.elabTerm term none
      let proof ← ProofCarrier.checkCompletedProof "CAS using hint" proof
      let result ← isProp (← inferType proof)
      saved.restore
      return result) fun error ↦ do
        saved.restore
        if error.isRuntime then
          throw error
        return false
  if ← isCompleteProof side then
    return side
  let terms : Array (TSyntax `term) :=
    #[⟨side.raw[0]⟩] ++ side.raw[1].getArgs.map (⟨·⟩)
  unless ← terms.allM isCompleteProof do
    return side
  let mut proof := terms.back!
  for term in terms.pop.reverse do
    proof ← `($(mkIdent `_root_.And.intro) $term $proof)
  return proof

/-- Make an independently elaborated proposition available to arithmetic and domain solvers.
Expected-type-dependent evidence is left for the route that supplies its expected type. -/
private def noteUsingFact (side : TSyntax `term) : TacticM Unit := do
  let saved ← saveState
  tryCatchRuntimeEx (withMainContext do
    let proof ← Term.withoutErrToSorry <| Term.elabTerm side none
    let proof ← ProofCarrier.checkCompletedProof "CAS using fact" proof
    unless ← isProp (← inferType proof) do
      throwError "cas requires a proof as side evidence"
    unless proof.isFVar do
      let (_, goal) ← (← getMainGoal).note (← mkFreshUserName `hcasFact) proof
      replaceMainGoal [goal]) fun error ↦ do
        saved.restore
        if error.isRuntime then
          throw error

/--
Validate explicit evidence in the expected type supplied by the route that uses it. If the route
ignores the hint, check it independently before accepting success. Failed routes roll back the
marker with their metavariable assignments. The returned replay keeps a single hint's syntax;
a juxtaposed sequence of proofs becomes an explicit conjunction, since route-specific replays
take a single proof term.

Normalization disables preliminary fact insertion: its evidence may require the exact
generated side-condition type, which is not available before the normalizer runs.
-/
private def withValidatedUsing (side? : Option (TSyntax `term))
    (action : Option (TSyntax `term) → TacticM SelectedRoute)
    (noteFact : Bool := true) : TacticM SelectedRoute := do
  let some side := side? | return ← action none
  ProofCarrier.preservingStateOnFailure do
    let evidenceSide ← conjoinUsingProofs side
    let goal ← getMainGoal
    let checked ← withMainContext <| mkFreshExprMVar (mkConst ``True)
    let tracked : TSyntax `term := ⟨Syntax.node evidenceSide.raw.getHeadInfo
      `CAS.ExactTactic.validatedUsingEvidence
      #[mkIdent checked.mvarId!.name, evidenceSide.raw]⟩
    if noteFact then
      noteUsingFact tracked
    let result ← action (some tracked)
    unless ← checked.mvarId!.isAssigned do
      goal.withContext do
        let evidence ← Term.withoutErrToSorry <| Term.elabTerm evidenceSide none
        let evidence ← ProofCarrier.checkCompletedProof "CAS using hint" evidence
        unless ← isProp (← inferType evidence) do
          throwError "cas requires a proof as side evidence"
    let restoreReplay (replay : TSyntax `tactic) : TacticM (TSyntax `tactic) := do
      return ⟨← replay.raw.replaceM fun node ↦
        pure <| if node == tracked.raw then some evidenceSide.raw else none⟩
    result.mapReplays restoreReplay

private def attemptEquationHintRoute (side : TSyntax `term) :
    TacticM (Except Exception SelectedRoute) := do
  match ← attemptRoute "CAS equation hint route"
      (Tactic.Arithmetic.closeWithEquation side) with
  | .ok _ => return .ok .arithmetic
  | .error error => return .error error

/-- Try the commutative-ring equation solver and retain the operation that closed the goal. -/
private def attemptPolynomialEquations (equations : Array (TSyntax `term)) :
    TacticM (Except Exception SelectedRoute) := do
  let attempt ← tryCatchRuntimeEx (Tactic.PolynomialEquations.attempt equations) fun error ↦ do
    unless error.isMaxRecDepth do
      throw error
    return .error <| .error (← getRef)
      m!"CAS polynomial equations exceeded Lean's maximum recursion depth and was abandoned"
  match attempt with
  | .ok closed =>
      return .ok <| match closed.value with
        | .grobner => .polynomialEquations
        | .denominatorClearing => .arithmetic
  | .error error => return .error error

private def arithmeticLemmas
    (side? : Option (TSyntax `term))
    (defs? : Option (Array (TSyntax ``Lean.Parser.Tactic.simpLemma))) :
    MacroM (Option (Array (TSyntax ``Lean.Parser.Tactic.simpLemma))) := do
  let lemmas := defs?.getD #[]
  match side? with
  | none => pure defs?
  | some side =>
      pure <| some (lemmas.push (← `(Parser.Tactic.simpLemma| $side:term)))

private def attemptSemanticRoute (side? : Option (TSyntax `term)) :
    TacticM (Except (Exception × Option Exception) SelectedRoute) := do
  match side? with
  | some _ =>
      match ← attemptRoute "CAS semantic route"
          (Tactic.Exact.closeSemanticTarget side?) with
      | .ok _ => return .ok .semantic
      | .error error => return .error (error, none)
  | none =>
      let solveSideConditions : TSyntax `tactic ←
        `(tactic| symbolic_assumptions)
      let inferredSide ←
        `(by
          first
            | intro i j p hp
              fin_cases i <;> fin_cases j <;> $solveSideConditions:tactic
            | intro i p hp
              fin_cases i <;> $solveSideConditions:tactic
            | intro p hp
              $solveSideConditions:tactic)
      -- A route without emitted obligations is certified by one kernel evaluation; the
      -- inferred side-condition route, which discharges the emitted list with
      -- `symbolic_assumptions`, runs only when that fails.
      match ← attemptRoute "CAS semantic route"
          (Tactic.Exact.closeSemanticTarget none) with
      | .ok _ => return .ok .semantic
      | .error semanticError =>
          match ← attemptRoute "CAS inferred side-condition route"
              (Tactic.Exact.closeSemanticTarget (some inferredSide)) with
          | .ok _ => return .ok .inferredSide
          | .error inferredSideError =>
              return .error (semanticError, some inferredSideError)

private def returnsCheckedExpression : Lean.Expr → Bool
  | .forallE _ _ body _ => returnsCheckedExpression body
  | type => type.getAppFn.isConstOf ``Verified.Expr

private def unfoldLocalCheckedExpressionDefs : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let env ← getEnv
  let mut goal ← getMainGoal
  -- User definitions should elaborate as cheaply as the corresponding literal AST.
  -- Restrict unfolding to checked expressions declared in the current module, so the
  -- differentiation bridge does not expand imported implementation details.
  for name in target.getUsedConstants do
    if !env.isImportedConst name then
      match env.find? name with
      | some (.defnInfo info) =>
          if returnsCheckedExpression info.type then
            goal ← Meta.unfoldTarget goal name
      | _ => pure ()
  replaceMainGoal [goal]

private def evalReflectedCasDerive
    (valid? : Option (TSyntax `term)) : TacticM Unit := do
  discard <| ProofCarrier.runClosingMainGoal "checked symbolic differentiation" do
    unfoldLocalCheckedExpressionDefs
    let saved ← saveState
    try
      let solveValidity ← `(tactic| symbolic_assumptions)
      let validity := valid?.getD (← `(term| by $solveValidity:tactic))
      evalTactic (← `(tactic|
        first
          | rw [Verified.Expr.deriv_eval_add_smul_single_eq_diff_eval (h := $validity)]
          | rw [Verified.Expr.fderiv_eval_apply_eq_sum_closedPartial (h := $validity)]))
      evalTactic (← `(tactic|
        dsimp [Verified.Expr.diff, Verified.Expr.eval, Verified.Expr.closedPartial,
          Verified.Expr.simplify, EuclideanSpace.single]))
      evalTactic (← `(tactic|
        simp [EuclideanSpace.single, PiLp.single_apply] <;> ring))
    catch scalarError =>
      saved.restore
      try
        Tactic.DerivativeRegistry.reflected valid?
      catch backendError =>
        throwError
          "checked scalar/Fréchet route:{indentD scalarError.toMessageData}\n\
           derivative backend route:{indentD backendError.toMessageData}"

private def targetUsesCheckedEvaluation : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  return target.getUsedConstants.contains ``Verified.Expr.eval

private def isDerivativeGoal : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if Tactic.RealDeriv.isScalarDerivativeGoal target then
    return true
  if ← Tactic.Regularity.isRegularityGoal target then
    return true
  Tactic.DerivativeRegistry.isGoal target

private def mentionsIntervalIntegral : TacticM Bool := withMainContext do
  -- A locally named primitive can hide its integral in a let binding.
  let target ← zetaReduce (← instantiateMVars (← getMainTarget))
  return target.getUsedConstants.contains ``intervalIntegral

/-- Whether the goal mentions a Bochner integral, such as the improper integral
`∫ t in Set.Ioi 0, f t`. -/
private def mentionsBochnerIntegral : TacticM Bool := withMainContext do
  let target ← zetaReduce (← instantiateMVars (← getMainTarget))
  return target.getUsedConstants.contains ``MeasureTheory.integral

/--
Implementation hook that closes an ordinary scalar or Euclidean derivative goal, or a
reflected checked derivative identity, for the derivative stage of `cas`.

Scalar shapes (`deriv`, `iteratedDeriv` and `iteratedDerivWithin` of a literal order,
`HasDerivAt`, `HasDerivWithinAt`, `DifferentiableAt` over `ℝ`) go to `Tactic.RealDeriv.close`;
Euclidean shapes go to the backend registered in `Tactic.DerivativeRegistry`, when one is
imported; regularity shapes (`Differentiable`, `DifferentiableOn`, `ContDiffAt`, `ContDiffOn`,
`ContDiff`, `ContinuousAt`, `ContinuousOn`, `Continuous`, `AnalyticAt`, `AnalyticOnNhd`, and
`DifferentiableAt` on `ℝ^n`, for functions `ℝ → ℝ` and `ℝ^n → ℝ` with a literal dimension) go
to `Tactic.Regularity.close`. The reflected route is used only when the goal already mentions
the checked evaluator.
-/
def closeDerivative (valid? : Option (TSyntax `term)) : TacticM Unit := do
  let target ← withMainContext do
    let goal ← getMainGoal
    let target ← zetaReduce (← instantiateMVars (← goal.getType)) (zetaDelta := false)
    replaceMainGoal [← goal.change target]
    return target
  if ← withMainContext (Tactic.Regularity.isRegularityGoal target) then
    match ← attemptRoute "checked regularity"
        (Tactic.Regularity.close valid?) with
    | .ok _ => return
    | .error regularityError => throw regularityError
  else if Tactic.RealDeriv.isScalarDerivativeGoal target then
    match ← attemptRoute "ordinary scalar differentiation"
        (Tactic.RealDeriv.close valid?) with
    | .ok _ => return
    | .error scalarError =>
        unless ← targetUsesCheckedEvaluation do
          throw scalarError
        try
          evalReflectedCasDerive valid?
        catch reflectedError =>
          throwError
            "cas could not prove this derivative identity.\n\
             ordinary scalar route:{indentD scalarError.toMessageData}\n\
             checked-expression route:{indentD reflectedError.toMessageData}"
  else if ← withMainContext (Tactic.DerivativeRegistry.isGoal target) then
    match ← attemptRoute "ordinary Euclidean differentiation"
        (Tactic.DerivativeRegistry.close valid?) with
    | .ok _ => return
    | .error euclideanError =>
        unless ← targetUsesCheckedEvaluation do
          throw euclideanError
        try
          evalReflectedCasDerive valid?
        catch reflectedError =>
          throwError
            "cas could not prove this derivative identity.\n\
             ordinary Euclidean route:{indentD euclideanError.toMessageData}\n\
             checked-expression route:{indentD reflectedError.toMessageData}"
  else if ← targetUsesCheckedEvaluation then
    evalReflectedCasDerive valid?
  else
    throwError
      "cas expected a derivative statement: an equality with an ordinary `deriv`, \
       `iteratedDeriv` or `iteratedDerivWithin` of a literal order, or \
       `fderiv ℝ f p (EuclideanSpace.single i 1)` application or an operator of a derivative \
       backend registered with `@[cas_derivative_backend]`, a `HasDerivAt`, \
       `HasDerivWithinAt`, or `DifferentiableAt` \
       proposition about a scalar function, or a `DifferentiableAt`, `DifferentiableOn`, \
       `Differentiable`, `ContDiffAt`, `ContDiffOn`, `ContDiff`, `ContinuousAt`, \
       `ContinuousOn`, `Continuous`, `AnalyticAt`, or `AnalyticOnNhd` statement about a \
       function ℝ → ℝ or ℝ^n → ℝ with a literal dimension"

private def closeIntegralRoute (side? : Option (TSyntax `term)) :
    TacticM SelectedRoute := do
  match ← Tactic.RouteRegistry.closer? `integral with
  | some closer =>
      match ← attemptRoute "CAS integration route" (closer side?) with
      | .ok closed => return .integral closed.value
      | .error integralError => throw integralError
  | none =>
      throwError
        "cas found an interval integral, but the checked integration frontend is not \
         loaded. Import `CAS.IntegrationTactic` (or `CAS`) so that \
         bare `cas` can dispatch to it."

/-- Whether `residual` is an equality between two integer or natural-number literals, or its
negation: a comparison of numerals, for which a kernel decision is normally cheap (the
recognizers do not inspect the instance arguments). -/
private def isNumeralEquality (residual : Expr) : Bool :=
  let residual := residual.consumeMData
  let equality? := if residual.isAppOfArity ``Not 1 then residual.appArg!.consumeMData.eq?
    else if residual.isAppOfArity ``Ne 3 then
      some (residual.getArg! 0, residual.getArg! 1, residual.getArg! 2)
    else residual.eq?
  match equality? with
  | some (type, lhs, rhs) =>
      (type.isConstOf ``Int && lhs.int?.isSome && rhs.int?.isSome) ||
        (type.isConstOf ``Nat && lhs.nat?.isSome && rhs.nat?.isSome)
  | none => false

/-- Whether `target` is `Matrix.det A = v` or `v = Matrix.det A`, so that a false residual says
that `v` is not the determinant. -/
private def isDeterminantValueEquation (target : Expr) : Bool :=
  match target.consumeMData.eq? with
  | some (_, lhs, rhs) =>
      (lhs.consumeMData.isAppOf ``Matrix.det && !Tactic.Determinant.hasLiteralDeterminant rhs) ||
        (rhs.consumeMData.isAppOf ``Matrix.det && !Tactic.Determinant.hasLiteralDeterminant lhs)
  | none => false

/-- The failure report of `cas` after it evaluated the determinants of matrix literals: the goal
that remained. It is said to be false only when it is `False`, or an equality of two integer or
natural-number literals or the negation of one, whose negation the kernel decides; and only when
the goal was `Matrix.det A = v` (`direct`) is `v` said not to be the determinant. -/
private def determinantFailure (direct : Bool) (residual : Expr) (error : Exception) :
    TacticM Exception := do
  let refuted ← if residual.consumeMData.isConstOf ``False then pure true
    else if isNumeralEquality residual then
      tryCatchRuntimeEx
        (do
          discard <| KernelReadBack.decideByKernel "CAS determinant residual" (mkNot residual)
          pure true)
        fun failure ↦ do
          if failure.isRuntime then throw failure
          pure false
    else
      pure false
  let became := m!"cas evaluated the determinant with `norm_det`; the goal became\
    {indentExpr residual}"
  let note := if !refuted then became
    else if direct then m!"{became}\nwhich is false, so the stated value is not the determinant."
    else m!"{became}\nwhich is false."
  return .error (← getRef) m!"{note}\n{error.toMessageData}"

/-! ## The stages of `cas` -/

/-- What one run of the stages of `cas` shares: its inputs, the classification of the goal and
the failures recorded for the final report. -/
private structure Search where
  side? : Option (TSyntax `term)
  defs? : Option (Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
  /-- `defs?` with the `using` term added as a simp lemma, for the arithmetic script. -/
  arithmeticDefs? : Option (Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
  kind : Classify.GoalKind
  /-- Whether the goal was `Matrix.det A = v` or `v = Matrix.det A` before the stages ran. -/
  direct : Bool
  /-- The goal after the evaluation of determinants, with the state to restore before the
  failure report names it. -/
  residual? : Option (Expr × Tactic.SavedState) := none
  /-- Whether the arithmetic script already failed on the goal as it stands. -/
  arithmeticTried : Bool := false
  /-- The failure of the reflected symbolic route on a reflected equality; the later stages then
  read the goal as an ordinary equality (`kind` is `.equality`). -/
  reflectedError? : Option Exception := none
  /-- The failure of the exposure of evaluated checked expressions in a relation; the later
  stages then read the relation unexposed. -/
  exposureError? : Option Exception := none
  earlyCommandError? : Option Exception := none
  derivativeFailure? : Option MessageData := none
  integralError? : Option Exception := none
  equations : Array (TSyntax `term) := #[]
  hintError? : Option Exception := none
  equationError? : Option Exception := none
  identityError? : Option Exception := none
  boxError? : Option Exception := none
  commandError? : Option Exception := none
  elementaryError? : Option Exception := none
  normNumError? : Option Exception := none
  grindError? : Option Exception := none
  registeredErrors : Array (Name × Exception) := #[]

/-- A stage of `cas`. It closes the main goal and returns its route, or records its failure in the
search and returns `none`, or throws to end the search. -/
private structure Stage where
  name : Name
  priority : Nat
  run : IO.Ref Search → TacticM (Option SelectedRoute)

private def isRelation (kind : Classify.GoalKind) : Bool :=
  kind == .equality || kind == .disequality || kind == .order

/-- Determinants of matrix literals in a relation are evaluated first: left in place, they send
`rfl` and `simp` in the later stages into a definitional or row-by-row expansion. The certificate
of a large determinant is a deep term, so its evaluation and validation get a deeper recursion
limit. -/
private def determinantStage (search : IO.Ref Search) : TacticM (Option SelectedRoute) := do
  unless isRelation (← search.get).kind do return none
  let goal ← getMainGoal
  let target ← withMainContext <| instantiateMVars (← goal.getType)
  let siblings := (← getGoals).drop 1
  let unassignedSiblings ← siblings.filterM fun sibling ↦
    return !(← sibling.isAssignedOrDelayedAssigned)
  let (closed, evaluated) ← withAtLeastMaxRecDepth Tactic.Determinant.recursionDepth do
    if ← Tactic.Determinant.evaluate then
      for sibling in unassignedSiblings do
        if ← sibling.isAssignedOrDelayedAssigned then
          throwError "CAS determinant evaluation assigned a sibling goal"
      if (← getGoals) == siblings then
        discard <| ProofCarrier.validateAssignedProof "CAS determinant evaluation" goal target
        return (true, true)
      return (false, true)
    return (false, false)
  if closed then
    return some .arithmetic
  if evaluated then
    let residual ← withMainContext do instantiateMVars (← getMainTarget)
    let saved ← saveState
    search.modify fun state ↦
      { state with residual? := some (residual, saved), kind := Classify.goalKind residual }
  return none

/-- The goals of the algebra, matrix and number theory commands go to the command route first:
the algebraic-equality stage would, for example, try to evaluate a modular power directly. A
computed value that differs from the stated one ends the search, since the later stages would only
evaluate the same terms, for instance a power with a huge exponent. -/
private def algebraStatementStage (search : IO.Ref Search) : TacticM (Option SelectedRoute) := do
  unless CommandShapes.isAlgebraStatement (← withMainContext do
      instantiateMVars (← getMainTarget)) do
    return none
  match ← attemptCommandRoute (← search.get).side? with
  | some (.ok result) => return some (.command result)
  | some (.error error) =>
      if CommandShapes.isRefutation error then throw error
      search.modify ({ · with earlyCommandError? := some error })
      return none
  | none => return none

private def algebraicEqualityStage (search : IO.Ref Search) :
    TacticM (Option SelectedRoute) := do
  unless (← search.get).kind == .equality do return none
  if let .ok _ ← attemptRoute "CAS algebraic equality"
      Tactic.Arithmetic.closeAlgebraicEquality then
    return some .arithmetic
  return none

/-- A limit or a count of real roots is the statement of a `#cas` command. Its failure leads the
report, and the later stages still run, since supplied lemmas or hypotheses can simplify such a
statement. -/
private def commandStatementStage (search : IO.Ref Search) :
    TacticM (Option SelectedRoute) := do
  if (← search.get).earlyCommandError?.isSome then return none
  unless ← isCommandStatement do return none
  match ← attemptCommandRoute (← search.get).side? with
  | some (.ok result) => return some (.command result)
  | some (.error error) =>
      search.modify ({ · with earlyCommandError? := some error })
      return none
  | none => return none

/-- Derivative statements (see `closeDerivative`). Evaluated checked-expression constants inside
an ordinary relation are exposed first, so that this stage and the arithmetic stages see ordinary
real syntax; a relation whose exposure fails goes on unexposed, with the failure kept for the
report, and one that the unfolding of the evaluator proves is closed as `.arithmetic`. When the
derivative routes fail, an equality goes to the arithmetic script with the derivatives as atoms
and a goal with an interval integral to the integral stage; otherwise the derivative failure ends
the search. -/
private def derivativeStage (search : IO.Ref Search) : TacticM (Option SelectedRoute) := do
  let state ← search.get
  if isRelation state.kind then
    let unsolved := (← getUnsolvedGoals).length
    let saved ← saveState
    try Tactic.DerivativeBridge.exposeCheckedExpressions "cas"
    catch error =>
      saved.restore
      search.modify ({ · with exposureError? := some error })
    if (← getUnsolvedGoals).length < unsolved then return some .arithmetic
  unless ← isDerivativeGoal do return none
  match ← attemptRoute "CAS derivative route" (closeDerivative state.side?) with
  | .ok _ => return some .derivative
  | .error derivativeError =>
      if state.kind == .equality then
        if let .ok _ ← attemptArithmeticRoute state.arithmeticDefs? then
          return some .arithmetic
        search.modify ({ · with arithmeticTried := true })
      unless ← mentionsIntervalIntegral do
        throw derivativeError
      return none

/-- Goals with an interval integral go to the integral route of `CAS.IntegrationTactic`. When it
fails on a relation, the arithmetic script runs with the integrals as atoms, since an integral
inside an opaque argument can remain an atom in a rational identity or order goal; otherwise the
integral failure ends the search. A goal with a Bochner integral and no interval integral, such
as an improper integral, goes to the integral route when it is loaded, and its failure passes the
goal on to the later stages. -/
private def integralStage (search : IO.Ref Search) : TacticM (Option SelectedRoute) := do
  let interval ← mentionsIntervalIntegral
  unless interval do
    unless (← Tactic.RouteRegistry.closer? `integral).isSome && (← mentionsBochnerIntegral) do
      return none
  let state ← search.get
  match ← attemptRoute "CAS integral dispatch" (closeIntegralRoute state.side?) with
  | .ok closed => return some closed.value
  | .error integralError =>
      unless interval do
        search.modify ({ · with integralError? := some integralError })
        return none
      if isRelation state.kind && !state.arithmeticTried then
        if let .ok route ← withoutRecover <| attemptArithmeticRoute state.arithmeticDefs? then
          return some route
      throw integralError

/-- Whether `e` is the literal `0`. -/
private def isZeroLiteral (e : Expr) : Bool :=
  let e := e.consumeMData
  (e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).rawNatLit? == some 0) ||
    e.isAppOfArity ``Zero.zero 2

/-- Whether the main goal is `Set.EqOn f g s` or `ApproxOn f g s 0`, which hold when `f x = g x`
for every `x ∈ s`. -/
private def isPointwiseTarget : TacticM Bool := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  return target.isAppOfArity ``Set.EqOn 5 ||
    (target.isAppOfArity ``CAS.Certificate.ApproxOn 7 && isZeroLiteral target.appArg!)

/-- Prove `Set.EqOn f g s` or `ApproxOn f g s 0` from the equality `f x = g x` under `x ∈ s`,
which `recurse`, the stages of `cas`, proves. -/
private def closePointwise (recurse : TacticM SelectedRoute) : TacticM SelectedRoute := do
  let target ← withMainContext do return (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOfArity ``Set.EqOn 5 do
    evalTactic (← `(tactic| apply CAS.Certificate.approxOn_of_eqOn))
  evalTactic (← `(tactic| intro x hx))
  let goal ← getMainGoal
  let pointwise ← goal.withContext do Core.betaReduce (← instantiateMVars (← goal.getType))
  replaceMainGoal [← goal.change pointwise]
  recurse

/-- Semantic targets go to the checked `Verified.Expr` pipeline and, between ordinary functions,
to the pointwise route; their failure ends the search. -/
private def semanticStage (recurse : TacticM SelectedRoute) (search : IO.Ref Search) :
    TacticM (Option SelectedRoute) := do
  let state ← search.get
  unless state.kind == .semantic do return none
  match ← attemptSemanticRoute state.side? with
  | .ok route => return some route
  | .error (semanticError, inferredSideError?) =>
      unless ← isPointwiseTarget do
        throwSemanticFailure semanticError inferredSideError?
      match ← attemptRoute "CAS pointwise route" (closePointwise recurse) with
      | .ok closed => return some (.pointwise closed.value)
      | .error pointwiseError =>
          throwSemanticFailure semanticError inferredSideError? pointwiseError

/-- A reflected equality goes to the raw symbolic route, then to the side-conditioned normalizer.
When both fail, the goal goes on to the later stages as an ordinary equality whose evaluations are
atoms, so that the arithmetic script can unfold them with the lemmas of `cas [l₁, l₂]`; the
failure of the reflected route leads the final report. -/
private def reflectedEqualityStage (search : IO.Ref Search) :
    TacticM (Option SelectedRoute) := do
  let state ← search.get
  unless state.kind == .reflectedEquality do return none
  match ← attemptRoute "CAS raw symbolic route" (runRawSymbolic state.side? state.defs?) with
  | .ok _ => return some .rawSymbolic
  | .error rawError =>
      search.modify ({ · with reflectedError? := some rawError, kind := .equality })
      return none

/-- The Mathlib arithmetic script on an ordinary relation, after every derivative subterm of an
explicit function is rewritten to its checked closed form; retried once with the real-valued
definitions of the current module unfolded, while imported definitions stay folded. -/
private def arithmeticStage (search : IO.Ref Search) : TacticM (Option SelectedRoute) := do
  let state ← search.get
  unless isRelation state.kind do return none
  let derivativeFailure? ← Tactic.DerivativeRewrite.prepareIdentity state.side?
  search.modify ({ · with derivativeFailure? })
  if let .ok route ← attemptArithmeticRoute state.arithmeticDefs? then
    return some route
  if ← Tactic.DerivativeRewrite.unfoldLocalRealDefinitions then
    if let .ok route ← attemptArithmeticRoute state.arithmeticDefs? then
      return some route
  return none

/-- An equation hypothesis supplied with `using` is used as a polynomial multiple of a real goal
after clearing denominators, and is passed to polynomial consequence search over the goal's
commutative ring. -/
private def equationHintStage (search : IO.Ref Search) : TacticM (Option SelectedRoute) := do
  let state ← search.get
  let some side := state.side? | return none
  unless state.kind == .equality do return none
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  let some (carrier, _, _) := target.consumeMData.eq? | return none
  unless ← isEquationOver side carrier do return none
  search.modify ({ · with equations := #[side] })
  unless ← ProofCarrier.isDefEqReadOnly carrier (mkConst ``Real) do return none
  match ← attemptEquationHintRoute side with
  | .ok route => return some route
  | .error error =>
      search.modify ({ · with hintError? := some error })
      return none

private def polynomialEquationsStage (search : IO.Ref Search) :
    TacticM (Option SelectedRoute) := do
  let state ← search.get
  unless state.kind == .equality do return none
  match ← attemptPolynomialEquations state.equations with
  | .ok route => return some route
  | .error error =>
      search.modify ({ · with equationError? := some error })
      return none

private def checkedIdentityStage (search : IO.Ref Search) : TacticM (Option SelectedRoute) := do
  let state ← search.get
  unless state.kind == .equality do return none
  match ← attemptCheckedIdentityRoute state.side? state.defs? with
  | .ok route => return some route
  | .error error =>
      search.modify ({ · with identityError? := some error })
      return none

/-- An order goal on real variables bounded by rational literal hypotheses is a finite-box
question, which the checked CEGA box query of `CAS.CEGA` answers. -/
private def boxStage (search : IO.Ref Search) : TacticM (Option SelectedRoute) := do
  let kind := (← search.get).kind
  unless kind == .order || kind == .other do return none
  match ← attemptBoxInequalityRoute with
  | some (.ok query) => return some (.boxInequality query)
  | some (.error error) =>
      search.modify ({ · with boxError? := some error })
      return none
  | none => return none

/-- A polynomial sign condition in a variable that no hypothesis bounds, or a root in an
interval, is the statement of `#cas [reduce x]` or `#cas [roots x]`. -/
private def commandStage (search : IO.Ref Search) : TacticM (Option SelectedRoute) := do
  let state ← search.get
  unless state.kind == .order || state.kind == .other do return none
  if state.earlyCommandError?.isSome then return none
  match ← attemptCommandRoute state.side? with
  | some (.ok result) => return some (.command result)
  | some (.error error) =>
      search.modify ({ · with commandError? := some error })
      return none
  | none => return none

/-- An identity among elementary functions may need a multiple-angle formula, the exponential of
a multiple of a logarithm, or a sum of real exponents. -/
private def elementaryStage (search : IO.Ref Search) : TacticM (Option SelectedRoute) := do
  let state ← search.get
  unless state.kind == .equality do return none
  unless ← Tactic.ElementaryRewrites.applicable do return none
  match ← attemptRoute "CAS elementary rewrite route"
      (Tactic.ElementaryRewrites.close state.arithmeticDefs?) with
  | .ok _ => return some .elementary
  | .error error =>
      search.modify ({ · with elementaryError? := some error })
      return none

private def normNumStage (search : IO.Ref Search) : TacticM (Option SelectedRoute) := do
  unless (← search.get).kind == .other do return none
  let closed ← withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    pure (!target.hasFVar && !target.hasMVar)
  unless closed do return none
  match ← Tactic.Fallback.attemptWithinBudget "norm_num"
      (attemptRoute "CAS norm_num fallback" Tactic.Fallback.closeClosedByNormNum) with
  | .ok _ => return some .normNum
  | .error error =>
      search.modify ({ · with normNumError? := some error })
      return none

/-- The general automation of core `grind`, under the budget `cas.grindHeartbeats`. It runs last
so that every goal an earlier stage proves keeps that stage's proof. -/
private def grindStage (search : IO.Ref Search) : TacticM (Option SelectedRoute) := do
  let kind := (← search.get).kind
  unless isRelation kind || kind == .other do return none
  match ← attemptGrind with
  | .ok _ => return some .grind
  | .error error =>
      search.modify ({ · with grindError? := some error })
      return none

/-- The built-in stages of `cas` with their priorities. -/
private def builtinStages (recurse : TacticM SelectedRoute) : Array Stage := #[
  { name := `determinant, priority := 2000, run := determinantStage },
  { name := `algebraStatement, priority := 1900, run := algebraStatementStage },
  { name := `algebraicEquality, priority := 1800, run := algebraicEqualityStage },
  { name := `commandStatement, priority := 1700, run := commandStatementStage },
  { name := `derivative, priority := 1600, run := derivativeStage },
  { name := `integral, priority := 1500, run := integralStage },
  { name := `semantic, priority := 1400, run := semanticStage recurse },
  { name := `reflectedEquality, priority := 1300, run := reflectedEqualityStage },
  { name := `arithmetic, priority := 1200, run := arithmeticStage },
  { name := `equationHint, priority := 1150, run := equationHintStage },
  { name := `polynomialEquations, priority := 1100, run := polynomialEquationsStage },
  { name := `checkedIdentity, priority := 1050, run := checkedIdentityStage },
  { name := `box, priority := 900, run := boxStage },
  { name := `command, priority := 800, run := commandStage },
  { name := `elementary, priority := 700, run := elementaryStage },
  { name := `normNum, priority := 600, run := normNumStage },
  { name := `grind, priority := 500, run := grindStage }]

/-- A route registered with `@[cas_route]` as a stage of its own. -/
private def registeredStage (entry : Tactic.RouteRegistry.Registration) : Stage where
  name := entry.route
  priority := entry.priority
  run search := do
    unless ← Tactic.RouteRegistry.accepts entry do return none
    let closer ← Tactic.RouteRegistry.closer entry
    match ← attemptRoute s!"CAS {entry.route} route" (closer (← search.get).side?) with
    | .ok closed => return some (.registered entry.route closed.value)
    | .error error =>
        search.modify fun state ↦
          { state with registeredErrors := state.registeredErrors.push (entry.route, error) }
        return none

/-- The stages of `cas` in the order it runs them: the built-in stages and the routes registered
with `@[cas_route]` (other than the routes of `RouteRegistry.stageProviders`, which built-in
stages call), by priority, a registered route after the built-in stages of equal priority. -/
private def stages (recurse : TacticM SelectedRoute) : CoreM (Array Stage) := do
  let registered := (Tactic.RouteRegistry.extensionRoutes (← getEnv)).map registeredStage
  return (builtinStages recurse ++ registered).insertionSort fun a b ↦ a.priority > b.priority

/-- The stages of `cas` in the current environment, in the order it runs them, with their
priorities. -/
def routeOrder : CoreM (Array (Name × Nat)) := do
  return (← stages (pure .arithmetic)).map fun stage ↦ (stage.name, stage.priority)

/-- The failure report of `cas` after every stage declined or failed. -/
private def throwSearchFailure {α : Type} (state : Search) : TacticM α := do
  let detail (title : String) : Option Exception → MessageData
    | some error => m!"\n{title}:{indentD error.toMessageData}"
    | none => m!""
  let fallbackDetail (title : String) : Option Exception → TacticM MessageData
    | some error => return m!"\n{title}:{indentD (← fallbackSummary error)}"
    | none => return m!""
  let registeredDetail := state.registeredErrors.foldl
    (init := detail "Integral route" state.integralError?) fun detail (route, error) ↦
      detail ++ m!"\nRegistered route {route}:{indentD error.toMessageData}"
  let grindDetail ← fallbackDetail "Grind fallback" state.grindError?
  let commandHeadline : MessageData :=
    "cas could not prove this statement of a `#cas` command."
  let commandDetail :=
    detail "Command theorem route" (state.commandError? <|> state.earlyCommandError?)
  let boxDetail := detail "Box enclosure route" state.boxError?
  if isRelation state.kind then
    let exposureDetail := detail "Exposure of checked expressions" state.exposureError?
    let derivativeDetail := match state.derivativeFailure? with
      | none => m!""
      | some failure => m!"\nDerivative subterms were left in place: {failure}"
    let hintDetail := detail "Equation hint route" state.hintError?
    let equationDetail := detail "Polynomial equation route" state.equationError?
    let identityDetail := detail "Checked identity route" state.identityError?
    let elementaryDetail := detail "Elementary rewrite route" state.elementaryError?
    if let some reflectedError := state.reflectedError? then
      throwError "cas failed on a reflected symbolic equality:\
        {indentD reflectedError.toMessageData}{exposureDetail}{derivativeDetail}{hintDetail}\
        {equationDetail}{identityDetail}{boxDetail}{elementaryDetail}{commandDetail}\
        {registeredDetail}{grindDetail}"
    if state.earlyCommandError?.isSome then
      throwError "{commandHeadline}{commandDetail}{exposureDetail}{derivativeDetail}{hintDetail}\
        {equationDetail}{identityDetail}{boxDetail}{elementaryDetail}{registeredDetail}\
        {grindDetail}"
    let hint? ← withMainContext do
      Classify.analyticSideConditionHint? (← instantiateMVars (← getMainTarget))
    match hint? with
    | some hint =>
        throwError
          "cas could not close this ordinary arithmetic goal.\n{hint}{exposureDetail}\
            {derivativeDetail}{hintDetail}{equationDetail}{identityDetail}{boxDetail}\
            {elementaryDetail}{commandDetail}{registeredDetail}{grindDetail}"
    | none =>
        throwError
          "cas could not prove this arithmetic relation. The statement may be false, or it \
            may lie outside the supported normalization and arithmetic fragment\
            {exposureDetail}{derivativeDetail}{hintDetail}{equationDetail}{identityDetail}\
            {boxDetail}{elementaryDetail}{commandDetail}{registeredDetail}{grindDetail}"
  let normNumDetail ← fallbackDetail "norm_num fallback" state.normNumError?
  if state.earlyCommandError?.isSome then
    throwError "{commandHeadline}{commandDetail}{boxDetail}{registeredDetail}{grindDetail}\
      {normNumDetail}"
  throwError
    "cas expected a checked semantic proposition, reflected equality, arithmetic \
     relation, an ordinary inequality on real variables bounded by rational literal \
     hypotheses (a two-sided bound `a ≤ f x ∧ f x ≤ b`, a membership \
     `f x ∈ Set.Icc a b`, or a universally quantified bound), or the statement of a \
     `#cas` command (a limit, a polynomial root count, a polynomial sign condition)\
     {commandDetail}{boxDetail}{registeredDetail}{grindDetail}{normNumDetail}"

/--
Implementation hook for `cas` and `cas?`.

It closes a supported exact symbolic goal and returns diagnostic metadata identifying the
theorem-producing route. Positive-error certificates belong to `cega`, not this exact frontend.

The stages run in the order `routeOrder` lists. Determinants of matrix literals are evaluated
first. The statements of the algebra, matrix and number theory commands, limits and root counts
go to the `command` route of `Tactic.RouteRegistry` before and after the algebraic closure of an
equality. Derivative shapes (see `closeDerivative`) report `.derivative`; an equality falls back
to the arithmetic script when differentiation fails. The integration route, registered in
`Tactic.RouteRegistry` by `CAS.IntegrationTactic`, can apply an analytic theorem, one
integration-by-parts step or check a primitive, and returns `.integral` with its replay and
explanation; when it fails, relations containing integrals can still use ordinary arithmetic,
including denominator clearing. Semantic and reflected targets run the verified `Verified.Expr`
pipeline (the `.semantic`, `.inferredSide` and `.rawSymbolic` outcomes), and `Set.EqOn` and
zero-error `ApproxOn` between ordinary functions are proved pointwise (`.pointwise`). A reflected
equality that the pipeline does not prove goes on to the routes of ordinary equalities, with its
evaluations as atoms, and its failure leads the report when they fail too. Ordinary
equalities, disequalities and order relations first rewrite every derivative subterm of an
explicit function to its checked closed form (`Tactic.DerivativeRewrite.prepareIdentity`), then
run `Tactic.Arithmetic.close`, which uses target simplification with relevant hypotheses,
`field_simp`, `ring`, `norm_num`, `positivity`, `linarith` and `nlinarith`, retried once with the
real-valued definitions of the current module unfolded when it fails; that route reports
`.arithmetic`. A remaining commutative-ring equality is offered to `Tactic.PolynomialEquations`,
which reports `.polynomialEquations` when core `grobner` closes it and `.arithmetic` when guarded
denominator clearing suffices. An ordinary real equality these routes still do not close is
retried by the checked identity route (`Tactic.Identity.closeRealIdentity`, reporting
`.checkedIdentity`), which reflects the two sides over atoms and certifies the checked
normalizer's run in the kernel. An order relation that the script does not close, and a goal
outside the relation language, are offered to the box inequality route installed in
`Tactic.RouteRegistry` by `CAS.CEGA` (reporting `.boxInequality` with the explicit `cega` call it
ran), then to the `command` route; an ordinary real identity goes to the elementary rewrites
(`.elementary`), a proposition outside the relation language without variables to `norm_num`
(`.normNum`), and every goal, last, to `grind` under the budget `cas.grindHeartbeats` (`.grind`).
A route registered with `@[cas_route]` under another name runs at its priority and reports
`.registered`. The hint attached to an arithmetic failure comes from
`Classify.analyticSideConditionHint?`, which reads denominators and branch subterms off the goal
syntax, and is followed by the derivative subterms that could not be rewritten and by the checked
route's own failure, which names the recorded conditions it could not prove.
-/
partial def closeCore (side? : Option (TSyntax `term))
    (defs? : Option (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := none) :
    TacticM SelectedRoute := do
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  let arithmeticDefs? ← liftMacroM <| arithmeticLemmas side? defs?
  let initial : Search := {
    side? := side?, defs? := defs?, arithmeticDefs? := arithmeticDefs?
    kind := Classify.goalKind target, direct := isDeterminantValueEquation target }
  let search ← IO.mkRef initial
  let ordered ← stages (closeCore side? defs?)
  try
    for stage in ordered do
      if let some route ← stage.run search then
        return route
    throwSearchFailure (← search.get)
  catch error =>
    -- After a determinant evaluation the report names the goal that remained.
    let state ← search.get
    let some (residual, saved) := state.residual? | throw error
    let .error .. := error | throw error
    let report ← determinantFailure state.direct residual error
    saved.restore
    throw report

/-- `closeCore` with the explicit evidence `side?` validated once, as every form of `cas` takes
it. -/
def close (side? : Option (TSyntax `term))
    (defs? : Option (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := none) :
    TacticM SelectedRoute := withValidatedUsing side? fun side? ↦ closeCore side? defs?

/--
Close a target using separately elaborated proposition proofs as local facts.

Every fact is checked before attempting a proof, even if the target is reflexive or the
fact is redundant. Only the equality subset over the target's coefficient type is passed
to polynomial consequence search. All facts remain available to arithmetic and analytic
side-condition discharge. Failure restores the original goals and local context.
-/
def closeWithFacts (facts : Array (TSyntax `term)) : TacticM SelectedRoute :=
  ProofCarrier.preservingStateOnFailure do
    let proofs ← withMainContext do
      facts.mapM fun fact ↦ do
        let proof ← Term.withoutErrToSorry <| Term.elabTerm fact none
        let proof ← ProofCarrier.checkCompletedProof "CAS fact hint" proof
        unless ← isProp (← inferType proof) do
          throwErrorAt fact "cas using [...] expects complete proposition proofs"
        return proof
    let carrier? ← withMainContext do
      return (← instantiateMVars (← getMainTarget)).consumeMData.eq?.map (·.1)
    let mut equations := #[]
    for proof in proofs do
      let isEquation ← withMainContext do
        let type ← whnf (← inferType proof)
        match carrier?, type.eq? with
        | some carrier, some (hintCarrier, _, _) =>
            ProofCarrier.isDefEqReadOnly hintCarrier carrier
        | _, _ => pure false
      let name ← mkFreshUserName `hcasFact
      let (_, goal) ← withMainContext <| (← getMainGoal).note name proof
      replaceMainGoal [goal]
      if isEquation then
        equations := equations.push (⟨mkIdent name⟩ : TSyntax `term)
    if !equations.isEmpty then
      if let .ok route ← attemptPolynomialEquations equations then
        return route
    close none

/-! ## The route record of `cas?` -/

/-- While `cas?` runs a form of `cas`, the route that closed the goal, `some none` until the form
records one; `none` otherwise. -/
private initialize routeRecord : EnvExtension (Option (Option SelectedRoute)) ←
  registerEnvExtension (pure none) (asyncMode := .local)

/-- Record `route` as the route that closed the goal, when `cas?` runs this form of `cas`, and
return whether it does. A frontend that elaborates its own form of `cas` records the route it
ran. A form that ends by suggesting a call records the suggestion as the route's replay and adds
its own suggestion only outside `cas?`, which suggests the recorded replay. -/
def recordRoute (route : SelectedRoute) : TacticM Bool := do
  let some _ := routeRecord.getState (← getEnv) | return false
  modifyEnv (routeRecord.setState · (some (some route)))
  return true

/-- Run the tactic `stx`, a form of `cas`, and return the route its elaborator recorded with
`recordRoute`, or `none` when it records none. -/
def runRecordingRoute (stx : Syntax) : TacticM (Option SelectedRoute) := do
  let previous := routeRecord.getState (← getEnv)
  modifyEnv (routeRecord.setState · (some none))
  try
    evalTactic stx
    return (routeRecord.getState (← getEnv)).join
  finally
    modifyEnv (routeRecord.setState · previous)

/-! ## Public tactic syntax -/

/-- Elaborate the lemmas of `cas [l₁, l₂]` before any route runs, each as `simp only [l]`
elaborates it in the context of the main goal, so that an unknown name or an ill-typed lemma
fails at once instead of when a route that uses the lemmas runs. The tactic state and messages
are restored afterwards. -/
private def checkLemmas (args : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :
    TacticM Unit := do
  let saved ← saveState
  for arg in args do
    try
      discard <| withoutRecover <| mkSimpContext (← `(tactic| simp only [$arg])) false
    catch error =>
      saved.restore
      throw error
  saved.restore

/-- The core forms of `cas`: bare `cas`, `cas using h`, `cas using [h₁, h₂]` and `cas [l₁, l₂]`.
The lemmas of `cas [l₁, l₂]` are elaborated before the routes run (`checkLemmas`). The frontends
elaborate their own forms. -/
@[tactic tacticCas] def evalCas : Tactic := fun stx ↦ do
  match stx with
  | `(tactic| cas) =>
      ProofCarrier.tacticEntry "cas" do discard <| recordRoute (← close none)
  | `(tactic| cas using [$facts,*]) =>
      ProofCarrier.tacticEntry "cas using" do
        discard <| recordRoute (← closeWithFacts facts.getElems)
  | `(tactic| cas using $side:term) =>
      ProofCarrier.tacticEntry "cas using" do discard <| recordRoute (← close (some side))
  | `(tactic| cas [$defs,*]) =>
      ProofCarrier.tacticEntry "cas" do
        checkLemmas defs.getElems
        discard <| recordRoute (← close none (some defs))
  | _ => throwUnsupportedSyntax

/-- `cas_nf` rewrites the real terms of the goal, or of the hypotheses that `at` names, to a normal
form, with a checked proof of each rewrite.

## Theorem
`cas_nf` turns the goal `P e` into `P e'`, and `cas_nf at h` turns `h : P e` into `h : P e'`,
where `e'` is the normal form of `e` and the rewrite comes with a proof of `e = e'`. A polynomial
gets the normal form of Mathlib's `ring_nf`, such as `x * y * 2 + x ^ 2 + y ^ 2` for
`(x + y) ^ 2`; an analytic or reflected expression, with quotients, roots, logarithms or
trigonometric functions, gets the normal form of the checked symbolic routes. A goal that becomes
a reflexive equality is closed.

## Conditions and limits
`at h`, `at h ⊢` and `at *` choose the locations as for `simp`; the default is the goal. A
rewrite that needs a domain condition, such as `x - y ≠ 0` to cancel `(x ^ 2 - y ^ 2) / (x - y)`
to `x + y`, takes it from the local context, or from `h` in `cas_nf using h`; for a reflected
evaluator, `h` proves each exact side bundle. `cas_nf` normalizes and is not an equality solver:
two equal analytic expressions can keep different normal forms. It fails when it changes nothing.
In `conv` mode, `cas_nf` and `cas_nf using h` rewrite the focused term.

## Options
None.

## Examples
```lean
example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  cas_nf
```
```lean
example (F : ℝ → ℝ) (x y z : ℝ) (hden : x - y ≠ 0) (h : F (x + y) = z) :
    F ((x ^ 2 - y ^ 2) / (x - y)) = z := by
  cas_nf using hden
  exact h
```
```lean
example (P : ℝ → ℝ → Prop) (x y : ℝ) (h : P (x * y * 2 + x ^ 2 + y ^ 2) ((x + y) ^ 2)) :
    P ((x + y) ^ 2) ((x + y) ^ 2) := by
  conv =>
    arg 1
    cas_nf
  exact h
```

## In a proof
```lean
theorem square_le (x y c : ℝ) (h : (x + y) ^ 2 ≤ c) : x ^ 2 + 2 * x * y + y ^ 2 ≤ c := by
  cas_nf at h ⊢
  exact h
```
`cas_nf at h ⊢` brings the hypothesis and the goal to the same normal form, and `exact h` closes
the goal.

## See also
Mathematica `Simplify` and `Together`, SymPy `simplify`, Mathlib `ring_nf` and `field_simp`. The
tactic `cas` and the modes `simplify`, `expand` and `together`.

## Possible issues
```lean
example (P : ℝ → Prop) (x : ℝ) (h : P x) : P x := by
  cas_nf
```
```output
`cas_nf` made no progress on the goal
```
The goal is in normal form already, and `exact h` closes it.
```lean
example (P : ℝ → Prop) (x : ℝ) (h : P ((x ^ 2 - 1) / (x - 1))) : P (x + 1) := by
  cas_nf at h
  exact h
```
```output
cas_nf could not prove the real analytic domain conditions.
A denominator or logarithm argument may need to be nonzero, a square-root argument may need to be
positive, or an inverse-trigonometric argument may need to avoid a branch endpoint. Supply the
relevant ordinary hypothesis with `cas_nf using h`.
```
The message lists the unproved condition, that `x - 1` is nonzero. A proof `hx : x - 1 ≠ 0`, in
the local context or as `cas_nf using hx at h`, lets `cas_nf` cancel the quotient.
-/
elab "cas_nf" loc:(location)? : tactic =>
  Tactic.RealNormalization.normalizeAtLocation none
    ((loc.map expandLocation).getD (.targets #[] true))

/-- `cas_nf using h` normalizes as `cas_nf` does, with `h` as additional domain evidence: for a
reflected evaluator, `h` proves each exact side bundle, and for ordinary terms it supplies facts
to the domain solver.
-/
@[tactic_alt tacticCas_nf_]
elab "cas_nf" " using " side:term loc:(location)? : tactic =>
  discard <| withValidatedUsing (noteFact := false) (some side) fun evidence? ↦ do
    Tactic.RealNormalization.normalizeAtLocation evidence?
      ((loc.map expandLocation).getD (.targets #[] true))
    return .arithmetic

/-- `cas_nf using h` normalizes as `cas_nf` does, with `h` as additional domain evidence: for a
reflected evaluator, `h` proves each exact side bundle, and for ordinary terms it supplies facts
to the domain solver.
-/
tactic_extension tacticCas_nf_

/-- `cas_nf` in `conv` mode rewrites the focused term to its normal form, as the tactic `cas_nf`
does, with a checked proof of the replacement.
-/
elab (name := convCasNF) "cas_nf" : conv =>
  Tactic.RealNormalization.normalizeConv none

/-- `cas_nf using h` in `conv` mode rewrites the focused term as the `conv` form `cas_nf` does, with
`h` as additional domain evidence, as for the tactic `cas_nf using h`.
-/
elab (name := convCasNFUsing) "cas_nf" " using " side:term : conv =>
  discard <| withValidatedUsing (noteFact := false) (some side) fun evidence? ↦ do
    Tactic.RealNormalization.normalizeConv evidence?
    return .arithmetic

end ExactTactic
end CAS

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.CEGA.Elaboration
public import CAS.CEGA.Integration
public meta import CAS.CEGA.Integration
public import CAS.CEGA.ExpressionSyntax
public meta import CAS.CEGA.ExpressionSyntax
public import CAS.CEGA.Query
public import CAS.ExactTactic
public import CAS.Tactic.BoxInequality
public meta import CAS.Tactic.BoxInequality
public import CAS.Tactic.CEGA
public import CAS.Continuum.Interval.Inclusion.Elementary
import Mathlib.Tactic.Inclusion.Core.Elab
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Certified Enclosures, Guarantees, and Approximations

`cega` proves statements about real expressions on finite boxes with checked rational
interval arithmetic. The main forms are:

* Bare `cega` first projects a checked carrier (a certificate, a `CertificateRoute`, or a
  registered attempt type) found in the local context or in the goal, through its soundness
  theorem (`CAS.Tactic.CEGA`). A goal about one interval integral `∫ x in a..b, f x` with
  rational limits and a closed elementary integrand is proved by a checked batch quadrature
  (`CAS.CEGA.Integration`): Simpson panels with a fourth-derivative remainder where the domain
  checker certifies the integrand and its first four derivatives on `[a, b]`, and range panels,
  which need only continuity, otherwise; the panel count doubles until the goal holds, up to
  `cega.maxIntegrationPanels`, or `(panels := n)` sets it. A certificate goal
  (`EnclosedOn f s lo hi`, `BoundOn f s c`, `ApproxOn f g s ε`, `ResidualBound r s ε`) whose
  domain `s` is a coordinate box is unfolded to an ordinary goal on the coordinates of its
  point. An ordinary inequality on real variables bounded by rational literal hypotheses, or a
  conjunction of such inequalities, is proved by the checked query on the box those hypotheses
  describe (`CAS.Tactic.BoxInequality`). A goal without free variables that no route proves,
  such as a conjunction, a negation or an equality of real constants, is evaluated with
  `dyadic_interval [cega_real, prec := n]` (`CAS.Continuum.Interval.Inclusion.Elementary`), with
  `n` from `(prec := n)`, about `3.3 d + 8` for `(digits := d)`, and `32` otherwise. If the
  semantic routes refuse a closed decidable proposition, bare `cega` tries a kernel certificate
  check. When the box query does not prove the bound, the box route subdivides the box, by
  default to depth two; `cega (prec := n) (depth := n)` sets the precision and that depth.
* `cega using h` projects the one carrier `h`. The proof keeps every hypothesis and axiom that
  the proof of `h` uses, a native-evaluation axiom included, and projection does not check
  where the data of `h` came from; `cega.nativeCertificates` governs only new checks.
* `cega [fast]` first tries a closed finite decidable certificate, then the computable
  natural interval evaluator. These numerical checks use native evaluation when
  `cega.nativeCertificates` is true, and trust Lean's compiler and runtime; their generated
  axioms have names containing `_native.cegaFast.ax`. The option is false by default, and then
  `cega [fast]` is bare `cega`. Failed native attempts restore the proof state and environment
  before kernel CEGA runs. The ordinary symbolic proofs and semantic planner remain kernel
  checked.
* `cega [enclose x in [a, b], …] e` runs the query on `e` over the stated rational box and
  proves the projection the goal needs. The goal is a certificate proposition
  (`EnclosedOn f s lo hi`, `BoundOn f s c`, `ApproxOn f g s ε`) whose domain `s` lies in the box,
  or an ordinary inequality on the box's variables; an enclosure, an upper bound, an absolute
  bound for `BoundOn (fun x ↦ |f x|) s c` or `|f x| ≤ c`, or a midpoint approximation is
  certified accordingly. A configuration such as `(prec := 40)` sets the precision policy, and
  `(depth := 3)` computes the enclosure after three levels of checked box refinement, whichever
  of these the goal needs.

For example, `x * (1 - x) ≤ 1 / 4` under `0 ≤ x` and `x ≤ 1` is closed by bare `cega` and by
`cega [enclose x in [0, 1]] (x * (1 - x))`. A hypothesis `|x| ≤ r` or `|x| < r` gives the box
`[-r, r]`, and an applied term such as `f x` is a coordinate when hypotheses bound it. A closed
inequality such as `Real.sqrt 2 ≤ 2` uses the box with no coordinates, written
`cega [enclose] √(2 : ℝ)` in explicit form. A nonrational closed endpoint is compared by the same
checked evaluator, so `Real.exp x ≤ Real.exp 3` is proved on `x ∈ Set.Icc 0 1`.

A query certifies the value of a total expression on a closed box. Analytic domain conditions,
such as those needed for differentiation, are separate obligations. Strict hypotheses are
weakened to closed bounds, so a strict goal needs a strict gap between the requested bound and
the certified endpoint.

Importing `CAS.CEGA` registers `boxRoute` with `@[cas_route box]`, and bare `cas` calls it from
its `box` stage (`CAS/ExactTactic.lean`) when its earlier stages, its Mathlib arithmetic script
among them, have not closed the goal. The numerical `#cas` commands come with `CAS`, and `cega?`
reporting with `CAS.Reporting`.

## Main definitions

* `closeBare`: the routes of bare `cega`, in their order, with a refusal that leads with the
  reason of the route that applies to the goal.
* `closeEncloseQuery`: the explicit query `cega [enclose x in [a, b]] e`.
* `closeBoxQuery`: run a checked box query and close a certificate goal, or an ordinary
  inequality on the box's variables, with its result.
* `closeClosedByInclusion`, `inclusionQuery`: `dyadic_interval` with the `cega_real` ranges on a
  goal without free variables.
* `BareRoute`: the route by which bare `cega` closed a goal and, except for a projected carrier,
  the call that replays it.
* `boxRoute`: the box route as a route of bare `cas`.

## Implementation notes

Bare `cega` tries its routes in a fixed order (`closeBare`): the projection of a carrier
(`CAS/Tactic/CEGA.lean`), the quadrature of `CAS/CEGA/Integration.lean`, a certificate goal on a
coordinate box and then an ordinary inequality (`CAS/Tactic/BoxInequality.lean`), and for a
closed goal `dyadic_interval` with the ranges of
`CAS/Continuum/Interval/Inclusion/Elementary.lean`. When all of them refuse a closed decidable
goal, we evaluate its decision in the kernel (`decideClosedCertificate` in
`CAS/CEGA/Elaboration.lean`). The routes compute no enclosure themselves:
`CAS/CEGA/Elaboration.lean` quotes a query, bounds its size and has the kernel evaluate it, and
the planner that the kernel runs, in `CAS/CEGA/Query.lean` (finite charts, monotonicity faces,
the centered mean-value form, checked bisection), carries the references to the classical
interval methods. What we add is the order of the routes, the reading of the goal and the
transport of a checked theorem to the goal as it is stated.

We run every form except native `cega [fast]` as a kernel-only route
(`Tactic.ProofCarrier.withKernelOnlyAxioms`): its proof may use no axiom beyond `propext`,
`Classical.choice` and `Quot.sound` that the goal, the hypotheses it uses, or an explicit carrier
does not already use, and a proof that does is rejected with the axiom's name. Natively checked
theorems are added outside Lean's auxiliary-lemma cache, so a later kernel route for the same
statement, in the same declaration or another, cannot receive one. `CAS.Examples.CEGA.Trust`
tests this contract on the kernel routes.

A goal that states its bounds with closed numerals, such as `EnclosedOn f s (-1) 1` or
`x * (1 - x) ≤ 1 / 4`, is first tried by the stated-bound route: the kernel checks one theorem
that compares the interval of the query with the stated numbers
(`CEGA.Elaboration.checkStatedBounds`), running the planner while it checks, so the search in the
elaborator and the read-back of the endpoints are skipped; the checked theorem is transported to
the goal like a query result. When the kernel rejects the check, bare `cega` checks the
subdivided query the same way, where it would subdivide, and refuses the goal with the values
that its queries certify, read back in one kernel evaluation. The explicit form then runs the
search, whose diagnostics and refusals are the tactic's, so a goal it refuses costs the rejected
check as well. A query that the search has memoized runs the search.

On a certificate goal, the generated proof is accepted when it matches the goal after unfolding;
otherwise it is transported by inclusion of the domains, equality of the functions on the goal's
domain, and endpoint arithmetic, and as a last step the certificate itself is projected by
`Tactic.Certificate.closeUsingCertificate`. When both fail, the error shows both causes,
including the inclusion or endpoint inequality that transport could not prove. Planner traces
and rendered metadata are never proof carriers. Certificate code calls the same checked queries
directly through `CAS.CEGA.Query`.
-/

public meta section

namespace CAS.CEGA

open Lean Elab Tactic Meta
open CAS.CEGA.Elaboration

/-- Compare one applied semantic relation without unfolding the relation itself. -/
private def appliedRelationDefEq?
    (lhs rhs : Lean.Expr) : TacticM Bool := do
  let lhs := lhs.consumeMData
  let rhs := rhs.consumeMData
  unless lhs.getAppFn == rhs.getAppFn do
    return false
  let lhsArgs := lhs.getAppArgs
  let rhsArgs := rhs.getAppArgs
  unless lhsArgs.size = rhsArgs.size do
    return false
  for (lhsArg, rhsArg) in lhsArgs.zip rhsArgs do
    let equivalent ← withTransparency .all <| isDefEq lhsArg rhsArg
    unless equivalent do
      return false
  return true

/--
Prove that an ordinary theorem domain lies inside the exact box certified by a query.

The generated source domain unfolds to finitely many rational coordinate inequalities.
`fin_cases` exposes those coordinates, after which `simp_all` and `norm_num` can use the
set-builder hypotheses of the theorem statement. It is used when a certificate goal's
domain is not definitionally the query box.
-/
private def inferDomainSubsetProof
    (targetDomain sourceDomain : Lean.Expr) : TacticM Lean.Expr := do
  -- Retain set-builder syntax so `simp_all` can use `Set.mem_ofPred_eq` after unfolding a name.
  let predicate ← withTransparency .all <| whnf targetDomain
  let targetDomain ← mkAppM ``Set.ofPred #[predicate]
  let expected ← mkAppM ``Set.Subset #[targetDomain, sourceDomain]
  let proof ← mkFreshExprMVar expected
  let tactic ← `(tactic|
    (intro point membership coordinate; fin_cases coordinate) <;>
      simp_all [CAS.Continuum.RationalInterval.MemReal,
        CAS.Continuum.RationalInterval.ofBounds])
  let remaining ← proof.mvarId!.withContext do
    evalTacticAt tactic proof.mvarId!
  let remaining ← remaining.flatMapM fun goal ↦ goal.withContext do
    evalTacticAt (← `(tactic| norm_num)) goal
  unless remaining.isEmpty do
    let targets ← remaining.mapM fun goal ↦
      goal.withContext do Meta.ppGoal goal
    throwError
      "the theorem domain was not proved to lie inside the certified rational box\
       \n{String.intercalate "\n" (targets.map (·.pretty))}"
  Tactic.ProofCarrier.checkCompletedProof "CEGA theorem-domain inclusion" proof

/-- Use reflexivity when both domains coincide, or prove the needed box inclusion. -/
private def domainSubsetProof
    (targetDomain sourceDomain : Lean.Expr) : TacticM Lean.Expr := do
  if ← withTransparency .all <| isDefEq targetDomain sourceDomain then
    mkAppM ``Set.Subset.refl #[sourceDomain]
  else
    inferDomainSubsetProof targetDomain sourceDomain

/-- Use definitional equality before invoking the reflected-function normalizer. -/
private def functionEqOnProof
    (targetFn sourceFn domain : Lean.Expr) : TacticM Lean.Expr := do
  if ← Tactic.ProofCarrier.isDefEqReadOnly targetFn sourceFn then
    mkAppM ``Set.eqOn_refl #[sourceFn, domain]
  else
    Tactic.Certificate.inferNormalizedEqOnProof targetFn sourceFn domain

/-- Transport a generated enclosure directly to its ordinary theorem presentation. -/
private def assignTransportedEnclosureProof?
    (proof : Lean.Expr) (target : Lean.Expr) : TacticM Bool :=
  Tactic.ProofCarrier.restoringStateOnFalse do
    let source := (← inferType proof).consumeMData
    let target := target.consumeMData
    unless source.getAppFn.isConstOf ``Certificate.EnclosedOn ∧
        target.getAppFn.isConstOf ``Certificate.EnclosedOn do
      return false
    let sourceArgs := source.getAppArgs
    let targetArgs := target.getAppArgs
    unless sourceArgs.size ≥ 4 ∧ targetArgs.size ≥ 4 do
      return false
    let sourceFn := sourceArgs[sourceArgs.size - 4]!
    let sourceDomain := sourceArgs[sourceArgs.size - 3]!
    let sourceLower := sourceArgs[sourceArgs.size - 2]!
    let sourceUpper := sourceArgs[sourceArgs.size - 1]!
    let targetFn := targetArgs[targetArgs.size - 4]!
    let targetDomain := targetArgs[targetArgs.size - 3]!
    let targetLower := targetArgs[targetArgs.size - 2]!
    let targetUpper := targetArgs[targetArgs.size - 1]!
    let hsub ← domainSubsetProof targetDomain sourceDomain
    let hfn ← functionEqOnProof targetFn sourceFn targetDomain
    let lowerGoal ← mkAppM ``LE.le #[targetLower, sourceLower]
    let upperGoal ← mkAppM ``LE.le #[sourceUpper, targetUpper]
    let hlower ←
      Tactic.Certificate.inferArithmeticProof "CEGA enclosure lower endpoint" lowerGoal
    let hupper ←
      Tactic.Certificate.inferArithmeticProof "CEGA enclosure upper endpoint" upperGoal
    let transported ←
      mkAppM ``Certificate.enclosedOn_congr #[proof, hsub, hfn]
    let widened ← mkAppM ``Certificate.enclosedOn_mono #[transported, hlower, hupper]
    Tactic.ProofCarrier.assignExactProof "CEGA enclosure transport" widened

/-- Transport a generated upper bound directly to its ordinary theorem presentation. -/
private def assignTransportedBoundProof?
    (proof : Lean.Expr) (target : Lean.Expr) : TacticM Bool :=
  Tactic.ProofCarrier.restoringStateOnFalse do
    let source := (← inferType proof).consumeMData
    let target := target.consumeMData
    unless source.getAppFn.isConstOf ``Certificate.BoundOn ∧
        target.getAppFn.isConstOf ``Certificate.BoundOn do
      return false
    let sourceArgs := source.getAppArgs
    let targetArgs := target.getAppArgs
    unless sourceArgs.size ≥ 3 ∧ targetArgs.size ≥ 3 do
      return false
    let sourceFn := sourceArgs[sourceArgs.size - 3]!
    let sourceDomain := sourceArgs[sourceArgs.size - 2]!
    let sourceUpper := sourceArgs[sourceArgs.size - 1]!
    let targetFn := targetArgs[targetArgs.size - 3]!
    let targetDomain := targetArgs[targetArgs.size - 2]!
    let targetUpper := targetArgs[targetArgs.size - 1]!
    let hsub ← domainSubsetProof targetDomain sourceDomain
    let hfn ← functionEqOnProof targetFn sourceFn targetDomain
    let upperGoal ← mkAppM ``LE.le #[sourceUpper, targetUpper]
    let hupper ←
      Tactic.Certificate.inferArithmeticProof "CEGA upper-bound endpoint" upperGoal
    let transported ←
      mkAppM ``Certificate.boundOn_congr #[proof, hsub, hfn]
    let widened ← mkAppM ``Certificate.boundOn_mono #[transported, hupper]
    Tactic.ProofCarrier.assignExactProof "CEGA upper-bound transport" widened

/-- Transport a generated midpoint approximation to its ordinary theorem presentation. -/
private def assignTransportedApproxProof?
    (proof : Lean.Expr) (target : Lean.Expr) : TacticM Bool :=
  Tactic.ProofCarrier.restoringStateOnFalse do
    let source := (← inferType proof).consumeMData
    let target := target.consumeMData
    unless source.getAppFn.isConstOf ``Certificate.ApproxOn ∧
        target.getAppFn.isConstOf ``Certificate.ApproxOn do
      return false
    let sourceArgs := source.getAppArgs
    let targetArgs := target.getAppArgs
    unless sourceArgs.size ≥ 4 ∧ targetArgs.size ≥ 4 do
      return false
    let sourceFn := sourceArgs[sourceArgs.size - 4]!
    let sourceReference := sourceArgs[sourceArgs.size - 3]!
    let sourceDomain := sourceArgs[sourceArgs.size - 2]!
    let sourceError := sourceArgs[sourceArgs.size - 1]!
    let targetFn := targetArgs[targetArgs.size - 4]!
    let targetReference := targetArgs[targetArgs.size - 3]!
    let targetDomain := targetArgs[targetArgs.size - 2]!
    let targetError := targetArgs[targetArgs.size - 1]!
    let hsub ← domainSubsetProof targetDomain sourceDomain
    let hfn ← functionEqOnProof targetFn sourceFn targetDomain
    let href ← functionEqOnProof targetReference sourceReference targetDomain
    let errorGoal ← mkAppM ``LE.le #[sourceError, targetError]
    let herror ←
      Tactic.Certificate.inferArithmeticProof "CEGA approximation error" errorGoal
    let transported ←
      mkAppM ``Certificate.approxOn_congr #[proof, hsub, hfn, href]
    let widened ← mkAppM ``Certificate.approxOn_mono_error #[transported, herror]
    Tactic.ProofCarrier.assignExactProof "CEGA approximation transport" widened

/--
Assign a kernel-checked query theorem `proof`, the one validated by `runBoxQuery` or by
`checkStatedBounds`, when its semantic proposition matches the theorem goal after unfolding user
definitions. Otherwise transport it to the goal by domain inclusion, function equality on the
domain, and endpoint arithmetic (`assignTransportedEnclosureProof?`,
`assignTransportedBoundProof?`, `assignTransportedApproxProof?`, by query mode).

The raw query syntax has no named boxes or functions, so the generated
proposition contains their quoted lambda forms. The argument-wise comparison
with the goal is the only step that runs at all transparency.
-/
private def assignValidatedBoxProof?
    (mode : BoxQueryMode) (proof : Lean.Expr) : TacticM Bool := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let proof ← instantiateMVars proof
  let proposition ← instantiateMVars (← inferType proof)
  if ← appliedRelationDefEq? proposition target then
    return ← Tactic.ProofCarrier.assignExactProof "CEGA generated query" proof
  match mode with
  | .enclose => assignTransportedEnclosureProof? proof target
  | .bound | .absBound => assignTransportedBoundProof? proof target
  | .approx => assignTransportedApproxProof? proof target

/-- Whether a goal is one of the certificate propositions a box query proves directly. -/
private def isCertificateTarget (target : Expr) : Bool :=
  let head := target.consumeMData.getAppFn.consumeMData
  head.isConstOf ``Certificate.EnclosedOn ∨ head.isConstOf ``Certificate.BoundOn ∨
    head.isConstOf ``Certificate.ApproxOn

/-- Run a checked finite-box query and close the current matching semantic goal, or the
current ordinary inequality on the box's variables.

On a certificate goal (`EnclosedOn`, `BoundOn`, `ApproxOn`) the generated proof is first
compared with the goal up to unfolding. Failing that, it is transported by domain inclusion,
function equality on the domain, and endpoint arithmetic. If certificate projection
also fails, the diagnostic includes both its refusal and the transport error.

On an ordinary inequality (after introducing leading binders, so that `∀ x ∈ Set.Icc a b, …`
is accepted) the coordinates of the query must be local real variables whose hypotheses place
them inside the stated box, and the certificate is transported by
`Tactic.BoxInequality.closeWithExplicitQuery`. Any other goal is refused with its head symbol
and the shapes the query proves. -/
def closeBoxQuery
    (ref : Syntax) (mode : BoxQueryMode) (method : EnclosureMethod)
    (precision : Continuum.RationalInterval.Precision)
    (bindingSyntax : Array Syntax) (expression : Syntax) :
    TacticM BoxQueryResult :=
  Tactic.ProofCarrier.preservingStateOnFailure do
    let bindings ← parseBindings bindingSyntax
    let coordinates := bindings.map BoxBinding.coordinate
    let reified ← parseExpression expression coordinates
    let box := bindings.map BoxBinding.interval
    Tactic.BoxInequality.introduceBinders
    let target ← withMainContext do instantiateMVars (← getMainTarget)
    let ordinary? ←
      if isCertificateTarget target then pure none
      else withMainContext do Tactic.BoxInequality.recognize? target
    unless isCertificateTarget target ∨ ordinary?.isSome do
      throwErrorAt ref
        "cega [enclose ...] proves a certificate goal `EnclosedOn f s lo hi`, \
         `BoundOn f s c`, or `ApproxOn f g s ε` whose domain lies in the stated box, or an \
         ordinary inequality on the box's variables ({Tactic.BoxInequality.supportedShapes}). \
         This goal has {← Tactic.BoxInequality.describeHead target}."
    let some result ← liftM <| runBoxQuery mode method precision box reified.expr
      | throwErrorAt ref (boxQueryFailureMessage method reified.expr)
    match ordinary? with
    | some _ =>
        try
          Tactic.BoxInequality.closeWithExplicitQuery "cega" bindings result precision
        catch error =>
          throwErrorAt ref
            "cega generated a checked {mode.certificateName} certificate for the stated query, but \
             could not transport it to this ordinary inequality.\n{error.toMessageData}"
    | none =>
        let transport : Except Exception Bool ← try
          pure (.ok (← Tactic.ProofCarrier.preservingStateOnFailure
            (assignValidatedBoxProof? mode result.proof)))
        catch error =>
          pure (.error error)
        unless transport matches .ok true do
          try
            Tactic.Certificate.closeUsingCertificate result.certificate
          catch error =>
            let detail := match transport with
              | .error cause => m!"Transport:{indentD cause.toMessageData}"
              | .ok _ => m!"Transport: the generated relation did not match the goal."
            throwErrorAt ref
              "cega generated a checked {mode.certificateName} certificate, but it does not prove \
               this exact goal. Check the expression, rational box, and requested bounds.\n\
               {detail}\nCertificate projection:{indentD error.toMessageData}"
    return result

/-- The bound that a certificate goal states with closed numerals, for the query mode `mode`: the
endpoints of `EnclosedOn f s lo hi` for the enclosure mode, `c` in `BoundOn f s c` for the
upper-bound and absolute-bound modes, and the constant reference `c` and error `ε` of
`ApproxOn f (fun _ ↦ c) s ε` for the midpoint approximation. Only reads the goal; the transport
proves the stated terms equal to these values. -/
private def statedCertificateBound? (mode : BoxQueryMode) (target : Lean.Expr) :
    MetaM (Option StatedBound) := do
  let target := target.consumeMData
  let head := target.getAppFn.consumeMData
  let arguments := target.getAppArgs
  let rational (term : Lean.Expr) : MetaM (Option ℚ) :=
    if term.hasFVar ∨ term.hasMVar then pure none
    else Tactic.BoxInequality.statedRational? term
  match mode with
  | .enclose =>
      unless head.isConstOf ``Certificate.EnclosedOn ∧ arguments.size = 5 do return none
      let some lo ← rational arguments[3]! | return none
      let some hi ← rational arguments[4]! | return none
      return some (.enclosure lo hi)
  | .bound | .absBound =>
      unless head.isConstOf ``Certificate.BoundOn ∧ arguments.size = 4 do return none
      let some c ← rational arguments[3]! | return none
      return some (if mode = .bound then .upper c false else .absolute c false)
  | .approx =>
      unless head.isConstOf ``Certificate.ApproxOn ∧ arguments.size = 7 do return none
      unless arguments[1]!.consumeMData.headBeta.isConstOf ``Real do return none
      let .lam _ _ body _ := arguments[4]!.consumeMData | return none
      if body.hasLooseBVars then return none
      let some center ← rational body | return none
      let some radius ← rational arguments[6]! | return none
      return some (.approx center radius)

/--
The stated-bound route of an explicit query, tried before `closeBoxQuery`: when the goal states
its bound with closed numerals, as `EnclosedOn f s (-1) 1` or `f x ≤ 1 / 4` does, the bound is
checked for the query of `mode` whose enclosure is computed by `method` in one kernel check
(`checkStatedBounds`) and the checked theorem is
transported to the goal as `closeBoxQuery` transports a query result. Returns `false`, with the
state restored, when the route does not apply, when the search route has this query memoized,
when the kernel rejects the check, or when the transport fails; `closeBoxQuery` then runs the
search, whose diagnostics and refusals are the tactic's.
-/
private def closeStatedBoxQuery (mode : BoxQueryMode) (method : EnclosureMethod)
    (precision : Continuum.RationalInterval.Precision) (bindingSyntax : Array Syntax)
    (expression : Syntax) : TacticM Bool :=
  Tactic.ProofCarrier.restoringStateOnFalse <| Tactic.BoxInequality.falseOnFailure do
    let bindings ← parseBindings bindingSyntax
    let reified ← parseExpression expression (bindings.map BoxBinding.coordinate)
    let box := bindings.map BoxBinding.interval
    Tactic.BoxInequality.introduceBinders
    let target ← withMainContext do instantiateMVars (← getMainTarget)
    unless isCertificateTarget target do
      return ← Tactic.BoxInequality.closeWithStatedQuery "cega" method bindings reified.expr
        precision
    let some stated ← statedCertificateBound? mode target | return false
    if ← liftM <| boxQueryMemoized mode method precision box reified.expr then
      return false
    let .checked proofs ← liftM <| checkStatedBounds method precision box reified.expr #[stated]
      | return false
    let some proof := proofs[0]? | return false
    try
      if ← assignValidatedBoxProof? mode proof then
        return true
      trace[cega.stated] "the checked theorem does not transport to the goal; the search runs"
    catch error =>
      trace[cega.stated] "the checked theorem does not transport to the goal; the search runs:\
        {indentD error.toMessageData}"
    return false

/-- The route by which bare `cega` closed a goal. -/
inductive BareRoute where
  /-- A registered checked carrier in the local context or the goal was projected. -/
  | carrier (route : Tactic.CEGA.SelectedRoute)
  /-- An ordinary inequality on bounded real variables was closed by a checked box query;
  `query` is the explicit `cega [...]` call that runs it. -/
  | boxInequality (query : TSyntax `tactic)
  /-- A goal about one interval integral was closed by a checked batch quadrature; `replay` is
  the bare `cega` call that runs it. -/
  | integral (replay : TSyntax `tactic)
  /-- A certificate goal on a coordinate box was unfolded to an ordinary goal and closed by a
  checked box query; `replay` is the bare `cega` call that runs it. -/
  | certificateGoal (replay : TSyntax `tactic)
  /-- A goal without free variables was closed by dyadic interval evaluation with CEGA's
  ranges; `query` is the `dyadic_interval` call that runs it. -/
  | inclusion (query : TSyntax `tactic)

/-- Stable diagnostic label of a bare `cega` route. -/
def BareRoute.label : BareRoute → String
  | .carrier route => route.label
  | .boxInequality _ => "checked box enclosure of an ordinary inequality"
  | .integral _ => "checked batch quadrature of an interval integral"
  | .certificateGoal _ => "checked box enclosure of a certificate goal on a coordinate box"
  | .inclusion _ => "dyadic interval evaluation of a closed goal"

/-- The call bare `cega` runs on a closed goal that its other routes refuse. Its working
precision is `n` bits for `(prec := n)`, about `3.3 d + 8` bits for `(digits := d)`, and 32 bits
otherwise. -/
def inclusionQuery (config : BareConfig := {}) : TacticM (TSyntax `tactic) := do
  let bits := match config.prec?, config.precision.digits with
    | some bits, _ => bits
    | none, some digits => digits * 3322 / 1000 + 8
    | none, none => 32
  `(tactic| dyadic_interval [$(mkIdent `cega_real):ident, $(mkIdent `prec):ident := $(quote bits)])

/--
Close a goal without free variables, such as a conjunction, negation, membership or equality
of real constants, with `dyadic_interval` and the `cega_real` ranges of
`CAS.Continuum.Interval.Inclusion.Elementary`, at the precision of `inclusionQuery`. Goals with
free variables use the box route, which reads their bounds from the hypotheses.
-/
def closeClosedByInclusion (config : BareConfig := {}) : TacticM (TSyntax `tactic) := do
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  if target.hasFVar || target.hasMVar then
    throwError "interval evaluation is tried only on goals without free variables"
  let query ← inclusionQuery config
  evalTactic query
  return query

/-- Whether this call is native `cega [fast]`, whose routes may use native certificates. -/
private def nativeFastMode : TacticM Bool := do
  let options ← getOptions
  return options.getBool `cega.nativePolynomial false &&
    options.getBool `cega.nativeCertificates false

/-- Run one route of `cega` as a kernel-only route
(`Tactic.ProofCarrier.withKernelOnlyAxioms`), except inside native `cega [fast]`. A rejected
proof is an ordinary route failure, so the next route is tried. -/
private def kernelOnlyRoute {α : Type} (description : String) (route : TacticM α) :
    TacticM α := do
  if ← nativeFastMode then
    route
  else
    Tactic.ProofCarrier.withKernelOnlyAxioms description do
      return (← route, #[])

/--
Close the goal by the routes of bare `cega`, in this order: a matching checked carrier from the
local context or the goal; for a goal about one interval integral, the checked batch quadrature
of `Integration.close`; for a certificate goal whose domain is a coordinate box, the checked box
query on the coordinates of its point (`Tactic.BoxInequality.prepareCertificateGoal`); for an
ordinary inequality on real variables bounded by rational literal hypotheses, the checked box
query those hypotheses describe; and for a goal without free variables, the interval evaluation
of `inclusionQuery`. A refusal leads with the reason of the route that applies to the goal (the
integral route, the certificate route, or the box route for a recognized inequality), or else
names the goal's head, and then gives the other routes' reasons and the supported shapes. Each
route is kernel-only (`kernelOnlyRoute`) unless this is native `cega [fast]`. A refusal also
stores its reasons in `routeReport?`, when it is given, so that a caller can report them under
its own headline.
-/
def closeBare (config : BareConfig := {})
    (routeReport? : Option (IO.Ref MessageData) := none) : TacticM BareRoute := do
  -- The box queries subdivide a box whose first query falls short, except in native
  -- `cega [fast]`, whose polynomial certificate does not subdivide.
  let subdivide := !(← nativeFastMode)
  let carrierError ← match ← Tactic.ProofCarrier.attemptClosingMainGoal "cega carrier route"
      (kernelOnlyRoute "cega carrier route" Tactic.CEGA.closeFromLocalCarriers) with
    | .ok closed => return .carrier closed.value
    | .error error => pure error
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  let mut integralError? : Option Exception := none
  if (Integration.findIntegral? target).isSome then
    -- The quadrature certificate is evaluated in the kernel, also in native `cega [fast]`.
    match ← Tactic.ProofCarrier.attemptClosingMainGoal "cega integral route"
        (kernelOnlyRoute "cega integral route" <|
          withOptions (fun options ↦ options.setBool `cega.nativePolynomial false)
            (Integration.close config)) with
    | .ok closed => return .integral closed.value
    | .error error => integralError? := some error
  let preparation ← IO.mkRef Tactic.BoxInequality.CertificatePreparation.notCertificate
  let certificateError ← match ← Tactic.ProofCarrier.attemptClosingMainGoal
      "cega certificate route" (kernelOnlyRoute "cega certificate route" do
        preparation.set (← Tactic.BoxInequality.prepareCertificateGoal)
        let .prepared ← preparation.get
          | throwError "this goal is not a certificate proposition on a coordinate box"
        discard <| Tactic.BoxInequality.closeMainGoal "cega" config.precision subdivide
        Tactic.BoxInequality.bareSyntax config.precision) with
    | .ok closed => return .certificateGoal closed.value
    | .error error => pure error
  let preparation ← preparation.get
  let certificate := match preparation with
    | .notCertificate => false
    | _ => true
  -- A certificate goal is the certificate route's goal; the box route reads ordinary goals.
  let mut boxError? : Option Exception := none
  unless certificate do
    match ← Tactic.ProofCarrier.attemptClosingMainGoal "cega box route"
        (kernelOnlyRoute "cega box route"
          (Tactic.BoxInequality.closeMainGoal "cega" config.precision subdivide)) with
    | .ok closed => return .boxInequality closed.value
    | .error error => boxError? := some error
  let mut inclusionError? : Option Exception := none
  if !target.hasFVar && !target.hasMVar then
    match ← Tactic.ProofCarrier.attemptClosingMainGoal "cega interval route"
        (kernelOnlyRoute "cega interval route" (closeClosedByInclusion config)) with
    | .ok closed => return .inclusion closed.value
    | .error error => inclusionError? := some error
  -- The route that applies to the goal leads the refusal, and the other routes follow it.
  let head ← Tactic.BoxInequality.describeHead target
  let recognized := (← withMainContext do Tactic.BoxInequality.recognize? target).isSome
  let mut lead? : Option MessageData := integralError?.map (·.toMessageData)
  if lead?.isNone then
    match preparation with
    | .notBox domain coordinate =>
        lead? := some (← withMainContext <| addMessageContext m!"This goal has {head}, a \
          certificate proposition whose domain{indentExpr domain}\nis not a coordinate box: it \
          gives no rational bounds on {coordinate}. `cega using h` projects a checked carrier \
          `h`, and `cega [enclose x in [a, b]] expr` synthesizes one on a rational box.")
    | .prepared => lead? := some certificateError.toMessageData
    | .notCertificate => pure ()
  let mut others := #[m!"carrier search:{indentD carrierError.toMessageData}"]
  if let some boxError := boxError? then
    if lead?.isNone && recognized then
      lead? := some boxError.toMessageData
    else
      others := others.push m!"box route:{indentD boxError.toMessageData}"
  if let some inclusionError := inclusionError? then
    others := others.push m!"interval route:{indentD inclusionError.toMessageData}"
  let lead := lead?.getD
    m!"This goal has {head}; its outer shape is not supported by these routes."
  let body := m!"{lead}\nOther routes:{indentD (MessageData.joinSep others.toList m!"\n")}"
  if let some report := routeReport? then
    report.set body
  throwError "{body}\n\
    Bare `cega` proves an ordinary real inequality ({Tactic.BoxInequality.supportedShapes}), a \
    bound on an interval integral `∫ x in a..b, f x` with rational limits, a certificate goal \
    (`EnclosedOn f s lo hi`, `BoundOn f s c`, `ApproxOn f g s ε`, `ResidualBound r s ε`) on a \
    coordinate box or from a checked carrier in the local context or the goal, and a closed goal \
    that interval evaluation proves."

/-- Close a fully specified finite certificate without using local assumptions. -/
private def closeFiniteCertificate (native : Bool) : TacticM Unit := withMainContext do
  let proof ← decideClosedCertificate (← getMainTarget) native
  let assigned ← profileitM Exception "CEGA finite proof validation" (← getOptions) do
    Tactic.ProofCarrier.assignExactProof "CEGA finite certificate" proof
  unless assigned do
    throwError "CEGA finite certificate did not match the goal"

/-- Whether the main goal, with its local definitions expanded, is a closed proposition with a
`Decidable` instance: the goal of the finite certificate, which expands them the same way. -/
private def closedDecidableTarget : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let target ← if target.hasFVar then zetaReduce target else pure target
  if target.hasFVar || target.hasMVar then
    return false
  try
    unless ← isProp target do
      return false
    return (← synthInstance? (mkApp (mkConst ``Decidable) target)).isSome
  catch _ =>
    return false

/-- Keep the semantic routes first, then, for a closed decidable proposition, try a kernel
certificate. When that certificate applies to the goal and the kernel fails on it, its failure
leads the report. -/
private def closeKernelOrBare (config : BareConfig := {}) : TacticM Unit := do
  let routeReport ← IO.mkRef m!""
  match ← Tactic.ProofCarrier.attemptClosingMainGoal "CEGA semantic routes"
      (discard <| closeBare config (some routeReport)) with
  | .ok _ => pure ()
  | .error semanticError =>
      unless ← closedDecidableTarget do
        throw semanticError
      match ← Tactic.ProofCarrier.attemptClosingMainGoal "CEGA finite kernel certificate"
          (kernelOnlyRoute "CEGA finite kernel certificate" (closeFiniteCertificate false)) with
      | .ok _ => pure ()
      | .error finiteError =>
          -- A closed statement with a decision procedure is the finite route's goal: its kernel
          -- failure leads the report, and the other routes follow without their refusal of the
          -- goal's shape.
          if Tactic.KernelReadBack.isKernelCertificateFailure finiteError then
            throwError "{finiteError.toMessageData}\n\
              This is a closed statement with a decision procedure, which `cega` proves by \
              evaluating it in the kernel; its other routes, for certificate goals, interval \
              integrals and bounded real inequalities, did not apply either:\
              {indentD (← routeReport.get)}"
          throwError "{semanticError.toMessageData}\n{finiteError.toMessageData}"

/-- The native profile of `cega [fast]`: for a closed decidable proposition a finite certificate
by native evaluation, then the semantic routes with the native polynomial enclosure. -/
private def closeFast (config : BareConfig := {}) : TacticM Unit := do
  let mut finiteError? : Option Exception := none
  if ← closedDecidableTarget then
    match ← Tactic.ProofCarrier.attemptClosingMainGoal "CEGA finite native certificate"
        (closeFiniteCertificate true) with
    | .ok _ =>
        trace[cega.native] "Finite native proof assigned and validated"
        return
    | .error error =>
        -- The probe has restored its state, so this diagnostic survives its rollback.
        trace[cega.native] "Finite native attempt refused; trying semantic CEGA:\n\
          {error.toMessageData}"
        finiteError? := some error
  try
    withOptions (fun options ↦ options.setBool `cega.nativePolynomial true)
      (discard <| closeBare config)
  catch semanticError =>
    if semanticError.isRuntime then
      throw semanticError
    let some error := finiteError? | throw semanticError
    throwError "Finite native attempt: {error.toMessageData}\n\
      Semantic CEGA attempt: {semanticError.toMessageData}"

/-- Bare `cas` dispatches ordinary inequalities on rational boxes to the box route once this
module is imported. -/
@[cas_route box]
def boxRoute : Tactic.RouteRegistry.Closer := fun _ ↦ do
  Tactic.ProofCarrier.withKernelOnlyAxioms "cas box route" do
    return ({ replay := ← Tactic.BoxInequality.closeMainGoal "cas" }, #[])

/--
Close the goal by projecting a matching checked CEGA carrier found in the local context or
target, by the checked batch quadrature of a goal about one interval integral, by the checked
box query of a certificate goal on a coordinate box or of an ordinary inequality on real
variables bounded by rational literal hypotheses, or, for a closed goal that these routes
refuse, by `dyadic_interval [cega_real, prec := n]` at the precision of `inclusionQuery`.
-/
elab_rules : tactic
  | `(tactic| cega) =>
      Tactic.ProofCarrier.tacticEntry "cega" closeKernelOrBare
  | `(tactic| cega [fast]) => Tactic.ProofCarrier.tacticEntry "cega [fast]" do
      -- Without native checking, `cega [fast]` is bare `cega`, run once.
      unless (← getOptions).getBool `cega.nativeCertificates false do
        return ← closeKernelOrBare
      let saved ← saveState
      tryCatchRuntimeEx
        closeFast
        fun error ↦ do
          saved.restore
          if error.isRuntime then
            throw error
          trace[cega.native] "Fast CEGA restored state; using kernel fallback:\n\
            {error.toMessageData}"
          try
            closeKernelOrBare
          catch kernelError =>
            let .error .. := kernelError | throw kernelError
            throwError "{kernelError.toMessageData}\n\
              The native attempt of `cega [fast]`, before this kernel fallback, failed with:\
              {indentD error.toMessageData}"
  | `(tactic| cega using $carrier:term) =>
      Tactic.ProofCarrier.tacticEntry "cega using" <|
        Tactic.ProofCarrier.withKernelOnlyAxioms "cega using" do
          let (_, carrierExpr) ← Tactic.CEGA.closeUsingCarrier carrier
          return ((), #[carrierExpr])

/-- Bare `cega` with the precision policy, subdivision depth and panel count of its configuration
items. -/
@[tactic tacticCega]
def evalCegaConfigured : Tactic := fun stx ↦ do
  let arguments := stx[1][0]
  unless arguments.isOfKind ``cegaConfigured do throwUnsupportedSyntax
  Tactic.ProofCarrier.tacticEntry "cega" do
    closeKernelOrBare (← parseBareConfig arguments[0])

/--
`cega using carrier`

Close the goal by projecting one explicitly supplied checked CEGA carrier.
-/
tactic_extension tacticCega

/-- The query mode an explicit query runs for the main goal, the projection the goal needs: an
enclosure for `EnclosedOn`, an upper bound for `BoundOn f s c`, an absolute bound for
`BoundOn (fun x ↦ |f x|) s c`, a midpoint approximation for `ApproxOn`, and the mode of the shape
of an ordinary inequality (`Tactic.BoxInequality.Shape.mode`). The mode does not depend on how
the enclosure is computed: `(depth := n)` subdivides the box for every mode. -/
private def explicitQueryMode : TacticM BoxQueryMode := do
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  let target := target.consumeMData
  let head := target.getAppFn.consumeMData
  if head.isConstOf ``Certificate.BoundOn then
    let absolute : Bool := match target.getAppArgs[1]?.map Lean.Expr.consumeMData with
      | some (.lam _ _ body _) => body.consumeMData.isAppOf ``abs
      | _ => false
    return bif absolute then .absBound else .bound
  if head.isConstOf ``Certificate.ApproxOn then
    return .approx
  if head.isConstOf ``Certificate.EnclosedOn then
    return .enclose
  match ← withMainContext do Tactic.BoxInequality.recognize? target with
  | some recognized => return recognized.shape.mode
  | none => return .enclose

/-- Close the main goal with the explicit query `cega cfg [enclose bindings] expression` as a
kernel-only route (`Tactic.ProofCarrier.withKernelOnlyAxioms`), in the mode the goal needs
(`explicitQueryMode`) and with the enclosure method that `cfg` requests (`requestedMethod`): the
stated-bound route first (`closeStatedBoxQuery`), then the search (`closeBoxQuery`). Returns the
mode and the method. -/
def closeEncloseQuery (cfg : Syntax) (bindings : Array Syntax) (expression : Syntax) :
    TacticM (BoxQueryMode × EnclosureMethod) :=
  Tactic.ProofCarrier.withKernelOnlyAxioms "cega [enclose]" do
    let precision ← parsePrecision cfg
    let method := requestedMethod cfg
    Tactic.BoxInequality.introduceBinders
    let mode ← explicitQueryMode
    unless ← closeStatedBoxQuery mode method precision bindings expression do
      discard <| closeBoxQuery expression mode method precision bindings expression
    return ((mode, method), #[])

elab_rules : tactic
  | `(tactic| cega $cfg:optConfig [enclose $bindings:cegaIntervalBinding,*] $expr:term) =>
      Tactic.ProofCarrier.tacticEntry "cega [enclose]" do
        discard <| closeEncloseQuery cfg bindings.getElems expr

end CAS.CEGA

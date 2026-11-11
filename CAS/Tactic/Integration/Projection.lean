/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.Antiderivative
public import CAS.Tactic.Assumptions
public import CAS.Tactic.Integration.Basic
public meta import CAS.Tactic.Integration.Basic
public meta import CAS.Tactic.ProofCarrier
public meta import CAS.Tactic.RouteRegistry

/-!
# Analytic projection of antiderivative certificates

An `AntiderivativeCert` records a checked symbolic identity `∂ᵢ F = f` together with the
validity requirements under which that identity becomes a statement of real calculus. Given the
goal shape (`HasDerivAt` or an `intervalIntegral`), projection names the calculus theorem of
`CAS/Calculus/Antiderivative.lean` that consumes the certificate, and it discharges the one
remaining argument of that theorem, the proof that the requirements hold at the point or on the
whole integration interval. Candidate search comes before it, in
`CAS.Tactic.Integration.Planning`, and the conversion to the user's statement after it, in
`CAS.Tactic.Integration.Conversion`.

## Main definitions

* `theoremName`, `argumentCount`: the calculus theorem selected for each projection.
* `proveRequirements`: discharge the requirements goal, with or without user evidence.
* `complete`: apply the theorem to the certificate and geometric data and return the
  analytic proof together with the requirements proof it consumed.
* `certificateEvidence`, `result`: bundle the residual and requirements proofs for
  the query and reporting layers.

## Implementation notes

Requirements are proved by `symbolic_assumptions` (`CAS/Tactic/Assumptions.lean`), optionally
primed with the evidence given in the `using` form. When the planner certified the certificate's
requirement lists explicitly, we first rewrite the collection to those lists, so no normalizer
run is reduced here. Interval evidence is pointwise, so it is specialized to the bound variable
before the requirement collection is reduced, and the membership of the bound variable in
`Set.uIcc a b` is split into its two endpoint inequalities first, so that `0 < 1 - t ^ 2` on
`[0, 1/2]` is within reach of the finishers. When the endpoints are rational literals, an atom
that the finishers leave, such as `Real.cos t ≠ 0` on `[0, 1]`, is proved from those two
inequalities by the box route of `cas` (`CAS.CEGA.boxRoute`, reached through
`CAS.Tactic.RouteRegistry.closer?`). The requirements of an improper integral carry the
membership of the bound variable in a half-line, or no membership on the whole line. Failure
messages spell out what the user must supply: nonzero denominators and logarithm arguments, and
positive square-root arguments.
-/

public meta section

namespace CAS.Tactic.Integration

open Lean Elab Tactic Meta

namespace Projection

/-- The calculus theorem implementing an integration projection. -/
def theoremName : Projection → Name
  | .hasDerivAt =>
      ``IntegrationCheck.AntiderivativeCert.hasDerivAt_eval_add_smul_single
  | .intervalIntegral =>
      ``IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_eval_add_smul_single

/-- Number of explicit arguments following the certificate. -/
def argumentCount : Projection → Nat
  | .hasDerivAt => 3
  | .intervalIntegral => 4

-- Contextual proofs need the requirements type; a global fact or pointwise family can have a
-- different proposition. Validate either form before automation can ignore the supplied syntax.
private def validateEvidence (hint : TSyntax `term) (expected : Expr) : TacticM Unit :=
  ProofCarrier.preservingStateOnFailure do
    let saved ← saveState
    tryCatchRuntimeEx
      (do
        let proof ← Term.withoutErrToSorry <| Term.elabTermEnsuringType hint expected
        discard <| ProofCarrier.checkCompletedProof "cas side evidence" proof)
      fun error ↦ do
        saved.restore
        if error.isRuntime then throw error
        let proof ← Term.withoutErrToSorry <| Term.elabTerm hint none
        let proof ← ProofCarrier.checkCompletedProof "cas side evidence" proof
        unless ← isProp (← inferType proof) do
          throwError "cas requires a proof as side evidence"

/-- Prove `0 < e` by the box route of `cas`, which proves inequalities between real expressions
whose variables are bounded by hypotheses with rational literal endpoints. -/
private def closeByBox (goal : MVarId) : TacticM Unit := do
  let goals ← getGoals
  try
    setGoals [goal]
    let some closer ← RouteRegistry.closer? `box
      | throwError "cas: the box route is not installed"
    discard <| closer none
  finally
    setGoals goals
  unless ← goal.isAssigned do
    throwError "cas: the box route left the goal open"

/-- Close an atom of the requirements by the box route: `e ≠ c` from `c < e` or from `e < c`, and
any other atom, such as `0 < e`, as it is. -/
private def boxFallback (atom : MVarId) : TacticM Unit := atom.withContext do
  let target := (← instantiateMVars (← atom.getType)).consumeMData
  let some (_, lhs, rhs) := target.ne? | closeByBox atom
  for (proposition, inequality) in
      [(← mkAppM ``LT.lt #[rhs, lhs], ``LT.lt.ne'), (← mkAppM ``LT.lt #[lhs, rhs], ``LT.lt.ne)] do
    let saved ← saveState
    try
      let proof ← mkFreshExprSyntheticOpaqueMVar proposition
      closeByBox proof.mvarId!
      atom.assign (← mkAppM inequality #[proof])
      return
    catch error =>
      if error.isRuntime then throw error
      saved.restore
  throwError "cas: the box route proved neither `{rhs} < {lhs}` nor `{lhs} < {rhs}`"

/-- Prove requirements `∀ t, t ∈ Set.uIcc a b → R t` by splitting the membership into the endpoint
inequalities of `t` and running `symbolic_assumptions` with `boxFallback` for the atoms that resist
its finishers. -/
private def proveOnIntervalByBox (goal : MVarId) : TacticM Unit := do
  let goals ← evalTacticAt (← `(tactic|
    (intro t ht
     rcases Set.mem_uIcc.mp ht with ⟨hcasLower, hcasUpper⟩ | ⟨hcasLower, hcasUpper⟩))) goal
  let saved ← getGoals
  try
    for goal in goals do
      setGoals [goal]
      Assumptions.closeMainGoal (some boxFallback)
  finally
    setGoals saved

/--
Prove the certificate requirements, using explicit evidence first when the
`using` form supplied it.
-/
def proveRequirements
    (requirements : Expr) (requirementsSyntax? : Option (TSyntax `term))
    (requirementsEquation? : Option Expr := none) :
    TacticM Expr := do
  let .mvar requirementsGoal := requirements
    | throwError
        "cas internal error: the certificate requirements were \
         not represented by a proof goal"
  -- The requirement collection is replaced by its explicit lists, certified together with the
  -- certificate, so that the side-condition tactic works on explicit atoms.
  let requirementsGoal ←
    match requirementsEquation? with
    | none => pure requirementsGoal
    | some equation => requirementsGoal.withContext do
        let target ← instantiateMVars (← requirementsGoal.getType)
        let result ← requirementsGoal.rewrite target equation
        unless result.mvarIds.isEmpty do
          throwError
            "cas internal error: exposing the requirement lists left auxiliary goals"
        requirementsGoal.replaceTargetEq result.eNew result.eqProof
  let requirementsTarget ← instantiateMVars (← requirementsGoal.getType)
  if let some evidenceSyntax := requirementsSyntax? then
    requirementsGoal.withContext <| validateEvidence evidenceSyntax requirementsTarget
  -- The integration domain `D` of a pointwise requirement `∀ t, t ∈ D → ...`. The requirement of
  -- a whole-line integral is pointwise with no membership.
  let domain? : Option Expr :=
    if requirementsTarget.isForall then
      let membership := requirementsTarget.bindingBody!.consumeMData
      if membership.isForall && membership.bindingDomain!.isAppOfArity ``Membership.mem 5 then
        some (membership.bindingDomain!.getAppArgs[3]!)
      else
        none
    else
      none
  let onInterval := domain?.any (·.isAppOf ``Set.uIcc)
  -- The scripts name the membership hypothesis only when the requirement has one: `rcases`
  -- elaborates an unknown name to `sorry` instead of failing.
  let introduction : TSyntax `tactic ←
    if domain?.isSome then `(tactic| intro t ht) else `(tactic| intro t)
  -- Pointwise evidence is specialized at the bound variable before the certificate's symbolic
  -- requirement collection is reduced.
  let pointEvidence : TSyntax `tactic ←
    if domain?.isSome then
      `(tactic|
        first
          | have hcasPointRequirements := hcasRequirements t ht
          | have hcasPointRequirements := hcasRequirements t
          | skip)
    else
      `(tactic| first | have hcasPointRequirements := hcasRequirements t | skip)
  -- The membership `t ∈ Set.uIcc a b` unfolds to a disjunction of two endpoint pairs, which the
  -- side-condition finishers do not split, so it is split here; the branch with the reversed
  -- endpoints is contradictory for `a < b` and closes by linear arithmetic. A requirement read
  -- back from a normalizer run can carry a product such as `4 * (1 + 1 / 4 * t * t)`, in which
  -- `positivity` does not see the square; the retry after `ring_nf` presents it as `4 + t ^ 2`.
  let finisher : TSyntax `tactic ←
    if onInterval then
      `(tactic|
        first
          | (rcases Set.mem_uIcc.mp ht with ⟨hcasLower, hcasUpper⟩ | ⟨hcasLower, hcasUpper⟩
             <;> first | symbolic_assumptions | (ring_nf; symbolic_assumptions))
          | symbolic_assumptions
          | (ring_nf; symbolic_assumptions))
    else
      `(tactic| first | symbolic_assumptions | (ring_nf; symbolic_assumptions))
  let tactic : TSyntax `tactic ←
    match requirementsSyntax? with
    | some evidenceSyntax =>
        if requirementsTarget.isForall then
          `(tactic|
            first
              | exact $evidenceSyntax
              | have hcasRequirements := $evidenceSyntax
                $introduction:tactic
                $pointEvidence:tactic
                $finisher:tactic
              | $introduction:tactic
                $finisher:tactic)
        else
          `(tactic|
            first
              | exact $evidenceSyntax
              | have hcasRequirements := $evidenceSyntax
                symbolic_assumptions
              | symbolic_assumptions)
    | none =>
        if requirementsTarget.isForall then
          `(tactic| ($introduction:tactic; $finisher:tactic))
        else
          `(tactic| first | symbolic_assumptions | (ring_nf; symbolic_assumptions))
  let evidenceShape :=
    match domain? with
    | some domain => m!"∀ t ∈ {domain}, ..."
    | none => m!"∀ t : ℝ, ..."
  let failureMessage : MessageData :=
    if requirementsTarget.isForall then
      if requirementsSyntax?.isSome then
        m!"cas could not use the supplied pointwise evidence on the \
         whole integration domain. Check that it proves every denominator \
         nonzero, every logarithm argument nonzero, and every square-root argument positive."
      else
        m!"cas needs pointwise domain evidence on the whole integration \
         domain. Supply `h : {evidenceShape}` and write \
         `cas using h`; denominators and logarithm arguments must be \
         nonzero, and square-root arguments must be positive."
    else if requirementsSyntax?.isSome then
      m!"cas could not use the supplied evidence to prove every \
       antiderivative domain condition."
    else
      m!"cas could not prove every antiderivative domain condition; \
       supply the relevant nonzero or positivity fact with \
       `cas using h`."
  -- On an interval the atoms that resist are given to the box route of `cas`, which reads the
  -- endpoint inequalities of the bound variable when the endpoints are rational literals.
  let remaining ←
    try
      evalTacticAt tactic requirementsGoal
    catch error =>
      try
        unless onInterval do
          throw error
        proveOnIntervalByBox requirementsGoal
        pure []
      catch _ =>
        throwError
          "{failureMessage}\n\
           Detail:{indentD error.toMessageData}"
  unless remaining.isEmpty do
    let targets ← remaining.mapM fun goal ↦ do
      instantiateMVars (← goal.getType)
    let targetMessages := targets.map fun target ↦ m!"{target}"
    throwError
      "{failureMessage}\n\
       Remaining obligations:{indentD (MessageData.joinSep targetMessages m!"\n")}"
  let proof ← instantiateMVars requirements
  if proof.hasMVar ∨ proof.hasSorry then
    throwError "cas left incomplete requirements evidence"
  unless ← isTypeCorrect proof do
    throwError "cas constructed ill-typed requirements evidence"
  return proof

/--
Discharge the sole requirements argument left after all geometric data have
been supplied to a calculus theorem. The result pairs the completed analytic
proof with the checked requirements proof it consumed.
-/
def complete
    (base : Expr) (requirementsSyntax? : Option (TSyntax `term))
    (requirementsEquation? : Option Expr := none) :
    TacticM (Expr × Expr) := do
  let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType base)
  unless arguments.size == 1 do
    throwError
      "cas internal error: an ordinary certificate projection \
       has an unexpected argument shape"
  let requirements := arguments[0]!
  let requirementsProof ← proveRequirements requirements requirementsSyntax? requirementsEquation?
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars (mkAppN base arguments)
  if proof.hasMVar ∨ proof.hasSorry then
    throwError "cas constructed incomplete analytic evidence"
  unless ← isTypeCorrect proof do
    throwError "cas constructed ill-typed analytic evidence"
  return (proof, requirementsProof)

/-- Bundle one certificate's residual and requirements proof expressions for later validation. -/
def certificateEvidence
    (certificate requirementsProof : Expr) : TacticM CertificateEvidence := do
  let routeZeroProof ← instantiateMVars <|
    ← mkAppM ``IntegrationCheck.AntiderivativeCert.routeZero #[certificate]
  return { routeZeroProof, requirementsProof }

/-- Bundle residual and requirements proof expressions for query reporting. -/
def result
    (projection : Integration.Projection) (certificate : Expr)
    (requirementsProof : Expr) (closedRelation : Bool := false) : TacticM Result := do
  let evidence ← certificateEvidence certificate requirementsProof
  return { projection? := some projection, closedRelation, evidence := #[evidence] }

end Projection

end CAS.Tactic.Integration

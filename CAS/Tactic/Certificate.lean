/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Tactic.Arithmetic
public import CAS.Certificate.ModelApproximation
public import CAS.Certificate.Quadrature
public import CAS.Certificate.Residual
public import CAS.Exact.ExpressionSideConditions

/-!
# CEGA certificate inference

The verified computer algebra and CEGA layers return ordinary checked
structures: `ApproxCert`, `ResidualCert`, `BoundCert`, `EnclosureCert`,
`ModelApproxCert`, and `QuadratureCert`. One tactic, `cega`, handles all of
them: its carrier route (`CAS.Tactic.CEGA`) finds a matching certificate in the local context
or among the subterms of the target, projects its semantic theorem, and, when necessary,
restricts its domain or proves that its error budget is no larger than the requested one.

## Main definitions

* `closeFromLocalCertificates`: close the main goal from a certificate of the local context or
  of the target.
* `closeUsingCertificate`: close the main goal from one explicit certificate, such as the one a
  CEGA computation returns.
* `inferArithmeticProof`, `inferNormalizedEqOnProof`, `inferSubsetProof`: the side proofs of a
  projection; `CAS.CEGA` uses the first two as well.

## Implementation notes

No certificate is trusted because of its type name alone. We first try the exact projection
`X.sound` of the certificate (`ProofCarrier.assignExactProof`). Otherwise we build a weaker
theorem from the certificate's own operations, all in `CAS.Certificate`: `X.restrict` to the
goal's domain, with the inclusion proved by `assumption`, `simp_all` or `aesop`; `X.weaken` to
the requested budget (for an enclosure, to wider bounds at both endpoints), each inequality
proved by the shared arithmetic phase `Arithmetic.close`; and `ApproxCert.replaceRhs` or
`EnclosureCert.replaceFn` when the goal states another reference function, the pointwise
equality proved by `simp` with the evaluator's equations, then `norm_num`, `field_simp` and
`ring`. The statement obtained must agree with the goal by definitional equality, and the proof
assigned to the goal is validated by `ProofCarrier.validateAssignedProof`. The soundness
statements are the certificates' own: the `sound` field of each structure, and the theorem
`ModelApproxCert.sound`.
-/

public meta section

namespace CAS.Tactic.Certificate

open Lean Elab Tactic Meta
open CAS.Certificate
open CAS.Continuum

private def certificateDescriptors :
    Array (Name × Name) := #[
  (``ApproxCert, ``ApproxCert.sound),
  (``ResidualCert, ``ResidualCert.sound),
  (``BoundCert, ``BoundCert.sound),
  (``EnclosureCert, ``EnclosureCert.sound),
  (``ModelApproxCert, ``ModelApproxCert.sound),
  (``QuadratureCert, ``QuadratureCert.sound)
]

private def certificateDescriptor? (type : Expr) :
    Option (Name × Name) :=
  ProofCarrier.findByTypeHead? certificateDescriptors type

private def soundProjection
    (soundTheorem : Name) (certificate : Expr) : MetaM Expr :=
  mkAppM soundTheorem #[certificate]

private def targetFinalArg (target : Expr) : Option Expr :=
  let args := target.consumeMData.getAppArgs
  if args.isEmpty then none else some args[args.size - 1]!

private def reduceProjectionApplication? (field : Expr) : MetaM (Option Expr) := do
  let .const projectionName .. := field.getAppFn | return none
  let some projection ← getProjectionFnInfo? projectionName | return none
  let some (.ctorInfo constructor) := (← getEnv).find? projection.ctorName
    | return none
  let arguments := field.getAppArgs
  let some major := arguments[projection.numParams]? | return none
  unless major.isAppOfArity projection.ctorName
      (constructor.numParams + constructor.numFields) do
    return none
  return major.getAppArgs[projection.numParams + projection.i]?

/--
Expose one certificate field without normalizing its value or traversing its proof.

Lean represents structure projections both as kernel projections and as
applications of generated projection functions. Full weak-head normalization
would unfold rational casts and the certificate's soundness proof, so
weakening deliberately handles only these two structural forms.
-/
private def reduceCertificateField (field : Expr) : MetaM Expr := do
  if let some reduced ← reduceProj? field then
    return reduced
  return (← reduceProjectionApplication? field).getD field

private def closeArithmeticGoals
    (description : String) (goals remaining : List MVarId) : TacticM Unit := do
  setGoals goals
  allGoals Arithmetic.close
  let unresolved ← getGoals
  unless unresolved.isEmpty do
    let targets ← unresolved.mapM fun goal ↦
      goal.withContext do instantiateMVars (← goal.getType)
    if targets.any fun target ↦ target.consumeMData.isConstOf ``False then
      throwError
        "{description} failed: the generated certificate is weaker than the \
         requested target"
    else
      throwError
        "{description} left arithmetic side conditions unresolved\
         {indentD targets}"
  setGoals remaining

/-- Construct and check a proof of a closed arithmetic proposition. -/
def inferArithmeticProof (description : String) (target : Expr) : TacticM Expr := do
  let proof ← mkFreshExprMVar target
  let goals ← getGoals
  closeArithmeticGoals description [proof.mvarId!] goals
  ProofCarrier.checkCompletedProof description proof

/-- Prove pointwise equality between an ordinary function and a reflected certificate function. -/
def inferNormalizedEqOnProof
    (lhs rhs domain : Expr) : TacticM Expr := do
  let expected ← mkAppM ``Set.EqOn #[lhs, rhs, domain]
  let proof ← mkFreshExprMVar expected
  let (_, pointGoal) ← proof.mvarId!.withContext do proof.mvarId!.intro1P
  let (_, equalityGoal) ← pointGoal.withContext do pointGoal.intro1P
  let simpNames := #[
    ``CAS.Exact.exprFn,
    ``CAS.Verified.Expr.eval,
    ``CAS.Verified.Expr.SymVar.expr,
    ``Rat.cast_def,
    ``Real.tan_eq_sin_div_cos,
    ``Real.sinh_eq,
    ``Real.cosh_eq,
    ``Real.tanh_eq,
    ``Real.sqrt_sq_eq_abs]
  let simpArgs ← simpNames.mapM fun name ↦
    `(Parser.Tactic.simpLemma| $(mkIdent name):ident)
  let remaining ← equalityGoal.withContext do
    evalTacticAt
      (← `(tactic|
        simp [$[$simpArgs],*] <;>
          norm_num <;>
          field_simp (disch := positivity) <;>
          ring))
      equalityGoal
  unless remaining.isEmpty do
    let targets ← remaining.mapM fun goal ↦
      goal.withContext do Meta.ppExpr (← instantiateMVars (← goal.getType))
    throwError
      "certificate reference normalization left unresolved equality goals\
       \n  {String.intercalate "\n  " (targets.map (·.pretty))}"
  ProofCarrier.checkCompletedProof "certificate reference normalization" proof

private def normalizeApproxReference
    (certificate target : Expr) : TacticM Expr := do
  let target := target.consumeMData
  let targetArgs := target.getAppArgs
  unless target.getAppFn.isConstOf ``ApproxOn ∧ targetArgs.size >= 4 do
    return certificate
  let targetReference := targetArgs[targetArgs.size - 3]!
  let targetDomain := targetArgs[targetArgs.size - 2]!
  let certificateType ← instantiateMVars (← inferType certificate)
  let certificateArgs := certificateType.consumeMData.getAppArgs
  if certificateArgs.isEmpty then
    return certificate
  let certificateDomain := certificateArgs[certificateArgs.size - 1]!
  unless ← ProofCarrier.isDefEqReadOnly targetDomain certificateDomain do
    return certificate
  let certificateReference ←
    reduceCertificateField <| ← mkAppM ``ApproxCert.rhs #[certificate]
  if ← ProofCarrier.isDefEqReadOnly certificateReference targetReference then
    return certificate
  let proof ←
    inferNormalizedEqOnProof
      certificateReference targetReference certificateDomain
  mkAppM ``ApproxCert.replaceRhs #[certificate, targetReference, proof]

private def applyOneBudgetWeakening
    (kind : Name) (certificate target : Expr) : TacticM Bool := do
  let some targetBudget := targetFinalArg target | return false
  let certificate ←
    if kind == ``ModelApproxCert then
      mkAppM ``ModelApproxCert.toApproxCert #[certificate]
    else
      pure certificate
  let kind := if kind == ``ModelApproxCert then ``ApproxCert else kind
  let certificateBudget ← reduceCertificateField <| ←
    if kind == ``ApproxCert then
      mkAppM ``ApproxCert.eps #[certificate]
    else if kind == ``ResidualCert then
      mkAppM ``ResidualCert.eps #[certificate]
    else if kind == ``BoundCert then
      mkAppM ``BoundCert.upper #[certificate]
    else
      return false
  let certificate ←
    if kind == ``ApproxCert then
      normalizeApproxReference certificate target
    else
      pure certificate
  let budgetGoal ← mkAppM ``LE.le #[certificateBudget, targetBudget]
  let budgetProof ← mkFreshExprSyntheticOpaqueMVar budgetGoal
  let widened ←
    if kind == ``ApproxCert then
      mkAppM ``ApproxCert.weaken #[certificate, budgetProof]
    else if kind == ``ResidualCert then
      mkAppM ``ResidualCert.weaken #[certificate, budgetProof]
    else if kind == ``BoundCert then
      mkAppM ``BoundCert.weaken #[certificate, budgetProof]
    else
      return false
  let proof ←
    if kind == ``ApproxCert then
      mkAppM ``ApproxCert.sound #[widened]
    else if kind == ``ResidualCert then
      mkAppM ``ResidualCert.sound #[widened]
    else if kind == ``BoundCert then
      mkAppM ``BoundCert.sound #[widened]
    else
      throwError "unsupported CEGA certificate weakening kind {kind}"
  let goalsBefore ← getGoals
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let proofType ← instantiateMVars (← inferType proof)
  unless ← isDefEq proofType target do
    return false
  goal.assign (← instantiateMVars proof)
  closeArithmeticGoals "certificate budget weakening"
    [budgetProof.mvarId!] (goalsBefore.drop 1)
  discard <|
    ProofCarrier.validateAssignedProof "certificate projection" goal target
  return true

private def applyQuadratureWeakening
    (certificate target : Expr) : TacticM Bool := do
  let target := target.consumeMData
  let targetArgs := target.getAppArgs
  unless target.getAppFn.isConstOf ``LE.le ∧ targetArgs.size >= 2 do
    return false
  let targetBudget := targetArgs[targetArgs.size - 1]!
  let soundBudget ←
    reduceCertificateField <| ← mkAppM ``QuadratureCert.error #[certificate]
  let budgetGoal ← mkAppM ``LE.le #[soundBudget, targetBudget]
  let budgetProof ← mkFreshExprSyntheticOpaqueMVar budgetGoal
  let widened ← mkAppM ``QuadratureCert.weaken #[certificate, budgetProof]
  let proof ← mkAppM ``QuadratureCert.sound #[widened]
  let goalsBefore ← getGoals
  let goal ← getMainGoal
  let proofType ← instantiateMVars (← inferType proof)
  unless ← isDefEq proofType target do
    return false
  goal.assign (← instantiateMVars proof)
  closeArithmeticGoals "quadrature error weakening"
    [budgetProof.mvarId!] (goalsBefore.drop 1)
  discard <|
    ProofCarrier.validateAssignedProof "certificate projection" goal target
  return true

private def applyEnclosureWeakening
    (certificate target : Expr) : TacticM Bool := do
  let target := target.consumeMData
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``EnclosedOn ∧ args.size >= 4 do
    return false
  let targetLo := args[args.size - 2]!
  let targetHi := args[args.size - 1]!
  let targetFn := args[args.size - 4]!
  let targetDomain := args[args.size - 3]!
  let certificateType ← instantiateMVars (← inferType certificate)
  let certificateArgs := certificateType.consumeMData.getAppArgs
  if certificateArgs.isEmpty then
    return false
  let certificateDomain := certificateArgs[certificateArgs.size - 1]!
  unless ← ProofCarrier.isDefEqReadOnly targetDomain certificateDomain do
    return false
  let certificateFn ←
    reduceCertificateField <| ← mkAppM ``EnclosureCert.fn #[certificate]
  let certificate ←
    if ← ProofCarrier.isDefEqReadOnly targetFn certificateFn then
      pure certificate
    else
      let proof ← inferNormalizedEqOnProof targetFn certificateFn certificateDomain
      mkAppM ``CAS.Certificate.EnclosureCert.replaceFn
        #[certificate, targetFn, proof]
  let certLo ←
    reduceCertificateField <| ← mkAppM ``EnclosureCert.lo #[certificate]
  let certHi ←
    reduceCertificateField <| ← mkAppM ``EnclosureCert.hi #[certificate]
  let lowerGoal ← mkAppM ``LE.le #[targetLo, certLo]
  let upperGoal ← mkAppM ``LE.le #[certHi, targetHi]
  let lowerProof ← mkFreshExprSyntheticOpaqueMVar lowerGoal
  let upperProof ← mkFreshExprSyntheticOpaqueMVar upperGoal
  let widened ←
    mkAppM ``EnclosureCert.weaken #[certificate, lowerProof, upperProof]
  let proof ← mkAppM ``EnclosureCert.sound #[widened]
  let goalsBefore ← getGoals
  let goal ← getMainGoal
  let proofType ← instantiateMVars (← inferType proof)
  unless ← isDefEq proofType target do
    return false
  goal.assign (← instantiateMVars proof)
  closeArithmeticGoals "certificate enclosure weakening"
    [lowerProof.mvarId!, upperProof.mvarId!] (goalsBefore.drop 1)
  discard <|
    ProofCarrier.validateAssignedProof "certificate projection" goal target
  return true

private def tryProjectedCertificate
    (kind soundTheorem : Name)
    (certificate target : Expr) : TacticM Bool := do
  let exactMatch ←
    ProofCarrier.assignExactProof "certificate projection"
      (← soundProjection soundTheorem certificate)
  if exactMatch then
    return true
  ProofCarrier.restoringStateOnFalse do
    if kind == ``QuadratureCert then
      applyQuadratureWeakening certificate target
    else if kind == ``EnclosureCert then
      applyEnclosureWeakening certificate target
    else
      applyOneBudgetWeakening kind certificate target

private def targetDomain? (kind : Name) (target : Expr) : Option Expr :=
  let target := target.consumeMData
  let args := target.getAppArgs
  if kind == ``EnclosureCert then
    if target.getAppFn.isConstOf ``EnclosedOn ∧ args.size >= 3 then
      some args[args.size - 3]!
    else
      none
  else if kind == ``ApproxCert ∨ kind == ``ModelApproxCert then
    if target.getAppFn.isConstOf ``ApproxOn ∧ args.size >= 2 then
      some args[args.size - 2]!
    else
      none
  else if kind == ``ResidualCert then
    if target.getAppFn.isConstOf ``ResidualBound ∧ args.size >= 2 then
      some args[args.size - 2]!
    else
      none
  else if kind == ``BoundCert then
    if target.getAppFn.isConstOf ``BoundOn ∧ args.size >= 2 then
      some args[args.size - 2]!
    else
      none
  else
    none

private def restrictCertificate
    (kind : Name) (certificate targetDomain subsetProof : Expr) :
    MetaM Expr :=
  if kind == ``ApproxCert then
    mkAppM ``ApproxCert.restrict #[certificate, targetDomain, subsetProof]
  else if kind == ``ResidualCert then
    mkAppM ``ResidualCert.restrict #[certificate, targetDomain, subsetProof]
  else if kind == ``BoundCert then
    mkAppM ``BoundCert.restrict #[certificate, targetDomain, subsetProof]
  else if kind == ``EnclosureCert then
    mkAppM ``EnclosureCert.restrict #[certificate, targetDomain, subsetProof]
  else if kind == ``ModelApproxCert then
    mkAppM ``ModelApproxCert.restrict #[certificate, targetDomain, subsetProof]
  else
    throwError "certificate kind {kind} has no domain restriction"

/-- Infer the domain inclusion needed to restrict a generated certificate. -/
def inferSubsetProof (smaller larger : Expr) : TacticM Expr := do
  let expected ← mkAppM ``Set.Subset #[smaller, larger]
  let proof ← mkFreshExprMVar expected
  let remaining ←
    try
      evalTacticAt
        (← `(tactic| solve | assumption | simp_all [Set.Subset] | aesop)) proof.mvarId!
    catch _ =>
      throwError
        "certificate domain restriction could not prove that the theorem domain is a subset \
         of the generated certificate domain"
  unless remaining.isEmpty do
    throwError
      "certificate domain restriction could not prove that the theorem domain is a subset \
       of the generated certificate domain"
  ProofCarrier.checkCompletedProof "certificate subset inference" proof

private def tryCertificate
    (certificate type target : Expr) : TacticM Bool := do
  let some (kind, soundTheorem) := certificateDescriptor? type | return false
  if ← tryProjectedCertificate kind soundTheorem certificate target then
    return true
  let some certificateDomain := targetFinalArg type | return false
  let some targetDomain := targetDomain? kind target | return false
  if ← ProofCarrier.isDefEqReadOnly targetDomain certificateDomain then
    return false
  let subsetProof ← inferSubsetProof targetDomain certificateDomain
  let restricted ←
    restrictCertificate kind certificate targetDomain subsetProof
  tryProjectedCertificate kind soundTheorem restricted target

/--
Close the main goal from one explicit checked certificate.

The same exact projection, domain restriction, and budget weakening rules used
by local certificate inference apply. Failure leaves the tactic state
unchanged.
-/
def closeUsingCertificate (certificate : Expr) : TacticM Unit :=
  ProofCarrier.preservingStateOnFailure do
    discard <| ProofCarrier.runClosingMainGoal "certificate projection" do
      withMainContext do
        let type ← instantiateMVars (← inferType certificate)
        let target ← instantiateMVars (← getMainTarget)
        unless ← tryCertificate certificate type target do
          throwError
            "the supplied certificate does not prove the target, even after \
             supported domain restriction or budget weakening"

/--
Close the main goal from a matching checked certificate in the local
context.

Exact projections are tried first.  Approximation, residual, bound, model, and
quadrature certificates may then be weakened to a larger requested budget;
enclosures may be widened at both endpoints.  Every generated inequality must
be discharged by the shared arithmetic phase.
-/
def closeFromLocalCertificates : TacticM Unit :=
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let context ← getLCtx
    for declaration in context do
      unless declaration.isImplementationDetail do
        try
          if ← ProofCarrier.restoringStateOnFalse do
              tryCertificate
                (mkFVar declaration.fvarId) declaration.type target then
            return
        catch _ =>
          pure ()
    let targetCertificates ←
      ProofCarrier.collectTypedSubexpressions
        (fun type ↦ (certificateDescriptor? type).isSome) target
    for (certificate, certificateType) in targetCertificates do
      try
        if ← ProofCarrier.restoringStateOnFalse do
            tryCertificate certificate certificateType target then
          return
      catch _ =>
        pure ()
    throwError
      "cega found no checked certificate in the local context or target whose \
       semantic theorem matches the goal"

end CAS.Tactic.Certificate

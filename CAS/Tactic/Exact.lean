/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Exact.ApproximationRoutes
public import CAS.Exact.TensorResidual
public import CAS.Exact.VectorResidual
public import CAS.Tactic.Assumptions -- shake: keep: the scalar route quotes `symbolic_assumptions` in tactic syntax

/-!
# Exact symbolic goals

The semantic stage of the public `cas` tactic. It recognizes semantic projections of checked
scalar, vector, and tensor routes, computes their exact readiness obligations in the kernel, and
constructs proofs of ordinary `Set.EqOn`, zero `ResidualBound`, and supported zero-error
`ApproxOn` targets; an `ApproxOn` with a positive error is a certificate goal of `cega`. Syntax
policy, arithmetic fallback, and differentiation belong to the public `CAS.ExactTactic` module,
whose semantic stage calls `closeSemanticTarget`.

## Implementation notes

The checked normalizer proposes the route: a scalar residual goes through the configured
side-conditioned pipeline (`Exact.SymbolicClaimRoute.withSideConditions`, and
`Exact.symbolicApproxRoute` for two expressions), and a residual that the pipeline does not
close is retried with the multivariate canonical form `Verified.Expr.Alg.canonical` of the
difference, whose route proves the same projections. The facts about a scalar route, that its
target is the literal zero and what its essential side conditions are
(`CAS.Verified.Expr.essentialSide`, the emitted obligations the structural sign checker does not
prove), are certified together by one `decide +kernel`
(`CAS.Tactic.KernelReadBack.decideByKernel`). The empty essential list is tried first, so a
route without essential obligations costs one kernel evaluation; otherwise the route is read back
once and its essential conditions are discharged on the patch by `symbolic_assumptions`. With
`cas using h`, the kernel checks the zero normal form first and `h` must prove the side
conditions. Vector and tensor routes are checked component by component, by `fin_cases` and
`decide +kernel`. The elaborator never unfolds a normalizer run.

The soundness theorems are those of the routes: `Exact.SymbolicClaimRoute.eqOn_zero` and
`Exact.SymbolicClaimRoute.residualBound_zero` in `CAS.Exact.ZeroResidual`,
`Exact.eqOn_of_symbolicApproxRoute` and `Exact.approxOn_zero_of_symbolicApproxRoute` in
`CAS.Exact.ApproximationRoutes`, the zero theorems of `CAS.Exact.VectorResidual` and
`CAS.Exact.TensorResidual`, and, for the canonical form, `approxOn_of_difference_residualBound` and
`eqOn_of_approxOn_zero`.
-/

public meta section

namespace CAS.Tactic.Exact

open Lean Elab Tactic Meta
open CAS.Certificate

private def finalArgOf? (e : Expr) (name : Name) : Option Expr :=
  let e := e.consumeMData
  let args := e.getAppArgs
  if e.getAppFn.isConstOf name ∧ !args.isEmpty then
    some args[args.size - 1]!
  else
    none

private def extractExprFnArg? (e : Expr) : TacticM (Option Expr) := do
  if let some expr := finalArgOf? e ``Exact.exprFn then
    return some expr
  let .lam _ _ body _ := e.consumeMData | return none
  let some expr := finalArgOf? body ``Verified.Expr.eval | return none
  let checkedFn ← mkAppM ``Exact.exprFn #[expr]
  if ← ProofCarrier.isDefEqReadOnly e checkedFn then
    return some expr
  return none

private def extractVectorFnRoute? (e : Expr) : Option Expr :=
  finalArgOf? e ``Exact.VectorResidual.vectorFn

private def extractTensorFnRoute? (e : Expr) : Option Expr :=
  finalArgOf? e ``Exact.TensorResidual.tensorFn

private def isZeroFnLike (e : Expr) : TacticM Bool := do
  if e.consumeMData.getAppFn.isConstOf ``Exact.zeroFn then
    return true
  try
    let ty ← inferType e
    let zeroFn ← Term.elabTerm (← `(fun _ ↦ 0)) (some ty)
    ProofCarrier.isDefEqReadOnly e zeroFn
  catch _ =>
    return false

private def zeroScalarLike (e : Expr) : TacticM Bool := do
  try
    let zero ← Term.elabTerm (← `(0)) (some (← inferType e))
    ProofCarrier.isDefEqReadOnly e zero
  catch _ =>
    return false

/-- The fact `route.rhs = 0` of a scalar route, certified by the kernel. -/
private def routeZeroFact (route : Expr) : TacticM Expr := do
  let rhs ← mkAppM ``Verified.Expr.SideClaimRoute.rhs #[route]
  let zero ← Term.elabTerm (← `(0)) (some (← inferType rhs))
  KernelReadBack.decideByKernel "cas" (← mkEq rhs zero)

/--
Certify a scalar route on a patch without user evidence: the proof of `route.rhs = 0` and a
proof of `route.SideHoldsOn patch`. One `decide +kernel` certifies the zero normal form
together with the essential side list, guessed empty first; when the guess fails the route is
read back in one kernel evaluation, certified against the essential list read back, and that
explicit list is discharged at every point of the patch by `symbolic_assumptions`.
-/
private def scalarRouteEvidence (route patch : Expr) : TacticM (Expr × Expr) := do
  let rhs ← mkAppM ``Verified.Expr.SideClaimRoute.rhs #[route]
  let nonzero ← mkAppM ``Verified.Expr.SideClaimRoute.nonzero #[route]
  let zero ← Term.elabTerm (← `(0)) (some (← inferType rhs))
  let nil ← Term.elabTerm (← `([])) (some (← inferType nonzero))
  let essential ← mkAppM ``Verified.Expr.essentialSide #[nonzero]
  let certify (side : Expr) : TacticM (Option Expr) := do
    try
      some <$> KernelReadBack.decideByKernel "cas" (mkAnd (← mkEq rhs zero) (← mkEq essential side))
    catch _ =>
      pure none
  match ← certify nil with
  | some both =>
      let hside ← mkAppM ``Exact.SymbolicClaimRoute.sideHoldsOn_of_essentialSide_eq_nil
        #[route, patch, ← mkAppM ``And.right #[both]]
      return (← mkAppM ``And.left #[both], hside)
  | none =>
      let index ← KernelReadBack.finIndexOfType (← inferType rhs)
      let (normalForm, sideList) ← KernelReadBack.readBackPair index rhs nonzero
      unless normalForm == .nat 0 do
        throwError
          "cas: the checked route does not reduce the residual to zero.\nNormalized residual:\
           {indentExpr (← KernelReadBack.quoteNatExpression index normalForm)}"
      let side ← KernelReadBack.quoteNatList index (KernelReadBack.essentialConditions sideList)
      let some both ← certify side
        | throwError "cas could not certify the checked route"
      let transport ← mkAppOptM ``Exact.SymbolicClaimRoute.sideHoldsOn_of_essentialSide_eq
        #[none, some route, some patch, some side, some (← mkAppM ``And.right #[both])]
      let transportType ← whnf (← inferType transport)
      unless transportType.isForall do
        throwError "cas internal error: the essential side transport has no hypothesis"
      let holds ← mkFreshExprSyntheticOpaqueMVar transportType.bindingDomain!
      let remaining ←
        try
          KernelReadBack.withSuppressedMessagesMeta <| KernelReadBack.runTacticOnGoal holds.mvarId!
            (← `(tactic| (intro x hx; symbolic_assumptions)))
        catch error =>
          throwError
            "cas could not discharge the essential side conditions of the checked route on the \
             patch:{indentD error.toMessageData}"
      unless remaining.isEmpty do
        throwError "cas could not discharge the essential side conditions of the checked route"
      return (← mkAppM ``And.left #[both], mkApp transport (← instantiateMVars holds))

/--
Project a checked symbolic route to either a zero residual bound or equality with zero, given
the proof `hzero` that its residual is zero and the proof `hside` that its obligations hold on
the patch.
-/
private def mkSymbolicRouteZeroProof
    (route patch : Expr) (residual : Bool) (hzero hside : Expr) : TacticM Expr := do
  if residual then
    mkAppM ``Exact.SymbolicClaimRoute.residualBound_zero #[route, patch, hside, hzero]
  else
    mkAppM ``Exact.SymbolicClaimRoute.eqOn_zero #[route, patch, hside, hzero]

private def mkVectorRouteZeroProof
    (route patch : Expr) (residual : Bool) (hside? : Option Expr) : TacticM Expr := do
  let theoremName :=
    match hside?, residual with
    | none, true => ``Exact.VectorResidual.residualBound_zero_ready
    | none, false => ``Exact.VectorResidual.eqOn_zero_ready
    | some _, true => ``Exact.VectorResidual.residualBound_zero
    | some _, false => ``Exact.VectorResidual.eqOn_zero
  let base ← mkAppM theoremName #[route, patch]
  forallTelescope (← inferType base) fun params _ ↦ do
    let expectedCount := if hside?.isSome then 2 else 1
    unless params.size == expectedCount do
      throwError "cas internal error: unexpected vector projection obligations"
    match hside? with
    | none =>
        let hzero ← Term.withoutErrToSorry <| Term.elabTerm
          (← `(by intro i; fin_cases i <;> decide +kernel))
          (some (← inferType params[0]!))
        mkAppM theoremName #[route, patch, hzero]
    | some hside =>
        let actual ← inferType hside
        let expected ← inferType params[0]!
        unless ← isDefEq actual expected do
          throwError
            "cas vector side evidence has type{indentExpr actual}\n\
             but the route requires{indentExpr expected}"
        let hzero ← Term.withoutErrToSorry <| Term.elabTerm
          (← `(by intro i; fin_cases i <;> decide +kernel))
          (some (← inferType params[1]!))
        mkAppM theoremName #[route, patch, hside, hzero]

private def mkTensorRouteZeroProof
    (route patch : Expr) (residual : Bool) (hside? : Option Expr) : TacticM Expr := do
  let theoremName :=
    match hside?, residual with
    | none, true => ``Exact.TensorResidual.residualBound_zero_ready
    | none, false => ``Exact.TensorResidual.eqOn_zero_ready
    | some _, true => ``Exact.TensorResidual.residualBound_zero
    | some _, false => ``Exact.TensorResidual.eqOn_zero
  let base ← mkAppM theoremName #[route, patch]
  forallTelescope (← inferType base) fun params _ ↦ do
    let expectedCount := if hside?.isSome then 2 else 1
    unless params.size == expectedCount do
      throwError "cas internal error: unexpected tensor projection obligations"
    match hside? with
    | none =>
        let hzero ← Term.withoutErrToSorry <| Term.elabTerm
          (← `(by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel))
          (some (← inferType params[0]!))
        mkAppM theoremName #[route, patch, hzero]
    | some hside =>
        let actual ← inferType hside
        let expected ← inferType params[0]!
        unless ← isDefEq actual expected do
          throwError
            "cas tensor side evidence has type{indentExpr actual}\n\
             but the route requires{indentExpr expected}"
        let hzero ← Term.withoutErrToSorry <| Term.elabTerm
          (← `(by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel))
          (some (← inferType params[1]!))
        mkAppM theoremName #[route, patch, hside, hzero]

/-- Prove `Set.EqOn (exprFn lhs) (exprFn rhs) patch`, or its zero-error `ApproxOn` form, from
the zero residual of the difference route of `lhs` and `rhs` and the discharge of its
obligations on the patch. -/
private def mkSymbolicEqualityProof
    (lhs rhs patch : Expr) (approx : Bool) (hzero hside : Expr) : TacticM Expr := do
  if approx then
    mkAppM ``Exact.approxOn_zero_of_symbolicApproxRoute #[lhs, rhs, patch, hside, hzero]
  else
    mkAppM ``Exact.eqOn_of_symbolicApproxRoute #[lhs, rhs, patch, hside, hzero]

private def elaborateProof (side : TSyntax `term) (expected : Expr) : TacticM Expr := do
  let proof ← Term.withoutErrToSorry <| Term.elabTerm side (some expected)
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars proof

/-- The multivariate canonical form of `expr` as a scalar route, the fallback for residuals that
the configured pipeline does not close. -/
private def canonicalRoute (expr : Expr) : TacticM Expr :=
  mkAppM ``Verified.Expr.Alg.canonical #[expr]

/-- The zero fact and the patch discharge of a scalar route: from user evidence, whose
elaboration is preceded by the cheap kernel check of the zero normal form so that a route that
does not close fails before the evidence is elaborated, or from `scalarRouteEvidence`. -/
private def scalarRouteFacts
    (route patch : Expr) (side? : Option (TSyntax `term)) : TacticM (Expr × Expr) := do
  match side? with
  | none => scalarRouteEvidence route patch
  | some side =>
      let hzero ← routeZeroFact route
      let expected ← mkAppM ``Exact.SymbolicClaimRoute.SideHoldsOn #[route, patch]
      return (hzero, ← elaborateProof side expected)

private def scalarZeroProofWith
    (route patch : Expr) (residual : Bool)
    (side? : Option (TSyntax `term)) : TacticM Expr := do
  let (hzero, hside) ← scalarRouteFacts route patch side?
  mkSymbolicRouteZeroProof route patch residual hzero hside

private def scalarZeroProof
    (expr patch : Expr) (residual : Bool)
    (side? : Option (TSyntax `term)) : TacticM Expr := do
  let route ← mkAppM ``Exact.SymbolicClaimRoute.withSideConditions #[expr]
  try
    scalarZeroProofWith route patch residual side?
  catch pipelineError =>
    try
      scalarZeroProofWith (← canonicalRoute expr) patch residual side?
    catch canonicalError =>
      throwError
        "{pipelineError.toMessageData}\ncanonical form route:{indentD canonicalError.toMessageData}"

/-- Prove `Set.EqOn (exprFn lhs) (exprFn rhs) patch`, or the zero-error `ApproxOn` form, from the
zero residual of the canonical route of `lhs - rhs`. -/
private def mkCanonicalEqualityProof
    (lhs rhs patch : Expr) (approx : Bool)
    (side? : Option (TSyntax `term)) : TacticM Expr := do
  let route ← canonicalRoute (← mkAppM ``Verified.Expr.sub #[lhs, rhs])
  let residualProof ← scalarZeroProofWith route patch true side?
  let approxProof ←
    mkAppOptM ``approxOn_of_difference_residualBound
      #[none, none, none, some (← mkAppM ``Exact.exprFn #[lhs]),
        some (← mkAppM ``Exact.exprFn #[rhs]), none, none, some residualProof]
  if approx then
    return approxProof
  mkAppM ``eqOn_of_approxOn_zero #[approxProof]

private def vectorSideProof
    (route patch : Expr) (side : TSyntax `term) : TacticM Expr := do
  let base ← mkAppM ``Exact.VectorResidual.eqOn_zero #[route, patch]
  forallTelescope (← inferType base) fun params _ ↦ do
    unless params.size == 2 do
      throwError "cas internal error: the vector projection did not expose two obligations"
    elaborateProof side (← inferType params[0]!)

private def vectorZeroProof
    (route patch : Expr) (residual : Bool)
    (side? : Option (TSyntax `term)) : TacticM Expr := do
  let hside? ←
    match side? with
    | none => pure none
    | some side => some <$> vectorSideProof route patch side
  mkVectorRouteZeroProof route patch residual hside?

private def tensorSideProof
    (route patch : Expr) (side : TSyntax `term) : TacticM Expr := do
  let base ← mkAppM ``Exact.TensorResidual.eqOn_zero #[route, patch]
  forallTelescope (← inferType base) fun params _ ↦ do
    unless params.size == 2 do
      throwError "cas internal error: the tensor projection did not expose two obligations"
    elaborateProof side (← inferType params[0]!)

private def tensorSemanticZeroProof
    (route patch : Expr) (residual : Bool)
    (side? : Option (TSyntax `term)) : TacticM Expr := do
  let hside? ←
    match side? with
    | none => pure none
    | some side => some <$> tensorSideProof route patch side
  mkTensorRouteZeroProof route patch residual hside?

private def zeroFunctionProof
    (fn patch : Expr) (residual : Bool)
    (side? : Option (TSyntax `term)) : TacticM Expr := do
  match extractVectorFnRoute? fn with
  | some route => vectorZeroProof route patch residual side?
  | none =>
      match extractTensorFnRoute? fn with
      | some route => tensorSemanticZeroProof route patch residual side?
      | none =>
          match ← extractExprFnArg? fn with
          | some expr => scalarZeroProof expr patch residual side?
          | none => throwError "cas expected a checked symbolic function"

private def scalarEqualityProof
    (lhs rhs patch : Expr) (approx : Bool)
    (side? : Option (TSyntax `term)) : TacticM Expr := do
  let standard : TacticM Expr := do
    let route ← mkAppM ``Exact.symbolicApproxRoute #[lhs, rhs]
    let (hzero, hside) ← scalarRouteFacts route patch side?
    mkSymbolicEqualityProof lhs rhs patch approx hzero hside
  try
    standard
  catch pipelineError =>
    try
      mkCanonicalEqualityProof lhs rhs patch approx side?
    catch canonicalError =>
      throwError
        "{pipelineError.toMessageData}\ncanonical form route:{indentD canonicalError.toMessageData}"

private def residualTargetProof
    (target : Expr) (side? : Option (TSyntax `term)) : TacticM Expr := do
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``ResidualBound ∧ args.size >= 3 do
    throwError "not a ResidualBound target"
  let residual := args[args.size - 3]!
  let patch := args[args.size - 2]!
  let eps := args[args.size - 1]!
  unless ← zeroScalarLike eps do
    throwError "cas only proves exact zero-residual targets"
  zeroFunctionProof residual patch true side?

private def eqOnTargetProof
    (target : Expr) (side? : Option (TSyntax `term)) : TacticM Expr := do
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``Set.EqOn ∧ args.size >= 3 do
    throwError "not a Set.EqOn target"
  let lhs := args[args.size - 3]!
  let rhs := args[args.size - 2]!
  let patch := args[args.size - 1]!
  if ← isZeroFnLike rhs then
    zeroFunctionProof lhs patch false side?
  else if ← isZeroFnLike lhs then
    let proof ← zeroFunctionProof rhs patch false side?
    mkAppM ``Set.EqOn.symm #[proof]
  else
    match ← extractExprFnArg? lhs, ← extractExprFnArg? rhs with
    | some lhsExpr, some rhsExpr =>
        scalarEqualityProof lhsExpr rhsExpr patch false side?
    | _, _ =>
        throwError "cas expected Set.EqOn over checked symbolic expressions"

private def approxOnTargetProof
    (target : Expr) (side? : Option (TSyntax `term)) : TacticM Expr := do
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``ApproxOn ∧ args.size >= 4 do
    throwError "not an ApproxOn target"
  let lhs := args[args.size - 4]!
  let rhs := args[args.size - 3]!
  let patch := args[args.size - 2]!
  let eps := args[args.size - 1]!
  unless ← zeroScalarLike eps do
    throwError "cas proves `ApproxOn f g s 0`; an approximation with a positive error is a \
      certificate goal of `cega`"
  if ← isZeroFnLike rhs then
    let eqProof ← zeroFunctionProof lhs patch false side?
    mkAppM ``approxOn_of_eqOn #[eqProof]
  else if ← isZeroFnLike lhs then
    let eqProof ← zeroFunctionProof rhs patch false side?
    let reversed ← mkAppM ``Set.EqOn.symm #[eqProof]
    mkAppM ``approxOn_of_eqOn #[reversed]
  else
    match ← extractExprFnArg? lhs, ← extractExprFnArg? rhs with
    | some lhsExpr, some rhsExpr =>
        scalarEqualityProof lhsExpr rhsExpr patch true side?
    | _, _ =>
        throwError "cas expected `ApproxOn` over checked symbolic expressions"

private def semanticTargetProof
    (target : Expr) (side? : Option (TSyntax `term)) : TacticM Expr := do
  let target := target.consumeMData
  if target.getAppFn.isConstOf ``ResidualBound then
    residualTargetProof target side?
  else if target.getAppFn.isConstOf ``Set.EqOn then
    eqOnTargetProof target side?
  else if target.getAppFn.isConstOf ``ApproxOn then
    approxOnTargetProof target side?
  else
    throwError "cas expected `Set.EqOn`, a zero-error `ApproxOn` or a zero `ResidualBound`"

/-- Close the main goal when it is a supported semantic exact target: `Set.EqOn`, a zero-error
`ApproxOn` or a zero `ResidualBound` over checked symbolic expressions. -/
def closeSemanticTarget (side? : Option (TSyntax `term)) : TacticM Unit :=
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let proof ← semanticTargetProof target side?
    unless ← ProofCarrier.assignExactProof "cas exact semantic route" proof do
      throwError "cas exact semantic route produced evidence for a different target"

end CAS.Tactic.Exact

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Tactic.Certificate
public import CAS.Tactic.CEGA.Registrations
public meta import CAS.Tactic.CEGA.Registry
public import CAS.Tactic.CEGA.Registry

/-!
# CEGA proof projection

The carrier route of `cega`: a checked carrier is projected to the semantic goal through its
soundness theorem. A carrier is a certificate structure handled by
`CAS.Tactic.Certificate` (`ApproxCert`, `ResidualCert`, `BoundCert`, `EnclosureCert`,
`ModelApproxCert`, `QuadratureCert`), a `CertificateRoute` to an enclosure, bound or residual
certificate, or a type registered with `cega_carrier` (`CAS.Tactic.CEGA.Registry`).
Atlas certificates enter through their `toResidualCert` or `toApproxCert` conversions.

`closeFromLocalCarriers` searches the local context and then the subterms of the goal;
`closeUsingCarrier` projects one carrier supplied as `cega using h`. A term of any other type is
refused: an ordinary proof is applied with `exact`, not projected. Planner traces, charts, and
report metadata are not carriers.

## Main definitions

* `closeFromLocalCarriers`: the carrier route of bare `cega`, over the local context and the
  subterms of the goal.
* `closeUsingCarrier`: `cega using h`, for one supplied carrier.

## Implementation notes

We dispatch on the head of the carrier's type. A `CertificateRoute` over an `EnclosureCert`,
`BoundCert` or `ResidualCert` is projected by `CertificateRoute.cert`. For a registered type we
apply each of its soundness theorems to the carrier in turn, and assign a proof only when its
type agrees with the goal and the completed proof checks (`ProofCarrier.assignExactProof`);
failing that, its certificate projection goes to `Certificate.closeUsingCertificate`, which also
restricts the certificate to the goal's domain and weakens its budget to the requested one.
Any other term is tried as a certificate itself. `closeFromLocalCarriers` tries the hypotheses,
then the certificates that `Certificate.closeFromLocalCertificates` finds, then the carriers
among the subterms of the goal, and every failed attempt leaves the state as it was.

Nothing is trusted from the name of a type: a registration only says which theorems and which
projection to try, and the kernel checks the proof that results. The soundness theorems live
with the carriers, in `CAS/Certificate`, `CAS/Continuum/IntervalEval/Context.lean`,
`CAS/Continuum/IntervalEval/Attempt.lean` and `CAS/Continuum/IntervalEval/SymbolicApprox.lean`,
and the returned `SelectedRoute` is reporting metadata. Beyond this dispatch the carrier route
runs no algorithm of its own.
-/

public meta section

namespace CAS.Tactic.CEGA

open Lean Elab Tactic Meta
open CAS
open CAS.Certificate
open CAS.Continuum.RationalInterval

private def certificateRouteDescriptor? (type : Expr) :
    Option (Name × CarrierDescriptor) := do
  let type := type.consumeMData
  guard (type.getAppFn.isConstOf ``CertificateRoute)
  let args := type.getAppArgs
  guard !args.isEmpty
  let certificateType := args[args.size - 1]!.consumeMData.getAppFn
  let route : SelectedRoute ←
    if certificateType.isConstOf ``EnclosureCert then
      some SelectedRoute.enclosureRoute
    else if certificateType.isConstOf ``BoundCert then
      some SelectedRoute.boundRoute
    else if certificateType.isConstOf ``ResidualCert then
      some SelectedRoute.residualRoute
    else
      none
  pure
    (``CertificateRoute,
      { route := route
        soundTheorems := #[]
        certificateProjection := ``CertificateRoute.cert })

private def carrierDescriptor? (env : Environment) (type : Expr) :
    Option (Name × CarrierDescriptor) :=
  certificateRouteDescriptor? type <|>
    let typeName := type.consumeMData.getAppFn.constName?
    typeName.bind fun name ↦
      (registeredCarrier? env name).map fun descriptor ↦ (name, descriptor)

private def tryProjection (theoremName : Name) (carrier : Expr) :
    TacticM Bool := do
  try
    ProofCarrier.assignExactProof "cega projection"
      (← mkAppM theoremName #[carrier])
  catch _ =>
    return false

private def tryProjections
    (theoremNames : Array Name) (carrier : Expr) : TacticM Bool := do
  for theoremName in theoremNames do
    if ← tryProjection theoremName carrier then
      return true
  return false

private def tryCertificate (cert : Expr) : TacticM Bool := do
  match ← ProofCarrier.attemptClosingMainGoal "cega certificate projection"
      (Certificate.closeUsingCertificate cert) with
  | .ok _ => return true
  | .error _ => return false

private def tryCarrier (carrier : Expr) : TacticM (Option SelectedRoute) :=
  ProofCarrier.restoringStateOnNone do
    try
      let type ← instantiateMVars (← inferType carrier)
      match carrierDescriptor? (← getEnv) type with
      | some (_, descriptor) =>
        if ← tryProjections descriptor.soundTheorems carrier then
          return some descriptor.route
        let cert ← mkAppM descriptor.certificateProjection #[carrier]
        if ← tryCertificate cert then
          return some descriptor.route
      | none =>
          if ← tryCertificate carrier then
            return some .certificate
      return none
    catch _ =>
      return none

/--
Close the main goal using one explicitly supplied CEGA certificate or route.

The term must have one of the registered checked-carrier types handled by
`tryCarrier`. Ordinary proofs should be applied with Lean's `exact` or
`apply`; accepting them here would erase the distinction between CEGA
certification and general theorem application. Returns the route and the
elaborated carrier.
-/
def closeUsingCarrier (carrierSyntax : TSyntax `term) : TacticM (SelectedRoute × Expr) :=
  withMainContext do
    let carrier ← Term.withoutErrToSorry <| Term.elabTerm carrierSyntax none
    Term.synthesizeSyntheticMVarsNoPostponing
    let carrier ← instantiateMVars carrier
    let some route ← tryCarrier carrier
      | throwError
          "cega expected a registered checked carrier or direct certificate \
           proving the current semantic target"
    return (route, carrier)

/-- Close the main goal from a checked CEGA carrier in the local context or target. -/
def closeFromLocalCarriers : TacticM SelectedRoute :=
  withMainContext do
    let context ← getLCtx
    for declaration in context do
      unless declaration.isImplementationDetail do
        if let some route ← tryCarrier (mkFVar declaration.fvarId) then
          return route
    match ← ProofCarrier.attemptClosingMainGoal "cega local certificate projection"
        Certificate.closeFromLocalCertificates with
    | .ok _ => return .certificate
    | .error _ => pure ()
    let target ← instantiateMVars (← getMainTarget)
    let env ← getEnv
    let carriers ←
      ProofCarrier.collectTypedSubexpressions
        (fun type ↦ (carrierDescriptor? env type).isSome) target
    for (carrier, _) in carriers do
      if let some route ← tryCarrier carrier then
        return route
    throwError
      "cega found no registered checked carrier or direct certificate \
       matching the target"

end CAS.Tactic.CEGA

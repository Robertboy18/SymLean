/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Tactic.KernelReadBack
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import CAS.Expr.Rendering
public meta import CAS.Expr.Rendering
public import CAS.Integration.Planner
public meta import CAS.Integration.Planner
public meta import CAS.Tactic.RouteRegistry

/-!
# Checked antiderivative planning

`findCertificate` turns a reflected integrand into an antiderivative certificate
`IntegrationCheck.AntiderivativeCert` together with an equation that lists its domain
requirements explicitly, and `certifyCandidate` does the same for a given primitive. Candidate
discovery is heuristic and carries no trust: a found candidate and a supplied one must pass the
same kernel check against the original integrand, and a refusal says nothing about whether an
antiderivative exists.

## Main definitions

* `FoundCertificate`: a certificate with the equation giving its requirements as explicit lists.
* `findCertificate`: search with the planner, then certification.
* `certifyCandidate`: certification of a given candidate.
* `certifyPrimitive`: the certificate of a primitive against its own symbolic derivative.
* `plannerStrategies`: the strategies that a refusal lists.

## Implementation notes

We run the planner `IntegrationPlanner.candidate?` of `CAS/Integration/Planner.lean` in compiled
metaprogramming code, on the integrand read back by `KernelReadBack.readBackExpression`. In
search order it tries sparse-polynomial integration (`CAS/Integration/Polynomial.lean`), the
elementary table (`CAS/Integration/Elementary.lean`), polynomials in the sine and cosine of one
phase and Bioche's substitutions (`CAS/Integration/Bioche.lean`), linearity and substitution,
exponential-trigonometric recurrences (`CAS/Integration/ExponentialTrig.lean`), rational
reduction, the tangent half-angle substitution, integration by parts, and one retry on a
normalized quotient; linearity, the substitutions and integration by parts live in the planner
itself. Rational reduction (`CAS/Integration/Rational.lean`) integrates the polynomial quotient,
passes the proper part to the Hermite reduction of `CAS/Integration/Hermite.lean` and the
square-free remainder to `CAS/Integration/RationalElementary.lean`. A denominator factor of
degree three or more that the planner cannot split needs Hex's factorizer, which `CASHex.Factor`
installs and `CAS.Tactic.RouteRegistry.factorProvider?` returns; without it the refusal says so.
The planner prunes its search with its own derivative screen, which enters no proof.

The candidate is quoted as an explicit expression tree, simplified when it comes from search and
left as written when it is supplied or taken from the goal, so that a supplied primitive keeps
its original domain requirements. We read its canonical domain requirements back in one kernel
evaluation (`KernelReadBack.readBackRequirements`), and one `decide +kernel`
(`KernelReadBack.decideByKernel`) proves both that the residual route `IntegrationCheck.route`
of `CAS/Integration/Check.lean` (sparse polynomial normalization, followed when needed by
`IntegrationCheck.TrigNormalization.route`) reduces `∂ᵢ F - f` to zero and that the requirements
are the explicit lists read back. This avoids evaluating an unsuccessful heuristic search in the
kernel while keeping the proof independent of native evaluation, and the elaborator never
unfolds the planner or the normalizer. The public query `CAS.integrate?` accepts a candidate
through `IntegrationCheck.certifyCandidate?`, whose condition is that the residual route reaches
zero. The `#cas` command runs that query in compiled code and then decides both facts in the
kernel; the tactic decides them directly and uses `IntegrationCheck.certifyCandidate?` only in
`certifyPrimitive`.
-/

public meta section

namespace CAS.Tactic.Integration.Planning

open Lean Elab Tactic Meta

/-- A checked antiderivative certificate together with the kernel-certified equation
`certificate.requirements = ⟨nonzero, positive⟩` for its explicit requirement lists. -/
structure FoundCertificate where
  /-- The certificate, with an explicit candidate. -/
  certificate : Expr
  /-- The proof that the certificate's requirements are explicit lists. -/
  requirementsEquation : Expr

private def certificateFromOptionCore
    (query : Expr) (noneMessage : String) : TacticM Expr := do
  Term.synthesizeSyntheticMVarsNoPostponing
  let query ← instantiateMVars query
  let reduced ← KernelReadBack.kernelWhnf query
  if reduced.isAppOfArity ``Option.none 1 then
    throwError noneMessage
  unless reduced.isAppOfArity ``Option.some 2 do
    throwError
      "cas could not reduce symbolic integration to a certificate"
  let certificate := reduced.getAppArgs[1]!
  if certificate.hasMVar ∨ certificate.hasSorry then
    throwError "cas produced incomplete certificate evidence"
  unless ← isTypeCorrect certificate do
    throwError "cas produced an ill-typed certificate"
  return certificate

/--
Available strategies of `IntegrationPlanner.candidate?`, in search order.
The planner records no execution trace: shape checks and fuel may skip a strategy,
so this list does not assert that every strategy ran on a particular input.
-/
def plannerStrategies : List String := [
  "sparse-polynomial integration",
  "the elementary table (powers of the coordinate; exp, sin, cos, atan, asin, acos, log, sqrt, \
    and real powers of an argument with constant derivative; 1/sqrt(1 - u^2) and \
    1/(c^2 + u^2) with a constant c)",
  "polynomials in the sine and cosine of one affine phase, reduced modulo sin^2 + cos^2 = 1",
  "Bioche's substitutions t = cos u, sin u or tan u for rational functions of the sine and \
    cosine of one affine phase",
  "linearity and constant factors",
  "substitution into a fresh variable, followed by the same recursive integrator",
  "exponential-trigonometric recurrences with symbolic slopes and an optional exponential or \
    trigonometric factor",
  "rational reduction in the selected coordinate (parameter-dependent numerator coefficients; \
    rational factors and bounded parameter-dependent linear or quadratic denominators)",
  "tangent half-angle substitution for a common affine trigonometric phase",
  "integration by parts in LIATE order",
  "one retry on the normalized quotient"]

/-- Render the selected integration coordinate as `t` and the remaining coordinates
as coefficients. Reflected goals need not integrate coordinate zero. -/
private def renderIntegrand? (coordinate integrand : Expr) : TacticM (Option String) := do
  try
    let coordinateValue ← KernelReadBack.kernelWhnf (← mkAppM ``Fin.val #[coordinate])
    let some selected := coordinateValue.rawNatLit? | return none
    let index ← KernelReadBack.finIndexOfType (← inferType integrand)
    let expression ← KernelReadBack.readBackExpression index integrand
    return some (expression.renderWith fun i ↦ if i = selected then "t" else s!"c{i}")
  catch _ =>
    return none

/-- A refusal shows the reflected integrand and available strategies, without claiming
that no antiderivative exists. -/
private def noCandidateMessage (coordinate integrand : Expr) (hint : String := "") :
    TacticM MessageData := do
  let integrandText :=
    match ← renderIntegrand? coordinate integrand with
    | some rendered =>
        m!" for the integrand `{rendered}` (integration coordinate `t`; the `c` coordinates stand \
          for coefficients that do not depend on it)"
    | none => m!""
  let strategies := ((List.range plannerStrategies.length).zip plannerStrategies).map
    fun (index, strategy) ↦ m!"{index + 1}. {strategy}"
  return m!"cas found no supported checked antiderivative{integrandText}. \
    Available strategies, in search order (subject to shape checks and fuel):\
    {indentD (MessageData.joinSep strategies m!"\n")}\n\
    It keeps no residual for a rejected candidate, so no partial result can be shown. \
    `#cas [integrate t] expression` runs the same search on the written expression and \
    displays the primitive when one is found.{hint}"

/-- Certify a proposed primitive against the original integrand, sharing the residual and
requirement-list proof with candidates produced by search. -/
def certifyCandidate (coordinate integrand candidate : Expr) : TacticM FoundCertificate := do
  let variableType ← KernelReadBack.finIndexOfType (← inferType candidate)
  let quotedCandidate ←
    KernelReadBack.quoteNatExpression variableType
      (← KernelReadBack.readBackExpression variableType candidate)
  let route ←
    mkAppM ``IntegrationCheck.route #[coordinate, integrand, quotedCandidate]
  let routeRhs ← mkAppM ``Verified.Expr.SideClaimRoute.rhs #[route]
  let zero := mkAppN (.const ``Verified.Expr.nat [Level.zero]) #[variableType, Lean.toExpr 0]
  let requirements ←
    mkAppM ``IntegrationCheck.AntiderivativeCert.candidateRequirements
      #[coordinate, integrand, quotedCandidate]
  let (nonzero, positive) ← KernelReadBack.readBackRequirements variableType requirements
  let explicitRequirements ← mkAppM ``Verified.Expr.ValidityRequirements.mk
    #[← KernelReadBack.quoteNatList variableType nonzero,
      ← KernelReadBack.quoteNatList variableType positive]
  let both ←
    try
      KernelReadBack.decideByKernel "cas"
        (mkAnd (← mkEq routeRhs zero) (← mkEq requirements explicitRequirements))
    catch error =>
      throwError
        "cas found a candidate primitive but could not certify its residual \
         and domain requirements. This does not rule out another primitive.\n\
         Certification detail:{indentD error.toMessageData}"
  let certificate ←
    mkAppM ``IntegrationCheck.AntiderivativeCert.mk
      #[quotedCandidate, ← mkAppM ``And.left #[both]]
  if certificate.hasMVar ∨ certificate.hasSorry then
    throwError "cas produced an incomplete certificate"
  unless ← isTypeCorrect certificate do
    throwError "cas produced an ill-typed certificate"
  let requirementsEquation ← mkEqTrans
    (← mkAppM ``IntegrationCheck.AntiderivativeCert.requirements_eq_candidateRequirements
      #[certificate])
    (← mkAppM ``And.right #[both])
  return { certificate, requirementsEquation }

/-- Discover a candidate in compiled code and certify it against the original integrand
with kernel evaluation. Only the residual and requirement proofs enter the certificate. -/
def findCertificate (coordinate integrand : Expr) : TacticM FoundCertificate := do
  Term.synthesizeSyntheticMVarsNoPostponing
  let integrand ← instantiateMVars integrand
  let variableType ← KernelReadBack.finIndexOfType (← inferType integrand)
  let some boundTerm ← KernelReadBack.finBound? variableType
    | throwError "cas needs a finite coordinate type"
  let some bound := (← KernelReadBack.kernelWhnf boundTerm).rawNatLit?
    | throwError "cas needs a concrete coordinate dimension"
  let some selected :=
      (← KernelReadBack.kernelWhnf (← mkAppM ``Fin.val #[coordinate])).rawNatLit?
    | throwError "cas needs a concrete integration coordinate"
  let reflected ← KernelReadBack.readBackExpression variableType integrand
  match bound with
  | 0 => throwError "cas cannot select a coordinate in dimension zero"
  | dimension + 1 =>
      if h : selected < dimension + 1 then
        let expression := reflected.mapVars fun j ↦ .var (Fin.ofNat (dimension + 1) j)
        let provider? := (← Tactic.RouteRegistry.factorProvider?).map
          CAS.Polynomial.Sparse.Univariate.RationalFactorization.ofDense
        let some candidate := IntegrationPlanner.candidate? ⟨selected, h⟩ expression provider?
          | let hint := if provider?.isNone &&
                CAS.IntegrationPlanner.Rational.needsFactorProvider ⟨selected, h⟩ expression then
                "\nThe denominator has a factor of degree three or more, which is not factored \
                  without Hex: `import CASHex.Factor` (built with `lake -R -Khex=on build \
                  CASHex`) factors it."
              else ""
            throwError (← noCandidateMessage coordinate integrand hint)
        let candidate := candidate.simplify.mapVars (fun j ↦ .var j.val)
        certifyCandidate coordinate integrand
          (← KernelReadBack.quoteNatExpression variableType candidate)
      else
        throwError "cas received an out-of-range integration coordinate"

/--
Certify a user-supplied primitive against its own symbolic derivative.

This route checks the derivative residual exactly; reflection and displayed
derivative syntax are not trusted.
-/
def certifyPrimitive
    (coordinate candidate : Expr) : TacticM Expr := do
  let integrand ← mkAppM ``Verified.Expr.diff #[coordinate, candidate]
  let query ←
    mkAppM ``IntegrationCheck.certifyCandidate?
      #[coordinate, integrand, candidate]
  certificateFromOptionCore query
    "cas could not certify the supplied primitive"

end CAS.Tactic.Integration.Planning

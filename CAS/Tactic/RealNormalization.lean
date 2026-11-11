/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Tactic.DerivativeBridge
public meta import CAS.Tactic.DerivativeBridge
public import CAS.Tactic.Normalization
public meta import CAS.Tactic.Normalization

/-!
# Checked normalization of ordinary real expressions

The normalizer behind `cas_nf` and its `conv` form on ordinary real terms. Purely polynomial
real terms use Mathlib's proof-producing `ring_nf` normalizer. Other ordinary real terms are
reflected over a finite table of opaque atoms. The checked simplification route computes a
replacement and its domain conditions; its denotational certificate and the reflection bridges
justify replacing the term inside an arbitrary context.

## Main definitions

* `normalize`: a checked replacement of a term, with an equality proof that has no pending
  domain obligations.
* `normalizeAtLocation`: the replacement in the selected target and hypotheses.
* `normalizeConv`: the replacement of the focused expression of a conversion.

## Implementation notes

We traverse the term once with `Simp.main`. Evaluations `Verified.Expr.eval ρ e` go to the
reflected normalizer of `CAS/Tactic/Normalization.lean`; polynomial syntax (literal natural
powers, division only by closed rational constants) goes to `RingNF.evalExpr?` and
`RingNF.cleanup`; other real subterms are normalized after their arguments. Analytic branches are
resolved first, by a small set of sign-sensitive simp lemmas (`Real.exp_log`, `Real.sq_sqrt`,
`abs_of_nonneg` and their relatives) whose conditions `DerivativeBridge.closeValidity` proves
from the context or the `using` evidence.

The algebraic step reflects the term over its atoms, keeping absolute values as atoms, and the
kernel evaluates `Verified.Expr.simplifyFinSideClaimRoute`: `sideConditionPipeline`, then the
rational canonical form of `CAS/ClosedForm/RationalCanonical.lean` for one atom or the
multivariate one of `CAS/ClosedForm/Canonical.lean` for several. We read the normal form and its
conditions back with `KernelReadBack.readBackPair`, and three kernel decisions
(`KernelReadBack.decideByKernel`) tie the route's source, target and conditions to the quoted
terms. The equality is `Verified.Expr.SideClaimRoute.sound`, with the conditions proved by
`DerivativeBridge.closeValidity` and both reflections identified with ordinary terms by
`DerivativeBridge.bridgeReflection`. The closed proof is checked once by `Lean.Kernel.check`,
since a recheck in the elaborator would unfold the whole normalizer at an abstract index type.
Mathlib's `ring_nf` proves the polynomial parts; the rest rests on our checked pipeline.
-/

public meta section

namespace CAS.Tactic.RealNormalization

open Lean Elab Tactic Meta
open Mathlib.Tactic

private def proveCondition?
    (proposition : Expr) (side? : Option (TSyntax `term)) : MetaM (Option Expr) := do
  let saved ← saveState
  try
    let proof ← mkFreshExprSyntheticOpaqueMVar proposition
    DerivativeBridge.closeValidity "cas_nf" proof.mvarId! side?
    return some (← instantiateMVars proof)
  catch error =>
    saved.restore
    if error.isRuntime then throw error
    return none

private def cleanup (e : Expr) (side? : Option (TSyntax `term)) : MetaM Simp.Result := do
  let names := #[``Nat.cast_ofNat, ``Nat.cast_zero, ``Nat.cast_one, ``Int.cast_ofNat,
    ``Int.cast_zero, ``Int.cast_one, ``Int.cast_neg, ``Int.cast_negSucc, ``Int.cast_natCast,
    ``Real.exp_log, ``Real.exp_log_eq_abs, ``Real.log_zero, ``Real.exp_zero,
    ``Real.sqrt_sq_eq_abs, ``Real.sq_sqrt, ``Real.sqrt_eq_zero_of_nonpos,
    ``abs_of_nonneg, ``abs_of_nonpos, ``abs_of_pos, ``abs_of_neg,
    ``abs_zero, ``zero_div, ``div_zero]
  let mut theorems : SimpTheorems := {}
  for name in names do
    theorems ← theorems.addConst name
  let context ← Simp.mkContext { zetaDelta := false }
    (simpTheorems := #[theorems]) (congrTheorems := ← getSimpCongrTheorems)
  let discharge? : Expr → SimpM (Option Expr) := fun proposition ↦ do
    proveCondition? proposition side?
  let pre : Simp.Simproc := fun term ↦ do
    if term.getAppFn.isConstOf ``Verified.Expr.eval then
      return .done { expr := term }
    return .continue
  let post := Simp.postDefault #[]
  return (← Simp.main e context
    (methods := { pre, post, discharge?, wellBehavedDischarge := false })).1

private def normalizeAlgebra
    (e : Expr) (side? : Option (TSyntax `term)) : MetaM Simp.Result := do
  -- Keep absolute values as atoms after the sign-sensitive rewrites. Reflecting them as
  -- square roots would turn a valid nonzero branch back into a positivity obligation.
  let config : CAS.Elaboration.RealExpression.Config := {
    operation := "cas_nf"
    opaque? := fun term ↦ pure (RealExpression.isAtomHead term || term.isAppOf ``abs)
    exponentAllowed := fun _ ↦ pure true
    symbolicExponentsAsRealPowers := true
    unfoldLimit := RealExpression.localUnfoldLimit
  }
  let reification ← CAS.Elaboration.RealExpression.reify config e
  let atoms := reification.coordinates
  let index := mkApp (mkConst ``Fin) (mkNatLit atoms.size)
  let reflected ← reification.quoteWith index (RealExpression.finLiteral · atoms.size)
  if reflected.getAppFn.isConstOf ``Verified.Expr.var then
    return { expr := e }
  let environment ← RealExpression.parameterVector atoms
  let route ← mkAppM ``Verified.Expr.simplifyFinSideClaimRoute #[reflected]
  let lhs ← mkAppM ``Verified.Expr.SideClaimRoute.lhs #[route]
  let rhs ← mkAppM ``Verified.Expr.SideClaimRoute.rhs #[route]
  let nonzero ← mkAppM ``Verified.Expr.SideClaimRoute.nonzero #[route]
  let (normal, conditions) ← KernelReadBack.readBackPair index rhs nonzero
  let output ← DerivativeBridge.lowerEmbedded "cas_nf" atoms #[] normal
  if Lean.Kernel.isDefEqGuarded (← getEnv) (← getLCtx) e output then
    return { expr := e }
  let quoted ← KernelReadBack.quoteNatExpression index normal
  let side ← KernelReadBack.quoteNatList index conditions
  let hright ← KernelReadBack.decideByKernel "cas_nf" (← mkEq rhs quoted)
  let hleft ← KernelReadBack.decideByKernel "cas_nf" (← mkEq lhs reflected)
  let hconditions ← KernelReadBack.decideByKernel "cas_nf" (← mkEq nonzero side)
  let sideProof ← mkFreshExprSyntheticOpaqueMVar
    (← mkAppM ``Verified.Expr.Alg.SideHolds #[environment, side])
  DerivativeBridge.closeValidity "cas_nf" sideProof.mvarId! side?
  let sideFunction ← withLocalDeclD `ds (← inferType side) fun ds ↦ do
    mkLambdaFVars #[ds] (← mkAppM ``Verified.Expr.Alg.SideHolds #[environment, ds])
  let originalSide ← mkEqMPR (← mkCongrArg sideFunction hconditions)
    (← instantiateMVars sideProof)
  let sound ← mkAppM ``Verified.Expr.SideClaimRoute.sound #[route, environment]
  let sound := mkApp sound originalSide
  let evaluator ← withLocalDeclD `t (← inferType reflected) fun t ↦ do
    mkLambdaFVars #[t] (← mkAppM ``Verified.Expr.eval #[environment, t])
  let evaluated ← mkEqTrans (← mkEqSymm (← mkCongrArg evaluator hright)) sound
  let evaluated ← mkEqTrans evaluated (← mkCongrArg evaluator hleft)
  let inputBridge ← DerivativeBridge.bridgeReflection "cas_nf" environment reflected e
  let outputBridge ← DerivativeBridge.bridgeReflection "cas_nf" environment quoted output
  let proof ← mkEqTrans (← mkEqSymm inputBridge) (← mkEqSymm evaluated)
  let proof ← mkEqTrans proof outputBridge
  return { expr := output, proof? := some proof }

private def normalizeReal
    (e : Expr) (side? : Option (TSyntax `term)) : MetaM (Option Simp.Result) := do
  unless (← whnfD (← inferType e)).isConstOf ``Real do
    return none
  if e.getAppFn.isConstOf ``Verified.Expr.eval then
    return none
  let cleaned ← cleanup e side?
  let algebra ← normalizeAlgebra cleaned.expr side?
  let lowered ← cleanup algebra.expr side?
  let result ← cleaned.mkEqTrans (← algebra.mkEqTrans lowered)
  if Lean.Kernel.isDefEqGuarded (← getEnv) (← getLCtx) e result.expr then
    return none
  return some result

/-- Rational expressions over local variables have no opaque function arguments to visit.
Normalize each maximal such expression once, rather than certifying every arithmetic node. -/
private partial def isRationalExpression (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  if e.isFVar then
    return true
  if e.isAppOfArity ``OfNat.ofNat 3 then
    return true
  let args := e.getAppArgs
  let head := e.getAppFn
  if #[``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv].any head.isConstOf then
    if args.size < 2 then return false
    return (← isRationalExpression args[args.size - 2]!) &&
      (← isRationalExpression args[args.size - 1]!)
  if #[``Neg.neg, ``Inv.inv].any head.isConstOf then
    if args.isEmpty then return false
    return ← isRationalExpression args.back!
  if head.isConstOf ``HPow.hPow && args.size ≥ 2 then
    if (← getNatValue? args.back!).isNone then return false
    return ← isRationalExpression args[args.size - 2]!
  return false

/-- Polynomial syntax over real variables, with literal natural powers and rational
coefficients. Variable denominators and analytic functions retain the symbolic route. -/
private partial def isPolynomialExpression (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  if e.isFVar || e.isAppOfArity ``OfNat.ofNat 3 then return true
  let args := e.getAppArgs
  let head := e.getAppFn
  if #[``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul].any head.isConstOf then
    if args.size < 2 then return false
    return (← isPolynomialExpression args[args.size - 2]!) &&
      (← isPolynomialExpression args.back!)
  if head.isConstOf ``Neg.neg && !args.isEmpty then
    return ← isPolynomialExpression args.back!
  if head.isConstOf ``HPow.hPow && args.size ≥ 2 then
    if (← getNatValue? args.back!).isNone then return false
    return ← isPolynomialExpression args[args.size - 2]!
  if head.isConstOf ``HDiv.hDiv && args.size ≥ 2 then
    let denominator := args.back!
    return !denominator.hasFVar && !denominator.hasMVar &&
      (← isRationalExpression denominator) &&
      (← isPolynomialExpression args[args.size - 2]!)
  return false

private def normalizePolynomial (atoms : IO.Ref AtomM.State) (e : Expr) :
    MetaM Simp.Result := do
  let result? ← RingNF.evalExpr? e { red := .reducible } atoms
  let result ← RingNF.cleanup {} (result?.getD { expr := e })
  if Lean.Kernel.isDefEqGuarded (← getEnv) (← getLCtx) e result.expr then
    return { expr := e }
  return result

private def normalizeCore (reflected : Expr → MetaM (Option Simp.Result))
    (atoms : IO.Ref AtomM.State) (e : Expr) (side? : Option (TSyntax `term)) :
    MetaM Simp.Result := do
  let context ← Simp.mkContext
    { zetaDelta := false, singlePass := true }
    (simpTheorems := #[← Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) {}])
    (congrTheorems := ← getSimpCongrTheorems)
  let pre : Simp.Simproc := fun term ↦ do
    if term.getAppFn.isConstOf ``Verified.Expr.eval then
      return .done ((← reflected term).getD { expr := term })
    if (← whnfD (← inferType term)).isConstOf ``Real &&
        (← isPolynomialExpression term) then
      return .done (← normalizePolynomial atoms term)
    if (← whnfD (← inferType term)).isConstOf ``Real &&
        (← isRationalExpression term) then
      return .done ((← normalizeReal term side?).getD { expr := term })
    -- Resolve analytic branches before normalizing their arguments. The congruence traversal
    -- still visits every argument of an opaque atom before the algebraic pass at its parent.
    if (← whnfD (← inferType term)).isConstOf ``Real then
      return .continue (some (← cleanup term side?))
    return .continue
  let post : Simp.Simproc := fun term ↦ do
    match ← normalizeReal term side? with
    | some result => return .done result
    | none => Simp.postDefault #[] term
  return (← Simp.main e context (methods := { pre, post, wellBehavedDischarge := false })).1

private def normalizeWithAtoms (atoms : IO.Ref AtomM.State)
    (e : Expr) (side? : Option (TSyntax `term)) : MetaM Simp.Result := do
  let action : TacticM Simp.Result := do
    let result ← Normalization.withNormalizer side? fun reflected ↦
      normalizeCore reflected atoms e side?
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars (← result.getProof)
    let closed ← mkLambdaFVars (← getLCtx).getFVars proof (usedOnly := true)
    let closed ← instantiateMVars closed
    if closed.hasMVar ∨ closed.hasSorry then
      throwError "cas_nf constructed incomplete normalization evidence"
    ProofCarrier.rejectIncompleteDependencies "cas_nf" closed
    -- Generic reflected computation equalities are certified by kernel reduction. Rechecking
    -- them in the elaborator would unfold the entire normalizer at an abstract index type.
    -- Abstracting the used locals also instantiates their types, as needed under conv binders.
    match Lean.Kernel.check (← getEnv) {} closed with
    | .ok _ => pure ()
    | .error error =>
      throwError "cas_nf constructed invalid evidence: {error.toMessageData (← getOptions)}"
    return { result with proof? := some proof }
  Term.TermElabM.run' (ctx := { errToSorry := false }) <|
    (action { elaborator := `cas_nf, recover := false }).run' { goals := [] }

/-- Compute a checked replacement inside an ordinary context, retaining reflected evaluators
and their index types. The returned equality has no pending domain obligations or proof holes.
Pure polynomials use Mathlib's normalizer. Opaque functions remain atoms for symbolic algebra,
while congruence normalizes their arguments. -/
def normalize (e : Expr) (side? : Option (TSyntax `term)) : MetaM Simp.Result := do
  normalizeWithAtoms (← IO.mkRef {}) e side?

/-- Normalize ordinary real subterms in the selected target and hypotheses. -/
def normalizeAtLocation (side? : Option (TSyntax `term)) (loc : Location) : TacticM Unit := do
  ProofCarrier.preservingStateOnFailure do
    let atoms ← IO.mkRef {}
    let errors ← IO.mkRef (#[] : Array Exception)
    let transform (term : Expr) : MetaM Simp.Result := do
      try
        normalizeWithAtoms atoms term side?
      catch error =>
        errors.modify (·.push error)
        throw error
    -- Wildcard locations skip unchanged hypotheses. They must not swallow a failed domain
    -- proof or checked computation after another location has already changed.
    try
      transformAtLocation (transform ·) "cas_nf" loc
    catch error =>
      throw ((← errors.get)[0]?.getD error)
    if let some error := (← errors.get)[0]? then
      throw error

/-- Normalize the focused ordinary expression in a conversion. -/
def normalizeConv (side? : Option (TSyntax `term)) : TacticM Unit := withMainContext do
  ProofCarrier.preservingStateOnFailure do
    let source ← instantiateMVars (← Conv.getLhs)
    let result ← normalize source side?
    if source.cleanupAnnotations == result.expr.cleanupAnnotations then
      throwError "cas_nf made no progress on the focused expression"
    Conv.applySimpResult result

end CAS.Tactic.RealNormalization

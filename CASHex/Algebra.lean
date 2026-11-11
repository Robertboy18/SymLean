/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
public meta import CAS
public import HexBerlekampTheory
public meta import HexBerlekampTheory
public import HexBerlekampZassenhausTheory
public meta import HexBerlekampZassenhausTheory
public import HexBareissTheory
public meta import HexBareissTheory
public import HexPrimalityTheory
public meta import HexPrimalityTheory

/-!
# Exact algebra through Hex in bare `cas`

Built only with `lake -R -Khex=on build CASHex`, `CASHex.Algebra` gives bare `cas` three tactics
of Hex, registered as the route `hex` of `cas` (`hexRoute`, `@[cas_route hex]` in
`CAS.Tactic.RouteRegistry`):

* `Irreducible p` for a polynomial `p` over `ℤ` or `ZMod n` with literal coefficients goes to
  Hex's `irreducibility!`;
* `Matrix.det A = d` or `d = Matrix.det A` for an integer or rational matrix literal `A` goes to
  Hex's `det`, instead of Mathlib's `norm_det`;
* `Nat.Prime n` for a numeral `n` goes to Hex's `primality`.

`cas?` reports the route and suggests `cas`. No module of `CAS` imports this one, so no proof of
the library changes. The other modules of `CASHex` serve the `#cas` commands that call Hex:
`CASHex.Factor` (the backend of `factor` and the factorizer over `ℚ` of `apart`, `product`,
`inverseLaplace`, `eigenvalues`, `eigenvectors`, `rsolve` and rational integration),
`CASHex.LinearAlgebra` (`det`) and `CASHex.NumberTheory` (`factorInteger` and the calls
`primeQ`, `moebiusMu` and `eulerPhi`); `CASHex.Examples` exercises all four.

## Main definitions

* `hexRoute`: the route `hex` of `cas`, offered the goals of `isHexGoal`.
* `closeWithHex`: runs a Hex tactic on a copy of the goal and closes the goal with the theorem
  that the kernel checked.
* `cas.hexHeartbeats`: the heartbeat budget of Hex's search; `0` turns the route off.

## Implementation notes

The searches and the certificates are Hex's. Its `irreducibility!` finds an irreducibility
certificate in compiled code and has the kernel check it: a Rabin certificate over `ZMod p`
(`HexBerlekampTheory`), and over `ℤ` (`HexBerlekampZassenhausTheory`) a single-prime or
Eisenstein-after-shift witness or a multi-prime degree-obstruction certificate. For an input
outside those languages, such as the Swinnerton-Dyer polynomial `X ^ 4 - 10 * X ^ 2 + 1`, it
replays Hex's factorizer in the kernel, which Hex allows up to degree 12 only. In a `module` that
replay needs `import all` of Hex's executable modules, which Hex does not expose, so there the
goal is refused. Hex's `det` (`HexBareissTheory`) checks a certificate of the fraction-free
(Bareiss) elimination of the matrix in the kernel, and `primality` (`HexPrimalityTheory`) builds a
Pocklington certificate whose check the kernel replays.

What we add is the routing and the checks around it. The route is offered its goals before the
built-in stages of `cas` (`CAS.ExactTactic.routeOrder` lists the order). When Hex fails with an
ordinary error, the other routes of `cas` run as before; a declaration-wide heartbeat timeout ends
the tactic instead. `closeWithHex` takes only goals without local variables, forces kernel
checking on for the whole run, and checks the proof as an auxiliary theorem in the kernel. It runs
as a kernel-only route (`ProofCarrier.withKernelOnlyAxioms`): the proofs of Hex's released
libraries use no axiom beyond Lean's three standard ones and no native evaluation, and the route
checks that.

## References

* The Lean FRO and the Hex contributors, *hex: Verified computational algebra in Lean 4*,
  release v0.10.0, 2026, <https://github.com/leanprover/hex/tree/v0.10.0>. We call the tactics
  `irreducibility!` of HexBerlekampZassenhausTheory (with HexBerlekampTheory over `ZMod p`),
  `det` of HexBareissTheory and `primality` of HexPrimalityTheory.
* Benjamin Grégoire, Laurent Théry and Benjamin Werner, "A Computational Approach to Pocklington
  Certificates in Type Theory", in *Functional and Logic Programming (FLOPS 2006)*, Lecture Notes
  in Computer Science 3945, Springer, 2006, pp. 97-113, <https://doi.org/10.1007/11737414_8>.
  Section 2 for the recursive Pocklington certificates that `primality` builds; Hex's primality
  specification cites this paper.
* Erwin H. Bareiss, "Sylvester's Identity and Multistep Integer-Preserving Gaussian Elimination",
  *Mathematics of Computation* 22 (1968), pp. 565-578,
  <https://doi.org/10.1090/S0025-5718-1968-0226829-0>.
  The one-step integer-preserving elimination of Section I, Eq. (8), is the fraction-free
  elimination behind the certificate of `det`.
-/

public meta section

namespace CASHex.Algebra

open Lean Elab Tactic Meta
open CAS CAS.Tactic

register_option cas.hexHeartbeats : Nat := {
  defValue := 20000
  descr := "heartbeat budget (in thousands) of the Hex route of cas; 0 turns the route off"
}

/-- Whether `type` is `Polynomial ℤ` or `Polynomial (ZMod n)`. -/
def isSupportedPolynomialType (type : Expr) : MetaM Bool := do
  let type ← whnfR type
  unless type.isAppOfArity ``Polynomial 2 do
    return false
  let ring ← whnfR type.appFn!.appArg!
  return ring.isConstOf ``Int || ring.isAppOfArity ``ZMod 1

/-- Whether `target` is `Irreducible p` for a polynomial `p` over `ℤ` or `ZMod n`. -/
def isIrreducibleGoal (target : Expr) : MetaM Bool := do
  let target := target.consumeMData
  unless target.isAppOfArity ``Irreducible 3 do
    return false
  isSupportedPolynomialType (← inferType target.appArg!)

/-- Whether `target` is `Matrix.det A = d` or `d = Matrix.det A` over `ℤ` or `ℚ`, with `A` a
matrix literal and no determinant of a matrix literal in `d`: the shape Hex's `det` closes. -/
def isDeterminantGoal (target : Expr) : Bool :=
  match target.consumeMData.eq? with
  | some (type, lhs, rhs) =>
      (type.isConstOf ``Int || type.isConstOf ``Rat) &&
        ((lhs.consumeMData.isAppOf ``Matrix.det && Determinant.hasLiteralDeterminant lhs &&
            !Determinant.hasLiteralDeterminant rhs) ||
          (rhs.consumeMData.isAppOf ``Matrix.det && Determinant.hasLiteralDeterminant rhs &&
            !Determinant.hasLiteralDeterminant lhs))
  | none => false

/-- Run the Hex tactic `tactic` on a copy of the main goal, which must have no local variables;
check its proof synchronously as an auxiliary theorem in the kernel
(`ProofCarrier.cacheClosedProof`) and close the main goal with that theorem, as a kernel-only
route. Hex's certificates are Boolean checks that the kernel evaluates; the elaborator's check of
the goal would evaluate them in `whnf` instead, which costs far more and, in a `module`, cannot
unfold the definitions Hex does not expose.

The whole run has kernel checking forced on (`debug.skipKernelTC` false), since Hex adds
auxiliary theorems of its own, and the recursion limit of the determinant route, for Hex's deep
certificate terms. Hex's search runs under the budget `cas.hexHeartbeats`, given both to the
elaborator and, as the `maxHeartbeats` option, to Hex's own kernel checks; the final kernel check
gets what the declaration has left. Hex's `Kernel.whnf` prechecks
cannot be interrupted and are charged when they return. -/
def closeWithHex (description : String) (budget : Nat) (tactic : TSyntax `tactic) :
    TacticM Unit := do
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  if target.hasFVar || target.hasMVar then
    throwError "{description} needs a goal without local variables"
  let depth := max (maxRecDepth.get (← getOptions)) Determinant.recursionDepth
  withOptions (fun options ↦ maxRecDepth.set (debug.skipKernelTC.set options false) depth) <|
    discard <| ProofCarrier.runClosingMainGoal description do
      ProofCarrier.withKernelOnlyAxioms description do
        let copy ← mkFreshExprSyntheticOpaqueMVar target
        let remaining ← Fallback.withHeartbeatBudget description budget
            (option := `cas.hexHeartbeats) do
          withOptions (fun options ↦ maxHeartbeats.set options budget) do
            evalTacticAt tactic copy.mvarId!
        unless remaining.isEmpty do
          throwError "{description} left goals"
        let theoremConstant ← ProofCarrier.cacheClosedProof description (← instantiateMVars copy)
        (← getMainGoal).assign theoremConstant
        replaceMainGoal []
        return ((), #[])

/-- Whether `target` is `Nat.Prime n`. -/
def isPrimalityGoal (target : Expr) : Bool :=
  target.consumeMData.isAppOfArity ``Nat.Prime 1

/-- The goals of the route `hex`: `Irreducible p` over `ℤ` or `ZMod n`, `Matrix.det A = d` over
`ℤ` or `ℚ` for a matrix literal `A`, and `Nat.Prime n`, while `cas.hexHeartbeats` is positive. -/
def isHexGoal : RouteRegistry.GoalPredicate := fun target ↦ do
  if cas.hexHeartbeats.get (← getOptions) == 0 then
    return false
  return (← isIrreducibleGoal target) || isDeterminantGoal target || isPrimalityGoal target

/-- The route `hex` of `cas`: Hex's `irreducibility!` on `Irreducible p`, `det` on a determinant
of a matrix literal and `primality` on `Nat.Prime n`, each through `closeWithHex`. -/
@[cas_route hex (priority := high) (goal := isHexGoal)]
def hexRoute : RouteRegistry.Closer := fun _ ↦ do
  let budget := cas.hexHeartbeats.get (← getOptions)
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  let (certificate, tactic) ← if ← withMainContext (isIrreducibleGoal target) then
      -- `irreducibility!` searches Hex's certificates first; for an input outside their languages
      -- (such as the Swinnerton-Dyer polynomials) it replays Hex's factorizer in the kernel.
      pure ("irreducibility", ← `(tactic| irreducibility!))
    else if isDeterminantGoal target then
      pure ("det", ← `(tactic| det))
    else
      -- Hex's `primality` (`HexPrimalityTheory`): a Pocklington certificate replayed in the kernel.
      pure ("primality", ← `(tactic| first
        | primality
        | (simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul]; primality)))
  closeWithHex s!"cas through Hex {certificate}" budget tactic
  return {
    replay := ← `(tactic| cas)
    plannerMetadata := #[{
      label := s!"Hex {certificate} certificate, checked by the kernel"
      status := .selected
    }]
  }

end CASHex.Algebra

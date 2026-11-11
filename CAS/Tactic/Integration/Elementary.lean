/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import CAS.Tactic.ProofCarrier
public meta import CAS.Tactic.ProofCarrier

/-!
# Direct exact interval integrals

`close` evaluates an interval-integral equality by Mathlib's closed formulas (`integral_pow`,
`integral_rpow`, `integral_exp`, `integral_sin`, `integral_cos`, the integral of a constant and
the rules for constant factors), retaining every integrability or exponent restriction of the
theorem it applies. These formulas cover symbolic natural powers and integrable endpoint
singularities, and they do not require a primitive differentiable at the endpoints.

## Implementation notes

`cas` tries this route before antiderivative search because the certificate theorem
`IntegrationCheck.AntiderivativeCert.intervalIntegral_eq_sub_eval_add_smul_single` needs the
primitive's domain requirements on all of `Set.uIcc a b`: `x ^ r` with `-1 < r < 0` on an
interval containing zero is out of its reach, while `integral_rpow` asks only for `-1 < r`. One
`simp only` call rewrites with the formulas and discharges their side conditions by assumption,
`norm_num`, the left or right disjunct, or `linarith`; `norm_num only [Real.zero_rpow]` and
`ring1` close the arithmetic that remains.
-/

public meta section

namespace CAS.Tactic.Integration.Elementary

open Lean Meta Elab Tactic

/-- Close a supported elementary interval-integral equality by Mathlib formulas.

The natural-power formula permits symbolic exponents. The real-power formula requires
`-1 < r`, or `r ≠ -1` and an interval avoiding zero. Arbitrary singular integrands are
outside this route. Supplied evidence must be a complete proof even when it is redundant.
-/
def close (evidence? : Option (TSyntax `term) := none) : TacticM Unit :=
  ProofCarrier.preservingStateOnFailure do
    -- Record the caller's goal before preprocessing and isolate it from sibling goals.
    discard <| ProofCarrier.runClosingMainGoal "elementary interval integration" <|
      focus <| withMainContext do
      let target ← zetaReduce (← instantiateMVars (← getMainTarget))
      unless target.eq?.isSome && target.getUsedConstants.contains ``intervalIntegral do
        throwError "elementary integration expects an interval-integral equality"
      let goal ← getMainGoal
      let goal ← goal.change target
      replaceMainGoal [goal]
      if let some evidence := evidence? then
        let proof ← Term.withoutErrToSorry <| Term.elabTerm evidence none
        let proof ← ProofCarrier.checkCompletedProof "integration side evidence" proof
        unless ← isProp (← inferType proof) do
          throwError "integration requires a proof as side evidence"
        let (_, goal) ← goal.note (← mkFreshUserName `hcasIntegral) proof
        replaceMainGoal [goal]
      evalTactic (← `(tactic|
        simp (disch := (solve
          | assumption
          | norm_num
          | (left; solve | assumption | norm_num | linarith)
          | (right; solve | assumption | (constructor <;> assumption))
          | linarith)) only
          [intervalIntegral.integral_same, intervalIntegral.integral_const,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
            integral_pow, integral_rpow, integral_exp, integral_sin, integral_cos,
            Real.zero_rpow, Real.one_rpow, smul_eq_mul]))
      unless (← getGoals).isEmpty do
        -- Preserve the equality shape; unrestricted simplification can replace
        -- cancellation by a disjunction about a scalar multiplier.
        evalTactic (← `(tactic| norm_num only [Real.zero_rpow]))
      unless (← getGoals).isEmpty do
        evalTactic (← `(tactic| ring1))

end CAS.Tactic.Integration.Elementary

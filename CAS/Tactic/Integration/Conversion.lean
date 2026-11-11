/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public meta import Lean.Meta.Tactic.Unfold
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.Positivity
public import CAS.Expr.Syntax

/-!
# Conversion from checked expressions to ordinary real syntax

`close` proves the user's goal from an analytic certificate theorem about checked expressions
along a coordinate line. Only definitional reduction, checked-expression evaluation equations,
simplification and ring normalization take part in the conversion, so a primitive or value
that differs from the stated one fails, with the first conversion goal that remains.

## Implementation notes

We unfold the caller's local definitions that reflection unfolded, then match the theorem
against the goal with Mathlib's `Lean.MVarId.convert` at depth one under a cheap configuration.
Integrands are aligned pointwise first (`intervalIntegral.integral_congr`). Then `simp` with the
evaluation equations of `Verified.Expr.eval` and `Verified.Expr.diff` and the rewrites of the
tangent, the hyperbolic functions, the arccosine, `Real.sqrt_sq_eq_abs` and `Real.cos_sq'`
brings both sides to ordinary syntax, and `ring_nf` normalizes them. What remains goes to
`field_simp`, whose side conditions are discharged by assumption, `positivity` or `nlinarith`,
followed by `ring`, to `simp` with a Pythagorean identity and `ring`, or to `ring` after the
logarithm of a negative number is written as that of its absolute value (`Real.log_neg_eq_log`),
as the value of a primitive with `log |x|` at negative points has it. The failure message points
to `#cas [integrate x]`, which shows the computed primitive.
-/

public meta section

namespace CAS.Tactic.Integration.Conversion

open Lean Elab Tactic Meta

/--
Close the current goal by converting a checked coordinate-line theorem to the
user's ordinary real syntax.
-/
def close (proof : Expr) (localDefinitions : Array Name) : TacticM Unit := do
  let mut goal ← getMainGoal
  for name in localDefinitions do
    goal ← Meta.unfoldTarget goal name
  replaceMainGoal [goal]
  let remainingGoals := (← getGoals).drop 1
  let convertConfig := ({} : Convert.CheapConfig).toConfig
  let conversionGoals ←
    (← getMainGoal).convert proof false (some 1) convertConfig
  setGoals conversionGoals
  try
    -- Align integrands before simp, which need not unfold aliases of the measure.
    withSuppressedMessages <| evalTactic (← `(tactic|
      all_goals
        try
          apply intervalIntegral.integral_congr
          intro t ht
        first
          | rfl
          | (funext t
             simp [Verified.Expr.eval, Verified.Expr.diff,
               PiLp.single_apply, Real.tan_eq_sin_div_cos,
               Real.sinh_eq, Real.cosh_eq, Real.tanh_eq,
               Real.arccos_eq_pi_div_two_sub_arcsin,
               Real.sqrt_sq_eq_abs,
               Real.cos_sq'] <;>
             ring_nf)
          | (simp [Verified.Expr.eval, Verified.Expr.diff,
               PiLp.single_apply, Real.tan_eq_sin_div_cos,
               Real.sinh_eq, Real.cosh_eq, Real.tanh_eq,
               Real.arccos_eq_pi_div_two_sub_arcsin,
               Real.sqrt_sq_eq_abs,
               Real.cos_sq'] <;>
             ring_nf)))
  catch _ => pure ()
  try
    withSuppressedMessages <| evalTactic (← `(tactic|
      all_goals
        solve
          | (field_simp
              (disch := first
                | assumption
                | positivity
                | nlinarith [sq_pos_of_ne_zero (by assumption)]) <;>
              ring)
          | (simp [Real.cos_sq'] <;> ring)
          | (simp [Real.sin_sq] <;> ring)
          | (simp only [neg_div, Real.log_neg_eq_log, one_div, Real.log_inv] <;> ring)))
  catch _ => pure ()
  let unresolved ← getGoals
  unless unresolved.isEmpty do
    let firstTarget ← instantiateMVars (← unresolved[0]!.getType)
    throwError
      "cas found a checked antiderivative, but it does not match the \
       stated primitive or integral value. Run `#cas [integrate x] expression` \
       with the intended integration variable to inspect the computed primitive, \
       then compare it with the function or endpoint difference in this goal.\n\
       First remaining conversion goal:{indentExpr firstTarget}"
  setGoals remainingGoals

end CAS.Tactic.Integration.Conversion

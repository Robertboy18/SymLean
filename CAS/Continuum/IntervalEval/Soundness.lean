/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Core

/-!
# Soundness of rational interval evaluation

The inclusion property of the three rational interval evaluators of `Core`: if every variable
`ρ i` lies in `env i` and the evaluator returns `I`, then `expr.eval ρ ∈ I`. For
`evalPolynomial_sound` this needs nothing more. For `evalWithLookups_sound`, which also applies
to `evalRational`, the denominator lower bounds returned by the lookup must hold at `ρ`,
and each unary range must contain the image of its whole argument interval.
`rationalCallbacks_sound` checks that the rational division and unary callbacks then meet the
contract of `IntervalExprCallbacks.Sound`. Certificates valid on a whole domain are assembled
from these by `CertifiedEvalContext`.

## Implementation notes

The two evaluator theorems instantiate the generic inductions `IntervalExprBackend.eval_sound`
and `IntervalExprCallbacks.evalWithCallbacks_sound`. The case analysis is in
`rationalCallbacks_sound`: it follows the three division branches of `rationalCallbacks` (a
reciprocal range, the interval's own bound on `|b|`, a provider bound `δ ≤ |b|`), and it rewrites
a real power on a positive base by `Real.rpow_def_of_pos`, so the exponential range is applied
to the interval the evaluator computes for `log a * b`.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Verified

/-- Successful polynomial interval evaluation encloses the corresponding real evaluation whenever
each variable lies in its assigned interval. -/
theorem evalPolynomial_sound {ι : Type*}
    (env : ι → RationalInterval) (ρ : ι → ℝ)
    (henv : ∀ i, (env i).MemReal (ρ i)) :
    ∀ expr I, evalPolynomial env expr = some I → I.MemReal (expr.eval ρ)
  | expr, I, h =>
      IntervalExprBackend.eval_sound intervalExprBackend_verifiedExprOps env ρ henv expr I h

/-- The rational division and unary providers satisfy the shared callback contract. -/
theorem rationalCallbacks_sound {ι : Type*}
    (env : ι → RationalInterval) (divLower : Verified.Expr ι → Option AbsLowerResult)
    (unaryRange : UnaryKind → Verified.Expr ι → RationalInterval → Option RationalInterval)
    (ρ : ι → ℝ)
    (henv : ∀ i, (env i).MemReal (ρ i))
    (hdiv : ∀ den cert, divLower den = some cert →
      (cert.delta : ℝ) ≤ |den.eval ρ|)
    (hunary : ∀ op arg IA result,
      evalWithLookups env divLower unaryRange arg = some IA →
      unaryRange op arg IA = some result →
      ∀ z, IA.MemReal z → result.MemReal (op.apply z)) :
    IntervalExprCallbacks.Sound
      (ops := verifiedExprOps)
      (callbacks := rationalCallbacks divLower unaryRange)
      (env := env) (ρ := ρ) := by
  refine {
    vars := henv
    div := ?_
    unary := ?_
    rpow := ?_
  }
  · intro a b IA IB result hA hB hcallback ha hb
    by_cases hdom : IB.hi < 0 ∨ 0 < IB.lo
    · cases hinv : unaryRange .inv b IB with
      | some invCert =>
          simp [rationalCallbacks, hdom, hinv] at hcallback
          subst result
          simpa [UnaryKind.apply, div_eq_mul_inv] using
            mul_sound ha (hunary .inv b IB invCert hB hinv (b.eval ρ) hb)
      | none =>
          by_cases hneg : IB.hi < 0
          · simp only [rationalCallbacks, hinv, hneg] at hcallback
            obtain rfl := Option.some.inj hcallback
            exact divByAbsLower_sound
              (by simpa [negativeAbsLower] using neg_pos.mpr hneg)
              ha (negativeAbsLower_sound hneg hb)
          · have hpos : 0 < IB.lo := hdom.resolve_left hneg
            simp only [rationalCallbacks, hinv, hneg, hpos] at hcallback
            obtain rfl := Option.some.inj hcallback
            exact divByAbsLower_sound
              (by simpa [positiveAbsLower] using hpos)
              ha (positiveAbsLower_sound hpos hb)
    · cases hcert : divLower b with
      | none => simp [rationalCallbacks, hdom, hcert] at hcallback
      | some cert =>
          simp only [rationalCallbacks, hdom, hcert] at hcallback
          obtain rfl := Option.some.inj hcallback
          exact divByAbsLower_sound cert.pos ha (hdiv b cert hcert)
  · intro op arg IA result hArg hcallback hmem
    have hcallback' : unaryRange op arg IA = some result := by
      cases op <;> exact hcallback
    exact hunary op arg IA result hArg hcallback' (arg.eval ρ) hmem
  · intro a b IA IB result hA hB hcallback ha hb
    by_cases hpos : 0 < IA.lo
    · cases hlog : unaryRange .log a IA with
      | none => simp [rationalCallbacks, hpos, hlog] at hcallback
      | some logInterval =>
          simp only [rationalCallbacks, hpos, hlog, ↓reduceIte] at hcallback
          have hlogEval :
              evalWithLookups env divLower unaryRange (.log a) = some logInterval := by
            unfold evalWithLookups
            rw [IntervalExprOps.evalWithCallbacks, hA]
            exact hlog
          have hArgEval :
              evalWithLookups env divLower unaryRange (.mul (.log a) b) =
                some (logInterval.mul IB) := by
            unfold evalWithLookups at hlogEval ⊢
            rw [IntervalExprOps.evalWithCallbacks, hlogEval, hB]
            rfl
          rw [Real.rpow_def_of_pos ((by exact_mod_cast hpos : (0 : ℝ) < IA.lo).trans_le ha.1)]
          simpa [UnaryKind.apply] using
            hunary .exp _ _ result hArgEval hcallback _
              (mul_sound (hunary .log a IA logInterval hA hlog (a.eval ρ) ha) hb)
    · simp [rationalCallbacks, hpos] at hcallback

/-- Successful interval evaluation with division and unary lookups encloses the corresponding real
evaluation when both lookup providers satisfy their semantic soundness conditions. -/
theorem evalWithLookups_sound {ι : Type*}
    (env : ι → RationalInterval) (divLower : Verified.Expr ι → Option AbsLowerResult)
    (unaryRange : UnaryKind → Verified.Expr ι → RationalInterval → Option RationalInterval)
    (ρ : ι → ℝ)
    (henv : ∀ i, (env i).MemReal (ρ i))
    (hdiv : ∀ den cert, divLower den = some cert →
      (cert.delta : ℝ) ≤ |den.eval ρ|)
    (hunary : ∀ op arg IA result,
      evalWithLookups env divLower unaryRange arg = some IA →
      unaryRange op arg IA = some result →
      ∀ z, IA.MemReal z → result.MemReal (op.apply z)) :
    ∀ expr I, evalWithLookups env divLower unaryRange expr = some I →
      I.MemReal (expr.eval ρ) :=
  IntervalExprCallbacks.evalWithCallbacks_sound intervalExprBackend_verifiedExprOps
    (rationalCallbacks_sound env divLower unaryRange ρ henv hdiv hunary)

end RationalInterval
end CAS.Continuum

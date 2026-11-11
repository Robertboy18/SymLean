/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.IteratedDifferentiation
public import CAS.Calculus.Series
public import CAS.Continuum.IntervalEval.Digits

/-!
# Certified simple roots of one-variable expressions

`rootCheck p f lo hi` evaluates, with the interval evaluator `DigitsEval.eval` at precision `p`,
the values of `f` at the two endpoints and its symbolic derivative `∂f` on the whole interval
`[lo, hi]`. It accepts when the endpoint values have opposite strict signs and the derivative
enclosure has the sign of the change. Together with the analytic validity of `f` on `[lo, hi]`,
`existsUnique_root_of_rootCheck` concludes that `f` has exactly one zero in `[lo, hi]`.

## Main definitions

* `valueOn`: the interval value of an expression on a rational interval.
* `rootCheck`: the root check.

## Main results

* `existsUnique_zero_of_hasDerivAt`: a function whose derivative has one strict sign on
  `[a, b]` and whose values at `a` and `b` have opposite strict signs, matching that sign, has
  exactly one zero in `[a, b]`.
* `existsUnique_root_of_rootCheck`: the same for a checked expression that passes `rootCheck`
  and is valid on `[lo, hi]`.

## Implementation notes

`rootCheck` is the certificate of `#cas [findRoot x in [a, b]] f` (`CAS.Command.FindRoot`). The
search samples `f` at 65 points of `[a, b]` and narrows the first sign change by bisection in
compiled code; only the final interval reaches the kernel. The kernel evaluates `rootCheck` on
it, and the CEGA domain checker (`validIteratesOnIcc?`) proves `f` valid there. The soundness of
the three interval evaluations is `DigitsEval.eval_sound`.

The proof is classical calculus from Mathlib: the intermediate value theorem
(`intermediate_value_Icc`, `intermediate_value_Icc'`) gives a zero, and strict monotonicity from
the sign of the derivative (`strictMonoOn_of_deriv_pos`, `strictAntiOn_of_deriv_neg`) rules out
a second. Since the derivative must have one strict sign on the whole interval, a root where
it vanishes, or two roots inside the final interval, cannot pass the check, and the command
refuses them.
-/

@[expose] public section

namespace CAS.Verified.Expr

open Set
open CAS.Continuum

/-- The interval value of a one-variable expression on the interval `I`. -/
def valueOn (p : DigitsEval.Precision) (expr : Verified.Expr (Fin 1)) (I : RationalInterval) :
    Option RationalInterval :=
  DigitsEval.eval p (fun _ ↦ I) expr

/-- The endpoint values of `expr` on `[lo, hi]` have opposite strict signs, and the enclosure of
its derivative on `[lo, hi]` has the sign of the change. -/
def rootCheck (p : DigitsEval.Precision) (expr : Verified.Expr (Fin 1)) (lo hi : ℚ) : Bool :=
  if h : lo ≤ hi then
    match valueOn p expr (.const lo), valueOn p expr (.const hi),
        valueOn p (expr.diff 0) (.ofBounds lo hi h) with
    | some A, some B, some D =>
        (decide (A.hi < 0) && decide (0 < B.lo) && decide (0 < D.lo)) ||
          (decide (0 < A.lo) && decide (B.hi < 0) && decide (D.hi < 0))
    | _, _, _ => false
  else false

/-- A function with a derivative of one strict sign on `[a, b]` and values of opposite signs at
the endpoints has exactly one zero in `[a, b]`. -/
theorem existsUnique_zero_of_hasDerivAt {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hsign : (f a < 0 ∧ 0 < f b ∧ ∀ x ∈ Icc a b, 0 < f' x) ∨
      (0 < f a ∧ f b < 0 ∧ ∀ x ∈ Icc a b, f' x < 0)) :
    ∃! x : ℝ, x ∈ Icc a b ∧ f x = 0 := by
  have hcont : ContinuousOn f (Icc a b) := fun x hx ↦
    (hderiv x hx).continuousAt.continuousWithinAt
  have hderiv' (x : ℝ) (hx : x ∈ interior (Icc a b)) : deriv f x = f' x :=
    (hderiv x (interior_subset hx)).deriv
  rcases hsign with ⟨ha, hb, hpos⟩ | ⟨ha, hb, hneg⟩
  · have hmono : StrictMonoOn f (Icc a b) :=
      strictMonoOn_of_deriv_pos (convex_Icc a b) hcont fun x hx ↦
        (hderiv' x hx) ▸ hpos x (interior_subset hx)
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hab hcont ⟨ha.le, hb.le⟩
    exact ⟨c, ⟨hc, hfc⟩, fun y hy ↦ hmono.injOn hy.1 hc (hy.2.trans hfc.symm)⟩
  · have hanti : StrictAntiOn f (Icc a b) :=
      strictAntiOn_of_deriv_neg (convex_Icc a b) hcont fun x hx ↦
        (hderiv' x hx) ▸ hneg x (interior_subset hx)
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' hab hcont ⟨hb.le, ha.le⟩
    exact ⟨c, ⟨hc, hfc⟩, fun y hy ↦ hanti.injOn hy.1 hc (hy.2.trans hfc.symm)⟩

/-- A checked sign change with a derivative of fixed sign: an expression valid on `[lo, hi]`
has exactly one zero there. -/
theorem existsUnique_root_of_rootCheck {p : DigitsEval.Precision} {expr : Verified.Expr (Fin 1)}
    {lo hi : ℚ} (hvalid : expr.ValidIteratesOn 1 (Icc (lo : ℝ) (hi : ℝ)))
    (h : rootCheck p expr lo hi = true) :
    ∃! x : ℝ, x ∈ Icc (lo : ℝ) (hi : ℝ) ∧ expr.univariateEval x = 0 := by
  unfold rootCheck at h
  split_ifs at h with hle
  rcases hA : valueOn p expr (.const lo) with _ | A <;>
    rcases hB : valueOn p expr (.const hi) with _ | B <;>
    rcases hD : valueOn p (expr.diff 0) (.ofBounds lo hi hle) with _ | D <;>
    simp only [hA, hB, hD, Bool.false_eq_true] at h
  have hval (q : ℚ) {I : RationalInterval} (hI : valueOn p expr (.const q) = some I) :
      I.MemReal (expr.univariateEval q) := by
    rw [univariateEval, euclideanSingle_eq_const]
    exact DigitsEval.eval_sound p _ (fun _ ↦ (q : ℝ)) (fun _ ↦ RationalInterval.memReal_const q)
      expr hI
  have hdiff (x : ℝ) (hx : x ∈ Icc (lo : ℝ) (hi : ℝ)) :
      D.MemReal ((expr.diff 0).univariateEval x) := by
    rw [univariateEval, euclideanSingle_eq_const]
    exact DigitsEval.eval_sound p _ (fun _ ↦ x)
      (fun _ ↦ RationalInterval.memReal_ofBounds hle hx) (expr.diff 0) hD
  have hderiv (x : ℝ) (hx : x ∈ Icc (lo : ℝ) (hi : ℝ)) :
      HasDerivAt expr.univariateEval ((expr.diff 0).univariateEval x) x :=
    hasDerivAt_univariateEval expr x (hvalid 0 Nat.one_pos x hx)
  have hA' := hval lo hA
  have hB' := hval hi hB
  have hle' : (lo : ℝ) ≤ hi := by exact_mod_cast hle
  refine existsUnique_zero_of_hasDerivAt hle' hderiv ?_
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨hAneg, hBpos⟩, hDpos⟩ | ⟨⟨hApos, hBneg⟩, hDneg⟩
  · refine Or.inl ⟨hA'.2.trans_lt (by exact_mod_cast hAneg),
      (show ((0 : ℚ) : ℝ) < B.lo by exact_mod_cast hBpos).trans_le hB'.1 |>.trans_eq' ?_,
      fun x hx ↦ (show ((0 : ℚ) : ℝ) < D.lo by exact_mod_cast hDpos).trans_le (hdiff x hx).1
        |>.trans_eq' ?_⟩ <;> simp
  · refine Or.inr ⟨(show ((0 : ℚ) : ℝ) < A.lo by exact_mod_cast hApos).trans_le hA'.1
        |>.trans_eq' ?_, hB'.2.trans_lt (by exact_mod_cast hBneg),
      fun x hx ↦ (hdiff x hx).2.trans_lt (by exact_mod_cast hDneg)⟩
    simp

end CAS.Verified.Expr

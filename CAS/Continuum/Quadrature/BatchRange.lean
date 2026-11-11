/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.BatchSimpson
public import CAS.Continuum.Quadrature.CellRange

/-!
# Range enclosures of an integral in one kernel check

`panels (panel p f) a h n` encloses `∫ x in a..a + n h, f x` by `n` range panels of width `h`
(`panels` and `panels_sound` of `BatchSimpson`, stated for every panel enclosure): on each
panel the precision-parametric interval evaluator `DigitsEval.eval` encloses the values of `f`,
and the integral over the panel lies in that range times the width (`cellIntegralInterval`). The
whole enclosure is one closed computation, so a single kernel evaluation of `rangeCheck` checks
every panel.

A range panel needs only the continuity of `f`, where a Simpson panel (`BatchSimpson`) needs four
derivatives, so it serves integrands such as `√x` on `[0, 1]` or `|x|`. The price is accuracy:
the width of the enclosure shrinks at best in proportion to the panel width, and not at all where
the evaluator's enclosure of `f` does not narrow on smaller panels, while each doubling of the
Simpson panels divides the Simpson remainder by 16.

`of_rangeCheck` gives `lo ≤ ∫ x in a..b, f x ≤ hi` from a passing check and the continuity of `f`
on `[a, b]`.

## Implementation notes

The caller is bare `cega` (`CAS.CEGA.Integration`). Its compiled search doubles the panel count
and chooses the precision and the bounds, and it takes range panels when the domain checker finds
no validity certificate for `f` and its first four derivatives, or when Simpson panels miss the
stated bound. The kernel then evaluates `rangeCheck`. Each panel rests on
`cellIntegralInterval_sound`: an integrable function with values in `R` on `[l, r]` has its
integral in `(r - l) • R`, which needs nothing beyond the monotonicity of the integral, and
`intervalIntegral.integral_add_adjacent_intervals` glues the panels together. Range times width
is the simplest enclosure of an integral in interval arithmetic; as in `BatchSimpson`, the
reduction of all panels to one Boolean that the kernel evaluates is ours.

## References

* Ramon E. Moore, *Interval Analysis*, Prentice-Hall, Englewood Cliffs, N.J., 1966,
  <https://zbmath.org/?q=an:0176.13301>. Interval quadrature is one of the applications of
  interval arithmetic that the book treats.
-/

@[expose] public section

namespace CAS.Continuum
namespace BatchRange

open Set RationalInterval CAS.Verified

/-- The range enclosure of the integral over one panel `[l, r]`. -/
def panel (p : DigitsEval.Precision) (f : Verified.Expr (Fin 1)) (l r : ℚ) :
    Option RationalInterval :=
  if hlr : l ≤ r then do
    let R ← DigitsEval.eval p (BatchSimpson.env (ofBounds l r hlr)) f
    some (cellIntegralInterval (ofBounds l r hlr) R)
  else none

/-- One range panel encloses its integral. -/
theorem panel_sound {p : DigitsEval.Precision} {f : Verified.Expr (Fin 1)} {l r : ℚ}
    {I : RationalInterval} (hcont : ContinuousOn f.univariateEval (Icc (l : ℝ) r))
    (h : panel p f l r = some I) :
    I.MemReal (∫ x in (l : ℝ)..r, f.univariateEval x) := by
  unfold panel at h
  split at h
  · rename_i hlr
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨R, hR, rfl⟩ := h
    have hlr' : (l : ℝ) ≤ r := by exact_mod_cast hlr
    exact cellIntegralInterval_sound (ofBounds l r hlr) R f.univariateEval
      (hcont.intervalIntegrable_of_Icc hlr')
      fun x hx ↦ DigitsEval.eval_sound p _ _ (BatchSimpson.env_sound hx) f hR
  · cases h

/-- The range enclosure of `∫ x in a..b, f x` by `N` panels lies in `[lo, hi]`. -/
def rangeCheck (p : DigitsEval.Precision) (f : Verified.Expr (Fin 1)) (a b : ℚ) (N : ℕ)
    (lo hi : ℚ) : Bool :=
  decide (0 < N) && decide (a < b) &&
    match panels (panel p f) a ((b - a) / N) N with
    | some I => decide (lo ≤ I.lo) && decide (I.hi ≤ hi)
    | none => false

/-- **Batch range certificate.** -/
theorem of_rangeCheck {p : DigitsEval.Precision} {f : Verified.Expr (Fin 1)} {a b : ℚ}
    {N : ℕ} {lo hi : ℚ} (hcont : ContinuousOn f.univariateEval (Icc (a : ℝ) b))
    (h : rangeCheck p f a b N lo hi = true) :
    (lo : ℝ) ≤ ∫ x in (a : ℝ)..b, f.univariateEval x ∧
      ∫ x in (a : ℝ)..b, f.univariateEval x ≤ hi := by
  unfold rangeCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hN, hab⟩, hrest⟩ := h
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hend : a + N * ((b - a) / N) = b := by field_simp; ring
  have hh : 0 < (b - a) / N := div_pos (sub_pos.mpr hab) (by exact_mod_cast hN)
  split at hrest
  · rename_i I hI
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
    have hcont' : ContinuousOn f.univariateEval
        (Icc (a : ℝ) ((a + N * ((b - a) / N) : ℚ) : ℝ)) := by
      rwa [hend]
    have hab' : (a : ℝ) ≤ ((a + N * ((b - a) / N) : ℚ) : ℝ) := by
      rw [hend]
      exact_mod_cast hab.le
    have hmem := panels_sound hh (hcont'.intervalIntegrable_of_Icc hab')
      (fun n hn J hJ ↦ panel_sound (hcont'.mono (Icc_panel_subset hh hn)) hJ) N le_rfl I hI
    rw [hend] at hmem
    exact ⟨(Rat.cast_le.mpr hrest.1).trans hmem.1, hmem.2.trans (Rat.cast_le.mpr hrest.2)⟩
  · cases hrest

end BatchRange
end CAS.Continuum

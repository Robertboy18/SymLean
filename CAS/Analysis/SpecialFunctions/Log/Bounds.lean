/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Secant bounds, clipping and translation of the real logarithm

We bound how much the kernel `y ↦ log (x - y)` changes in L¹ when `x` moves. Clipping the
logarithm at a radius `ε` (`clippedLog ε t = log (max ε |t|)`) gives a function that is
Lipschitz with constant `1 / ε` (`abs_clippedLog_sub_le`); the remainder `logTail ε` is
integrable with integral `2 ε` (`integral_logTail`). Together they give
`∫ y in a..b, |log (x - y) - log (m - y)| ≤ 4 ε + (b - a) |x - m| / ε` for every `ε > 0` when
`a ≤ b`.

## Main results

* `abs_log_sub_log_le`: on `[ε, ∞)` the logarithm is Lipschitz with constant `1 / ε`.
* `integrableOn_log_sub`: the translated kernel `y ↦ log (x - y)` is integrable on every
  compact interval, including intervals that contain the singular point `y = x`.
* `integral_abs_log_sub_le`: the L¹ translation estimate above, on any finite interval.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace CAS.Analysis

private theorem log_sub_le_div {ε a b : ℝ} (hε : 0 < ε)
    (ha : ε ≤ a) (hb : ε ≤ b) (hab : b ≤ a) :
    Real.log a - Real.log b ≤ (a - b) / ε := by
  have ha0 := hε.trans_le ha
  have hb0 := hε.trans_le hb
  calc
    _ = Real.log (a / b) := (Real.log_div ha0.ne' hb0.ne').symm
    _ ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    _ = (a - b) / b := by rw [sub_div, div_self hb0.ne']
    _ ≤ (a - b) / ε := div_le_div_of_nonneg_left (sub_nonneg.mpr hab) hε hb

/-- Above a positive floor `ε`, the logarithm is Lipschitz with constant `1 / ε`. -/
theorem abs_log_sub_log_le {ε a b : ℝ} (hε : 0 < ε)
    (ha : ε ≤ a) (hb : ε ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / ε := by
  rcases le_total b a with hab | hab
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (hε.trans_le hb) hab)),
      abs_of_nonneg (sub_nonneg.mpr hab)]
    exact log_sub_le_div hε ha hb hab
  · rw [abs_sub_comm (Real.log a), abs_sub_comm a,
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (hε.trans_le ha) hab)),
      abs_of_nonneg (sub_nonneg.mpr hab)]
    exact log_sub_le_div hε hb ha hab

/-- The translated logarithmic kernel `y ↦ log (x - y)` is integrable on every compact
interval. -/
theorem integrableOn_log_sub (x a b : ℝ) :
    IntegrableOn (fun y ↦ Real.log (x - y)) (Icc a b) := by
  rcases le_or_gt a b with hab | hba
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp (by simpa only [sub_sub_cancel]
      using (intervalIntegral.intervalIntegrable_log' (a := x - a) (b := x - b)).comp_sub_left x)
  · rw [Icc_eq_empty_of_lt hba]
    exact integrableOn_empty

noncomputable section

/-- The logarithm held constant within distance `ε` of zero. -/
def clippedLog (ε t : ℝ) : ℝ := Real.log (max ε |t|)

/-- Clipping removes the singular derivative without changing the logarithm away from zero. -/
theorem abs_clippedLog_sub_le {ε x y : ℝ} (hε : 0 < ε) :
    |clippedLog ε x - clippedLog ε y| ≤ |x - y| / ε := by
  apply (abs_log_sub_log_le hε (le_max_left _ _) (le_max_left _ _)).trans
  apply div_le_div_of_nonneg_right _ hε.le
  simpa only [max_comm ε] using
    (abs_max_sub_max_le_abs |x| |y| ε).trans (abs_abs_sub_abs_le_abs_sub x y)

/-- The removed logarithmic tail, with its value at the single singular point set to zero. -/
def logTail (ε t : ℝ) : ℝ :=
  if t = 0 then 0 else (Ioc (-ε) ε).indicator (fun s ↦ Real.log ε - Real.log s) t

/-- The tail agrees almost everywhere with an interval indicator. -/
theorem logTail_ae_eq (ε : ℝ) :
    logTail ε =ᵐ[volume] (Ioc (-ε) ε).indicator (fun s ↦ Real.log ε - Real.log s) := by
  filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
  simp only [logTail, ht, ↓reduceIte]

/-- Removing the value at zero makes the logarithmic tail nonnegative everywhere. -/
theorem logTail_nonneg (ε t : ℝ) : 0 ≤ logTail ε t := by
  by_cases ht : t = 0
  · simp [logTail, ht]
  · simp only [logTail, ht, ↓reduceIte]
    by_cases hs : t ∈ Ioc (-ε) ε
    · rw [indicator_of_mem hs, ← Real.log_abs t]
      exact sub_nonneg.mpr (Real.log_le_log (abs_pos.mpr ht)
        (abs_le.mpr ⟨hs.1.le, hs.2⟩))
    · rw [indicator_of_notMem hs]

/-- The compact logarithmic tail is absolutely integrable. -/
theorem integrable_logTail (ε : ℝ) : Integrable (logTail ε) := by
  have hi : IntervalIntegrable (fun t ↦ Real.log ε - Real.log t) volume (-ε) ε :=
    intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_log'
  exact ((integrable_indicator_iff measurableSet_Ioc).mpr hi.1).congr (logTail_ae_eq ε).symm

/-- The exact mass lost by clipping is twice the clipping radius. -/
theorem integral_logTail {ε : ℝ} (hε : 0 < ε) :
    (∫ t, logTail ε t) = 2 * ε := by
  rw [integral_congr_ae (logTail_ae_eq ε), integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -ε ≤ ε),
    intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_log',
    intervalIntegral.integral_const, integral_log, Real.log_neg_eq_log]
  ring

/-- The absolute difference is integrable across either logarithmic singularity. -/
theorem intervalIntegrable_abs_log_sub (a b x m : ℝ) :
    IntervalIntegrable (fun y ↦ |Real.log (x - y) - Real.log (m - y)|) volume a b := by
  have hlog (z : ℝ) :
      IntervalIntegrable (fun y ↦ Real.log (z - y)) volume a b := by
    simpa only [sub_sub_cancel] using
      (intervalIntegral.intervalIntegrable_log' (a := z - a) (b := z - b)).comp_sub_left z
  simpa only [Real.norm_eq_abs] using ((hlog x).sub (hlog m)).norm

/-- Away from the single totalized value, the tail is exactly what clipping removes. -/
theorem clippedLog_sub_log_eq_logTail (ε : ℝ) {t : ℝ} (ht : t ≠ 0) :
    clippedLog ε t - Real.log t = logTail ε t := by
  by_cases hs : t ∈ Ioc (-ε) ε
  · have habs : |t| ≤ ε := abs_le.mpr ⟨hs.1.le, hs.2⟩
    simp only [clippedLog, max_eq_left habs, logTail, ht, ↓reduceIte,
      indicator_of_mem hs]
  · have habs : ε ≤ |t| := le_of_not_gt fun h ↦ hs ⟨(abs_lt.mp h).1, (abs_lt.mp h).2.le⟩
    simp only [clippedLog, max_eq_right habs, Real.log_abs, sub_self,
      logTail, ht, ↓reduceIte, indicator_of_notMem hs]

/-- The two integrable tails dominate the error in replacing the singular kernel. -/
theorem abs_log_sub_le_tails {ε x y : ℝ} (hε : 0 < ε) (hx : x ≠ 0) (hy : y ≠ 0) :
    |Real.log x - Real.log y| ≤
      logTail ε x + |x - y| / ε + logTail ε y := by
  have hx' : |Real.log x - clippedLog ε x| = logTail ε x := by
    rw [abs_sub_comm, clippedLog_sub_log_eq_logTail ε hx,
      abs_of_nonneg (logTail_nonneg ε x)]
  have hy' : |clippedLog ε y - Real.log y| = logTail ε y := by
    rw [clippedLog_sub_log_eq_logTail ε hy, abs_of_nonneg (logTail_nonneg ε y)]
  calc
    _ ≤ |Real.log x - clippedLog ε x| +
          (|clippedLog ε x - clippedLog ε y| + |clippedLog ε y - Real.log y|) :=
      (abs_sub_le _ (clippedLog ε x) _).trans (add_le_add le_rfl (abs_sub_le _ _ _))
    _ ≤ logTail ε x + |x - y| / ε + logTail ε y := by
      rw [hx', hy', ← add_assoc]
      linarith [abs_clippedLog_sub_le (x := x) (y := y) hε]

/-- Logarithmic translation is controlled in L¹ on any finite interval. -/
theorem integral_abs_log_sub_le {a b ε x m : ℝ} (hab : a ≤ b) (hε : 0 < ε) :
    (∫ y in a..b, |Real.log (x - y) - Real.log (m - y)|) ≤
      4 * ε + (b - a) * |x - m| / ε := by
  have hf : IntegrableOn (fun y ↦ |Real.log (x - y) - Real.log (m - y)|) (Ioc a b) :=
    (intervalIntegrable_abs_log_sub a b x m).1
  have hx := (integrable_logTail ε).comp_sub_left x
  have hm := (integrable_logTail ε).comp_sub_left m
  have hc : IntegrableOn (fun _ : ℝ ↦ |x - m| / ε) (Ioc a b) :=
    integrableOn_const (by simp)
  have hxc : IntegrableOn (fun y ↦ logTail ε (x - y) + |x - m| / ε) (Ioc a b) :=
    hx.integrableOn.add hc
  have hmajor : IntegrableOn
      (fun y ↦ logTail ε (x - y) + |x - m| / ε + logTail ε (m - y)) (Ioc a b) :=
    hxc.add hm.integrableOn
  have hbnd := integral_mono_ae hf hmajor (show
      ∀ᵐ y ∂volume.restrict (Ioc a b),
        |Real.log (x - y) - Real.log (m - y)| ≤
          logTail ε (x - y) + |x - m| / ε + logTail ε (m - y) by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne x),
      ae_restrict_of_ae (volume.ae_ne m)] with y hyx hym
    simpa only [sub_sub_sub_cancel_right] using
      abs_log_sub_le_tails hε (sub_ne_zero.mpr hyx.symm) (sub_ne_zero.mpr hym.symm))
  have ht (z : ℝ) : (∫ y in Ioc a b, logTail ε (z - y)) ≤ 2 * ε :=
    (setIntegral_le_integral ((integrable_logTail ε).comp_sub_left z)
      (Eventually.of_forall fun y ↦ logTail_nonneg ε (z - y))).trans_eq
        (by rw [integral_sub_left_eq_self, integral_logTail hε])
  rw [integral_add hxc hm.integrableOn,
    integral_add hx.integrableOn hc, setIntegral_const,
    Real.volume_real_Ioc_of_le hab, smul_eq_mul, ← mul_div_assoc] at hbnd
  rw [intervalIntegral.integral_of_le hab]
  linarith [ht x, ht m]

end

end CAS.Analysis

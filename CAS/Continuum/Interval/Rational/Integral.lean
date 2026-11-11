/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Arithmetic
public import CAS.Continuum.Interval.Rational.FiniteSum

/-!
# Integrating rational interval enclosures

`intervalIntegral_mem`: if an integrable `f` takes values in `I` on `(a, b)`, where `a ≤ b` are
rationals, then `∫ x in a..b, f x` lies in `(b - a) • I`, computed by `scaleNonneg`.
`intervalIntegral_mem_sum` sums such enclosures over the cells `(a i, a (i + 1))` of a partition,
each cell with its own interval, and `intervalIntegral_mem_uniform` is the case of a uniform mesh
of width `h ≥ 0`. The sums keep the signs of the cell enclosures and are exact in rational
arithmetic.
-/

@[expose] public section

namespace CAS.Continuum.RationalInterval

open Set MeasureTheory

/-- If `f x ∈ I` for `x ∈ (a, b)`, then `∫ x in a..b, f x ∈ (b - a) • I`. -/
theorem intervalIntegral_mem {f : ℝ → ℝ} {a b : ℚ} {I : RationalInterval}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume (a : ℝ) b)
    (hI : ∀ x ∈ Ioo (a : ℝ) b, I.MemReal (f x)) :
    (I.scaleNonneg (b - a) (sub_nonneg.mpr hab)).MemReal
      (∫ x in (a : ℝ)..b, f x) := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hlo := intervalIntegral.integral_mono_on_of_le_Ioo hab' intervalIntegrable_const hf
    fun x hx ↦ (hI x hx).1
  have hhi := intervalIntegral.integral_mono_on_of_le_Ioo hab' hf intervalIntegrable_const
    fun x hx ↦ (hI x hx).2
  simpa only [MemReal, scaleNonneg_lo, scaleNonneg_hi, Rat.cast_mul, Rat.cast_sub,
    intervalIntegral.integral_const, smul_eq_mul] using And.intro hlo hhi

/-- If `f x ∈ I i` on each cell `(a i, a (i + 1))`, then `∫ x in a 0..a n, f x` lies in the sum of
the intervals `(a (i + 1) - a i) • I i`. -/
theorem intervalIntegral_mem_sum {f : ℝ → ℝ} {n : ℕ}
    (a : ℕ → ℚ) (I : Fin n → RationalInterval)
    (ha : ∀ i < n, a i ≤ a (i + 1))
    (hf : ∀ i < n, IntervalIntegrable f volume (a i : ℝ) (a (i + 1)))
    (hI : ∀ i : Fin n, ∀ x ∈ Ioo (a i : ℝ) (a (i + 1)), (I i).MemReal (f x)) :
    (sum Finset.univ (fun i : Fin n ↦
      (I i).scaleNonneg (a (i + 1) - a i) (sub_nonneg.mpr (ha i i.isLt)))).MemReal
        (∫ x in (a 0 : ℝ)..(a n : ℝ), f x) := by
  have hadj := intervalIntegral.sum_integral_adjacent_intervals hf
  rw [← Fin.sum_univ_eq_sum_range] at hadj
  exact hadj ▸ sum_sound fun i _ ↦ intervalIntegral_mem (ha i i.isLt) (hf i i.isLt) (hI i)

/-- Enclosures on a uniform rational mesh give a signed enclosure of the whole
integral. The number of panels, starting point, width, and local boxes are arbitrary;
zero-width panels and an empty mesh are included. -/
theorem intervalIntegral_mem_uniform {f : ℝ → ℝ} {n : ℕ} {a h : ℚ}
    (hh : 0 ≤ h) (I : Fin n → RationalInterval)
    (hf : ∀ i < n, IntervalIntegrable f volume
      ((a + i * h : ℚ) : ℝ) ((a + (i + 1 : ℕ) * h : ℚ) : ℝ))
    (hI : ∀ i : Fin n, ∀ x ∈ Ioo ((a + i * h : ℚ) : ℝ)
      ((a + (i + 1 : ℕ) * h : ℚ) : ℝ), (I i).MemReal (f x)) :
    (sum Finset.univ (fun i ↦ (I i).scaleNonneg h hh)).MemReal
      (∫ x in (a : ℝ)..((a + n * h : ℚ) : ℝ), f x) := by
  have ha (i : ℕ) (_ : i < n) : a + i * h ≤ a + (i + 1 : ℕ) * h := by
    push_cast
    linarith
  have hwidth (i : Fin n) : (a + (i + 1 : ℕ) * h) - (a + i * h) = h := by
    push_cast
    ring
  simpa only [hwidth, Nat.cast_zero, zero_mul, add_zero] using
    intervalIntegral_mem_sum (fun i ↦ a + i * h) I ha hf hI

end CAS.Continuum.RationalInterval

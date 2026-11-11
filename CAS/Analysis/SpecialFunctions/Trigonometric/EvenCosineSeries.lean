/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.SpecialFunctions.Trigonometric.CosineQuadrature
public import CAS.Analysis.SpecialFunctions.Trigonometric.MultipleAngle
public import Mathlib.Data.Nat.Dist

/-!
# Even cosine series and the exact tensor rule

A function `f : ℝ → ℝ` is an even cosine series of degree `D` when
`f x = ∑_{k ≤ D} a_k cos (2kx)` for every real `x`. The class is closed under sums and scalar
multiples, and it is exactly the class of trigonometric polynomials that are even about `0` and
about `π/2`: for `f x = ∑_{k ≤ E} (a_k cos (kx) + b_k sin (kx))` the reflection `x ↦ -x`
removes the sines and the reflection `x ↦ π - x` removes the odd frequencies, so
`f x = ∑_{j ≤ E/2} a_{2j} cos (2jx)`. These two reflections are the condition under which the
quarter-period rules apply.

The quarter-period trapezoid and sine rules hold for every even cosine series.
For a function of two variables whose sections in `β` and in `θ` are even cosine series, the
trapezoid rule in `β` and the sine rule in `θ` combine into an exact rule for
`∫_0^{π/2} ∫_0^{π/2} f (β, θ) sin θ dθ dβ`, with no Fubini argument: the inner rule is applied
for every `β` and the outer rule at the finitely many nodes `θ_n`.

## Main results

* `IsEvenCosineSeries.of_trigSeries`: parity about `0` and `π/2` gives an even cosine series.
* `IsEvenCosineSeries.integral_eq_trapezoid`, `IsEvenCosineSeries.integral_mul_sin_eq_rule`.
* `integral_integral_mul_sin_eq_rule`: the exact tensor rule on `[0, π/2]²`.
-/

@[expose] public noncomputable section

namespace CAS.Analysis

open Finset Filter
open scoped Topology

/-- `cos (2 |k - l| x) = cos (2kx - 2lx)`, with `|k - l|` the distance `Nat.dist k l`. -/
theorem cos_two_mul_dist (k l : ℕ) (x : ℝ) :
    Real.cos (2 * (Nat.dist k l : ℝ) * x) = Real.cos (2 * k * x - 2 * l * x) := by
  rcases le_total l k with h | h
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, mul_sub, sub_mul]
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, ← Real.cos_neg, mul_sub, sub_mul, neg_sub]

/-- A sum over `range (2M + 2)` grouped into consecutive pairs. -/
theorem sum_range_two_mul_add_two (G : ℕ → ℝ) (M : ℕ) :
    ∑ k ∈ range (2 * M + 2), G k = ∑ j ∈ range (M + 1), (G (2 * j) + G (2 * j + 1)) := by
  induction M with
  | zero => simp [sum_range_succ]
  | succ M ih =>
    rw [show 2 * (M + 1) + 2 = 2 * M + 2 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (fun j ↦ G (2 * j) + G (2 * j + 1)) (M + 1),
      show 2 * (M + 1) = 2 * M + 2 by ring]
    ring

/-- If the odd terms vanish, a sum over `range (E + 1)` is the sum of its even terms. -/
theorem sum_range_succ_eq_sum_even (G : ℕ → ℝ) (E : ℕ) (hodd : ∀ j, G (2 * j + 1) = 0) :
    ∑ k ∈ range (E + 1), G k = ∑ j ∈ range (E / 2 + 1), G (2 * j) := by
  have h₂ : ∑ k ∈ range (2 * (E / 2) + 2), G k = ∑ j ∈ range (E / 2 + 1), G (2 * j) := by
    rw [sum_range_two_mul_add_two]
    simp only [hodd, add_zero]
  rw [← h₂]
  rcases Nat.even_or_odd' E with ⟨m, hm | hm⟩
  · rw [show 2 * (E / 2) + 2 = E + 1 + 1 by omega, sum_range_succ G (E + 1),
      show G (E + 1) = 0 by rw [show E + 1 = 2 * m + 1 by omega]; exact hodd m, add_zero]
  · rw [show 2 * (E / 2) + 2 = E + 1 by omega]

/-- A function is an even cosine series of degree `D` when it equals
`∑_{k ≤ D} a_k cos (2kx)` at every real `x`. -/
def IsEvenCosineSeries (D : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ a : ℕ → ℝ, ∀ x, f x = ∑ k ∈ range (D + 1), a k * Real.cos (2 * k * x)

namespace IsEvenCosineSeries

variable {D E : ℕ} {f g : ℝ → ℝ}

/-- An even cosine series of degree `D` has coefficients indexed by `Fin (D + 1)`:
`f x = ∑ k, a k cos (2 k x)` for every real `x`. -/
theorem exists_fin (hf : IsEvenCosineSeries D f) :
    ∃ a : Fin (D + 1) → ℝ, ∀ x, f x = ∑ k, a k * Real.cos (2 * k * x) := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨fun k ↦ a k, fun x ↦ by
    rw [ha x, Fin.sum_univ_eq_sum_range (fun k ↦ a k * Real.cos (2 * k * x))]⟩

/-- A function equal at every point to an even cosine series of degree `D` is one, with the same
coefficients. -/
protected theorem congr (hf : IsEvenCosineSeries D f) (h : ∀ x, f x = g x) :
    IsEvenCosineSeries D g := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨a, fun x ↦ by rw [← h, ha]⟩

/-- An even cosine series is continuous on `ℝ`. -/
protected theorem continuous (hf : IsEvenCosineSeries D f) : Continuous f := by
  obtain ⟨a, ha⟩ := hf
  rw [show f = fun x ↦ ∑ k ∈ range (D + 1), a k * Real.cos (2 * k * x) from funext ha]
  fun_prop

/-- The zero function is an even cosine series of every degree `D`. -/
protected theorem zero : IsEvenCosineSeries D (fun _ ↦ 0) :=
  ⟨fun _ ↦ 0, fun x ↦ by simp⟩

/-- For `k ≤ D`, `x ↦ cos (2 k x)` is an even cosine series of degree `D`. -/
protected theorem cos_two_mul {k : ℕ} (hk : k ≤ D) :
    IsEvenCosineSeries D (fun x ↦ Real.cos (2 * k * x)) := by
  refine ⟨fun j ↦ if j = k then 1 else 0, fun x ↦ ?_⟩
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range, Nat.lt_succ_iff.mpr hk,
    ite_true]

/-- The sum of two even cosine series of degree `D` is one of degree `D`. -/
protected theorem add (hf : IsEvenCosineSeries D f) (hg : IsEvenCosineSeries D g) :
    IsEvenCosineSeries D (fun x ↦ f x + g x) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨fun k ↦ a k + b k, fun x ↦ ?_⟩
  dsimp only
  rw [ha, hb, ← sum_add_distrib]
  refine sum_congr rfl fun k _ ↦ ?_
  ring

/-- A real multiple `c f` of an even cosine series `f` of degree `D` is one of degree `D`. -/
protected theorem const_mul (c : ℝ) (hf : IsEvenCosineSeries D f) :
    IsEvenCosineSeries D (fun x ↦ c * f x) := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨fun k ↦ c * a k, fun x ↦ ?_⟩
  dsimp only
  rw [ha, mul_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  ring

/-- A finite sum `∑ i ∈ s, F i` of even cosine series of degree `D` is one of degree `D`. -/
protected theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, IsEvenCosineSeries D (F i)) :
    IsEvenCosineSeries D (fun x ↦ ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (IsEvenCosineSeries.zero (D := D)).congr fun x ↦ by simp
  | insert i s hi ih =>
    refine ((h i (mem_insert_self i s)).add
      (ih fun j hj ↦ h j (mem_insert_of_mem hj))).congr fun x ↦ ?_
    rw [sum_insert hi]

/-- An even cosine series of degree `D` is one of every degree `E ≥ D`. -/
theorem mono (hf : IsEvenCosineSeries D f) (hDE : D ≤ E) : IsEvenCosineSeries E f := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨fun k ↦ if k ≤ D then a k else 0, fun x ↦ ?_⟩
  rw [ha x]
  refine sum_subset_zero_on_sdiff (range_subset_range.mpr (by omega)) (fun k hk ↦ ?_)
    fun k hk ↦ ?_
  · simp only [Finset.mem_sdiff, mem_range] at hk
    simp [show ¬k ≤ D by omega]
  · simp [Nat.lt_succ_iff.mp (mem_range.mp hk)]

/-- A trigonometric polynomial that is even about `0` and about `π/2` is an even cosine series:
its sines and its odd frequencies cancel under the two reflections. -/
theorem of_trigSeries {E : ℕ} (a b : ℕ → ℝ)
    (hf : ∀ x, f x = ∑ k ∈ range (E + 1), (a k * Real.cos (k * x) + b k * Real.sin (k * x)))
    (h0 : ∀ x, f (-x) = f x) (hπ : ∀ x, f (Real.pi - x) = f x) :
    IsEvenCosineSeries (E / 2) f := by
  have hC (x : ℝ) : f x = ∑ k ∈ range (E + 1), a k * Real.cos (k * x) := by
    have h : f x + f (-x) = 2 * ∑ k ∈ range (E + 1), a k * Real.cos (k * x) := by
      rw [hf x, hf (-x), mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun k _ ↦ ?_
      rw [mul_neg, Real.cos_neg, Real.sin_neg]
      ring
    linarith [h0 x]
  have hE (x : ℝ) : f x =
      ∑ k ∈ range (E + 1), a k * ((1 + (-1) ^ k) / 2) * Real.cos (k * x) := by
    have h : f x + f (Real.pi - x) =
        2 * ∑ k ∈ range (E + 1), a k * ((1 + (-1) ^ k) / 2) * Real.cos (k * x) := by
      rw [hC x, hC (Real.pi - x), mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun k _ ↦ ?_
      rw [show (k : ℝ) * (Real.pi - x) = k * Real.pi - k * x by ring, Real.cos_sub,
        Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
      ring
    linarith [hπ x]
  refine ⟨fun j ↦ a (2 * j), fun x ↦ ?_⟩
  rw [hE x, sum_range_succ_eq_sum_even _ E fun j ↦ ?_]
  · refine sum_congr rfl fun j _ ↦ ?_
    simp only [pow_mul, neg_one_sq, one_pow]
    push_cast
    ring
  · simp only [pow_succ, pow_mul]
    ring

/-! ### The quarter-period rules for even cosine series -/

/-- The trapezoid rule on `[0, π/2]` with `N` subintervals integrates every even cosine series
of degree `D < 2N` exactly. -/
theorem integral_eq_trapezoid (hf : IsEvenCosineSeries D f) {N : ℕ} (hDN : D < 2 * N) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), f β =
      ∑ j : Fin (N + 1), quarterTrapezoidWeight N j * f (j * Real.pi / (2 * N)) := by
  obtain ⟨a, ha⟩ := hf.exists_fin
  obtain rfl : f = fun x ↦ ∑ k, a k * Real.cos (2 * k * x) := funext ha
  exact integral_cosSeries_eq_trapezoid hDN a

/-- The sine rule on `[0, π/2]` integrates `f (θ) sin θ` exactly for every even cosine series
`f` of degree `D ≤ N`. -/
theorem integral_mul_sin_eq_rule (hf : IsEvenCosineSeries D f) {N : ℕ} (hN : 0 < N)
    (hDN : D ≤ N) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ * Real.sin θ =
      ∑ n : Fin (N + 1), quarterSinWeight N n * f (n * Real.pi / (2 * N)) := by
  obtain ⟨a, ha⟩ := hf.exists_fin
  obtain rfl : f = fun x ↦ ∑ k, a k * Real.cos (2 * k * x) := funext ha
  exact integral_cosSeries_mul_sin_eq_rule hN hDN a

end IsEvenCosineSeries

/-! ### The tensor rule -/

/-- Two exact one-dimensional rules give an exact rule for an iterated integral: the inner rule
for every outer variable, the outer rule at each inner node. No Fubini argument is needed. -/
theorem integral_integral_eq_sum_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    {f : ℝ → ℝ → ℝ} {w : ℝ → ℝ} {a b c d : ℝ} (x : ι → ℝ) (y : κ → ℝ) (u : ι → ℝ)
    (v : κ → ℝ)
    (hθ : ∀ β, ∫ θ in c..d, f β θ * w θ = ∑ n ∈ t, v n * f β (y n))
    (hβ : ∀ n ∈ t, ∫ β in a..b, f β (y n) = ∑ j ∈ s, u j * f (x j) (y n))
    (hint : ∀ n ∈ t, IntervalIntegrable (fun β ↦ f β (y n)) MeasureTheory.volume a b) :
    ∫ β in a..b, ∫ θ in c..d, f β θ * w θ = ∑ j ∈ s, ∑ n ∈ t, u j * v n * f (x j) (y n) := by
  simp only [hθ]
  rw [intervalIntegral.integral_finsetSum fun n hn ↦ (hint n hn).const_mul (v n)]
  simp only [intervalIntegral.integral_const_mul]
  rw [sum_congr rfl fun n hn ↦ by rw [hβ n hn], sum_comm]
  simp only [mul_sum]
  refine sum_congr rfl fun j _ ↦ sum_congr rfl fun n _ ↦ ?_
  ring

/-- The exact tensor rule on `[0, π/2]²`: if every section in `β` is an even cosine series of
degree `D < 2N` and every section in `θ` one of degree `E ≤ P`, the trapezoid rule in `β` and
the sine rule in `θ` integrate `f (β, θ) sin θ` exactly. -/
theorem integral_integral_mul_sin_eq_rule {D E N P : ℕ} (hDN : D < 2 * N) (hP : 0 < P)
    (hEP : E ≤ P) {f : ℝ → ℝ → ℝ} (hβ : ∀ θ, IsEvenCosineSeries D (fun β ↦ f β θ))
    (hθ : ∀ β, IsEvenCosineSeries E (f β)) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), ∫ θ in (0 : ℝ)..(Real.pi / 2), f β θ * Real.sin θ =
      ∑ j : Fin (N + 1), ∑ n : Fin (P + 1), quarterTrapezoidWeight N j * quarterSinWeight P n *
        f (j * Real.pi / (2 * N)) (n * Real.pi / (2 * P)) :=
  integral_integral_eq_sum_sum univ univ (fun j : Fin (N + 1) ↦ (j : ℝ) * Real.pi / (2 * N))
    (fun n : Fin (P + 1) ↦ (n : ℝ) * Real.pi / (2 * P)) (fun j ↦ quarterTrapezoidWeight N j)
    (fun n ↦ quarterSinWeight P n) (fun β ↦ (hθ β).integral_mul_sin_eq_rule hP hEP)
    (fun _ _ ↦ (hβ _).integral_eq_trapezoid hDN)
    (fun _ _ ↦ (hβ _).continuous.intervalIntegrable _ _)

end CAS.Analysis

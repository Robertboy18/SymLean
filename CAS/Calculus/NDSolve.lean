/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import CAS.Polynomial.CoefficientList

/-!
# Certified numerical solutions of scalar polynomial ODEs

For `y' = f (t, y)` with `f` a polynomial in `t` and `y` with rational coefficients
(`fieldEval`: `c₀ (t) + y (c₁ (t) + y (…))`, each `cⱼ` a coefficient list in `t`), a list of
`Piece`s certifies a piecewise polynomial approximation on `[a, b]`. When the checker `check`
accepts the pieces and the output enclosures, the problem with `y (a) = y₀` has a solution on
`[a, b]`, any two solutions agree there, and every solution lies in the enclosures
(`check_sound`).

## Main definitions

* `Piece`, `Piece.check`: one polynomial piece with its bounds, and their test in `ℚ`.
* `run`: the pieces chained from `a`, with the enclosure `|y (tᵢ) - c| ≤ r` at each piece end.
* `check`: a successful `run` from `a` to `b` whose nodes lie in the output enclosures.

## Main results

* `abs_sub_le_gronwallBound_of_tube`: the one-sided tube Grönwall bound.
* `Piece.sound`, `run_sound`: the enclosures of every solution, piece by piece.
* `exists_solution`, `eqOn_of_isIntegralCurveOn`, `check_sound`: existence, uniqueness and
  enclosures.

## Implementation notes

The search of `#cas [ndsolve …]` (untrusted) proposes the pieces, Taylor polynomials with their
bounds, and the kernel decides `check`. On a piece `[tᵢ, tᵢ + hᵢ]` with approximation
`p (t) = qᵢ (t - tᵢ)`, `Piece.check` verifies in `ℚ` a bound `δᵢ` of the residual
`p' - f (t, p)` (`absEval`), an upper bound `Kᵢ > 0` of `∂f/∂y` in the tube `|y - p| ≤ Rᵢ`
(`upperEval` of `∂f/∂y (t, p)`, from `fieldDerivY`, plus `Rᵢ` times its Lipschitz bound in `y`
from `lipBound`), `Eᵢ ≥ exp (Kᵢ hᵢ)` (`exp_le_expUpper`, from `Real.exp_bound'`), and an end
deviation `eᵢ₊₁ < Rᵢ` with `eᵢ₊₁ ≥ δ₀ Eᵢ + δᵢ (Eᵢ - 1) / Kᵢ`, hence
`eᵢ₊₁ ≥ gronwallBound δ₀ Kᵢ δᵢ hᵢ` (`Piece.gronwall_le`) for the deviation `δ₀` at `tᵢ`. The
bound is Teschl's Theorem 2.8, with `p` an exact solution of a field within `δᵢ` of `f`.
There, as in Mathlib's `dist_le_of_approx_trajectories_ODE_of_mem`, the Lipschitz constant is
two-sided and both curves are assumed to stay in a set where it holds. We change two things.
The Lipschitz constant becomes the one-sided `F t z - F t w ≤ K (z - w)` for `w ≤ z`, so that
a negative slope `∂f/∂y` (a dissipative problem) costs only the small positive `K` the checker
requires, not `|∂f/∂y|`; the error still grows by at least `e ^ (K h)` on each piece. And the
slope bound is needed only in the tube: in `abs_sub_le_gronwallBound_of_tube` the right slope of
`|y - p|` is at most `K |y - p| + δ` while `|y - p| ≤ R`, and the strict `< R` keeps every
solution in the tube (`le_gronwallBound_of_le_of_lt`), so no a priori bound on the solution is
needed.

`run` carries the enclosure `|y (tᵢ) - c| ≤ r` from piece to piece and enters each piece with
`δ₀ = r + |c - p (tᵢ)|` (`run_sound`, for any field that agrees with `f` on the box `|y| ≤ boxOf`).
Existence (`exists_solution`) is Picard-Lindelöf (`IsPicardLindelof`) for `f` clamped to the box,
which is globally Lipschitz; `run_sound` keeps its solution in the box, where the clamped field is
`f`. Uniqueness (`eqOn_of_isIntegralCurveOn`) is `ODE_solution_unique_of_mem_Icc_right` on a strip
`|y| ≤ Y` containing both solutions, which are continuous on the compact `[a, b]`; the field is
Lipschitz on the strip (`exists_fieldEval_bounds`).

## References

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, Graduate Studies in
  Mathematics 140, American Mathematical Society, Providence, 2012,
  <https://doi.org/10.1090/gsm/140>. Theorem 2.2 (Picard-Lindelöf) and Theorem 2.8, the bound
  `|x₀ - y₀| e ^ (L t) + (M / L) (e ^ (L t) - 1)` from Grönwall's inequality (Lemma 2.7); we
  read them in the author's online version, <https://www.mat.univie.ac.at/~gerald/ftp/book-ode/>.
* N. S. Nedialkov, K. R. Jackson and G. F. Corliss, "Validated solutions of initial value
  problems for ordinary differential equations", *Applied Mathematics and Computation* 105
  (1999), pp. 21-68, <https://doi.org/10.1016/S0096-3003(98)10083-8>. A survey of validated
  methods for initial value problems: mainly interval Taylor series methods, and a method that
  controls the defect of the computed solution.
-/

@[expose] public section

open Set Filter Topology
open CAS.Polynomial

namespace CAS.Calculus.NDSolve

/-! ### Tube Grönwall -/

/-- Grönwall's bound for `f ≤ R` only: if `f' ≤ K f + ε` wherever `f ≤ R`, and the bound stays
below `R` on `[a, b]`, then `f` stays below the bound. -/
theorem le_gronwallBound_of_le_of_lt {f f' : ℝ → ℝ} {δ K ε R a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (f z - f x) < r)
    (ha : f a ≤ δ) (bound : ∀ x ∈ Ico a b, f x ≤ R → f' x ≤ K * f x + ε)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hR : gronwallBound δ K ε (b - a) < R) :
    ∀ x ∈ Icc a b, f x ≤ gronwallBound δ K ε (x - a) := by
  -- Budgets `ε' > ε` close enough to `ε` keep the bound below `R` on `[a, b]`.
  have hcont := gronwallBound_continuous_ε δ K (b - a)
  obtain ⟨η, hη, hηR⟩ : ∃ η > 0, ∀ ε' ∈ Ioo ε (ε + η), gronwallBound δ K ε' (b - a) < R := by
    have := (hcont.tendsto ε).eventually (gt_mem_nhds hR)
    rcases Metric.eventually_nhds_iff.mp this with ⟨η, hη, h⟩
    refine ⟨η, hη, fun ε' hε' ↦ h ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hε'.1, hε'.2]
  have H : ∀ x ∈ Icc a b, ∀ ε' ∈ Ioo ε (ε + η), f x ≤ gronwallBound δ K ε' (x - a) := by
    intro x hx ε' hε'
    apply image_le_of_liminf_slope_right_lt_deriv_boundary hf hf'
    · rwa [sub_self, gronwallBound_x0]
    · exact fun x ↦ hasDerivAt_gronwallBound_shift δ K ε' x a
    · intro y hy hfy
      have hmono := gronwallBound_mono hδ (hε.trans hε'.1.le) hK
      have hle : gronwallBound δ K ε' (y - a) ≤ gronwallBound δ K ε' (b - a) :=
        hmono (by linarith [hy.2])
      have hfR : f y ≤ R := by linarith [hηR ε' hε']
      have := bound y hy hfR
      rw [← hfy]
      have := hε'.1
      nlinarith [hK]
    · exact hx
  intro x hx
  change f x ≤ (fun ε' ↦ gronwallBound δ K ε' (x - a)) ε
  have hsub : ε ∈ closure (Ioo ε (ε + η)) := by
    rw [closure_Ioo (by linarith)]
    exact ⟨le_rfl, by linarith⟩
  exact ContinuousWithinAt.closure_le hsub continuousWithinAt_const
    (gronwallBound_continuous_ε δ K (x - a)).continuousWithinAt (H x hx)

/-- A posteriori enclosure of an ODE solution in a tube around an approximate solution, with a
one-sided Lipschitz bound `F t z - F t w ≤ K (z - w)` for `w ≤ z` in the tube: no a priori bound
on the solution is needed, the strict inequality `< R` keeps it in the tube. -/
theorem abs_sub_le_gronwallBound_of_tube {F : ℝ → ℝ → ℝ} {y p p' : ℝ → ℝ} {a b δ₀ δ K R : ℝ}
    (hy : ContinuousOn y (Icc a b))
    (hy' : ∀ t ∈ Ico a b, HasDerivWithinAt y (F t (y t)) (Ici t) t)
    (hp : ContinuousOn p (Icc a b))
    (hp' : ∀ t ∈ Ico a b, HasDerivWithinAt p (p' t) (Ici t) t)
    (hres : ∀ t ∈ Ico a b, |p' t - F t (p t)| ≤ δ)
    (hlip : ∀ t ∈ Ico a b, ∀ z w, |z - p t| ≤ R → |w - p t| ≤ R → w ≤ z →
      F t z - F t w ≤ K * (z - w))
    (h₀ : |y a - p a| ≤ δ₀) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hR : gronwallBound δ₀ K δ (b - a) < R) :
    ∀ t ∈ Icc a b, |y t - p t| ≤ gronwallBound δ₀ K δ (t - a) := by
  set e : ℝ → ℝ := fun t ↦ y t - p t with he
  set e' : ℝ → ℝ := fun t ↦ F t (y t) - p' t with he'
  have hd : ∀ t ∈ Ico a b, HasDerivWithinAt e (e' t) (Ici t) t :=
    fun t ht ↦ (hy' t ht).sub (hp' t ht)
  -- The right derivative of `|e|`: `± e'` where `e ≠ 0`, at most `|e'|` where `e = 0`.
  set g : ℝ → ℝ := fun t ↦ if 0 < e t then e' t else if e t < 0 then -e' t else |e' t| with hg
  have hslope : ∀ x ∈ Ico a b, ∀ r, g x < r →
      ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (|e z| - |e x|) < r := by
    intro x hx r hr
    by_cases hpos : 0 < e x
    · simp only [g, hpos, ↓reduceIte] at hr
      have h := ((hasDerivAt_abs_pos hpos).comp_hasDerivWithinAt x
        (hd x hx)).liminf_right_slope_le (by simpa using hr)
      simpa [slope_def_field, div_eq_inv_mul] using h
    · by_cases hneg : e x < 0
      · simp only [g, hpos, hneg, ↓reduceIte] at hr
        have h := ((hasDerivAt_abs_neg hneg).comp_hasDerivWithinAt x
          (hd x hx)).liminf_right_slope_le (by simpa using hr)
        simpa [slope_def_field, div_eq_inv_mul] using h
      · simp only [g, hpos, hneg, ↓reduceIte] at hr
        have h := (hd x hx).liminf_right_slope_norm_le (by simpa [Real.norm_eq_abs] using hr)
        simpa [Real.norm_eq_abs] using h
  refine le_gronwallBound_of_le_of_lt (f := fun t ↦ |e t|) (f' := g)
    (continuous_abs.comp_continuousOn (hy.sub hp)) hslope h₀ ?_
    ((abs_nonneg _).trans h₀) hδ hK hR
  intro t ht hR'
  have hr := hres t ht
  rw [abs_le] at hr
  simp only [g]
  split_ifs with hpos hneg
  · -- `y > p`: `e' = (F y - F p) + (F p - p') ≤ K (y - p) + δ`.
    have h1 := hlip t ht (y t) (p t) hR' (by simp; linarith [hR'.trans' (abs_nonneg _)])
      (by simp only [e] at hpos; linarith)
    simp only [e, e', abs_of_pos hpos] at h1 ⊢
    linarith
  · -- `y < p`: `-e' = (F p - F y) + (p' - F p) ≤ K (p - y) + δ`.
    have h1 := hlip t ht (p t) (y t) (by simp; linarith [hR'.trans' (abs_nonneg _)]) hR'
      (by simp only [e] at hneg; linarith)
    simp only [e, e', abs_of_neg hneg] at h1 ⊢
    linarith
  · have h0 : e t = 0 := by linarith [not_lt.1 hpos, not_lt.1 hneg]
    have hyp : y t = p t := by simp only [e] at h0; linarith
    simp only [e', hyp, h0, abs_zero, mul_zero, zero_add]
    rw [abs_le]
    constructor <;> linarith [hr.1, hr.2]

/-! ### Polynomials in `t` and `y` -/

/-- `Σ |lₖ| hᵏ`, a bound of `|l (u)|` for `0 ≤ u ≤ h`. -/
def absEval (l : List ℚ) (h : ℚ) : ℚ := coeffEvalRat (l.map fun c ↦ |c|) h

/-- For `0 ≤ h`, `absEval l h` is nonnegative. -/
theorem absEval_nonneg (l : List ℚ) {h : ℚ} (hh : 0 ≤ h) : 0 ≤ absEval l h := by
  induction l with
  | nil => simp [absEval, coeffEvalRat]
  | cons a l ih =>
    simp only [absEval, List.map_cons, coeffEvalRat] at ih ⊢
    have := abs_nonneg a
    positivity

/-- For `0 ≤ u ≤ h`, the value `coeffEval l u` has absolute value at most `absEval l h`. -/
theorem abs_coeffEval_le (l : List ℚ) {h : ℚ} {u : ℝ} (hu : 0 ≤ u) (huh : u ≤ h) :
    |coeffEval l u| ≤ absEval l h := by
  have hh : (0 : ℚ) ≤ h := by exact_mod_cast hu.trans huh
  induction l with
  | nil => simp [absEval, coeffEvalRat]
  | cons a l ih =>
    have hl := absEval_nonneg l hh
    simp only [absEval, List.map_cons, coeffEvalRat, coeffEval_cons, Rat.cast_add,
      Rat.cast_mul, Rat.cast_abs] at ih hl ⊢
    calc |(a : ℝ) + u * coeffEval l u| ≤ |(a : ℝ)| + u * |coeffEval l u| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg hu]
      _ ≤ |(a : ℝ)| + h * (coeffEvalRat (l.map fun c ↦ |c|) h : ℝ) := by
          gcongr

/-- `c₀ (t) + y (c₁ (t) + y (c₂ (t) + …))`, with each `cⱼ` a coefficient list in `t`. -/
noncomputable def fieldEval : List (List ℚ) → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | c :: cs, t, y => coeffEval c t + y * fieldEval cs t y

/-- For fixed `z`, the map `t ↦ fieldEval f t z` is continuous. -/
theorem continuous_fieldEval_left (f : List (List ℚ)) (z : ℝ) :
    Continuous fun t ↦ fieldEval f t z := by
  induction f with
  | nil => exact continuous_const
  | cons c cs ih => exact (continuous_coeffEval c).add (continuous_const.mul ih)

/-- `f (t₀ + u, q (u))` as a coefficient list in `u`. -/
def compose (f : List (List ℚ)) (t₀ : ℚ) (q : List ℚ) : List ℚ :=
  f.foldr (fun c acc ↦ coeffAdd (coeffShift t₀ c) (coeffMul q acc)) []

/-- The list `compose f t₀ q` evaluates at `u` to `fieldEval f (t₀ + u) (coeffEval q u)`. -/
theorem coeffEval_compose (f : List (List ℚ)) (t₀ : ℚ) (q : List ℚ) (u : ℝ) :
    coeffEval (compose f t₀ q) u = fieldEval f (t₀ + u) (coeffEval q u) := by
  induction f with
  | nil => simp [compose, fieldEval]
  | cons c cs ih =>
    simp only [compose, List.foldr_cons] at ih ⊢
    rw [coeffEval_coeffAdd, coeffEval_coeffMul, ih, coeffEval_coeffShift, fieldEval]

/-- Horner bounds `(B, L)` of `|f|` and of its Lipschitz constant in `y` on `|y| ≤ Y`, for
`t ∈ [t₀, t₀ + h]`. -/
def lipBound (t₀ h Y : ℚ) : List (List ℚ) → ℚ × ℚ
  | [] => (0, 0)
  | c :: cs => (absEval (coeffShift t₀ c) h + Y * (lipBound t₀ h Y cs).1,
      (lipBound t₀ h Y cs).1 + Y * (lipBound t₀ h Y cs).2)

/-- For `0 ≤ Y`, `0 ≤ u ≤ h` and `|z| ≤ Y`, `|w| ≤ Y`, the field at time `t₀ + u` satisfies
`|fieldEval f (t₀ + u) z| ≤ (lipBound t₀ h Y f).1` and
`|fieldEval f (t₀ + u) z - fieldEval f (t₀ + u) w| ≤ (lipBound t₀ h Y f).2 |z - w|`. -/
theorem lipBound_sound (f : List (List ℚ)) {t₀ h Y : ℚ} (hY : 0 ≤ Y) {u : ℝ} (hu : 0 ≤ u)
    (huh : u ≤ h) {z w : ℝ} (hz : |z| ≤ Y) (hw : |w| ≤ Y) :
    |fieldEval f (t₀ + u) z| ≤ (lipBound t₀ h Y f).1 ∧
      |fieldEval f (t₀ + u) z - fieldEval f (t₀ + u) w| ≤ (lipBound t₀ h Y f).2 * |z - w| := by
  have hYR : (0 : ℝ) ≤ Y := by exact_mod_cast hY
  induction f with
  | nil => simp [fieldEval, lipBound]
  | cons c cs ih =>
    obtain ⟨hB, hL⟩ := ih
    have hC := abs_coeffEval_le (coeffShift t₀ c) hu huh
    rw [coeffEval_coeffShift] at hC
    simp only [fieldEval, lipBound, Rat.cast_add, Rat.cast_mul]
    constructor
    · calc |coeffEval c (t₀ + u) + z * fieldEval cs (t₀ + u) z|
          ≤ |coeffEval c (t₀ + u)| + |z| * |fieldEval cs (t₀ + u) z| := by
            refine (abs_add_le _ _).trans ?_; rw [abs_mul]
        _ ≤ _ := by gcongr
    · have e : coeffEval c (t₀ + u) + z * fieldEval cs (t₀ + u) z -
          (coeffEval c (t₀ + u) + w * fieldEval cs (t₀ + u) w) =
          (z - w) * fieldEval cs (t₀ + u) z +
            w * (fieldEval cs (t₀ + u) z - fieldEval cs (t₀ + u) w) := by ring
      rw [e]
      have hB0 : 0 ≤ |fieldEval cs (t₀ + u) z| := abs_nonneg _
      calc _ ≤ |z - w| * |fieldEval cs (t₀ + u) z| +
            |w| * |fieldEval cs (t₀ + u) z - fieldEval cs (t₀ + u) w| := by
            refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
        _ ≤ |z - w| * ((lipBound t₀ h Y cs).1 : ℝ) +
            Y * (((lipBound t₀ h Y cs).2 : ℝ) * |z - w|) := by
            gcongr
        _ = _ := by ring

/-- For `0 ≤ h` and `0 ≤ Y`, both components of `lipBound t₀ h Y f` are nonnegative. -/
theorem lipBound_nonneg (f : List (List ℚ)) {t₀ h Y : ℚ} (hh : 0 ≤ h) (hY : 0 ≤ Y) :
    0 ≤ (lipBound t₀ h Y f).1 ∧ 0 ≤ (lipBound t₀ h Y f).2 := by
  induction f with
  | nil => simp [lipBound]
  | cons c cs ih =>
    have := absEval_nonneg (coeffShift t₀ c) hh
    simp only [lipBound]
    exact ⟨by nlinarith [ih.1], by nlinarith [ih.1, ih.2]⟩

/-- The sum of two fields. -/
def fieldAdd : List (List ℚ) → List (List ℚ) → List (List ℚ)
  | [], m => m
  | l, [] => l
  | a :: l, b :: m => coeffAdd a b :: fieldAdd l m

/-- `fieldAdd l m` evaluates at every `(t, y)` to the sum of the values of `l` and `m`. -/
theorem fieldEval_fieldAdd (l m : List (List ℚ)) (t y : ℝ) :
    fieldEval (fieldAdd l m) t y = fieldEval l t y + fieldEval m t y := by
  fun_induction fieldAdd l m with
  | case1 => simp [fieldEval]
  | case2 => simp [fieldEval]
  | case3 a l b m ih =>
    simp only [fieldEval, coeffEval_coeffAdd, ih]
    ring

/-- The derivative in `y`: `(c₀ + y G)' = G + y G'`. -/
def fieldDerivY : List (List ℚ) → List (List ℚ)
  | [] => []
  | _ :: cs => fieldAdd cs ([] :: fieldDerivY cs)

/-- For every `t` and `z`, the map `y ↦ fieldEval f t y` has derivative
`fieldEval (fieldDerivY f) t z` at `z`. -/
theorem hasDerivAt_fieldEval (f : List (List ℚ)) (t z : ℝ) :
    HasDerivAt (fieldEval f t) (fieldEval (fieldDerivY f) t z) z := by
  induction f generalizing z with
  | nil => exact hasDerivAt_const z 0
  | cons c cs ih =>
    have h := ((hasDerivAt_id z).mul (ih z)).const_add (coeffEval c t)
    refine h.congr_deriv ?_
    simp only [fieldDerivY, fieldEval_fieldAdd, fieldEval, coeffEval_nil, id]
    ring

/-- `l₀ + Σ_{k ≥ 1} |lₖ| hᵏ`, an upper bound of `l (u)` for `0 ≤ u ≤ h`. -/
def upperEval : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: l, h => a + h * absEval l h

/-- For `0 ≤ u ≤ h`, `coeffEval l u ≤ upperEval l h`. -/
theorem coeffEval_le_upperEval (l : List ℚ) {h : ℚ} {u : ℝ} (hu : 0 ≤ u) (huh : u ≤ h) :
    coeffEval l u ≤ upperEval l h := by
  cases l with
  | nil => simp [upperEval]
  | cons a l =>
    have hl := abs_coeffEval_le l hu huh
    have hh : (0 : ℝ) ≤ h := hu.trans huh
    have hA : (0 : ℝ) ≤ absEval l h := (abs_nonneg _).trans hl
    simp only [coeffEval_cons, upperEval, Rat.cast_add, Rat.cast_mul]
    have h1 : u * coeffEval l u ≤ |u * coeffEval l u| := le_abs_self _
    have h2 : |u * coeffEval l u| ≤ h * absEval l h := by
      rw [abs_mul, abs_of_nonneg hu]
      exact mul_le_mul huh hl (abs_nonneg _) hh
    linarith

/-- Real bounds `B`, `L` of `|f|` and of its Lipschitz constant in `y` on `S × [-Y, Y]`, for a
compact `S`. -/
theorem exists_fieldEval_bounds (f : List (List ℚ)) {S : Set ℝ} (hS : IsCompact S) (Y : ℝ) :
    ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ ∀ t ∈ S, ∀ z w : ℝ, |z| ≤ Y → |w| ≤ Y →
      |fieldEval f t z| ≤ B ∧ |fieldEval f t z - fieldEval f t w| ≤ L * |z - w| := by
  rcases lt_or_ge Y 0 with hY | hY
  · exact ⟨0, 0, le_rfl, le_rfl, fun t _ z w hz _ ↦ absurd (hz.trans_lt hY) (abs_nonneg z).not_gt⟩
  induction f with
  | nil => exact ⟨0, 0, le_rfl, le_rfl, fun t _ z w _ _ ↦ by simp [fieldEval]⟩
  | cons c cs ih =>
    obtain ⟨B, L, hB0, hL0, h⟩ := ih
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (continuous_coeffEval c).continuousOn
    have hC0 : ∀ t ∈ S, |coeffEval c t| ≤ max C 0 := fun t ht ↦
      (by simpa [Real.norm_eq_abs] using hC t ht : |coeffEval c t| ≤ C).trans (le_max_left _ _)
    refine ⟨max C 0 + Y * B, B + Y * L, by positivity, by positivity, fun t ht z w hz hw ↦ ?_⟩
    obtain ⟨hBz, hLzw⟩ := h t ht z w hz hw
    simp only [fieldEval]
    constructor
    · calc |coeffEval c t + z * fieldEval cs t z|
          ≤ |coeffEval c t| + |z| * |fieldEval cs t z| := by
            refine (abs_add_le _ _).trans ?_; rw [abs_mul]
        _ ≤ _ := by gcongr; exact hC0 t ht
    · have e : coeffEval c t + z * fieldEval cs t z - (coeffEval c t + w * fieldEval cs t w) =
          (z - w) * fieldEval cs t z + w * (fieldEval cs t z - fieldEval cs t w) := by ring
      rw [e]
      calc _ ≤ |z - w| * |fieldEval cs t z| + |w| * |fieldEval cs t z - fieldEval cs t w| := by
            refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
        _ ≤ |z - w| * B + Y * (L * |z - w|) := by gcongr
        _ = _ := by ring

/-! ### The exponential bound -/

/-- `Σ_{m < n} xᵐ / m!`. -/
def expPartial (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | m + 1 => expPartial x m + x ^ m / m.factorial

/-- The cast of `expPartial x n` to `ℝ` is `∑_{m < n} xᵐ / m!`. -/
theorem expPartial_cast (x : ℚ) (n : ℕ) :
    (expPartial x n : ℝ) = ∑ m ∈ Finset.range n, (x : ℝ) ^ m / m.factorial := by
  induction n with
  | zero => simp [expPartial]
  | succ n ih => rw [expPartial, Rat.cast_add, ih, Finset.sum_range_succ]; push_cast; ring

/-- An upper bound of `exp x` for `0 ≤ x ≤ 1` (`Real.exp_bound'` with 12 terms). -/
def expUpper (x : ℚ) : ℚ := expPartial x 12 + x ^ 12 * 13 / (Nat.factorial 12 * 12)

/-- For rational `x` with `0 ≤ x ≤ 1`, `exp x ≤ expUpper x`. -/
theorem exp_le_expUpper {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ expUpper x := by
  have h := Real.exp_bound' (x := (x : ℝ)) (by exact_mod_cast h0) (by exact_mod_cast h1)
    (n := 12) (by norm_num)
  rw [expUpper, Rat.cast_add, expPartial_cast]
  convert h using 2
  push_cast
  ring

/-! ### Pieces -/

/-- One piece of a certified solution: on `[start, start + length]` the approximation
`p (t) = poly (t - start)`, with the residual bound `residual`, an upper bound `lipschitz > 0` of
the slope `∂f/∂y` in the tube `|y - p| ≤ radius` (a one-sided Lipschitz constant),
`growth ≥ exp (lipschitz length)` and the deviation `error` at the end. -/
structure Piece where
  /-- The left end `tᵢ`. -/
  start : ℚ
  /-- The length `hᵢ`. -/
  length : ℚ
  /-- The approximation, a polynomial in `t - tᵢ`. -/
  poly : List ℚ
  /-- The bound `δᵢ` of the residual `p' - f (t, p)`. -/
  residual : ℚ
  /-- The one-sided Lipschitz constant `Kᵢ > 0`: an upper bound of `∂f/∂y` in the tube. -/
  lipschitz : ℚ
  /-- An upper bound `Eᵢ` of `exp (Kᵢ hᵢ)`. -/
  growth : ℚ
  /-- The radius `Rᵢ` of the tube. -/
  radius : ℚ
  /-- The bound `eᵢ₊₁` of the deviation on the piece. -/
  error : ℚ
  deriving Repr

/-- The residual polynomial `p' (tᵢ + u) - f (tᵢ + u, p (tᵢ + u))` in `u`. -/
def Piece.residualPoly (f : List (List ℚ)) (P : Piece) : List ℚ :=
  coeffAdd (coeffDeriv P.poly) (coeffScale (-1) (compose f P.start P.poly))

/-- The bound `absEval poly length + radius` of `|y|` in the tube. -/
def Piece.reach (P : Piece) : ℚ := absEval P.poly P.length + P.radius

/-- The checks of one piece entered with the deviation `δ₀`. -/
def Piece.check (f : List (List ℚ)) (δ₀ : ℚ) (P : Piece) : Bool :=
  decide (0 < P.length) && decide (0 < P.lipschitz) && decide (P.lipschitz * P.length ≤ 1) &&
  decide (0 ≤ δ₀) &&
  decide (absEval (P.residualPoly f) P.length ≤ P.residual) &&
  decide (upperEval (compose (fieldDerivY f) P.start P.poly) P.length +
    (lipBound P.start P.length P.reach (fieldDerivY f)).2 * P.radius ≤ P.lipschitz) &&
  decide (expUpper (P.lipschitz * P.length) ≤ P.growth) &&
  decide (δ₀ * P.growth + P.residual * (P.growth - 1) / P.lipschitz ≤ P.error) &&
  decide (P.error < P.radius)

/-- The Grönwall bound from the checked constants. -/
theorem Piece.gronwall_le {f : List (List ℚ)} {δ₀ : ℚ} {P : Piece} (hP : P.check f δ₀ = true) :
    gronwallBound δ₀ P.lipschitz P.residual P.length ≤ P.error := by
  simp only [Piece.check, Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hh, hK⟩, hKh⟩, hδ₀⟩, hres⟩, _⟩, hE⟩, he⟩, _⟩ := hP
  have hKR : (0 : ℝ) < P.lipschitz := by exact_mod_cast hK
  have hres0 : (0 : ℝ) ≤ P.residual := by
    have := absEval_nonneg (P.residualPoly f) hh.le
    exact_mod_cast this.trans hres
  have hexp : Real.exp (P.lipschitz * P.length) ≤ P.growth := by
    have := exp_le_expUpper (x := P.lipschitz * P.length) (by positivity) hKh
    push_cast at this
    exact this.trans (by exact_mod_cast hE)
  rw [gronwallBound_of_K_ne_0 hKR.ne']
  have he' : (δ₀ : ℝ) * P.growth + P.residual * (P.growth - 1) / P.lipschitz ≤ P.error := by
    exact_mod_cast he
  have hδ₀' : (0 : ℝ) ≤ δ₀ := by exact_mod_cast hδ₀
  calc (δ₀ : ℝ) * Real.exp (P.lipschitz * P.length) +
        P.residual / P.lipschitz * (Real.exp (P.lipschitz * P.length) - 1)
      ≤ δ₀ * P.growth + P.residual / P.lipschitz * (P.growth - 1) := by
        gcongr
    _ = δ₀ * P.growth + P.residual * (P.growth - 1) / P.lipschitz := by ring
    _ ≤ P.error := he'

/-- One checked piece: a solution of a field `G` that agrees with `f` on `|y| ≤ reach`, entered
within `δ₀` of `poly 0`, stays within `error` of the approximation on the piece and in
`|y| ≤ reach`. -/
theorem Piece.sound {f : List (List ℚ)} {G : ℝ → ℝ → ℝ} {δ₀ : ℚ} {P : Piece}
    (hP : P.check f δ₀ = true)
    (hG : ∀ t z : ℝ, |z| ≤ (P.reach : ℝ) → G t z = fieldEval f t z)
    {y : ℝ → ℝ} (hy : ContinuousOn y (Icc (P.start : ℝ) (P.start + P.length)))
    (hy' : ∀ t ∈ Ico (P.start : ℝ) (P.start + P.length),
      HasDerivWithinAt y (G t (y t)) (Ici t) t)
    (h0 : |y P.start - coeffEval P.poly 0| ≤ δ₀) :
    ∀ t ∈ Icc (P.start : ℝ) (P.start + P.length),
      |y t - coeffEval P.poly (t - P.start)| ≤ P.error ∧ |y t| ≤ P.reach := by
  have hgr := Piece.gronwall_le hP
  simp only [Piece.check, Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hh, hK⟩, _⟩, hδ₀⟩, hres⟩, hlip⟩, _⟩, _⟩, heR⟩ := hP
  have hhR : (0 : ℝ) < P.length := by exact_mod_cast hh
  have hKR : (0 : ℝ) < P.lipschitz := by exact_mod_cast hK
  have hres0 : (0 : ℝ) ≤ P.residual := by
    have := absEval_nonneg (P.residualPoly f) hh.le
    exact_mod_cast this.trans hres
  have hA0 := absEval_nonneg P.poly hh.le
  have hδ₀R : (0 : ℝ) ≤ δ₀ := by exact_mod_cast hδ₀
  have he0 : (0 : ℝ) ≤ P.error := by
    have := gronwallBound_mono hδ₀R hres0 hKR.le (show (0 : ℝ) ≤ P.length from hhR.le)
    rw [gronwallBound_x0] at this
    linarith
  have heRR : (P.error : ℝ) < P.radius := by exact_mod_cast heR
  have hreach : (P.reach : ℝ) = absEval P.poly P.length + P.radius := by
    simp [Piece.reach]
  have hreach0R : (0 : ℝ) ≤ P.reach := by
    rw [hreach]
    have : (0 : ℝ) ≤ ((absEval P.poly P.length : ℚ) : ℝ) := by exact_mod_cast hA0
    linarith
  have hreach0 : (0 : ℚ) ≤ P.reach := by exact_mod_cast hreach0R
  set p : ℝ → ℝ := fun t ↦ coeffEval P.poly (t - P.start) with hp
  set p' : ℝ → ℝ := fun t ↦ coeffEval (coeffDeriv P.poly) (t - P.start) with hp'
  have hpd : ∀ t, HasDerivAt p (p' t) t := fun t ↦
    (hasDerivAt_coeffEval P.poly (t - P.start)).comp_sub_const t (P.start : ℝ)
  have hpc : ContinuousOn p (Icc (P.start : ℝ) (P.start + P.length)) :=
    ((continuous_coeffEval _).comp (continuous_sub_right _)).continuousOn
  have hpb : ∀ t ∈ Icc (P.start : ℝ) (P.start + P.length), |p t| ≤ absEval P.poly P.length :=
    fun t ht ↦ abs_coeffEval_le P.poly (by linarith [ht.1]) (by linarith [ht.2])
  have hpr : ∀ t ∈ Icc (P.start : ℝ) (P.start + P.length), |p t| ≤ P.reach := fun t ht ↦ by
    rw [hreach]; linarith [hpb t ht]
  have hresid : ∀ t ∈ Ico (P.start : ℝ) (P.start + P.length),
      |p' t - G t (p t)| ≤ P.residual := by
    intro t ht
    have htI : t ∈ Icc (P.start : ℝ) (P.start + P.length) := Ico_subset_Icc_self ht
    rw [hG t (p t) (hpr t htI)]
    have hb := abs_coeffEval_le (P.residualPoly f) (u := t - P.start) (h := P.length)
      (by linarith [ht.1]) (by linarith [ht.2])
    have e : coeffEval (P.residualPoly f) (t - P.start) = p' t - fieldEval f t (p t) := by
      simp only [Piece.residualPoly, coeffEval_coeffAdd, coeffEval_coeffScale,
        coeffEval_compose, p, p']
      rw [show (P.start : ℝ) + (t - P.start) = t by ring]
      push_cast
      ring
    rw [← e]
    exact hb.trans (by exact_mod_cast hres)
  have hlipG : ∀ t ∈ Ico (P.start : ℝ) (P.start + P.length), ∀ z w, |z - p t| ≤ P.radius →
      |w - p t| ≤ P.radius → w ≤ z → G t z - G t w ≤ P.lipschitz * (z - w) := by
    intro t ht z w hz hw hwz
    have htI : t ∈ Icc (P.start : ℝ) (P.start + P.length) := Ico_subset_Icc_self ht
    have hu0 : 0 ≤ t - P.start := by linarith [ht.1]
    have hu1 : t - P.start ≤ (P.length : ℝ) := by linarith [ht.2]
    have hin : ∀ ξ, |ξ - p t| ≤ P.radius → |ξ| ≤ P.reach := fun ξ hξ ↦ by
      rw [hreach]
      have := abs_sub_abs_le_abs_sub ξ (p t)
      linarith [hpb t htI]
    rw [hG t z (hin z hz), hG t w (hin w hw)]
    -- The derivative `∂f/∂y` is at most `lipschitz` in the tube.
    have hbound : ∀ ξ, |ξ - p t| ≤ P.radius →
        fieldEval (fieldDerivY f) t ξ ≤ P.lipschitz := by
      intro ξ hξ
      have hl := (lipBound_sound (fieldDerivY f) (t₀ := P.start) (h := P.length) hreach0 hu0 hu1
        (hin ξ hξ) (hpr t htI)).2
      have hg := coeffEval_le_upperEval (compose (fieldDerivY f) P.start P.poly) hu0 hu1
      rw [coeffEval_compose] at hg
      rw [show (P.start : ℝ) + (t - P.start) = t by ring] at hl hg
      have hL0 := (lipBound_nonneg (fieldDerivY f) (t₀ := P.start) hh.le hreach0).2
      have hL0' : (0 : ℝ) ≤ (lipBound P.start P.length P.reach (fieldDerivY f)).2 := by
        exact_mod_cast hL0
      have hlipR : ((upperEval (compose (fieldDerivY f) P.start P.poly) P.length : ℚ) : ℝ) +
          (lipBound P.start P.length P.reach (fieldDerivY f)).2 * P.radius ≤ P.lipschitz := by
        exact_mod_cast hlip
      have h1 := le_abs_self (fieldEval (fieldDerivY f) t ξ - fieldEval (fieldDerivY f) t (p t))
      have h2 : ((lipBound P.start P.length P.reach (fieldDerivY f)).2 : ℝ) * |ξ - p t| ≤
          (lipBound P.start P.length P.reach (fieldDerivY f)).2 * P.radius :=
        mul_le_mul_of_nonneg_left hξ hL0'
      simp only [p] at hg h1 hl h2 ⊢
      linarith
    have hD : Convex ℝ (Icc (p t - P.radius) (p t + P.radius)) := convex_Icc _ _
    have hmem : ∀ ξ, ξ ∈ Icc (p t - P.radius) (p t + P.radius) ↔ |ξ - p t| ≤ P.radius :=
      fun ξ ↦ by rw [abs_le]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    exact hD.image_sub_le_mul_sub_of_deriv_le
      (fun ξ _ ↦ (hasDerivAt_fieldEval f t ξ).continuousAt.continuousWithinAt)
      (fun ξ _ ↦ (hasDerivAt_fieldEval f t ξ).differentiableAt.differentiableWithinAt)
      (fun ξ hξ ↦ by
        rw [(hasDerivAt_fieldEval f t ξ).deriv]
        exact hbound ξ ((hmem ξ).1 (interior_subset hξ)))
      w ((hmem w).2 hw) z ((hmem z).2 hz) hwz
  have hR : gronwallBound δ₀ P.lipschitz P.residual
      ((P.start : ℝ) + P.length - P.start) < P.radius := by
    rw [show (P.start : ℝ) + P.length - P.start = P.length by ring]
    exact hgr.trans_lt heRR
  have htube := abs_sub_le_gronwallBound_of_tube (F := G) (p := p) (p' := p') hy hy' hpc
    (fun t _ ↦ (hpd t).hasDerivWithinAt) hresid hlipG
    (by simpa [p] using h0) hKR.le hres0 hR
  intro t ht
  have h1 := htube t ht
  have hmono := gronwallBound_mono hδ₀R hres0 hKR.le
    (show t - P.start ≤ (P.length : ℝ) by linarith [ht.2])
  have hdev : |y t - p t| ≤ P.error := h1.trans (hmono.trans hgr)
  refine ⟨hdev, ?_⟩
  rw [hreach]
  have := abs_sub_abs_le_abs_sub (y t) (p t)
  linarith [hpb t ht]

/-- The largest `reach` of the pieces. -/
def boxOf : List Piece → ℚ
  | [] => 0
  | P :: ps => max P.reach (boxOf ps)

/-- Check the pieces in order from time `t`, where the solution is within `r` of `c`; the end
time and the nodes `(time, centre, radius)` with the invariant at each piece end. -/
def run (f : List (List ℚ)) : ℚ → ℚ → ℚ → List Piece → Option (ℚ × List (ℚ × ℚ × ℚ))
  | t, c, r, [] => some (t, [(t, c, r)])
  | t, c, r, P :: ps =>
    if P.start = t ∧ P.check f (r + |c - coeffEvalRat P.poly 0|) = true then
      (run f (t + P.length) (coeffEvalRat P.poly P.length) P.error ps).map
        fun en ↦ (en.1, (t, c, r) :: en.2)
    else none

/-- If `run f t c r ps = some (e, ns)`, the end time `e` is at least the start time `t`. -/
theorem run_le {f : List (List ℚ)} :
    ∀ (ps : List Piece) (t c r e : ℚ) (ns : List (ℚ × ℚ × ℚ)),
      run f t c r ps = some (e, ns) → t ≤ e
  | [], t, c, r, e, ns, h => by
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.le
  | P :: ps, t, c, r, e, ns, h => by
    simp only [run] at h
    split_ifs at h with hc
    obtain ⟨⟨e', ns'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h2
    have hle := run_le ps _ _ _ _ _ h1
    have hpos : 0 < P.length := by
      have := hc.2
      simp only [Piece.check, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.1.1.1.1.1.1.1
    rw [← h2.1]
    linarith

/-- Soundness of `run`: let `run f t c r ps = some (e, ns)`, let the field `G` agree with
`fieldEval f` on `|z| ≤ boxOf ps`, and let `y` have derivative `G s (y s)` within `[t, e]` at every
`s ∈ [t, e]`, with `|y t - c| ≤ r`. Then `|y τ - c'| ≤ r'` at every node `(τ, c', r')` of `ns`, and
`|y s| ≤ max (|c| + r) (boxOf ps)` for every `s ∈ [t, e]`. -/
theorem run_sound {f : List (List ℚ)} {G : ℝ → ℝ → ℝ} :
    ∀ (ps : List Piece) (t c r e : ℚ) (ns : List (ℚ × ℚ × ℚ)),
      run f t c r ps = some (e, ns) →
      (∀ s z : ℝ, |z| ≤ (boxOf ps : ℝ) → G s z = fieldEval f s z) →
      ∀ y : ℝ → ℝ, (∀ s ∈ Icc (t : ℝ) e, HasDerivWithinAt y (G s (y s)) (Icc (t : ℝ) e) s) →
      |y t - c| ≤ r →
      (∀ n ∈ ns, |y n.1 - n.2.1| ≤ n.2.2) ∧
        ∀ s ∈ Icc (t : ℝ) e, |y s| ≤ max (|(c : ℝ)| + r) (boxOf ps)
  | [], t, c, r, e, ns, h, _, y, _, h0 => by
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simpa using h0, fun s hs ↦ ?_⟩
    have hst : s = t := le_antisymm hs.2 hs.1
    rw [hst]
    have := abs_sub_abs_le_abs_sub (y t) c
    exact le_max_of_le_left (by linarith)
  | P :: ps, t, c, r, e, ns, h, hG, y, hy, h0 => by
    have hrun := h
    simp only [run] at h
    split_ifs at h with hc
    obtain ⟨hst, hchk⟩ := hc
    obtain ⟨⟨e', ns'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    have hle : t + P.length ≤ e' := run_le ps _ _ _ _ _ h1
    have hleR : (t : ℝ) + P.length ≤ e' := by exact_mod_cast hle
    have hstR : (P.start : ℝ) = t := by exact_mod_cast hst
    have hpos : (0 : ℝ) < P.length := by
      have := hchk
      simp only [Piece.check, Bool.and_eq_true, decide_eq_true_eq] at this
      exact_mod_cast this.1.1.1.1.1.1.1.1
    have hboxP : P.reach ≤ boxOf (P :: ps) := le_max_left _ _
    have hboxs : boxOf ps ≤ boxOf (P :: ps) := le_max_right _ _
    -- The piece.
    have hpiece := Piece.sound (G := G) hchk
      (fun s z hz ↦ hG s z (hz.trans (by exact_mod_cast hboxP))) (y := y)
      (by
        rw [hstR]
        intro s hs
        exact ((hy s ⟨hs.1, hs.2.trans hleR⟩).continuousWithinAt).mono
          (Icc_subset_Icc_right hleR))
      (by
        rw [hstR]
        intro s hs
        exact (hy s ⟨hs.1, hs.2.le.trans hleR⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ⟨hs.1, hs.2.trans_le hleR⟩))
      (by
        rw [hstR]
        have e0 : coeffEval P.poly 0 = ((coeffEvalRat P.poly 0 : ℚ) : ℝ) := by
          rw [← coeffEval_ratCast]; simp
        rw [e0]
        have := abs_sub_le (y t) c (coeffEvalRat P.poly 0)
        push_cast
        linarith)
    rw [hstR] at hpiece
    -- The rest.
    have hend := hpiece (t + P.length) ⟨by linarith, le_rfl⟩
    have hrest := run_sound ps _ _ _ _ _ h1
      (fun s z hz ↦ hG s z (hz.trans (by exact_mod_cast hboxs))) y
      (by
        intro s hs
        push_cast at hs
        exact (hy s ⟨by linarith [hs.1], hs.2⟩).mono (Icc_subset_Icc_left (by push_cast; linarith)))
      (by
        push_cast
        rw [← coeffEval_ratCast]
        simpa using hend.1)
    refine ⟨?_, ?_⟩
    · intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact h0
      · exact hrest.1 n hn
    · intro s hs
      have hc' : |((coeffEvalRat P.poly P.length : ℚ) : ℝ)| + P.error ≤ P.reach := by
        have hb := abs_coeffEval_le P.poly (u := (P.length : ℝ)) (h := P.length) hpos.le le_rfl
        rw [coeffEval_ratCast] at hb
        have heR : (P.error : ℝ) < P.radius := by
          have := hchk
          simp only [Piece.check, Bool.and_eq_true, decide_eq_true_eq] at this
          exact_mod_cast this.2
        have : (P.reach : ℝ) = absEval P.poly P.length + P.radius := by simp [Piece.reach]
        linarith
      rcases le_total s (t + P.length) with hs' | hs'
      · have h1 := (hpiece s ⟨hs.1, hs'⟩).2
        have h2 : (P.reach : ℝ) ≤ boxOf (P :: ps) := by exact_mod_cast hboxP
        exact le_max_of_le_right (h1.trans h2)
      · have := hrest.2 s ⟨by push_cast; exact hs', hs.2⟩
        have h2 : (P.reach : ℝ) ≤ boxOf (P :: ps) := by exact_mod_cast hboxP
        have h3 : ((boxOf ps : ℚ) : ℝ) ≤ boxOf (P :: ps) := by exact_mod_cast hboxs
        refine this.trans (max_le ?_ ?_)
        · exact le_max_of_le_right (hc'.trans h2)
        · exact le_max_of_le_right h3

/-- `z` clamped to `[-Y, Y]`. -/
noncomputable def clamp (Y z : ℝ) : ℝ := max (-Y) (min Y z)

/-- For `0 ≤ Y`, `|clamp Y z| ≤ Y`. -/
theorem abs_clamp_le {Y : ℝ} (hY : 0 ≤ Y) (z : ℝ) : |clamp Y z| ≤ Y := by
  unfold clamp
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-- For `|z| ≤ Y`, `clamp Y z = z`. -/
theorem clamp_of_abs_le {Y z : ℝ} (hz : |z| ≤ Y) : clamp Y z = z := by
  unfold clamp
  rw [abs_le] at hz
  rw [min_eq_right hz.2, max_eq_right hz.1]

/-- Clamping does not increase distances: `|clamp Y z - clamp Y w| ≤ |z - w|` for every `Y`. -/
theorem abs_clamp_sub_clamp_le (Y z w : ℝ) : |clamp Y z - clamp Y w| ≤ |z - w| := by
  unfold clamp
  have h1 := abs_max_sub_max_le_max (-Y) (min Y z) (-Y) (min Y w)
  have h2 := abs_min_sub_min_le_max Y z Y w
  simp only [sub_self, abs_zero] at h1 h2
  exact h1.trans (max_le (abs_nonneg _) (h2.trans (max_le (abs_nonneg _) le_rfl)))

/-- Existence on `[a, b]` from a successful run: the field clamped to the box is globally
Lipschitz, so Picard-Lindelöf gives a solution of it, and the run keeps that solution in the
box, where the clamped field is the field. When `b ≤ a` the interval has at most one point and
any function with `y a = y₀` is a solution. -/
theorem exists_solution {f : List (List ℚ)} {a b y₀ : ℚ} {ps : List Piece}
    {ns : List (ℚ × ℚ × ℚ)} (hrun : run f a y₀ 0 ps = some (b, ns)) :
    ∃ y : ℝ → ℝ, y a = y₀ ∧ IsIntegralCurveOn y (fieldEval f) (Icc (a : ℝ) b) := by
  rcases lt_or_ge a b with hab | hba
  swap
  · refine ⟨fun _ ↦ (y₀ : ℝ), rfl, fun t _ ↦ ?_⟩
    exact hasDerivWithinAt_iff_hasFDerivWithinAt.mpr
      (.of_subsingleton (Set.subsingleton_Icc_of_ge (by exact_mod_cast hba)))
  set Y : ℝ := max |(y₀ : ℝ)| (boxOf ps) with hYdef
  have hY0 : 0 ≤ Y := le_max_of_le_left (by positivity)
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  obtain ⟨B, L, hB0, hL0, hbd⟩ :=
    exists_fieldEval_bounds f (isCompact_Icc : IsCompact (Icc (a : ℝ) b)) Y
  set G : ℝ → ℝ → ℝ := fun t z ↦ fieldEval f t (clamp Y z) with hGdef
  have hPL : IsPicardLindelof G (tmin := a) (tmax := b) ⟨a, left_mem_Icc.2 habR.le⟩ (y₀ : ℝ)
      ⟨B * (b - a), by have : (0 : ℝ) ≤ b - a := by linarith
                       positivity⟩ 0 ⟨B, hB0⟩ ⟨L, hL0⟩ := by
    refine ⟨fun t ht ↦ ?_, fun x _ ↦ ?_, fun t ht x _ ↦ ?_, ?_⟩
    · refine LipschitzOnWith.of_dist_le_mul fun z _ w _ ↦ ?_
      have := (hbd t ht (clamp Y z) (clamp Y w) (abs_clamp_le hY0 z) (abs_clamp_le hY0 w)).2
      simp only [Real.dist_eq, G]
      exact this.trans (mul_le_mul_of_nonneg_left (abs_clamp_sub_clamp_le Y z w) hL0)
    · exact (continuous_fieldEval_left f _).continuousOn
    · have := (hbd t ht (clamp Y x) (clamp Y x) (abs_clamp_le hY0 x) (abs_clamp_le hY0 x)).1
      change |fieldEval f t (clamp Y x)| ≤ B
      exact this
    · change B * max ((b : ℝ) - a) ((a : ℝ) - a) ≤ B * (b - a) - 0
      rw [max_eq_left (by linarith), sub_zero]
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hGf : ∀ s z : ℝ, |z| ≤ (boxOf ps : ℝ) → G s z = fieldEval f s z := fun s z hz ↦ by
    simp only [G]
    rw [clamp_of_abs_le (hz.trans (le_max_right _ _))]
  have hsound := run_sound (G := G) ps a y₀ 0 b ns hrun hGf α hα (by simp [hα0])
  simp only [Rat.cast_zero, add_zero] at hsound
  refine ⟨α, hα0, fun t ht ↦ ?_⟩
  have hbox := hsound.2 t ht
  have : G t (α t) = fieldEval f t (α t) := by
    simp only [G]; rw [clamp_of_abs_le hbox]
  rw [← this]
  exact hα t ht

/-- Every solution of the field stays in the box of a successful run. -/
theorem abs_le_box {f : List (List ℚ)} {a b y₀ : ℚ} {ps : List Piece}
    {ns : List (ℚ × ℚ × ℚ)} (hrun : run f a y₀ 0 ps = some (b, ns)) {y : ℝ → ℝ}
    (hy0 : y a = y₀) (hy : IsIntegralCurveOn y (fieldEval f) (Icc (a : ℝ) b)) :
    (∀ n ∈ ns, |y n.1 - n.2.1| ≤ n.2.2) ∧
      ∀ t ∈ Icc (a : ℝ) b, |y t| ≤ max |(y₀ : ℝ)| (boxOf ps) := by
  have := run_sound (G := fieldEval f) ps a y₀ 0 b ns hrun (fun _ _ _ ↦ rfl) y hy (by simp [hy0])
  simpa only [Rat.cast_zero, add_zero] using this

/-- Uniqueness on `[a, b]`: two solutions of the field with the same value at `a` agree. Both
are continuous on the compact `[a, b]`, hence bounded, and the field is Lipschitz on bounded
sets; no successful run is needed. -/
theorem eqOn_of_isIntegralCurveOn {f : List (List ℚ)} {a b y₀ : ℚ} {y z : ℝ → ℝ}
    (hy0 : y a = y₀) (hy : IsIntegralCurveOn y (fieldEval f) (Icc (a : ℝ) b))
    (hz0 : z a = y₀) (hz : IsIntegralCurveOn z (fieldEval f) (Icc (a : ℝ) b)) :
    EqOn y z (Icc (a : ℝ) b) := by
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc : IsCompact (Icc (a : ℝ) b)).exists_bound_of_continuousOn
    hy.continuousOn
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc : IsCompact (Icc (a : ℝ) b)).exists_bound_of_continuousOn
    hz.continuousOn
  set Y : ℝ := max (max C₁ C₂) 0
  obtain ⟨B, L, hB0, hL0, hbd⟩ :=
    exists_fieldEval_bounds f (isCompact_Icc : IsCompact (Icc (a : ℝ) b)) Y
  have hyb : ∀ t ∈ Icc (a : ℝ) b, |y t| ≤ Y := fun t ht ↦ by
    have := hC₁ t ht
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hzb : ∀ t ∈ Icc (a : ℝ) b, |z t| ≤ Y := fun t ht ↦ by
    have := hC₂ t ht
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_right _ _).trans (le_max_left _ _))
  have hlip : ∀ t ∈ Ico (a : ℝ) b, LipschitzOnWith ⟨L, hL0⟩ (fieldEval f t) (Icc (-Y) Y) := by
    intro t ht
    refine LipschitzOnWith.of_dist_le_mul fun u hu w hw ↦ ?_
    have hu' : |u| ≤ Y := abs_le.2 hu
    have hw' : |w| ≤ Y := abs_le.2 hw
    rw [Real.dist_eq, Real.dist_eq]
    exact (hbd t (Ico_subset_Icc_self ht) u w hu' hw').2
  have hderiv : ∀ {g : ℝ → ℝ}, IsIntegralCurveOn g (fieldEval f) (Icc (a : ℝ) b) →
      ∀ t ∈ Ico (a : ℝ) b, HasDerivWithinAt g (fieldEval f t (g t)) (Ici t) t :=
    fun hg t ht ↦ (hg t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  have hcont : ∀ {g : ℝ → ℝ}, IsIntegralCurveOn g (fieldEval f) (Icc (a : ℝ) b) →
      ContinuousOn g (Icc (a : ℝ) b) := fun hg ↦ hg.continuousOn
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ ↦ Icc (-Y) Y) hlip (hcont hy)
    (hderiv hy) (fun t ht ↦ abs_le.1 (hyb t (Ico_subset_Icc_self ht))) (hcont hz) (hderiv hz)
    (fun t ht ↦ abs_le.1 (hzb t (Ico_subset_Icc_self ht))) (by rw [hy0, hz0])

/-- The whole check: `a < b`, the pieces run from `a` (where the solution is `y₀`) to `b`, and
every output `(τ, lo, hi)` is a node `(τ, c, r)` with `[c - r, c + r] ⊆ [lo, hi]`. -/
def check (f : List (List ℚ)) (a b y₀ : ℚ) (ps : List Piece) (outs : List (ℚ × ℚ × ℚ)) :
    Bool :=
  decide (a < b) &&
    match run f a y₀ 0 ps with
    | some (e, ns) => decide (e = b) && outs.all fun o ↦ ns.any fun n ↦
        decide (n.1 = o.1) && decide (o.2.1 ≤ n.2.1 - n.2.2) && decide (n.2.1 + n.2.2 ≤ o.2.2)
    | none => false

/-- Soundness of the check: a solution of `y' = f (t, y)`, `y a = y₀` exists on `[a, b]`, it is
unique there, and every solution lies in `[lo, hi]` at each output time `τ`. -/
theorem check_sound {f : List (List ℚ)} {a b y₀ : ℚ} {ps : List Piece}
    {outs : List (ℚ × ℚ × ℚ)} (h : check f a b y₀ ps outs = true) :
    (∃ y : ℝ → ℝ, y a = y₀ ∧ IsIntegralCurveOn y (fieldEval f) (Icc (a : ℝ) b)) ∧
    (∀ y z : ℝ → ℝ, y a = y₀ → IsIntegralCurveOn y (fieldEval f) (Icc (a : ℝ) b) →
      z a = y₀ → IsIntegralCurveOn z (fieldEval f) (Icc (a : ℝ) b) → EqOn y z (Icc (a : ℝ) b)) ∧
    (∀ y : ℝ → ℝ, y a = y₀ → IsIntegralCurveOn y (fieldEval f) (Icc (a : ℝ) b) →
      ∀ o ∈ outs, (o.2.1 : ℝ) ≤ y o.1 ∧ y o.1 ≤ o.2.2) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, h⟩ := h
  split at h
  · rename_i e ns hrun
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at h
    obtain ⟨rfl, hout⟩ := h
    refine ⟨exists_solution hrun, fun y z hy0 hy hz0 hz ↦ eqOn_of_isIntegralCurveOn hy0 hy hz0 hz,
      fun y hy0 hy o ho ↦ ?_⟩
    obtain ⟨n, hn, ⟨h1, h2⟩, h3⟩ := hout o ho
    have hb := (abs_le_box hrun hy0 hy).1 n hn
    rw [abs_le] at hb
    have h2' : (o.2.1 : ℝ) ≤ n.2.1 - n.2.2 := by exact_mod_cast h2
    have h3' : (n.2.1 : ℝ) + n.2.2 ≤ o.2.2 := by exact_mod_cast h3
    rw [← h1]
    constructor <;> linarith
  · exact absurd h (by simp)

end CAS.Calculus.NDSolve

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import CAS.Continuum.Quadrature.Gaussian.Algebra

/-!
# Weighted polynomial integration

`polynomialIntegral a b w hw` is the linear functional `p ↦ ∫_a^b p x * w x` on real
polynomials, for a weight `w` continuous on the interval. When `a < b` and `w` is nonnegative
on `[a, b]` and strictly positive on `(a, b)`, `polynomialIntegral_square_pos_on_interior` shows
the functional is positive on nonzero squares. Its case of a weight strictly positive on
`[a, b]`, `polynomialIntegral_square_pos`, is the hypothesis the algebraic results of `Algebra`
and `Orthogonal` need.
-/

@[expose] public section

open Polynomial MeasureTheory Set

namespace CAS.Continuum

noncomputable section

/-- The functional `p ↦ ∫_a^b p x * w x` on `ℝ[X]`, linear in `p`. -/
def polynomialIntegral (a b : ℝ) (w : ℝ → ℝ)
    (hw : ContinuousOn w (uIcc a b)) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x in a..b, p.eval x * w x
  map_add' p q := by
    simp only [Polynomial.eval_add, add_mul]
    exact intervalIntegral.integral_add
      (p.continuous.continuousOn.mul hw).intervalIntegrable
      (q.continuous.continuousOn.mul hw).intervalIntegrable
  map_smul' c p := by
    simp only [Polynomial.eval_smul, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact intervalIntegral.integral_const_mul c _

/-- The integral of `p ^ 2` against `w` over `[a, b]` is strictly positive for `p ≠ 0` when
`w` is nonnegative on `[a, b]` and strictly positive on the open interval `(a, b)`. -/
theorem polynomialIntegral_square_pos_on_interior {a b : ℝ} (hab : a < b)
    (w : ℝ → ℝ) (hw : ContinuousOn w (uIcc a b))
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hwpos : ∀ x ∈ Ioo a b, 0 < w x)
    (p : ℝ[X]) (hp : p ≠ 0) :
    0 < polynomialIntegral a b w hw (p ^ 2) := by
  obtain ⟨x, hx, hpx⟩ : ∃ x ∈ Ioo a b, p.eval x ≠ 0 := by
    by_contra! h
    exact hp (eq_zero_of_infinite_isRoot p ((Set.Ioo_infinite hab).mono fun x hx ↦ h x hx))
  have hw' : ContinuousOn w (Icc a b) := by simpa [uIcc_of_le hab.le] using hw
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ : ℝ ↦ 0) (g := fun y ↦ p.eval y ^ 2 * w y) hab
    continuousOn_const (p.continuous.pow 2 |>.continuousOn.mul hw')
    (fun y hy ↦ mul_nonneg (sq_nonneg _) (hw0 y ⟨hy.1.le, hy.2⟩))
    ⟨x, ⟨hx.1.le, hx.2.le⟩, mul_pos (sq_pos_of_ne_zero hpx) (hwpos x hx)⟩
  simpa [polynomialIntegral, eval_pow] using h

/-- The integral of `p ^ 2` against `w` over `[a, b]` is strictly positive when `a < b`, `w`
is continuous and strictly positive on `[a, b]`, and `p ≠ 0`. -/
theorem polynomialIntegral_square_pos {a b : ℝ} (hab : a < b) (w : ℝ → ℝ)
    (hw : ContinuousOn w (uIcc a b)) (hwpos : ∀ x ∈ Icc a b, 0 < w x)
    (p : ℝ[X]) (hp : p ≠ 0) :
    0 < polynomialIntegral a b w hw (p ^ 2) :=
  polynomialIntegral_square_pos_on_interior hab w hw (fun x hx ↦ (hwpos x hx).le)
    (fun x hx ↦ hwpos x (Ioo_subset_Icc_self hx)) p hp

/-- The Christoffel numbers for a continuous strictly positive weight on `[a, b]` are
positive, provided the nodal polynomial is orthogonal to every polynomial of degree below
`n`. Specializes `gaussian_weight_pos`. -/
theorem integral_gaussian_weight_pos {a b : ℝ} (hab : a < b) (w : ℝ → ℝ)
    (hw : ContinuousOn w (uIcc a b)) (hwpos : ∀ x ∈ Icc a b, 0 < w x)
    {n : ℕ} (hn : 0 < n) (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (horth : ∀ q : ℝ[X], q.natDegree < n →
      polynomialIntegral a b w hw (Lagrange.nodal Finset.univ nodes * q) = 0)
    (i : Fin n) :
    0 < interpolatoryWeight (polynomialIntegral a b w hw) nodes i :=
  gaussian_weight_pos hn _ nodes hnodes horth (polynomialIntegral_square_pos hab w hw hwpos) i

end
end CAS.Continuum

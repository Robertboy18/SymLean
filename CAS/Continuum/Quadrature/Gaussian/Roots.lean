/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.FieldTheory.Perfect
public import CAS.Continuum.Quadrature.Gaussian.Orthogonal

/-!
# Roots of orthogonal polynomials

Let `p` be orthogonal to every polynomial of lower degree for a continuous positive weight
`w` on `[a, b]`, `a < b`. Every nonconstant factor `q` of `p` has a root in `[a, b]`: if
not, `q` has constant sign there, and writing `p = q * r` the integral of `p * r = q * r ^ 2`
against `w` is nonzero, contradicting orthogonality. Positivity of squares rules out
repeated factors in the same way (`orthogonal_squarefree`). Hence `p` splits over `ℝ` with
`deg p` distinct roots (`orthogonal_splits`), and a separate argument places them all in the
open interval `(a, b)` (`orthogonal_root_mem_Ioo`).

## References

* Gábor Szegő, *Orthogonal Polynomials*, 4th ed., Colloquium Publications 23, American
  Mathematical Society, Providence, 1975, <https://doi.org/10.1090/coll/023>.
-/

@[expose] public section

namespace CAS.Continuum

open Polynomial MeasureTheory Set

noncomputable section

/-- A continuous function with no zero on `[a, b]` is either positive throughout or negative
throughout, by the intermediate value theorem. -/
theorem constant_sign_of_no_zero {a b : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hn : ∀ x ∈ Icc a b, f x ≠ 0) :
    (∀ x ∈ Icc a b, 0 < f x) ∨ (∀ x ∈ Icc a b, f x < 0) := by
  by_cases hab : a ≤ b
  swap
  · exact Or.inl fun x hx ↦ absurd (hx.1.trans hx.2) hab
  rcases lt_or_gt_of_ne (hn a ⟨le_rfl, hab⟩) with ha | ha
  · refine Or.inr fun x hx ↦ (hn x hx).lt_of_le ?_
    by_contra h
    obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc hx.1 hf.continuousOn ⟨ha.le, (not_le.1 h).le⟩
    exact hn y ⟨hy.1, hy.2.trans hx.2⟩ hy0
  · refine Or.inl fun x hx ↦ (hn x hx).symm.lt_of_le ?_
    by_contra h
    obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc' hx.1 hf.continuousOn ⟨(not_le.1 h).le, ha.le⟩
    exact hn y ⟨hy.1, hy.2.trans hx.2⟩ hy0

/-- If `q` has no zero on `[a, b]` and `r ≠ 0`, the integral of `q * r ^ 2` against a
continuous positive weight is nonzero. `q` has constant sign, so `q * w` or `-q * w` is a
positive weight and `polynomialIntegral_square_pos` applies to `r`. -/
theorem polynomialIntegral_mul_square_ne_zero {a b : ℝ} (hab : a < b)
    (w : ℝ → ℝ) (hw : ContinuousOn w (uIcc a b))
    (hwpos : ∀ x ∈ Icc a b, 0 < w x)
    (q r : ℝ[X]) (hq : ∀ x ∈ Icc a b, q.eval x ≠ 0) (hr : r ≠ 0) :
    polynomialIntegral a b w hw (q * r ^ 2) ≠ 0 := by
  have hpos (s : ℝ[X]) (hs : ∀ x ∈ Icc a b, 0 < s.eval x) :
      0 < polynomialIntegral a b w hw (s * r ^ 2) := by
    have h := polynomialIntegral_square_pos hab (fun x ↦ s.eval x * w x)
      (s.continuous.continuousOn.mul hw) (fun x hx ↦ mul_pos (hs x hx) (hwpos x hx))
      r hr
    convert h using 1
    simp only [polynomialIntegral, LinearMap.coe_mk, AddHom.coe_mk, eval_mul, eval_pow]
    congr 1
    ext x
    ring
  rcases constant_sign_of_no_zero q.continuous hq with hqpos | hqneg
  · exact ne_of_gt (hpos q hqpos)
  · simpa only [neg_mul, map_neg, neg_ne_zero] using
      (hpos (-q) fun x hx ↦ by simpa using hqneg x hx).ne'

/-- Every nonconstant divisor `q` of an orthogonal polynomial `p` has a root in `[a, b]`.
Write `p = q * r`, so `deg r < deg p` and orthogonality gives `∫ p r w = ∫ q r² w = 0`,
which `polynomialIntegral_mul_square_ne_zero` forbids if `q` has no zero. -/
theorem orthogonal_factor_has_root {a b : ℝ} (hab : a < b)
    (w : ℝ → ℝ) (hw : ContinuousOn w (uIcc a b))
    (hwpos : ∀ x ∈ Icc a b, 0 < w x)
    (p : ℝ[X]) (hp : p ≠ 0)
    (horth : ∀ r : ℝ[X], r.degree < p.degree →
      polynomialIntegral a b w hw (p * r) = 0)
    (q : ℝ[X]) (hq : 0 < q.natDegree) (hqp : q ∣ p) :
    ∃ x ∈ Icc a b, q.eval x = 0 := by
  obtain ⟨r, hpr⟩ := hqp
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hr : r ≠ 0 := by intro h; simp [hpr, h] at hp
  have hdegree : r.degree < p.degree := by
    rw [hpr, degree_mul, degree_eq_natDegree hr, degree_eq_natDegree hq0]
    exact_mod_cast (show r.natDegree < q.natDegree + r.natDegree by omega)
  by_contra! hn
  apply polynomialIntegral_mul_square_ne_zero hab w hw hwpos q r hn hr
  rw [← horth r hdegree, hpr]
  congr 1
  ring

/-- A polynomial orthogonal to all polynomials of lower degree, for a functional positive on
nonzero squares, is squarefree. If `p = q ^ 2 * r` with `q` nonconstant then
`L ((q * r) ^ 2) = L (p * r) = 0`, contradicting positivity. -/
theorem orthogonal_squarefree (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hpositive : ∀ q : ℝ[X], q ≠ 0 → 0 < L (q ^ 2))
    (p : ℝ[X]) (hp : p ≠ 0)
    (horth : ∀ r : ℝ[X], r.degree < p.degree → L (p * r) = 0) :
    Squarefree p := by
  intro q ⟨r, hpr⟩
  by_contra hunit
  have hq0 : q ≠ 0 := by intro h; simp [hpr, h] at hp
  have hr : r ≠ 0 := by intro h; simp [hpr, h] at hp
  have hqpos : 0 < q.natDegree := Nat.pos_of_ne_zero fun h ↦ hunit
    (isUnit_iff_degree_eq_zero.mpr (by exact_mod_cast (degree_eq_iff_natDegree_eq hq0).2 h))
  have hdegree : r.degree < p.degree := by
    rw [hpr, degree_mul, degree_mul,
      degree_eq_natDegree hq0, degree_eq_natDegree hr]
    exact_mod_cast (show r.natDegree < q.natDegree + q.natDegree + r.natDegree by omega)
  have h := hpositive (q * r) (mul_ne_zero hq0 hr)
  rw [show (q * r) ^ 2 = p * r by linear_combination -r * hpr, horth r hdegree] at h
  exact lt_irrefl 0 h

/-- An orthogonal polynomial for a continuous positive weight on `[a, b]` splits over `ℝ`.
Every irreducible factor has a root in `[a, b]` by `orthogonal_factor_has_root`, hence has
degree one. -/
theorem orthogonal_splits {a b : ℝ} (hab : a < b)
    (w : ℝ → ℝ) (hw : ContinuousOn w (uIcc a b))
    (hwpos : ∀ x ∈ Icc a b, 0 < w x)
    (p : ℝ[X]) (hp : p ≠ 0)
    (horth : ∀ r : ℝ[X], r.degree < p.degree →
      polynomialIntegral a b w hw (p * r) = 0) :
    p.Splits := by
  have hfactor : ∀ q : ℝ[X], q ∣ p → q.Splits := by
    intro q
    induction q using WfDvdMonoid.induction_on_irreducible with
    | zero => exact fun h ↦ (hp (zero_dvd_iff.mp h)).elim
    | unit q hq =>
      exact fun _ ↦ Splits.of_degree_le_one ((degree_eq_zero_of_isUnit hq).trans_le zero_le_one)
    | mul q i _hi0 hi ih =>
      intro hd
      have hip : i ∣ p := (dvd_mul_right i q).trans hd
      obtain ⟨x, _, hx⟩ := orthogonal_factor_has_root hab w hw hwpos p hp horth
        i hi.natDegree_pos hip
      exact (Splits.of_degree_eq_one
        (degree_eq_one_of_irreducible_of_root hi hx)).mul
        (ih ((dvd_mul_left q i).trans hd))
  exact hfactor p dvd_rfl

/-- Every root of an orthogonal polynomial for a continuous positive weight lies in the open
interval `(a, b)`. A root at `a` would give `p = (X - a) * r` with `∫ (x - a) r² w = 0`, but
`(x - a) w x` is a weight positive on the interior, so this integral is positive. The
endpoint `b` is symmetric. -/
theorem orthogonal_root_mem_Ioo {a b : ℝ} (hab : a < b)
    (w : ℝ → ℝ) (hw : ContinuousOn w (uIcc a b))
    (hwpos : ∀ x ∈ Icc a b, 0 < w x)
    (p : ℝ[X]) (hp : p ≠ 0)
    (horth : ∀ r : ℝ[X], r.degree < p.degree →
      polynomialIntegral a b w hw (p * r) = 0)
    {x : ℝ} (hx : p.IsRoot x) :
    x ∈ Ioo a b := by
  have hdiv : X - C x ∣ p := dvd_iff_isRoot.mpr hx
  obtain ⟨y, hy, hyx⟩ := orthogonal_factor_has_root hab w hw hwpos p hp horth
    (X - C x) (by simp) hdiv
  obtain rfl : x = y := (sub_eq_zero.mp (by simpa using hyx)).symm
  obtain ⟨r, hpr⟩ := hdiv
  have hr : r ≠ 0 := by intro h; simp [hpr, h] at hp
  have hdegree : r.degree < p.degree := by
    rw [hpr, degree_mul, degree_X_sub_C, degree_eq_natDegree hr]
    exact_mod_cast (show r.natDegree < 1 + r.natDegree by omega)
  have hz := horth r hdegree
  have hleft : a ≠ x := by
    rintro rfl
    refine (polynomialIntegral_square_pos_on_interior hab (fun y ↦ (y - a) * w y)
      ((continuous_id.sub continuous_const).continuousOn.mul hw)
      (fun y hy ↦ mul_nonneg (sub_nonneg.mpr hy.1) (hwpos y hy).le)
      (fun y hy ↦ mul_pos (sub_pos.mpr hy.1) (hwpos y ⟨hy.1.le, hy.2.le⟩)) r hr).ne' ?_
    rw [← hz]
    simp only [polynomialIntegral, LinearMap.coe_mk, AddHom.coe_mk,
      hpr, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
    congr 1
    ext y
    ring
  have hright : x ≠ b := by
    intro heq
    subst x
    refine (polynomialIntegral_square_pos_on_interior hab (fun y ↦ (b - y) * w y)
      ((continuous_const.sub continuous_id).continuousOn.mul hw)
      (fun y hy ↦ mul_nonneg (sub_nonneg.mpr hy.2) (hwpos y hy).le)
      (fun y hy ↦ mul_pos (sub_pos.mpr hy.2) (hwpos y ⟨hy.1.le, hy.2.le⟩)) r hr).ne' ?_
    rw [← neg_zero, ← hz]
    simp only [polynomialIntegral, LinearMap.coe_mk, AddHom.coe_mk,
      hpr, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
    rw [← intervalIntegral.integral_neg]
    congr 1
    ext y
    ring
  exact ⟨lt_of_le_of_ne hy.1 hleft, lt_of_le_of_ne hy.2 hright⟩

end
end CAS.Continuum

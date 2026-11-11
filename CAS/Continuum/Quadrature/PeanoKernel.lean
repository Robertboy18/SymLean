/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.Simpson

/-!
# Peano-kernel tools for quadrature error bounds

Polynomial exactness alone gives no error bound for non-polynomial integrands.
A sharp derivative estimate comes from writing the quadrature error as
`∫ K f⁽ᵐ⁾` for an explicit piecewise-polynomial kernel `K` and bounding the
integral with the mass of `K`. The two rule-independent steps of that argument are:

* the fourth- and second-order integration-by-parts identities on a compact interval,
  `integral_mul_iteratedDerivWithin_four` and `integral_mul_iteratedDerivWithin_two`;
* the bound of `‖∫ k g‖` by the mass of a one-signed continuous kernel `k` times a bound for
  `‖g‖`, `norm_integral_mul_le_of_nonneg` and `norm_integral_mul_le_of_nonpos`.

The Simpson kernel (`SimpsonPeano`), the two-point Gauss-Legendre kernel
(`GaussLegendrePeano`) and the trapezoidal and midpoint kernels (`SecondOrder`)
are all handled by these two steps.

## Implementation notes

Peano's theorem builds the kernel of any rule that is exact for polynomials of degree less than
`m` by applying the error functional to a truncated power. We do not formalize that general
construction. Each rule writes its kernel down instead, as a chain `k₀, k₁, ...` with
`HasDerivAt kᵢ (kᵢ₊₁ x) x` at every real `x`, and the identities here are `m` applications of
Mathlib's `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt`. The rule's own
proof then checks with `ring` that the boundary terms and the last integral add up to its error.
Because the chain must be differentiable on all of `ℝ`, a kernel with a breakpoint is split
there and each piece is a polynomial on its own subinterval; Simpson's kernel is treated this way
at the midpoint.

## References

* Giuseppe Peano, "Resto nelle formule di quadratura, espresso con un integrale definito",
  *Atti della Reale Accademia dei Lincei, Rendiconti, Classe di scienze fisiche, matematiche e
  naturali*, series 5, 22, first semester (1913), pp. 562-569,
  <https://archive.org/details/rendiconti-lincei_1913-05-04_22_part-1/page/n33/mode/1up>.
  The rule on p. 562 that writes every quadrature remainder as an integral of a derivative.
* Philip J. Davis and Philip Rabinowitz, *Methods of Numerical Integration*, 2nd ed., Academic
  Press, Orlando, 1984, <https://doi.org/10.1016/C2013-0-10566-1>.
-/

@[expose] public section

open MeasureTheory Set

namespace CAS.Continuum

/--
Four integrations by parts against within-derivatives on an ordered compact
interval.

The statement does not mention a quadrature rule: the four kernel derivatives
are supplied explicitly, so every fourth-order Peano identity uses the same
analytic proof.
-/
theorem integral_mul_iteratedDerivWithin_four
    {f k₀ k₁ k₂ k₃ k₄ : ℝ → ℝ} {s : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hsub : Icc a b ⊆ s)
    (hunique : UniqueDiffOn ℝ s)
    (hf : ContDiffOn ℝ 4 f s)
    (hk₀ : ∀ x, HasDerivAt k₀ (k₁ x) x)
    (hk₁ : ∀ x, HasDerivAt k₁ (k₂ x) x)
    (hk₂ : ∀ x, HasDerivAt k₂ (k₃ x) x)
    (hk₃ : ∀ x, HasDerivAt k₃ (k₄ x) x)
    (hk₄ : IntervalIntegrable k₄ volume a b) :
    (∫ x in a..b, k₀ x * iteratedDerivWithin 4 f s x) =
      k₀ b * iteratedDerivWithin 3 f s b -
        k₀ a * iteratedDerivWithin 3 f s a -
      (k₁ b * iteratedDerivWithin 2 f s b -
        k₁ a * iteratedDerivWithin 2 f s a) +
      (k₂ b * iteratedDerivWithin 1 f s b -
        k₂ a * iteratedDerivWithin 1 f s a) -
      (k₃ b * f b - k₃ a * f a) +
      ∫ x in a..b, k₄ x * f x := by
  have hsub' : uIcc a b ⊆ s := (uIcc_of_le hab.le).trans_subset hsub
  have hkint {k k' : ℝ → ℝ} (hk : ∀ x, HasDerivAt k (k' x) x) : IntervalIntegrable k volume a b :=
    (continuous_iff_continuousAt.mpr fun x ↦ (hk x).continuousAt).intervalIntegrable a b
  -- One integration by parts moves a derivative from `f` to the kernel chain.
  have hparts {k k' : ℝ → ℝ} (m : ℕ) (hm : m < 4) (hk : ∀ x, HasDerivAt k (k' x) x)
      (hk' : IntervalIntegrable k' volume a b) :
      ∫ x in a..b, k x * iteratedDerivWithin (m + 1) f s x =
        k b * iteratedDerivWithin m f s b - k a * iteratedDerivWithin m f s a -
          ∫ x in a..b, k' x * iteratedDerivWithin m f s x := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
      (fun x _ ↦ (hk x).hasDerivWithinAt) (fun x hx ↦ ?_) hk'
      ((hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hm) hunique).mono
        hsub').intervalIntegrable
    rw [iteratedDerivWithin_succ]
    exact ((hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hm) hunique) x
      (hsub' hx)).hasDerivWithinAt.mono hsub'
  rw [hparts 3 (by norm_num) hk₀ (hkint hk₁), hparts 2 (by norm_num) hk₁ (hkint hk₂),
    hparts 1 (by norm_num) hk₂ (hkint hk₃), hparts 0 (by norm_num) hk₃ hk₄,
    iteratedDerivWithin_zero]
  ring

/--
Two integrations by parts against within-derivatives on an ordered compact interval.

As in `integral_mul_iteratedDerivWithin_four`, the kernel derivatives are supplied
explicitly, so every second-order Peano identity uses the same analytic proof.
-/
theorem integral_mul_iteratedDerivWithin_two
    {f k₀ k₁ k₂ : ℝ → ℝ} {s : Set ℝ} {a b : ℝ}
    (hab : a < b)
    (hsub : Icc a b ⊆ s)
    (hunique : UniqueDiffOn ℝ s)
    (hf : ContDiffOn ℝ 2 f s)
    (hk₀ : ∀ x, HasDerivAt k₀ (k₁ x) x)
    (hk₁ : ∀ x, HasDerivAt k₁ (k₂ x) x)
    (hk₂ : IntervalIntegrable k₂ volume a b) :
    (∫ x in a..b, k₀ x * iteratedDerivWithin 2 f s x) =
      k₀ b * iteratedDerivWithin 1 f s b -
        k₀ a * iteratedDerivWithin 1 f s a -
      (k₁ b * f b - k₁ a * f a) +
      ∫ x in a..b, k₂ x * f x := by
  have hsub' : uIcc a b ⊆ s := (uIcc_of_le hab.le).trans_subset hsub
  have hparts {k k' : ℝ → ℝ} (m : ℕ) (hm : m < 2) (hk : ∀ x, HasDerivAt k (k' x) x)
      (hk' : IntervalIntegrable k' volume a b) :
      ∫ x in a..b, k x * iteratedDerivWithin (m + 1) f s x =
        k b * iteratedDerivWithin m f s b - k a * iteratedDerivWithin m f s a -
          ∫ x in a..b, k' x * iteratedDerivWithin m f s x := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
      (fun x _ ↦ (hk x).hasDerivWithinAt) (fun x hx ↦ ?_) hk'
      ((hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hm) hunique).mono
        hsub').intervalIntegrable
    rw [iteratedDerivWithin_succ]
    exact ((hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hm) hunique) x
      (hsub' hx)).hasDerivWithinAt.mono hsub'
  rw [hparts 1 (by norm_num) hk₀
      ((continuous_iff_continuousAt.mpr fun x ↦ (hk₁ x).continuousAt).intervalIntegrable a b),
    hparts 0 (by norm_num) hk₁ hk₂, iteratedDerivWithin_zero]
  ring

/-- A continuous kernel that is nonnegative on `[l,r]` bounds `‖∫ k g‖` by its mass times any
bound `C` for `‖g‖` on `[l,r]`. -/
theorem norm_integral_mul_le_of_nonneg
    {k g : ℝ → ℝ} {l r C : ℝ}
    (hlr : l ≤ r)
    (hk : Continuous k)
    (hknonneg : ∀ x ∈ Icc l r, 0 ≤ k x)
    (hgbound : ∀ x ∈ Icc l r, ‖g x‖ ≤ C) :
    ‖∫ x in l..r, k x * g x‖ ≤ (∫ x in l..r, k x) * C := by
  rw [← intervalIntegral.integral_mul_const]
  refine intervalIntegral.norm_integral_le_of_norm_le hlr (.of_forall fun x hx ↦ ?_)
    ((hk.mul continuous_const).intervalIntegrable l r)
  have hkx := hknonneg x (Ioc_subset_Icc_self hx)
  rw [norm_mul, Real.norm_of_nonneg hkx]
  exact mul_le_mul_of_nonneg_left (hgbound x (Ioc_subset_Icc_self hx)) hkx

/-- A continuous kernel that is nonpositive on `[l,r]` bounds `‖∫ k g‖` by its absolute mass
`-∫ k` times any bound `C` for `‖g‖` on `[l,r]`. -/
theorem norm_integral_mul_le_of_nonpos
    {k g : ℝ → ℝ} {l r C : ℝ}
    (hlr : l ≤ r)
    (hk : Continuous k)
    (hknonpos : ∀ x ∈ Icc l r, k x ≤ 0)
    (hgbound : ∀ x ∈ Icc l r, ‖g x‖ ≤ C) :
    ‖∫ x in l..r, k x * g x‖ ≤ -(∫ x in l..r, k x) * C := by
  simpa using norm_integral_mul_le_of_nonneg (k := fun x ↦ -k x) hlr hk.neg
    (fun x hx ↦ neg_nonneg.mpr (hknonpos x hx)) hgbound

end CAS.Continuum

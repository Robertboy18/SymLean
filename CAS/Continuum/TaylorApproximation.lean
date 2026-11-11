/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Calculus.Taylor
public import CAS.Certificate.Approximation

/-!
# Scalar Taylor approximation certificates

Mathlib represents a vector-valued Taylor polynomial with
`PolynomialModule`. `scalarTaylorPolynomialWithin` is the same object for a real
function as an ordinary real polynomial, used by `TaylorJet` and by the Taylor
leaves of `RationalModelTree`, together with proofs that:

* its evaluation is Mathlib's `taylorWithinEval`;
* its degree is at most the requested order;
* Mathlib's Taylor remainder theorem gives an `ApproxCert` (`taylorApproxCertIcc`
  on `Icc a b`, `taylorApproxCert` on `uIcc a b`).

The coefficients of the generated model are the actual within-derivatives, and
its approximation budget is proved from the given derivative bound.

## Implementation notes

We use Mathlib's `taylor_mean_remainder_bound`, which expands at the left endpoint `a` with
derivatives within `Icc a b` and bounds the remainder by `C * (x - a)^(n+1) / n!`; we then bound
`x - a` by `b - a`. The bound is weaker by a factor `n + 1` than the Lagrange bound with
`(n+1)!`. Mathlib's Lagrange form `taylor_mean_remainder_lagrange` holds for real functions only
and takes its derivatives within `uIcc a x`, a set that changes with `x`. The caller supplies `C`
with a proof of the derivative bound, for example from an interval enclosure; the kernel checks
that proof and the remainder estimate.
-/

@[expose] public section

open scoped BigOperators

namespace CAS.Continuum

/--
The order-`n` scalar Taylor polynomial of `f` at `a`, using derivatives within
`s`.
-/
noncomputable def scalarTaylorPolynomialWithin
    (f : ℝ → ℝ) (n : ℕ) (s : Set ℝ) (a : ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C
        ((k.factorial : ℝ)⁻¹ * iteratedDerivWithin k f s a) *
      (Polynomial.X - Polynomial.C a) ^ k

/-- The scalar polynomial evaluates to Mathlib's Taylor evaluation. -/
theorem scalarTaylorPolynomialWithin_eval
    (f : ℝ → ℝ) (n : ℕ) (s : Set ℝ) (a x : ℝ) :
    (scalarTaylorPolynomialWithin f n s a).eval x =
      taylorWithinEval f n s a x := by
  simp [scalarTaylorPolynomialWithin, Polynomial.eval_finsetSum, taylorWithinEval, taylorWithin,
    taylorCoeffWithin, mul_comm]

/-- The generated Taylor polynomial has degree at most its requested order. -/
theorem scalarTaylorPolynomialWithin_natDegree_le
    (f : ℝ → ℝ) (n : ℕ) (s : Set ℝ) (a : ℝ) :
    (scalarTaylorPolynomialWithin f n s a).natDegree ≤ n := by
  unfold scalarTaylorPolynomialWithin
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk ↦
    (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  exact Finset.mem_range_succ_iff.mp hk

/--
Uniform Taylor approximation on an ordered closed interval.

If the `(n+1)`-st within-derivative is bounded by `C`, the generated order-`n`
polynomial approximates `f` uniformly with budget

`C * (b-a)^(n+1) / n!`.

The constant is the one of Mathlib's `taylor_mean_remainder_bound`.
-/
noncomputable def taylorApproxCertIcc
    {f : ℝ → ℝ} {n : ℕ} {a b C : ℝ}
    (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Set.Icc a b))
    (hderiv :
      ∀ x ∈ Set.Icc a b,
        ‖iteratedDerivWithin (n + 1) f (Set.Icc a b) x‖ ≤ C) :
    CAS.Certificate.ApproxCert ℝ ℝ (Set.Icc a b) where
  lhs := f
  rhs := fun x ↦ (scalarTaylorPolynomialWithin f n (Set.Icc a b) a).eval x
  eps := C * (b - a) ^ (n + 1) / n.factorial
  sound := by
    intro x hx
    change ‖f x -
      (scalarTaylorPolynomialWithin f n (Set.Icc a b) a).eval x‖ ≤
        C * (b - a) ^ (n + 1) / n.factorial
    rw [scalarTaylorPolynomialWithin_eval]
    have hlocal :=
      taylor_mean_remainder_bound hab hf hx hderiv
    calc
      ‖f x - taylorWithinEval f n (Set.Icc a b) a x‖
          ≤ C * (x - a) ^ (n + 1) / n.factorial :=
        hlocal
      _ ≤ C * (b - a) ^ (n + 1) / n.factorial := by
        have hCnonneg : 0 ≤ C :=
          (norm_nonneg
            (iteratedDerivWithin (n + 1) f (Set.Icc a b) a)).trans
            (hderiv a ⟨le_rfl, hab⟩)
        have hxa : 0 ≤ x - a := sub_nonneg.mpr hx.1
        have hxb : x - a ≤ b - a := sub_le_sub_right hx.2 a
        gcongr

/--
The ordered-interval Taylor certificate restated on the unoriented interval
used by quadrature and CEGA APIs.
-/
noncomputable def taylorApproxCert
    {f : ℝ → ℝ} {n : ℕ} {a b C : ℝ}
    (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Set.Icc a b))
    (hderiv :
      ∀ x ∈ Set.Icc a b,
        ‖iteratedDerivWithin (n + 1) f (Set.Icc a b) x‖ ≤ C) :
    CAS.Certificate.ApproxCert ℝ ℝ (Set.uIcc a b) where
  lhs := f
  rhs := fun x ↦ (scalarTaylorPolynomialWithin f n (Set.Icc a b) a).eval x
  eps := C * (b - a) ^ (n + 1) / n.factorial
  sound := by
    intro x hx
    apply (taylorApproxCertIcc hab hf hderiv).sound
    rwa [Set.uIcc_of_le hab] at hx

end CAS.Continuum

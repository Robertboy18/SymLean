/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.ModelApproximation
public import CAS.Continuum.RationalAdaptiveSearch
public import CAS.Continuum.TaylorApproximation

/-!
# Certified piecewise Taylor models

A classical Taylor model consists of a finite polynomial and a proved uniform
remainder on one local domain.  Adaptive validated numerics uses different
centers on different subintervals, so the global computational object is
piecewise rather than one polynomial with an increasingly pessimistic
remainder.

`RationalModelTree` assembles certified local reference functions into a
piecewise approximation tree:

* every leaf is a `ModelApproxCert`;
* a leaf may use a Taylor polynomial or any other reference function with a
  checked uniform error bound; `modelOrder` is descriptive metadata;
* internal nodes select the left or right local model at an exact rational
  split;
* `RationalModelTree.sound` projects the complete tree to the ordinary
  `ApproxOn` proposition;
* adaptive generation reuses the generic `RationalAdaptiveSystem`.

The tree error is the maximum of the leaf errors after clamping each at zero.
This combines uniform error bounds; quadrature errors on adjacent panels add instead.

## Implementation notes

Taylor model arithmetic in the sense of Makino and Berz carries a polynomial and a remainder
bound through every arithmetic operation and intrinsic function. We do not implement that
arithmetic: a leaf is a finished certificate. `taylorLeafCandidate` builds one from the Taylor
polynomial at the left endpoint and the remainder bound of `taylorApproxCertIcc`, with the exact
rational budget `rationalTaylorError` that the adaptive stopping test compares with the
tolerance. The adaptive search proposes the splits and the caller proves the bound `C` on the
`(n+1)`-st derivative, for example from an interval enclosure as in
`CAS.Continuum.ExprAdaptiveTaylor`. The kernel checks every leaf, and `sound_of_adaptive` turns an
accepted tree into `ApproxOn`.

## References

* Kyoko Makino and Martin Berz, "Taylor models and other validated functional inclusion
  methods", *International Journal of Pure and Applied Mathematics* 4 (2003), pp. 379-456,
  <https://zbmath.org/?q=an:1022.65051>. A review of the Taylor model method and its arithmetic.
-/

@[expose] public section

open Set

namespace CAS.Continuum

open CAS.Certificate

/--
A binary tree of certified local reference functions for one real-valued function.

The rational endpoint indices are part of the type.  A split therefore cannot
accidentally compose nonadjacent panels.
-/
inductive RationalModelTree (f : ℝ → ℝ) : ℚ → ℚ → Type
  /-- One checked local model. -/
  | leaf {a b : ℚ}
      (cert : ModelApproxCert ℝ ℝ (Icc (a : ℝ) (b : ℝ)))
      (lhs_eq : cert.toApproxCert.lhs = f) :
      RationalModelTree f a b
  /-- Two adjacent local models joined at one exact rational point. -/
  | split {a m b : ℚ}
      (left : RationalModelTree f a m)
      (right : RationalModelTree f m b) :
      RationalModelTree f a b

namespace RationalModelTree

variable {f : ℝ → ℝ} {a b : ℚ}

/-- Piecewise model function denoted by a model tree. -/
noncomputable def model :
    {a b : ℚ} → RationalModelTree f a b → ℝ → ℝ
  | _, _, .leaf cert _ => cert.toApproxCert.rhs
  | _, _, .split (m := m) left right =>
      fun x ↦ if x ≤ (m : ℝ) then left.model x else right.model x

/--
Uniform tree error.

Leaf errors are clamped at zero so the adaptive algebra is total even for a
certificate over an empty interval.  On every nonempty leaf this clamp is
mathematically redundant, because `ApproxOn` already forces a nonnegative
budget.
-/
def error : {a b : ℚ} → RationalModelTree f a b → ℝ
  | _, _, .leaf cert _ => max 0 cert.toApproxCert.eps
  | _, _, .split left right => max left.error right.error

/-- A tree error is always nonnegative. -/
theorem error_nonneg (tree : RationalModelTree f a b) :
    0 ≤ tree.error := by
  induction tree with
  | leaf cert => exact le_max_left 0 cert.toApproxCert.eps
  | split left right hleft => exact hleft.trans (le_max_left left.error right.error)

/-- The piecewise reference function approximates `f` on its interval within `tree.error`. -/
theorem sound (tree : RationalModelTree f a b) :
    ApproxOn f tree.model (Icc (a : ℝ) (b : ℝ)) tree.error := by
  induction tree with
  | leaf cert lhs_eq =>
      intro x hx
      change ‖f x - cert.toApproxCert.rhs x‖ ≤ max 0 cert.toApproxCert.eps
      exact (lhs_eq ▸ cert.toApproxCert.sound x hx).trans (le_max_right _ _)
  | @split a m b left right hleft hright =>
      intro x hx
      change ‖f x - (if x ≤ (m : ℝ) then left.model x else right.model x)‖ ≤
        max left.error right.error
      split_ifs with hxm
      · exact (hleft x ⟨hx.1, hxm⟩).trans (le_max_left _ _)
      · exact (hright x ⟨le_of_not_ge hxm, hx.2⟩).trans (le_max_right _ _)

/-- Rational adaptive-system instance for piecewise certified reference functions. -/
noncomputable def adaptiveSystem (f : ℝ → ℝ) :
    RationalAdaptiveSystem where
  Result := RationalModelTree f
  error := error
  combine := fun left right ↦ .split left right
  error_combine_le := by
    intro _a _m _b left right
    exact max_le
      (le_add_of_nonneg_right right.error_nonneg)
      (le_add_of_nonneg_left left.error_nonneg)

/--
Turn a certificate for a local reference function into an adaptive leaf candidate.

The caller supplies an exact-rational upper bound for the clamped leaf error.
This bound is the candidate datum inspected by the adaptive stopping test.
-/
noncomputable def leafCandidate
    {a b : ℚ}
    (cert : ModelApproxCert ℝ ℝ (Icc (a : ℝ) (b : ℝ)))
    (lhs_eq : cert.toApproxCert.lhs = f)
    (errorBound : ℚ)
    (error_le : max 0 cert.toApproxCert.eps ≤ (errorBound : ℝ)) :
    RationalBudgetCandidate (@(adaptiveSystem f).error a b) where
  cert := .leaf cert lhs_eq
  errorBound := errorBound
  error_le := by
    change max 0 cert.toApproxCert.eps ≤ (errorBound : ℝ)
    exact error_le

/-- A successful adaptive result gives an ordinary uniform approximation theorem. -/
theorem sound_of_adaptive
    {tolerance : ℚ}
    (result :
      AdaptiveResult (@(adaptiveSystem f).error a b) (tolerance : ℝ)) :
    ApproxOn f result.result.model
      (Icc (a : ℝ) (b : ℝ)) (tolerance : ℝ) :=
  approxOn_mono_error result.result.sound result.error_le

end RationalModelTree

/-! ## Taylor leaves -/

/--
Exact-rational form of the error budget supplied by Mathlib's scalar Taylor
remainder theorem.
-/
def rationalTaylorError (order : ℕ) (a b C : ℚ) : ℚ :=
  C * (b - a) ^ (order + 1) / order.factorial

/--
Build one order-`n` Taylor-model leaf.

The model coefficients are Mathlib's actual within-derivatives at the left
endpoint.  `C` is an exact-rational upper bound for the `(n+1)`-st derivative,
so the stopping budget is executable even though the polynomial coefficients
and semantic theorem live over `ℝ`.
-/
noncomputable def taylorLeafCandidate
    {f : ℝ → ℝ} {n : ℕ} {a b C : ℚ}
    (hab : (a : ℝ) < (b : ℝ))
    (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ (n + 1) f (Icc (a : ℝ) (b : ℝ)))
    (hderiv :
      ∀ x ∈ Icc (a : ℝ) (b : ℝ),
        ‖iteratedDerivWithin (n + 1) f
          (Icc (a : ℝ) (b : ℝ)) x‖ ≤ (C : ℝ)) :
    RationalBudgetCandidate
      (@(RationalModelTree.adaptiveSystem f).error a b) := by
  let approx :=
    taylorApproxCertIcc (n := n) hab.le hf hderiv
  let cert := ModelApproxCert.ofApproxCert n approx
  exact RationalModelTree.leafCandidate cert rfl
    (rationalTaylorError n a b C) (by
      have hwidth : 0 ≤ b - a := by
        exact sub_nonneg.mpr (Rat.cast_le.mp hab.le)
      have herrorNonneg : 0 ≤ cert.toApproxCert.eps := by
        dsimp [cert, approx, ModelApproxCert.ofApproxCert,
          taylorApproxCertIcc]
        positivity
      rw [max_eq_right herrorNonneg]
      simp only [cert, approx, ModelApproxCert.ofApproxCert,
        taylorApproxCertIcc, rationalTaylorError]
      norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
        Rat.cast_sub, Rat.cast_natCast]
      rfl)

end CAS.Continuum

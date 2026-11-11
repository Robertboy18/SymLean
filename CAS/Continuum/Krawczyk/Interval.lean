/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Arithmetic
public import CAS.Continuum.Interval.Rational.FiniteSum
public import CAS.Continuum.Krawczyk.Certificate

/-!
# Rational interval matrices for Krawczyk verification

An entrywise rational enclosure of a Jacobian compiles into an entrywise enclosure of the
Krawczyk residual `I - B J`. The proposed inverse `B` has exact rational entries, while every
Jacobian entry may vary independently within a `RationalInterval`.

The interval compiler is executable. Its soundness theorem is independent of how the Jacobian
bounds were found. `certifyFrobenius` computes an exact nonnegative-rational Frobenius bound and
converts it to the Euclidean operator-norm bound required by `Certificate.IsCertified`.

## Main definitions

* `residualBounds`: the rational interval matrix enclosing `I - B J`.
* `CertifiesOperatorNorm`: every real matrix contained in an interval matrix has Euclidean
  operator norm at most a given bound.
* `certifyFrobenius`: the executable Frobenius check.

## Main results

* `residualBounds_sound`: the compiled interval matrix contains `I - B J(x)` entrywise for every
  `x` in the set on which the Jacobian intervals are valid.
* `l2_opNorm_le_sqrt_sum_sq`: the Euclidean operator norm is bounded by the Frobenius norm
  (Cauchy–Schwarz applied row by row).
* `certifyFrobenius_sound`: a successful exact rational comparison
  `Σ |entry bound|² ≤ bound²` proves `CertifiesOperatorNorm` for the whole interval matrix.
* `isCertified_of_intervals`: assembles a full `Certificate.IsCertified` from the interval data,
  the exact Jacobian identity, and the two scalar Krawczyk inequalities.

## Implementation notes

Dependency between Jacobian entries is discarded: each entry ranges over its own interval. This
is the entrywise interval matrix of Moore, Kearfott and Cloud, so the bound is conservative but
simple to check. `Certificate.IsCertified` needs the Euclidean operator norm, since the
localization set is a Euclidean ball; a maximum row sum, as in `MatrixVerification.RowSum`,
bounds the infinity norm and not this one. We bound the operator norm by the Frobenius norm,
which can be larger by a factor of up to `√n`. In exchange the check is one comparison of exact
rational sums of squares, with no square root and no eigenvalue estimate.

## References

* Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud, *Introduction to Interval Analysis*,
  SIAM, Philadelphia, 2009, <https://doi.org/10.1137/1.9780898717716>. Chapter 7,
  <https://doi.org/10.1137/1.9780898717716.ch7>, for interval matrices, and Chapter 8,
  <https://doi.org/10.1137/1.9780898717716.ch8>, for the Krawczyk method.
-/

@[expose] public section

namespace CAS.Continuum.Krawczyk

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {n : Type*} [Fintype n]

/-- Summing singleton intervals is exact. -/
@[simp] theorem sum_univ_const (values : n → ℚ) :
    RationalInterval.sum Finset.univ (fun i ↦ RationalInterval.const (values i)) =
      RationalInterval.const (∑ i, values i) := by
  unfold RationalInterval.sum RationalInterval.const
  congr 1

/-- Cast an exact rational matrix to a real matrix. -/
def castMatrix (matrix : Matrix n n ℚ) : Matrix n n ℝ :=
  fun i j ↦ matrix i j

/-- An interval matrix contains a matrix field entrywise throughout a set. -/
def EnclosesMatrixOn (bounds : Matrix n n RationalInterval)
    (matrixField : EuclideanSpace ℝ n → Matrix n n ℝ)
    (set : Set (EuclideanSpace ℝ n)) : Prop :=
  ∀ x ∈ set, ∀ i j, (bounds i j).MemReal (matrixField x i j)

variable [DecidableEq n]

/--
Entrywise rational interval enclosure of `I - B J`.

The finite sum is evaluated using exact rational interval arithmetic. Dependency between Jacobian
entries is conservatively discarded at this layer.
-/
def residualBounds (approximateInverse : Matrix n n ℚ)
    (jacobianBounds : Matrix n n RationalInterval) : Matrix n n RationalInterval :=
  fun i j ↦
    (RationalInterval.const (if i = j then 1 else 0)).sub
      (RationalInterval.sum Finset.univ fun k ↦
        (RationalInterval.const (approximateInverse i k)).mul (jacobianBounds k j))

/-- Residual compilation is exact when every Jacobian interval is a singleton. -/
@[simp] theorem residualBounds_const (approximateInverse jacobian : Matrix n n ℚ)
    (i j : n) :
    residualBounds approximateInverse
        (fun k l ↦ RationalInterval.const (jacobian k l)) i j =
      RationalInterval.const ((1 - approximateInverse * jacobian) i j) := by
  by_cases hij : i = j <;> simp [residualBounds, Matrix.mul_apply, hij]

/-- The compiled residual intervals contain every residual matrix in the enclosed family. -/
theorem residualBounds_sound
    (approximateInverse : Matrix n n ℚ)
    (jacobianBounds : Matrix n n RationalInterval)
    (matrixField : EuclideanSpace ℝ n → Matrix n n ℝ)
    (set : Set (EuclideanSpace ℝ n))
    (hencloses : EnclosesMatrixOn jacobianBounds matrixField set)
    {x : EuclideanSpace ℝ n} (hx : x ∈ set) (i j : n) :
    (residualBounds approximateInverse jacobianBounds i j).MemReal
      (residualMatrix (castMatrix approximateInverse) (matrixField x) i j) := by
  have hsum := RationalInterval.sum_sound (s := Finset.univ)
    (f := fun k ↦
      (RationalInterval.const (approximateInverse i k)).mul (jacobianBounds k j))
    (g := fun k ↦ (approximateInverse i k : ℝ) * matrixField x k j)
    (fun k _ ↦ RationalInterval.mul_sound (RationalInterval.memReal_const _)
      (hencloses x hx k j))
  have hresidual := RationalInterval.sub_sound
    (RationalInterval.memReal_const (if i = j then 1 else 0)) hsum
  by_cases hij : i = j <;>
    simpa [residualBounds, residualMatrix, castMatrix, Matrix.mul_apply, hij] using hresidual

/--
An interval matrix certifies an operator-norm bound when every contained real matrix has norm at
most that bound.

`certifyFrobenius_sound` proves it from an exact rational Frobenius bound.
-/
def CertifiesOperatorNorm (bounds : Matrix n n RationalInterval) (bound : NNReal) : Prop :=
  ∀ matrix : Matrix n n ℝ,
    (∀ i j, (bounds i j).MemReal (matrix i j)) → ‖matrix‖₊ ≤ bound

/-- `RationalInterval.absMax`, the exact bound `max |lo| |hi|` for the absolute value of an
interval entry, as a nonnegative rational. -/
def entryAbsBound (interval : RationalInterval) : ℚ≥0 :=
  ⟨interval.absMax, interval.absMax_nonneg⟩

/-- The absolute endpoint bound of a singleton interval is exact. -/
@[simp] theorem entryAbsBound_const (value : ℚ) :
    entryAbsBound (RationalInterval.const value) = Rat.nnabs value := by
  ext
  simp [entryAbsBound, RationalInterval.absMax_eq_max, RationalInterval.const,
    FloatLib.Numerics.Interval.point]

/-- Every real number in an interval is bounded by its exact endpoint absolute maximum. -/
theorem abs_le_entryAbsBound {interval : RationalInterval} {value : ℝ}
    (hvalue : interval.MemReal value) :
    |value| ≤ (entryAbsBound interval : ℝ) := by
  simpa [entryAbsBound] using RationalInterval.abs_le_absMax hvalue

/-- Exact rational square of the Frobenius enclosure of an interval matrix. -/
def frobeniusBoundSq (bounds : Matrix n n RationalInterval) : ℚ≥0 :=
  ∑ i, ∑ j, (entryAbsBound (bounds i j)) ^ 2

/-- The Euclidean operator norm of a real matrix is at most its Frobenius norm. -/
theorem l2_opNorm_le_sqrt_sum_sq (matrix : Matrix n n ℝ) :
    ‖matrix‖ ≤ Real.sqrt (∑ i, ∑ j, (matrix i j) ^ 2) := by
  have hsum : 0 ≤ ∑ i, ∑ j, (matrix i j) ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x ↦ ?_
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hsum]
  simp only [EuclideanSpace.real_norm_sq_eq, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec]
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ ↦ Finset.sum_mul_sq_le_sq_mul_sq _ _ _

omit [DecidableEq n] in
/-- Entrywise interval containment bounds the exact sum of squared matrix entries. -/
theorem sum_sq_le_frobeniusBoundSq
    {bounds : Matrix n n RationalInterval} {matrix : Matrix n n ℝ}
    (hmatrix : ∀ i j, (bounds i j).MemReal (matrix i j)) :
    ∑ i, ∑ j, (matrix i j) ^ 2 ≤ (frobeniusBoundSq bounds : ℝ) := by
  rw [frobeniusBoundSq]
  change _ ≤ NNRat.castHom ℝ _
  simp only [map_sum, map_pow]
  exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_le_entryAbsBound (hmatrix i j)) 2

/-- A rational Frobenius bound implies the semantic Euclidean operator-norm enclosure. -/
theorem certifiesOperatorNorm_of_frobeniusBoundSq_le
    {bounds : Matrix n n RationalInterval} {bound : ℚ≥0}
    (hbound : frobeniusBoundSq bounds ≤ bound ^ 2) :
    CertifiesOperatorNorm bounds (bound : NNReal) := by
  intro matrix hmatrix
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  calc ‖matrix‖ ≤ Real.sqrt (∑ i, ∑ j, (matrix i j) ^ 2) := l2_opNorm_le_sqrt_sum_sq matrix
    _ ≤ (bound : ℝ) := Real.sqrt_le_iff.2
      ⟨NNRat.cast_nonneg bound, (sum_sq_le_frobeniusBoundSq hmatrix).trans (mod_cast hbound)⟩

/--
Check a Frobenius proposal using exact nonnegative-rational arithmetic.

Returning `true` means only that the executable rational comparison succeeded;
`certifyFrobenius_sound` supplies its kernel-checked semantic interpretation.
-/
def certifyFrobenius (bounds : Matrix n n RationalInterval) (bound : ℚ≥0) : Bool :=
  decide (frobeniusBoundSq bounds ≤ bound ^ 2)

/-- A successful exact-rational Frobenius check proves `CertifiesOperatorNorm`. -/
theorem certifyFrobenius_sound
    {bounds : Matrix n n RationalInterval} {bound : ℚ≥0}
    (hverified : certifyFrobenius bounds bound = true) :
    CertifiesOperatorNorm bounds (bound : NNReal) :=
  certifiesOperatorNorm_of_frobeniusBoundSq_le <| by
    simpa [certifyFrobenius] using hverified

/-- If the Jacobian intervals enclose `J` on `set` and `CertifiesOperatorNorm` holds for the
compiled residual intervals, then `‖I - B J(x)‖ ≤ q` for every `x ∈ set`. -/
theorem residualEnclosedOn_of_intervals
    {certificate : Certificate n}
    {jacobian : EuclideanSpace ℝ n → Matrix n n ℝ}
    {set : Set (EuclideanSpace ℝ n)}
    {rationalInverse : Matrix n n ℚ}
    {jacobianBounds : Matrix n n RationalInterval}
    (hinverse : certificate.approximateInverse = castMatrix rationalInverse)
    (hjacobian : EnclosesMatrixOn jacobianBounds jacobian set)
    (hnorm : CertifiesOperatorNorm
      (residualBounds rationalInverse jacobianBounds) certificate.contractionBound) :
    certificate.ResidualEnclosedOn jacobian set := by
  intro x hx
  rw [hinverse, residualOperator_eq_matrixOperator]
  change ‖residualMatrix (castMatrix rationalInverse) (jacobian x)‖₊ ≤
    certificate.contractionBound
  exact hnorm _ (residualBounds_sound rationalInverse jacobianBounds jacobian set
    hjacobian hx)

/-- Build a full analytic Krawczyk certificate from an entrywise Jacobian enclosure. -/
theorem isCertified_of_intervals
    {certificate : Certificate n}
    {function : EuclideanSpace ℝ n → EuclideanSpace ℝ n}
    {jacobian : EuclideanSpace ℝ n → Matrix n n ℝ}
    {rationalInverse : Matrix n n ℚ}
    {jacobianBounds : Matrix n n RationalInterval}
    (hcontraction : certificate.contractionBound < 1)
    (hselfMap :
      ‖matrixOperator certificate.approximateInverse (function certificate.center)‖ +
          (certificate.contractionBound : ℝ) * (certificate.radius : ℝ) ≤
            (certificate.radius : ℝ))
    (hderivative : Certificate.HasJacobianOn function jacobian certificate.domain)
    (hinverse : certificate.approximateInverse = castMatrix rationalInverse)
    (hjacobian : EnclosesMatrixOn jacobianBounds jacobian certificate.domain)
    (hnorm : CertifiesOperatorNorm
      (residualBounds rationalInverse jacobianBounds) certificate.contractionBound) :
    certificate.IsCertified function jacobian :=
  ⟨hcontraction, hselfMap, hderivative,
    residualEnclosedOn_of_intervals hinverse hjacobian hnorm⟩

end

end CAS.Continuum.Krawczyk

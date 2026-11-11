/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Krawczyk.Interval
public import CAS.Notation

/-!
# A two-dimensional Krawczyk certificate

The affine system `x ↦ A x - A c` on `ℝ^2`, with `A = diag(2, 3)` and center
`c = (1, -1)`, is checked with the inexact approximate inverse `diag(1/2, 1/4)`. The
preconditioned Jacobian residual is `diag(0, 1/4)`, so the proof uses the Krawczyk
contraction bound `1/4`, not exact inversion. The certificate gives a unique zero in the
closed unit ball around `c`, and that zero is `c`.
-/

@[expose] public section

namespace CAS.Examples.Numerics.Krawczyk

open CAS.Continuum
open CAS.Continuum.Krawczyk
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Exact rational constant Jacobian of the example system. -/
def rationalTarget : Matrix (Fin 2) (Fin 2) ℚ :=
  !![2, 0; 0, 3]

/-- Exact rational, deliberately inexact approximate inverse. -/
def rationalApproximateInverse : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1 / 2, 0; 0, 1 / 4]

/-- Real matrix obtained from the exact rational Jacobian. -/
def target : Matrix (Fin 2) (Fin 2) ℝ :=
  castMatrix rationalTarget

/-- Real matrix obtained from the exact rational approximate inverse. -/
def approximateInverse : Matrix (Fin 2) (Fin 2) ℝ :=
  castMatrix rationalApproximateInverse

/-- Center and exact zero selected for the localization ball. -/
def center : ℝ^2 :=
  WithLp.toLp 2 ![(1 : ℝ), (-1 : ℝ)]

/-- Affine two-variable system with Jacobian `target` and zero at `center`. -/
def system (x : ℝ^2) : ℝ^2 :=
  matrixOperator target x - matrixOperator target center

/-- Constant Jacobian enclosure for the affine system. -/
def jacobian (_x : ℝ^2) : Matrix (Fin 2) (Fin 2) ℝ :=
  target

/-- Singleton interval enclosure of every constant Jacobian entry. -/
def jacobianBounds : Matrix (Fin 2) (Fin 2) RationalInterval :=
  fun i j ↦ RationalInterval.const (rationalTarget i j)

/-- Proof-free Krawczyk proposal on the unit ball around `center`. -/
def certificate : Certificate (Fin 2) where
  center := center
  radius := 1
  approximateInverse := approximateInverse
  contractionBound := 1 / 4

/-- The proposed inverse is not an exact inverse. -/
theorem approximateInverse_mul_target_ne_one : approximateInverse * target ≠ 1 := by
  intro heq
  have hentry := congrFun (congrFun heq 1) 1
  norm_num [approximateInverse, target, castMatrix, rationalApproximateInverse,
    rationalTarget, Matrix.mul_apply] at hentry

/-- Exact matrix residual used by the Krawczyk checker. -/
theorem residualMatrix_eq :
    residualMatrix approximateInverse target = Matrix.diagonal ![0, 1 / 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [residualMatrix, approximateInverse, target, castMatrix,
      rationalApproximateInverse, rationalTarget, Matrix.mul_apply, Matrix.diagonal]

/-- The system has the advertised constant Fréchet derivative. -/
theorem system_hasFDerivAt (x : ℝ^2) :
    HasFDerivAt system (matrixOperator target) x := by
  unfold system
  exact (matrixOperator target).hasFDerivAt.sub_const (matrixOperator target center)

/-- The singleton interval matrix contains the exact Jacobian at every point. -/
theorem jacobianBounds_enclose :
    EnclosesMatrixOn jacobianBounds jacobian certificate.domain := by
  intro x _hx i j
  simp [jacobianBounds, jacobian, target, castMatrix]

/-- The compiled interval residuals certify the Euclidean contraction bound `1 / 4`. -/
theorem residualBounds_certify :
    CertifiesOperatorNorm
      (residualBounds rationalApproximateInverse jacobianBounds)
      certificate.contractionBound := by
  have hcheck :
      certifyFrobenius
          (residualBounds rationalApproximateInverse jacobianBounds)
          (1 / 4) = true := by
    decide +kernel
  simpa [certificate] using certifyFrobenius_sound hcheck

/-- The numerical proposal satisfies every semantic Krawczyk obligation. -/
theorem certificate_isCertified : certificate.IsCertified system jacobian := by
  refine isCertified_of_intervals (rationalInverse := rationalApproximateInverse)
    (jacobianBounds := jacobianBounds) (by norm_num [certificate])
    (by norm_num [certificate, system]) ?_ ?_
    jacobianBounds_enclose residualBounds_certify
  · intro x _hx
    simpa [jacobian] using system_hasFDerivAt x
  · rfl

/-- The checked proposal proves existence and uniqueness of a zero in the localization ball. -/
theorem existsUnique_zero :
    ∃! x : ℝ^2, x ∈ certificate.domain ∧ system x = 0 :=
  Certificate.existsUnique_zero certificate_isCertified

/-- The known center is the unique zero in the certified ball. -/
theorem zero_eq_center {x : ℝ^2}
    (hx : x ∈ certificate.domain) (hzero : system x = 0) : x = center := by
  rcases existsUnique_zero with ⟨root, hroot, hunique⟩
  have hcenterDomain : center ∈ certificate.domain :=
    Certificate.center_mem_domain certificate
  have hcenterZero : system center = 0 := by simp [system]
  exact (hunique x ⟨hx, hzero⟩).trans (hunique center ⟨hcenterDomain, hcenterZero⟩).symm

end

end CAS.Examples.Numerics.Krawczyk

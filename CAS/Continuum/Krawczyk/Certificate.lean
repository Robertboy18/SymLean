/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Contracting
public import CAS.Continuum.Krawczyk.Basic
public import CAS.Continuum.MatrixVerification

/-!
# Multivariate Krawczyk certificates

A finite-dimensional Krawczyk theorem on a closed Euclidean ball. A `Certificate` contains a
center `c`, a radius `r`, a proposed inverse `B` and a contraction bound `q`. It contains no proof
and does not assume that the proposed inverse is invertible. `Certificate.IsCertified` is the
checked predicate, and `Certificate.existsUnique_zero` turns it into exactly one zero of `F` in
the ball.

## Main definitions

* `Certificate`: the proof-free proposal.
* `Certificate.IsCertified`: the four checked obligations (`q < 1`, the self-map
  inequality `‖B F(c)‖ + q r ≤ r`, the Jacobian identity `HasJacobianOn`, and the residual bound
  `ResidualEnclosedOn`, which says `‖I - B J(x)‖ ≤ q` on the ball).

## Main results

* `Certificate.lipschitzOnWith_fixedPointMap`, `Certificate.mapsTo_fixedPointMap`:
  the preconditioned Newton map `x ↦ x - B F(x)` is a `q`-Lipschitz self-map of
  the ball, by the mean value inequality on a convex set.
* `Certificate.eq_zero_of_isFixedPt`: fixed points are zeros, because the
  residual bound at the center makes `B` invertible.
* `Certificate.existsUnique_zero`: there is exactly one zero of `F` in the ball.

## Implementation notes

Rump's form of Krawczyk's operator (Theorem 13.3 of the survey below) works with boxes: if
`-B F(c) + (I - B J(c + X)) X` lies in the interior of the interval vector `X`, then `F` has a
unique zero in `c + X`, and existence comes from Brouwer's fixed-point theorem. We use a closed
Euclidean ball and one operator-norm bound instead of the componentwise box inclusion common in
interval software. Then `x ↦ x - B F(x)` is a contraction of a complete set, and Banach's
fixed-point theorem (`ContractingWith.exists_fixedPoint'`, `ContractingWith.fixedPoint_unique'`)
gives existence and uniqueness together; Mathlib has Banach's theorem and not Brouwer's. The mean
value inequality `Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le` turns the residual bound
into the Lipschitz constant. A fixed point is a zero only if `B` is injective, and we do not
assume that: the residual bound at the center makes `B` a certified approximate inverse of
`J(c)`, so `B` is a unit by `MatrixVerification.ApproximateInverseCandidate.proposedInverse_isUnit`.

The kernel checks a proof of `IsCertified`; the data in `Certificate` may come from any numerical
solver. Interval arithmetic (`Krawczyk.Interval`) or another backend may prove the residual bound
and the self-map inequality. The Jacobian identity is an exact derivative statement and must be
proved exactly, typically by symbolic differentiation.

## References

* R. Krawczyk, "Newton-Algorithmen zur Bestimmung von Nullstellen mit Fehlerschranken",
  *Computing* 4 (1969), pp. 187-201, <https://doi.org/10.1007/BF02234767>. The origin of the
  Krawczyk operator.
* Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud, *Introduction to Interval Analysis*,
  SIAM, Philadelphia, 2009, <https://doi.org/10.1137/1.9780898717716>. Chapter 8,
  <https://doi.org/10.1137/1.9780898717716.ch8>, for the Krawczyk method for nonlinear systems.
* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Theorem 13.3 is the box form of the test, proved there with Brouwer's fixed-point theorem.
-/

@[expose] public section

namespace CAS.Continuum.Krawczyk

open Metric Set
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Proof-free numerical data proposed for a Krawczyk verification. -/
structure Certificate (n : Type*) where
  /-- Center of the localization ball. -/
  center : EuclideanSpace ℝ n
  /-- Intrinsically nonnegative radius of the localization ball. -/
  radius : NNReal
  /-- Numerically proposed inverse for the Jacobian. -/
  approximateInverse : Matrix n n ℝ
  /-- Proposed uniform bound for `‖I - B J(x)‖`. -/
  contractionBound : NNReal

namespace Certificate

/-- Closed ball in which a certificate localizes the zero. -/
def domain (certificate : Certificate n) : Set (EuclideanSpace ℝ n) :=
  closedBall certificate.center (certificate.radius : ℝ)

/--
The supplied matrix field is the Fréchet Jacobian of `function` on `set`.

This predicate identifies the exact derivative represented by a matrix field. Entrywise interval
containment is a separate notion in `Krawczyk.Interval`; keeping the two predicates distinct avoids
calling an exact Jacobian identity an interval enclosure.
-/
def HasJacobianOn
    (function : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (jacobian : EuclideanSpace ℝ n → Matrix n n ℝ)
    (set : Set (EuclideanSpace ℝ n)) : Prop :=
  ∀ x ∈ set, HasFDerivAt function (matrixOperator (jacobian x)) x

/-- Uniform operator-norm enclosure of all preconditioned Jacobian residuals. -/
def ResidualEnclosedOn (certificate : Certificate n)
    (jacobian : EuclideanSpace ℝ n → Matrix n n ℝ)
    (set : Set (EuclideanSpace ℝ n)) : Prop :=
  ∀ x ∈ set,
    ‖residualOperator certificate.approximateInverse (jacobian x)‖₊ ≤
      certificate.contractionBound

/--
Kernel-checked mathematical obligations for a Krawczyk proposal.

The second conjunct is the ball form of the Krawczyk forward-inclusion estimate:
`‖B F(center)‖ + q * radius ≤ radius`. The final two conjuncts are the checked Jacobian and
residual enclosures.
-/
def IsCertified (certificate : Certificate n)
    (function : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (jacobian : EuclideanSpace ℝ n → Matrix n n ℝ) : Prop :=
  certificate.contractionBound < 1 ∧
    ‖matrixOperator certificate.approximateInverse (function certificate.center)‖ +
        (certificate.contractionBound : ℝ) * (certificate.radius : ℝ) ≤
          (certificate.radius : ℝ) ∧
    HasJacobianOn function jacobian certificate.domain ∧
    certificate.ResidualEnclosedOn jacobian certificate.domain

variable {certificate : Certificate n}
variable {function : EuclideanSpace ℝ n → EuclideanSpace ℝ n}
variable {jacobian : EuclideanSpace ℝ n → Matrix n n ℝ}

omit [DecidableEq n] in
/-- The center belongs to its localization ball. -/
theorem center_mem_domain (certificate : Certificate n) :
    certificate.center ∈ certificate.domain :=
  mem_closedBall_self certificate.radius.coe_nonneg

/-- A checked certificate supplies the stated Jacobian throughout its domain. -/
theorem hasFDerivAt (hcert : certificate.IsCertified function jacobian)
    {x : EuclideanSpace ℝ n} (hx : x ∈ certificate.domain) :
    HasFDerivAt function (matrixOperator (jacobian x)) x :=
  hcert.2.2.1 x hx

/-- A checked certificate supplies the stated residual bound throughout its domain. -/
theorem residual_nnnorm_le (hcert : certificate.IsCertified function jacobian)
    {x : EuclideanSpace ℝ n} (hx : x ∈ certificate.domain) :
    ‖residualOperator certificate.approximateInverse (jacobian x)‖₊ ≤
      certificate.contractionBound :=
  hcert.2.2.2 x hx

/-- The checked derivative enclosure makes the preconditioned map Lipschitz on the ball. -/
theorem lipschitzOnWith_fixedPointMap
    (hcert : certificate.IsCertified function jacobian) :
    LipschitzOnWith certificate.contractionBound
      (fixedPointMap function certificate.approximateInverse) certificate.domain := by
  have hconvex : Convex ℝ certificate.domain :=
    convex_closedBall certificate.center (certificate.radius : ℝ)
  exact hconvex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (𝕜 := ℝ)
    (f' := fun x ↦ residualOperator certificate.approximateInverse (jacobian x))
    (fun x hx ↦ (hasFDerivAt_fixedPointMap (Certificate.hasFDerivAt hcert hx)).hasFDerivWithinAt)
    fun x hx ↦ Certificate.residual_nnnorm_le hcert hx

/-- The Krawczyk self-map inequality makes the localization ball forward invariant. -/
theorem mapsTo_fixedPointMap
    (hcert : certificate.IsCertified function jacobian) :
    MapsTo (fixedPointMap function certificate.approximateInverse)
      certificate.domain certificate.domain := by
  intro x hx
  have hstep :
      dist (fixedPointMap function certificate.approximateInverse certificate.center)
          certificate.center =
        ‖matrixOperator certificate.approximateInverse (function certificate.center)‖ := by
    simp [fixedPointMap]
  have hlip := (Certificate.lipschitzOnWith_fixedPointMap hcert).dist_le_mul x hx
    certificate.center (Certificate.center_mem_domain certificate)
  rw [domain, mem_closedBall] at hx ⊢
  linarith [hcert.2.1, mul_le_mul_of_nonneg_left hx certificate.contractionBound.coe_nonneg,
    dist_triangle (fixedPointMap function certificate.approximateInverse x)
      (fixedPointMap function certificate.approximateInverse certificate.center)
      certificate.center]

/-- The restricted preconditioned map is a strict contraction. -/
theorem contractingWith_restrict
    (hcert : certificate.IsCertified function jacobian) :
    ContractingWith certificate.contractionBound
      ((Certificate.mapsTo_fixedPointMap hcert).restrict
        (fixedPointMap function certificate.approximateInverse)
        certificate.domain certificate.domain) :=
  ⟨hcert.1, (Certificate.lipschitzOnWith_fixedPointMap hcert).mapsToRestrict
    (Certificate.mapsTo_fixedPointMap hcert)⟩

/-- Approximate-inverse candidate obtained from the Jacobian at the center. -/
def centerInverseCandidate (certificate : Certificate n)
    (jacobian : EuclideanSpace ℝ n → Matrix n n ℝ) :
    MatrixVerification.ApproximateInverseCandidate n ℝ where
  matrix := jacobian certificate.center
  proposedInverse := certificate.approximateInverse
  residualBound := certificate.contractionBound

/-- The Krawczyk residual enclosure certifies the center approximate-inverse candidate. -/
theorem centerInverseCandidate_isCertified
    (hcert : certificate.IsCertified function jacobian) :
    (certificate.centerInverseCandidate jacobian).IsCertified := by
  refine ⟨?_, by exact_mod_cast hcert.1⟩
  have h : ‖residualOperator certificate.approximateInverse (jacobian certificate.center)‖ ≤
      (certificate.contractionBound : ℝ) := by
    exact_mod_cast Certificate.residual_nnnorm_le hcert (Certificate.center_mem_domain certificate)
  rw [residualOperator_eq_matrixOperator] at h
  exact h

/-- A certified residual proves that the proposed inverse is an invertible matrix. -/
theorem approximateInverse_isUnit
    (hcert : certificate.IsCertified function jacobian) :
    IsUnit certificate.approximateInverse :=
  MatrixVerification.ApproximateInverseCandidate.proposedInverse_isUnit
    (Certificate.centerInverseCandidate_isCertified hcert)

/-- The proposed inverse acts injectively on Euclidean space. -/
theorem approximateInverse_injective
    (hcert : certificate.IsCertified function jacobian) :
    Function.Injective (matrixOperator certificate.approximateInverse) :=
  (ContinuousLinearMap.isUnit_iff_bijective.1 ((Certificate.approximateInverse_isUnit hcert).map
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)).toMonoidHom)).1

/-- Every fixed point of a certified preconditioned map is an actual zero of the system. -/
theorem eq_zero_of_isFixedPt
    (hcert : certificate.IsCertified function jacobian)
    {x : EuclideanSpace ℝ n}
    (hfixed : Function.IsFixedPt
      (fixedPointMap function certificate.approximateInverse) x) :
    function x = 0 := by
  have hpreconditioned : matrixOperator certificate.approximateInverse (function x) = 0 :=
    sub_eq_self.mp hfixed
  exact Certificate.approximateInverse_injective hcert (by simpa using hpreconditioned)

/--
Soundness of a multivariate Krawczyk certificate.

There exists exactly one zero of `function` in the certified closed ball. Uniqueness holds
within this ball only.
-/
theorem existsUnique_zero
    (hcert : certificate.IsCertified function jacobian) :
    ∃! x : EuclideanSpace ℝ n, x ∈ certificate.domain ∧ function x = 0 := by
  let newtonMap := fixedPointMap function certificate.approximateInverse
  have hmaps : MapsTo newtonMap certificate.domain certificate.domain :=
    Certificate.mapsTo_fixedPointMap hcert
  have hcontract : ContractingWith certificate.contractionBound
      (hmaps.restrict newtonMap certificate.domain certificate.domain) :=
    Certificate.contractingWith_restrict hcert
  obtain ⟨root, hrootDomain, hfixed, -⟩ := hcontract.exists_fixedPoint'
    isClosed_closedBall.isComplete hmaps (Certificate.center_mem_domain certificate)
    (edist_ne_top _ _)
  refine ⟨root, ⟨hrootDomain, Certificate.eq_zero_of_isFixedPt hcert hfixed⟩,
    fun other hother ↦ ?_⟩
  have h := hcontract.fixedPoint_unique' (x := ⟨root, hrootDomain⟩) (y := ⟨other, hother.1⟩)
    (Subtype.ext hfixed) (Subtype.ext (isFixedPt_fixedPointMap_of_eq_zero hother.2))
  exact (congrArg Subtype.val h).symm

end Certificate

end

end CAS.Continuum.Krawczyk

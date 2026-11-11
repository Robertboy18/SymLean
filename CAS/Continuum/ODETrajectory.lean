/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.ODE.Gronwall
public import CAS.Certificate.Approximation

/-!
# Validated ODE trajectories

A bound on the residual of an approximate ODE solution gives a bound on its distance to any
other approximate or exact solution, by Grönwall's inequality. An `ODETrajectoryCert` records:

* an ordinary Lean curve and its proposed velocity;
* the usual continuity and one-sided derivative facts on a time interval;
* membership in a time-dependent state set; and
* a backend-independent uniform bound for
  `velocity t - vectorField t (curve t)`.

Mathlib's approximate-trajectory Grönwall theorem `dist_le_of_approx_trajectories_ODE_of_mem`
then compares two such certificates (`ODETrajectoryCert.dist_le_gronwall`,
`ODETrajectoryCert.comparison`). Exact symbolic residuals and interval bounds enter through the
same `ResidualBound`. The validation is a posteriori: the trajectory is given, and only its
residual is checked.

## Implementation notes

The validated integrators surveyed by Nedialkov, Jackson and Corliss, in particular the interval
Taylor series methods, enclose the solution step by step: an a priori enclosure with a stepsize,
then a tight enclosure that reduces the wrapping effect. We do not integrate: untrusted code
proposes the curve, its velocity and the residual budget, and the kernel checks the proofs stored
in the certificate.

The analysis is Mathlib's `dist_le_of_approx_trajectories_ODE_of_mem`: if the vector field is
`K`-Lipschitz on the state sets and two trajectories start within `δ`, their distance at time `t`
is at most `gronwallBound δ K (ε₁ + ε₂) (t - a)`. `comparison` takes the value at `b - a` as one
uniform budget, by monotonicity of `gronwallBound` in the time argument.

## References

* N. S. Nedialkov, K. R. Jackson and G. F. Corliss, "Validated solutions of initial value
  problems for ordinary differential equations", *Applied Mathematics and Computation* 105
  (1999), pp. 21-68, <https://doi.org/10.1016/S0096-3003(98)10083-8>. A survey of validated
  methods for initial value problems, especially interval Taylor series methods.
-/

@[expose] public section

open Metric Set
open scoped NNReal

namespace CAS.Continuum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The strong ODE residual associated with a curve and a proposed velocity. -/
def odeResidual (vectorField : ℝ → E → E) (curve velocity : ℝ → E) :
    ℝ → E :=
  fun t ↦ velocity t - vectorField t (curve t)

/--
A checked approximate ODE trajectory on `[a, b]`.

The residual bound is a statement about the curve itself, so any proof of it,
symbolic or by interval arithmetic, fits this one structure.
-/
structure ODETrajectoryCert
    (vectorField : ℝ → E → E) (state : ℝ → Set E) (a b : ℝ) where
  /-- Candidate trajectory. -/
  curve : ℝ → E
  /-- Proposed time derivative of the candidate trajectory. -/
  velocity : ℝ → E
  /-- Continuity on the closed time interval. -/
  continuousOn : ContinuousOn curve (Icc a b)
  /-- Right derivative on the half-open time interval. -/
  hasDerivWithinAt :
    ∀ t ∈ Ico a b, HasDerivWithinAt curve (velocity t) (Ici t) t
  /-- The candidate remains in the region where the vector-field estimate is valid. -/
  mem_state : ∀ t ∈ Ico a b, curve t ∈ state t
  /-- Uniform error budget for the ODE residual. -/
  residualError : ℝ
  /-- Checked uniform bound for the actual ODE residual. -/
  residual_sound :
    CAS.Certificate.ResidualBound
      (odeResidual vectorField curve velocity) (Ico a b) residualError

namespace ODETrajectoryCert

variable {vectorField : ℝ → E → E} {state : ℝ → Set E} {a b : ℝ}

/-- The residual certificate gives the metric defect required by Mathlib's ODE theorem. -/
theorem dist_velocity_vectorField_le
    (cert : ODETrajectoryCert vectorField state a b) :
    ∀ t ∈ Ico a b,
      dist (cert.velocity t) (vectorField t (cert.curve t)) ≤
        cert.residualError := fun t ht ↦ by
  simpa [CAS.Certificate.ResidualBound, CAS.Certificate.ApproxOn, odeResidual, dist_eq_norm] using
    cert.residual_sound t ht

/--
Pointwise Grönwall comparison for two certified approximate trajectories.

This is a direct certificate-facing specialization of Mathlib's
`dist_le_of_approx_trajectories_ODE_of_mem`. The two residual budgets remain
separate until the theorem combines them.
-/
theorem dist_le_gronwall
    (left right : ODETrajectoryCert vectorField state a b)
    (K : ℝ≥0)
    (hLipschitz :
      ∀ t ∈ Ico a b, LipschitzOnWith K (vectorField t) (state t))
    {delta : ℝ}
    (hinitial : dist (left.curve a) (right.curve a) ≤ delta) :
    ∀ t ∈ Icc a b,
      dist (left.curve t) (right.curve t) ≤
        gronwallBound delta K
          (left.residualError + right.residualError) (t - a) :=
  dist_le_of_approx_trajectories_ODE_of_mem hLipschitz left.continuousOn left.hasDerivWithinAt
    left.dist_velocity_vectorField_le left.mem_state right.continuousOn right.hasDerivWithinAt
    right.dist_velocity_vectorField_le right.mem_state hinitial

/--
Uniform approximation certificate obtained from Grönwall comparison.

The endpoint value of the Grönwall bound is a uniform budget on `[a, b]`.
The strict inequality `a < b` also proves that both stored residual budgets
are nonnegative, so monotonicity of the Grönwall bound applies without an
extra caller hypothesis.
-/
noncomputable def comparison
    (left right : ODETrajectoryCert vectorField state a b)
    (hab : a < b)
    (K : ℝ≥0)
    (hLipschitz :
      ∀ t ∈ Ico a b, LipschitzOnWith K (vectorField t) (state t))
    (delta : ℝ)
    (hinitial : dist (left.curve a) (right.curve a) ≤ delta) :
    CAS.Certificate.ApproxCert ℝ E (Icc a b) where
  lhs := left.curve
  rhs := right.curve
  eps :=
    gronwallBound delta K
      (left.residualError + right.residualError) (b - a)
  sound := by
    have haIco : a ∈ Ico a b := ⟨le_rfl, hab⟩
    have hleftEps : 0 ≤ left.residualError := by
      exact le_trans (norm_nonneg _) (left.residual_sound a haIco)
    have hrightEps : 0 ≤ right.residualError := by
      exact le_trans (norm_nonneg _) (right.residual_sound a haIco)
    have hdelta : 0 ≤ delta :=
      le_trans dist_nonneg hinitial
    have hmono :
        Monotone
          (gronwallBound delta K
            (left.residualError + right.residualError)) :=
      gronwallBound_mono hdelta (add_nonneg hleftEps hrightEps) K.coe_nonneg
    intro t ht
    have hpoint := left.dist_le_gronwall right K hLipschitz hinitial t ht
    have htime : t - a ≤ b - a := sub_le_sub_right ht.2 a
    have hend := hmono htime
    simpa [dist_eq_norm] using le_trans hpoint hend

/-- Semantic theorem projected from `comparison`. When `b ≤ a` the interval has at most the
point `a`, where the Grönwall bound at time `0` is `delta`. -/
theorem comparison_sound
    (left right : ODETrajectoryCert vectorField state a b)
    (K : ℝ≥0)
    (hLipschitz :
      ∀ t ∈ Ico a b, LipschitzOnWith K (vectorField t) (state t))
    (delta : ℝ)
    (hinitial : dist (left.curve a) (right.curve a) ≤ delta) :
    CAS.Certificate.ApproxOn left.curve right.curve (Icc a b)
      (gronwallBound delta K
        (left.residualError + right.residualError) (b - a)) := by
  rcases lt_or_ge a b with hab | hba
  · exact (left.comparison right hab K hLipschitz delta hinitial).sound
  intro t ht
  obtain rfl : t = a := le_antisymm (ht.2.trans hba) ht.1
  rw [show b - t = 0 by linarith [ht.2], gronwallBound_x0]
  simpa [dist_eq_norm] using hinitial

end ODETrajectoryCert

end CAS.Continuum

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.RationalAdaptiveSearch
public import CAS.Certificate.Quadrature

/-!
# Certified search over quadrature candidates

Numerical quadrature often generates several checked candidates: a
coarse mesh, one or more refinements, or different arithmetic schedules.  The
candidate generator and its stopping policy should remain outside the trusted
analytic core, while every accepted result must retain an ordinary integral
error theorem.

`QuadratureCandidateFamily` separates the two. It associates candidate
keys with `QuadratureCert`s and an executable Boolean acceptance
test.  The sole proof obligation says that every accepted key meets the
requested tolerance.  An `AcceptedCandidate` is a key carrying that proof, and
its certificate satisfies the requested integral error bound.

The construction is independent of the quadrature rule and of the arithmetic: any
`QuadratureCert` can serve as a candidate.
-/

@[expose] public section

namespace CAS.Continuum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ → E} {a b tolerance : ℝ}

/--
A finite-search interface for checked quadrature candidates.

The Boolean test may be conservative: no completeness assumption is imposed.
Soundness requires only that a `true` result certifies the candidate's stored
error budget against the requested tolerance.
-/
structure QuadratureCandidateFamily
    (κ : Type*) (f : ℝ → E) (a b tolerance : ℝ) where
  /-- Build the quadrature certificate associated with a candidate key. -/
  candidate : κ → QuadratureCert f a b
  /-- Executable acceptance test supplied by the search policy or backend. -/
  accept : κ → Bool
  /-- Every accepted candidate meets the requested tolerance. -/
  accept_sound :
    ∀ key, accept key = true → (candidate key).error ≤ tolerance

namespace QuadratureCandidateFamily

variable {κ : Type*}
variable (family : QuadratureCandidateFamily κ f a b tolerance)

/--
A key selected by a sound acceptance policy, together with its tolerance proof.

This is the generic `AdaptiveResult` applied to candidate keys.
-/
abbrev AcceptedCandidate :=
  AdaptiveResult (fun key : κ ↦ (family.candidate key).error) tolerance

namespace AcceptedCandidate

variable {family : QuadratureCandidateFamily κ f a b tolerance}

/-- Key retained for inspecting the accepted mesh, rule, or arithmetic schedule. -/
def key (accepted : family.AcceptedCandidate) : κ :=
  accepted.result

/-- The quadrature certificate associated with an accepted key. -/
def cert (accepted : family.AcceptedCandidate) :
    QuadratureCert f a b :=
  family.candidate accepted.key

/--
Expose an accepted candidate with the requested tolerance as its stored error
budget.
-/
def withTolerance (accepted : family.AcceptedCandidate) :
    QuadratureCert f a b :=
  accepted.cert.weaken accepted.error_le

/-- The accepted candidate satisfies the requested integral error bound. -/
theorem sound (accepted : family.AcceptedCandidate) :
    ‖(∫ x in a..b, f x) - accepted.cert.value‖ ≤ tolerance :=
  accepted.cert.sound.trans accepted.error_le

/-- The tolerance-normalized certificate has exactly the requested budget. -/
@[simp]
theorem withTolerance_error (accepted : family.AcceptedCandidate) :
    accepted.withTolerance.error = tolerance :=
  rfl

/-- Normalizing the budget does not change the computed quadrature value. -/
@[simp]
theorem withTolerance_value (accepted : family.AcceptedCandidate) :
    accepted.withTolerance.value = accepted.cert.value :=
  rfl

end AcceptedCandidate

end QuadratureCandidateFamily

end CAS.Continuum

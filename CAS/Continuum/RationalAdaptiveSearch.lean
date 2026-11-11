/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Generic certified adaptive search on rational intervals

Adaptive quadrature, piecewise Taylor models, and validated local
approximations all use the same control structure:

1. try a certified local candidate;
2. accept it when its rational error bound meets the local tolerance;
3. otherwise bisect at the exact rational midpoint;
4. split the tolerance equally and compose the two certified children.

`RationalAdaptiveSystem` implements that control structure once, with no
reference to quadrature or Taylor polynomials.  A client supplies a
`RationalAdaptiveSystem`, consisting of its result type, semantic error, and a
proved binary composition rule. Search is fail-closed: when a local candidate
is absent or exceeds the tolerance, it subdivides if depth remains and otherwise
returns `none`. A successful local candidate can be accepted even at depth zero.

## Implementation notes

The search needs no separate checker. `AdaptiveResult` is a subtype carrying
`error result ≤ tolerance`, built at a leaf from `error_le_of_accepted` and at a split from
`error_combine_le` and the two halved tolerances, so every `some` returned is already a theorem.
The stopping test is `decide` on exact rationals; real numbers occur only in proofs. Halving
matches quadrature, whose panel errors add. For `RationalModelTree`, whose error is a maximum, it
is conservative, since each child could keep the whole tolerance.
-/

@[expose] public section

open Set

namespace CAS.Continuum

/--
A result together with an exact-rational upper bound for its semantic error.

The client result type is arbitrary. Only `errorBound` is inspected by the
executable stopping test; `error_le` supplies the semantic guarantee.
-/
structure RationalBudgetCandidate {Result : Type*} (error : Result → ℝ) where
  /-- The client-specific certified result. -/
  cert : Result
  /-- Exact-rational upper bound used by the stopping test. -/
  errorBound : ℚ
  /-- The rational number bounds the complete semantic error. -/
  error_le : error cert ≤ (errorBound : ℝ)

namespace RationalBudgetCandidate

variable {Result : Type*} {error : Result → ℝ}

/-- Exact stopping test for one candidate. -/
def accepted (candidate : RationalBudgetCandidate error)
    (tolerance : ℚ) : Bool :=
  decide (candidate.errorBound ≤ tolerance)

/-- An accepted candidate meets the requested real tolerance. -/
theorem error_le_of_accepted (candidate : RationalBudgetCandidate error)
    (tolerance : ℚ) (haccepted : candidate.accepted tolerance = true) :
    error candidate.cert ≤ (tolerance : ℝ) := by
  simp only [accepted, decide_eq_true_eq] at haccepted
  exact candidate.error_le.trans (by exact_mod_cast haccepted)

end RationalBudgetCandidate

/-- A client result whose semantic error meets a requested real budget. -/
abbrev AdaptiveResult {Result : Type*} (error : Result → ℝ)
    (tolerance : ℝ) :=
  {result : Result // error result ≤ tolerance}

namespace AdaptiveResult

variable {Result : Type*} {error : Result → ℝ} {tolerance : ℝ}

/-- The client-specific certified result. -/
abbrev result (certified : AdaptiveResult error tolerance) : Result :=
  certified.1

/-- The complete semantic error meets the requested budget. -/
theorem error_le (certified : AdaptiveResult error tolerance) :
    error certified.result ≤ tolerance :=
  certified.2

/-- Package a result whose semantic error meets the requested budget. -/
def mk (result : Result) (error_le : error result ≤ tolerance) :
    AdaptiveResult error tolerance :=
  ⟨result, error_le⟩

end AdaptiveResult

/--
Client semantics for generic rational adaptive search.

`Result a b` is the certified object attached to the rational panel `[a,b]`.
The only required algebra is binary composition at an exact rational split
point, with subadditivity of the semantic error.
-/
structure RationalAdaptiveSystem where
  /-- Certified result type on each exact-rational panel. -/
  Result : ℚ → ℚ → Type
  /-- Complete semantic error of a result. -/
  error : {a b : ℚ} → Result a b → ℝ
  /-- Compose adjacent certified panels. -/
  combine : {a m b : ℚ} → Result a m → Result m b → Result a b
  /-- Composition introduces no error beyond the sum of child errors. -/
  error_combine_le :
    ∀ {a m b : ℚ} (left : Result a m) (right : Result m b),
      error (combine left right) ≤ error left + error right

namespace RationalAdaptiveSystem

/-- Fail-closed local candidate builder on a checked ambient domain. -/
abbrev PartialBuilderOn (system : RationalAdaptiveSystem) (s : Set ℝ) :=
  {a b : ℚ} →
    ((a : ℝ) < (b : ℝ)) →
    Icc (a : ℝ) (b : ℝ) ⊆ s →
    Option (RationalBudgetCandidate (@system.error a b))

/-- Exact rational midpoint used by every adaptive client. -/
def midpoint (a b : ℚ) : ℚ :=
  (a + b) / 2

/-- Casting the exact rational midpoint to `ℝ` gives the real midpoint `(a + b) / 2`; this is
what lets the proof-only real inequalities `a < m < b` follow from `a < b`. -/
@[simp]
theorem cast_midpoint (a b : ℚ) :
    ((midpoint a b : ℚ) : ℝ) = ((a : ℝ) + (b : ℝ)) / 2 := by
  simp [midpoint]

/--
Depth-bounded generic adaptive search.

The domain arguments ensure every recursively generated panel remains inside
the ambient analytic domain.  They are proof-only; all executable decisions
use exact rational arithmetic.
-/
noncomputable def searchPartial
    (system : RationalAdaptiveSystem) {s : Set ℝ}
    (build : system.PartialBuilderOn s) :
    (depth : ℕ) → (a b : ℚ) → ((a : ℝ) < (b : ℝ)) →
      Icc (a : ℝ) (b : ℝ) ⊆ s → (tolerance : ℚ) →
      Option (AdaptiveResult (@system.error a b) (tolerance : ℝ))
  | 0, _a, _b, hab, hsub, tolerance =>
      match build hab hsub with
      | none => none
      | some candidate =>
          if haccepted : candidate.accepted tolerance = true then
            some
              (AdaptiveResult.mk candidate.cert
                (candidate.error_le_of_accepted tolerance haccepted))
          else
            none
  | depth + 1, a, b, hab, hsub, tolerance =>
      let subdivide (_ : Unit) :
          Option (AdaptiveResult (@system.error a b) (tolerance : ℝ)) :=
        let m := midpoint a b
        have hleft : (a : ℝ) < (m : ℝ) := by
          rw [cast_midpoint]
          exact left_lt_add_div_two.mpr hab
        have hright : (m : ℝ) < (b : ℝ) := by
          rw [cast_midpoint]
          exact add_div_two_lt_right.mpr hab
        have hleftSub : Icc (a : ℝ) (m : ℝ) ⊆ s :=
          (Icc_subset_Icc le_rfl hright.le).trans hsub
        have hrightSub : Icc (m : ℝ) (b : ℝ) ⊆ s :=
          (Icc_subset_Icc hleft.le le_rfl).trans hsub
        match
            searchPartial system build depth a m hleft hleftSub
              (tolerance / 2),
            searchPartial system build depth m b hright hrightSub
              (tolerance / 2) with
        | some left, some right =>
            some
              (AdaptiveResult.mk (system.combine left.result right.result) (by
                  apply (system.error_combine_le left.result right.result).trans
                  have hleftError := left.error_le
                  have hrightError := right.error_le
                  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hleftError
                  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hrightError
                  linarith))
        | _, _ => none
      match build hab hsub with
      | none => subdivide ()
      | some candidate =>
          if haccepted : candidate.accepted tolerance = true then
            some
              (AdaptiveResult.mk candidate.cert
                (candidate.error_le_of_accepted tolerance haccepted))
          else
            subdivide ()

end RationalAdaptiveSystem

end CAS.Continuum

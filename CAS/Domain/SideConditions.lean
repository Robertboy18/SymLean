/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Basic.Real.Basic

/-!
# Semantic side conditions

`PositiveOn f s` and `NonzeroOn f s` say that `f` is positive, respectively nonzero, at every
point of `s`. Exact symbolic routes emit nonvanishing obligations for the denominators they
cancel, and `NonzeroOn` states one of them on a patch (`CAS.Exact.ExprNonzeroCert`). The
real-root modules state root exclusion with it: a root-free interval
(`CAS.Polynomial.RealRoot.nonzeroOn_of_rootFree_eq_true`) or a disjoint interval-Newton image
(`CAS.Polynomial.RealRoot.IntervalNewtonCertificate.nonzeroOn_of_excludesRoots_eq_true`) gives
`NonzeroOn` of the polynomial on the interval.
-/

@[expose] public section

namespace CAS.Domain

/-!
## Semantic side-condition predicates

A nonvanishing proof discharges a generated cancellation obligation.
-/

/-- The function `f` is positive at every point of `s`. -/
def PositiveOn {α : Type*} (f : α → ℝ) (s : Set α) : Prop :=
  ∀ x, x ∈ s → 0 < f x

/-- A function is nonzero on a domain.  Exact symbolic routes require this of every cancelled
denominator. -/
def NonzeroOn {α : Type*} (f : α → ℝ) (s : Set α) : Prop :=
  ∀ x, x ∈ s → f x ≠ 0

end CAS.Domain

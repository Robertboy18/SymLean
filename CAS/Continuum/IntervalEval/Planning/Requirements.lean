/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Basic
public import CAS.Continuum.IntervalEval.Callbacks

/-!
# Missing facts for certified evaluation

`RegistryRequirements` lists what a rational-interval registry lacks to evaluate an expression:
denominators with no registered absolute lower bound, and unary operations (`UnaryRangeNeed`)
whose argument interval is known but whose range fact is missing. Requirements are computable
planner data, not certificates. They affect evaluation only after a solver turns them into
checked registry entries.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Verified

/-- A unary-operation range fact needed by a registry scan. -/
structure UnaryRangeNeed (ι : Type*) where
  /-- Operation whose range certificate is needed. -/
  op : UnaryKind
  /-- Argument expression of the unary operation. -/
  arg : Verified.Expr ι
  /-- Interval computed for the argument. -/
  argInterval : RationalInterval

/-- Facts a certified evaluator is missing for a given expression.

These requirements are computed from the same providers used by evaluation.
They are proof-search targets rather than certificates; a fact affects trusted
evaluation only after it has been turned into a checked registry entry. -/
structure RegistryRequirements (ι : Type*) where
  /-- Denominator expressions with no registered absolute-lower-bound fact. -/
  missingDenominators : List (Verified.Expr ι)
  /-- Unary operations whose argument interval is known but whose range fact is missing. -/
  missingUnaryRanges : List (UnaryRangeNeed ι)

namespace RegistryRequirements

/-- An empty set of registry requirements. -/
def empty {ι : Type*} : RegistryRequirements ι where
  missingDenominators := []
  missingUnaryRanges := []

/-- Combine two sets of registry requirements. -/
def append {ι : Type*} (a b : RegistryRequirements ι) : RegistryRequirements ι where
  missingDenominators := a.missingDenominators ++ b.missingDenominators
  missingUnaryRanges := a.missingUnaryRanges ++ b.missingUnaryRanges

end RegistryRequirements

end RationalInterval
end CAS.Continuum

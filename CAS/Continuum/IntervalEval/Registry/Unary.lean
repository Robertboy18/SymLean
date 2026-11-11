/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Registry.Core
public import CAS.Continuum.IntervalEval.Planning.Requirements
public import CAS.Continuum.Interval.Elementary.Acos
public import CAS.Continuum.Interval.Elementary.Atan

/-!
# Unary range facts for registries

Each `...RangeRouteEntry` turns an argument interval `IA` into a checked range entry for one
unary operation: square root, arctangent, arcsine, arccosine, exponential, logarithm on an
interval with `0 < IA.lo`, with `IA.hi < 0`, or equal to `{0}`, and reciprocal on an interval of
one sign. Most ranges are endpoint enclosures of a monotone function, and every entry is valid
for every argument in `IA`. Square-root digits, logarithm series terms and exponential Taylor
orders follow the registry's precision policy. `unaryRangeRouteEntry?` dispatches on the
operation and returns `none` when the required sign condition fails.

## Implementation notes

A monotone operation is evaluated at the endpoints of its argument interval
(`UnaryRangeRouteEntry.ofIncreasingOnInterval`, `ofDecreasingOnInterval`), with the endpoint
values enclosed by the elementary-function enclosures. The logarithm of a negative interval is
taken on its negation, since Mathlib's `Real.log` satisfies `log (-x) = log x`. An entry is
valid for every argument in its interval, which is the contract of `UnaryRangeProvider`, so the
solver needs only the requirement collected by the registry and no further search.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Verified

namespace CertifiedEvalRegistry

variable {α : Type*} {ι : Type*} [DecidableEq ι] {s : Set α} {ρ : α → ι → ℝ}

/--
Square-root range entry for an arbitrary argument interval.

The range is `sqrtRangeInterval` with the registry's number of binary digits: FloatLib's
integer square-root enclosure at nonnegative endpoints and `[0, 0]` at negative ones.
-/
def sqrtRangeRouteEntry
    (r : CertifiedEvalRegistry s ρ) (arg : Verified.Expr ι) (IA : RationalInterval) :
    UnaryRangeRouteEntry r.env (ExprAbsLowerProvider.fromRouteEntries r.divEntries).lookup :=
  UnaryRangeRouteEntry.ofIncreasingOnInterval
    .sqrt arg IA (sqrtRangeInterval IA r.precision.sqrtDigits)
    [.sqrtRange]
    (by
      intro u v _hu _hv huv
      simpa [UnaryKind.apply] using Real.sqrt_le_sqrt huv)
    (by
      simpa [UnaryKind.apply] using
        (sqrtRangeInterval_sound IA r.precision.sqrtDigits IA.lo_memReal).1)
    (by
      simpa [UnaryKind.apply] using
        (sqrtRangeInterval_sound IA r.precision.sqrtDigits IA.hi_memReal).2)

/-- Arctangent range entry `atanRange IA`, valid because `Real.arctan` is increasing. -/
def atanRangeRouteEntry
    (r : CertifiedEvalRegistry s ρ) (arg : Verified.Expr ι) (IA : RationalInterval) :
    UnaryRangeRouteEntry r.env (ExprAbsLowerProvider.fromRouteEntries r.divEntries).lookup :=
  UnaryRangeRouteEntry.ofIncreasingOnInterval
    .atan arg IA (atanRange IA)
    [.atanRange]
    (by
      intro u v _hu _hv huv
      simpa [UnaryKind.apply] using Real.arctan_mono huv)
    (by
      simpa [UnaryKind.apply] using (atanRange_sound IA IA.lo_memReal).1)
    (by
      simpa [UnaryKind.apply] using (atanRange_sound IA IA.hi_memReal).2)

/-- Arcsine range entry `asinRange IA`, valid because `Real.arcsin` is monotone. -/
def asinRangeRouteEntry
    (r : CertifiedEvalRegistry s ρ) (arg : Verified.Expr ι) (IA : RationalInterval) :
    UnaryRangeRouteEntry r.env (ExprAbsLowerProvider.fromRouteEntries r.divEntries).lookup :=
  UnaryRangeRouteEntry.ofIncreasingOnInterval
    .asin arg IA (asinRange IA)
    [.asinRange]
    (by
      intro u v _hu _hv huv
      simpa [UnaryKind.apply] using Real.arcsin_le_arcsin huv)
    (by
      simpa [UnaryKind.apply] using (asinRange_sound IA IA.lo_memReal).1)
    (by
      simpa [UnaryKind.apply] using (asinRange_sound IA IA.hi_memReal).2)

/-- Arccosine range entry `acosRange IA`, valid because `Real.arccos` is antitone. -/
def acosRangeRouteEntry
    (r : CertifiedEvalRegistry s ρ) (arg : Verified.Expr ι) (IA : RationalInterval) :
    UnaryRangeRouteEntry r.env (ExprAbsLowerProvider.fromRouteEntries r.divEntries).lookup :=
  UnaryRangeRouteEntry.ofDecreasingOnInterval
    .acos arg IA (acosRange IA)
    [.acosRange]
    (by
      intro u v _hu _hv huv
      simpa [UnaryKind.apply] using Real.arccos_le_arccos huv)
    (by
      simpa [UnaryKind.apply] using (acosRange_sound IA IA.hi_memReal).1)
    (by
      simpa [UnaryKind.apply] using (acosRange_sound IA IA.lo_memReal).2)

/-- Build the total checked logarithm range entry on a positive panel. -/
def logRangeRouteEntry
    (r : CertifiedEvalRegistry s ρ) (arg : Verified.Expr ι) (IA : RationalInterval)
    (hpos : 0 < IA.lo) :
    UnaryRangeRouteEntry r.env (ExprAbsLowerProvider.fromRouteEntries r.divEntries).lookup :=
  UnaryRangeRouteEntry.ofIncreasingOnInterval
    .log arg IA (logRangeWith IA r.precision.logTerms hpos)
    [.logRange]
    (by
      intro u v hu _hv huv
      have hu_pos : 0 < u := by
        exact (by exact_mod_cast hpos : (0 : ℝ) < (IA.lo : ℝ)).trans_le hu.1
      simpa [UnaryKind.apply] using Real.log_le_log hu_pos huv)
    (by
      simpa [UnaryKind.apply] using
        (logRangeWith_sound IA r.precision.logTerms hpos IA.lo_memReal).1)
    (by
      simpa [UnaryKind.apply] using
        (logRangeWith_sound IA r.precision.logTerms hpos IA.hi_memReal).2)

/-- Build a checked logarithm range entry on a strictly negative panel. -/
def logNegativeRangeRouteEntry
    (r : CertifiedEvalRegistry s ρ) (arg : Verified.Expr ι) (IA : RationalInterval)
    (hneg : IA.hi < 0) :
    UnaryRangeRouteEntry r.env (ExprAbsLowerProvider.fromRouteEntries r.divEntries).lookup :=
  let positiveInterval := IA.neg
  have hpositive : 0 < positiveInterval.lo := by
    simpa [positiveInterval] using neg_pos.mpr hneg
  { op := .log
    arg := arg
    argInterval := IA
    range := logRangeWith positiveInterval r.precision.logTerms hpositive
    steps := [.logRange]
    sound := by
      intro z hz
      have hnegated := RationalInterval.neg_sound hz
      have hrange := logRangeWith_sound positiveInterval r.precision.logTerms hpositive hnegated
      simpa [UnaryKind.apply, Real.log_neg_eq_log] using hrange }

/-- Build the exact logarithm range entry for the singleton panel `{0}`. -/
def logZeroRangeRouteEntry
    (r : CertifiedEvalRegistry s ρ) (arg : Verified.Expr ι) (IA : RationalInterval)
    (hzero : IA.lo = 0 ∧ IA.hi = 0) :
    UnaryRangeRouteEntry r.env (ExprAbsLowerProvider.fromRouteEntries r.divEntries).lookup :=
  { op := .log
    arg := arg
    argInterval := IA
    range := .const 0
    steps := [.logRange]
    sound := by
      intro z hz
      have hlo : (IA.lo : ℝ) = 0 := by exact_mod_cast hzero.1
      have hhi : (IA.hi : ℝ) = 0 := by exact_mod_cast hzero.2
      have hzle : z ≤ 0 := by simpa [hhi] using hz.2
      have hlez : 0 ≤ z := by simpa [hlo] using hz.1
      have hz0 : z = 0 := le_antisymm hzle hlez
      simpa [UnaryKind.apply, hz0] using RationalInterval.memReal_const 0 }

/-- Build the total checked exponential range entry on a rational panel. -/
def expRangeRouteEntry
    (r : CertifiedEvalRegistry s ρ) (arg : Verified.Expr ι) (IA : RationalInterval) :
    UnaryRangeRouteEntry r.env (ExprAbsLowerProvider.fromRouteEntries r.divEntries).lookup :=
  UnaryRangeRouteEntry.ofIncreasingOnInterval
    .exp arg IA (expRangeWith IA r.precision.expOrder)
    [.expRange]
    (by
      intro u v _hu _hv huv
      simpa [UnaryKind.apply] using Real.exp_le_exp_of_le huv)
    (by
      simpa [UnaryKind.apply] using
        (expRangeWith_sound IA r.precision.expOrder IA.lo_memReal).1)
    (by
      simpa [UnaryKind.apply] using
        (expRangeWith_sound IA r.precision.expOrder IA.hi_memReal).2)

/-- Build a checked reciprocal range entry from a positive argument interval. -/
def reciprocalPositiveRangeRouteEntry
    (r : CertifiedEvalRegistry s ρ) (arg : Verified.Expr ι) (IA : RationalInterval)
    (hpos : 0 < IA.lo) :
    UnaryRangeRouteEntry r.env (ExprAbsLowerProvider.fromRouteEntries r.divEntries).lookup :=
  UnaryRangeRouteEntry.ofDecreasingOnInterval
    .inv arg IA (IA.invPositive hpos)
    [.reciprocalPositiveRange]
    (by
      intro u v hu _hv huv
      have hu_pos : 0 < u := by
        have hposR : (0 : ℝ) < (IA.lo : ℝ) := by exact_mod_cast hpos
        exact lt_of_lt_of_le hposR hu.1
      simpa [UnaryKind.apply] using inv_anti₀ hu_pos huv)
    (by
      simp [UnaryKind.apply])
    (by
      simp [UnaryKind.apply])

/-- FloatLib's positive reciprocal applied after negating a negative interval. -/
def reciprocalNegativeRangeInterval
    (I : RationalInterval) (hneg : I.hi < 0) :
    RationalInterval :=
  (I.neg.invPositive (by simpa using neg_pos.mpr hneg)).neg

/-- Build a checked reciprocal range entry from a negative argument interval. -/
def reciprocalNegativeRangeRouteEntry
    (r : CertifiedEvalRegistry s ρ) (arg : Verified.Expr ι) (IA : RationalInterval)
    (hneg : IA.hi < 0) :
    UnaryRangeRouteEntry r.env (ExprAbsLowerProvider.fromRouteEntries r.divEntries).lookup :=
  UnaryRangeRouteEntry.ofDecreasingOnInterval
    .inv arg IA (reciprocalNegativeRangeInterval IA hneg)
    [.reciprocalNegativeRange]
    (by
      intro u v _hu hv huv
      have hv_neg : v < 0 := by
        have hnegR : (IA.hi : ℝ) < 0 := by exact_mod_cast hneg
        exact lt_of_le_of_lt hv.2 hnegR
      have hpos_neg_v : 0 < -v := neg_pos.mpr hv_neg
      have hneg_le : -v ≤ -u := neg_le_neg huv
      have hbase : 1 / (-u) ≤ 1 / (-v) :=
        one_div_le_one_div_of_le hpos_neg_v hneg_le
      have hnegbase : -(1 / (-v)) ≤ -(1 / (-u)) := neg_le_neg hbase
      simpa [UnaryKind.apply, one_div, inv_neg] using hnegbase)
    (by
      simp [UnaryKind.apply, reciprocalNegativeRangeInterval])
    (by
      simp [UnaryKind.apply, reciprocalNegativeRangeInterval])

/-- Try to solve a unary range target directly from interval endpoints.

It handles total square-root ranges over arbitrary intervals,
logarithm ranges on positive and negative intervals bounded away from zero
(plus the singleton zero), exponential ranges on every bounded rational
interval, and sign-aware inverse-trigonometric ranges. The output intervals
are conservative rational ranges chosen to keep the generated proofs small.
-/
def unaryRangeRouteEntry?
    (r : CertifiedEvalRegistry s ρ) (need : UnaryRangeNeed ι) :
    Option
      (UnaryRangeRouteEntry r.env
        (ExprAbsLowerProvider.fromRouteEntries r.divEntries).lookup) :=
  match need.op with
  | .inv =>
      if hpos : 0 < need.argInterval.lo then
        some
          (r.reciprocalPositiveRangeRouteEntry need.arg need.argInterval hpos)
      else if hneg : need.argInterval.hi < 0 then
        some
          (r.reciprocalNegativeRangeRouteEntry need.arg need.argInterval hneg)
      else
        none
  | .sqrt =>
      some (r.sqrtRangeRouteEntry need.arg need.argInterval)
  | .exp =>
      some (r.expRangeRouteEntry need.arg need.argInterval)
  | .log =>
      if hpos : 0 < need.argInterval.lo then
        some (r.logRangeRouteEntry need.arg need.argInterval hpos)
      else if hneg : need.argInterval.hi < 0 then
        some (r.logNegativeRangeRouteEntry need.arg need.argInterval hneg)
      else if hzero : need.argInterval.lo = 0 ∧ need.argInterval.hi = 0 then
        some (r.logZeroRangeRouteEntry need.arg need.argInterval hzero)
      else
        none
  | .atan =>
      some (r.atanRangeRouteEntry need.arg need.argInterval)
  | .asin =>
      some (r.asinRangeRouteEntry need.arg need.argInterval)
  | .acos =>
      some (r.acosRangeRouteEntry need.arg need.argInterval)

end CertifiedEvalRegistry
end RationalInterval
end CAS.Continuum

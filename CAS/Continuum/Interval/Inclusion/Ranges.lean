/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Inclusion.Basic
public import CAS.Continuum.Interval.Elementary.Acos
public import CAS.Continuum.Interval.Elementary.Atan
public import CAS.Continuum.Interval.Elementary.Exp
public import CAS.Continuum.Interval.Elementary.Hyperbolic
public import CAS.Continuum.Interval.Elementary.Log
public import CAS.Continuum.Interval.Elementary.Sqrt
public import CAS.Continuum.Interval.Elementary.Trig
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Total CEGA ranges for `cega_real`

The `cega_real` operations need ranges defined on every rational interval. `invRange?` and
`logRange?` extend CEGA's reciprocal and logarithm, which require an argument interval with a
positive lower endpoint, to every interval that excludes zero, and return `none` on an interval
that contains zero. `taylorOrder` fixes the Taylor order of the exponential family as a function
of the dyadic precision.

## Implementation notes

Each wrapper decides the sign by two rational comparisons, `0 < J.lo` and `0 < J.neg.lo`, and
negates a negative interval before calling `invPositive` or `logRangeWith`. The reciprocal
negates the result back; the logarithm keeps it, since Mathlib's `Real.log (-x) = Real.log x`.
On `none`, `liftUnary` returns its fallback, the whole line. `taylorOrder` is at least
`defaultExpTaylorOrder`, so small precisions keep the default order of `exp`. The only importer
is `CAS.Continuum.Interval.Inclusion.Elementary`, also through a `meta` import, since
`dyadic_interval` runs the ranges before the kernel checks the result. There `invRange?_sound`
and `logRange?_sound` split the branches and apply `invPositive_sound` or `logRangeWith_sound`,
with `neg_sound` in the negative branch.
-/

@[expose] public section

namespace CAS.Continuum.CEGAInclusion

open RationalInterval

/-- The Taylor order used for `exp`, `sinh`, `cosh` and `tanh` at precision `prec`. -/
def taylorOrder (prec : ℕ) : ℕ := max defaultExpTaylorOrder (prec / 2)

/-- CEGA's reciprocal on an interval that excludes zero; `none` if the interval contains zero. -/
def invRange? (J : RationalInterval) : Option RationalInterval :=
  if h : 0 < J.lo then some (J.invPositive h)
  else if h' : 0 < J.neg.lo then some (J.neg.invPositive h').neg
  else none

/-- CEGA's logarithm with `terms` series terms on an interval that excludes zero; `none` if the
interval contains zero. -/
def logRange? (terms : ℕ) (J : RationalInterval) : Option RationalInterval :=
  if h : 0 < J.lo then some (J.logRangeWith terms h)
  else if h' : 0 < J.neg.lo then some (J.neg.logRangeWith terms h')
  else none

end CAS.Continuum.CEGAInclusion

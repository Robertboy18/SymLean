/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
public meta import CAS.CEGA
public import CAS.Examples.CEGA.Basic

/-!
# Precision options of the `cega` tactic

`(prec := n)` sets the requested FloatLib degree for `exp`, `sinh`, `cosh`, and
`tanh`, the logarithm precision request, and the number of binary digits on the
square-root denominator grid. Exponential and hyperbolic ranges promote order
zero to one; logarithm requests use twice the positive requested term count.
`(depth := n)` computes the enclosure after `n` checked bisection levels, for every
projection the goal needs: an enclosure, an upper bound, an absolute bound, or an
approximation. The default policy (`8`, `12`, `10`, and depth `2`) is used when the
group is omitted.
-/

@[expose] public section

namespace CAS.Examples.CEGA.Precision

open CAS.Examples.CEGA.Basic
open CAS.Certificate
open CAS.CEGA

/-- Increasing the exponential degree certifies an upper bound with twenty-four decimal places. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ Real.exp (p 0))
      unitDomain (1 : ℝ) (2.718281828459045235360288 : ℝ) := by
  cega (prec := 40) [enclose x in [0, 1]] (exp x)

/-- A third bisection level sharpens `sin x · cos x` on `[0, 2]` from `[-0.379, 0.635]` at the
default depth to `[-0.379, 0.545]`; the true range is `[-0.379, 0.5]`. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ Real.sin (p 0) * Real.cos (p 0))
      {p : ℝ^1 | 0 ≤ p 0 ∧ p 0 ≤ 2} (-38 / 100 : ℝ) (55 / 100 : ℝ) := by
  cega (depth := 3) [enclose x in [0, 2]] (sin x * cos x)

end CAS.Examples.CEGA.Precision

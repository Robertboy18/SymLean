/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.Approximation
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Simpson's quadrature rule

The three-node Simpson rule as a normalized quadrature rule:

`(1/6) f(0) + (4/6) f(1/2) + (1/6) f(1)`.

The only rule-specific proof is the finite verification that its moments
through degree three agree with integration on `[0,1]`.  Polynomial exactness,
affine transport to arbitrary oriented intervals, and certificate generation
then follow from `QuadratureRule`.

## References

* NIST Digital Library of Mathematical Functions, §3.5 Quadrature, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/3.5>. Equation (3.5.6) gives Simpson's rule
  `(h/3) (f(a) + 4 f((a+b)/2) + f(b))` with `h = (b-a)/2`, whose weights on `[0,1]` are
  `1/6, 4/6, 1/6`.
-/

@[expose] public section

namespace CAS.Continuum

open CAS.Certificate
open MeasureTheory

/-- The normalized three-node Simpson rule on `[0,1]`. -/
noncomputable def simpsonRule : QuadratureRule where
  terms :=
    [((1 : ℝ) / 6, 0), ((4 : ℝ) / 6, 1 / 2), ((1 : ℝ) / 6, 1)]
  nodes_mem_unit := by
    intro term hterm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hterm
    rcases hterm with hterm | hterm | hterm <;> subst term <;> norm_num

namespace simpsonRule

/-- Simpson's rule has the exact normalized moments of degrees zero through three. -/
theorem exactUpTo_three : simpsonRule.ExactUpTo 3 := by
  intro k hk
  interval_cases k <;>
    norm_num [QuadratureRule.moment, QuadratureRule.normalizedValue, simpsonRule, weightedSum]

end simpsonRule
end CAS.Continuum

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.Approximation

/-!
# Two-point Gauss-Legendre quadrature

The two-point Gauss-Legendre rule on `[0,1]` as a normalized quadrature
rule.  Its nodes are

`(3 - √3) / 6` and `(3 + √3) / 6`,

both with weight `1 / 2`.  These are the zeros `±1/√3` of the second Legendre
polynomial, transported from `[-1,1]` to `[0,1]`.  The finite moment calculation
proves exactness for every polynomial of degree at most three, the maximal degree
`2n - 1` for an `n`-point Gauss rule.  The analytic remainder estimate is in
`GaussLegendrePeano`.

## Main results

* `gaussLegendreTwoRule.exactUpTo_three`: the moments of degree `0` to `3` are exact, so
  `QuadratureRule.valueOn_eq_integral_of_natDegree_le` integrates every cubic exactly on any
  oriented interval.

## References

* Carl Friedrich Gauss, "Methodus nova integralium valores per approximationem inveniendi",
  *Commentationes Societatis Regiae Scientiarum Gottingensis Recentiores* 3 (1816), pp. 39-76,
  <https://archive.org/details/bub_gb_J6S9H_VYVn4C>.
* NIST Digital Library of Mathematical Functions, §3.5 Quadrature, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/3.5>. §3.5(v) for the Gauss rule and its exactness for polynomials of
  degree at most `2n - 1`.
-/

@[expose] public section

namespace CAS.Continuum

open MeasureTheory

/-- Left node of the normalized two-point Gauss-Legendre rule. -/
noncomputable def gaussLegendreTwoLeftNode : ℝ :=
  (3 - Real.sqrt 3) / 6

/-- Right node of the normalized two-point Gauss-Legendre rule. -/
noncomputable def gaussLegendreTwoRightNode : ℝ :=
  (3 + Real.sqrt 3) / 6

/-- The square-root identity used to bound the Gauss nodes and simplify their polynomial moments. -/
theorem sqrt_three_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
  Real.sq_sqrt (by norm_num)

/-- The left Gauss node `(3 - √3)/6 ≈ 0.211` lies in `[0,1]`; it is the image of `-1/√3` under
the affine map from `[-1,1]` to `[0,1]`. -/
theorem gaussLegendreTwoLeftNode_mem_unit :
    gaussLegendreTwoLeftNode ∈ Set.Icc (0 : ℝ) 1 := by
  unfold gaussLegendreTwoLeftNode
  constructor <;> nlinarith [sqrt_three_sq, Real.sqrt_nonneg 3]

/-- The right Gauss node `(3 + √3)/6 ≈ 0.789` lies in `[0,1]`; it is the image of `1/√3` under
the affine map from `[-1,1]` to `[0,1]`. -/
theorem gaussLegendreTwoRightNode_mem_unit :
    gaussLegendreTwoRightNode ∈ Set.Icc (0 : ℝ) 1 := by
  unfold gaussLegendreTwoRightNode
  constructor <;> nlinarith [sqrt_three_sq, Real.sqrt_nonneg 3]

/-- The normalized two-point Gauss-Legendre rule on `[0,1]`. -/
noncomputable def gaussLegendreTwoRule : QuadratureRule where
  terms :=
    [((1 : ℝ) / 2, gaussLegendreTwoLeftNode),
      ((1 : ℝ) / 2, gaussLegendreTwoRightNode)]
  nodes_mem_unit := by
    intro term hterm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hterm
    rcases hterm with hterm | hterm <;> subst term
    · exact gaussLegendreTwoLeftNode_mem_unit
    · exact gaussLegendreTwoRightNode_mem_unit

namespace gaussLegendreTwoRule

/-- The two-point Gauss rule has the exact moments of degrees zero through three. -/
theorem exactUpTo_three : gaussLegendreTwoRule.ExactUpTo 3 := by
  intro k hk
  interval_cases k <;>
    norm_num [QuadratureRule.moment, QuadratureRule.normalizedValue, gaussLegendreTwoRule,
      gaussLegendreTwoLeftNode, gaussLegendreTwoRightNode, weightedSum] <;>
    nlinarith [sqrt_three_sq]

end gaussLegendreTwoRule
end CAS.Continuum

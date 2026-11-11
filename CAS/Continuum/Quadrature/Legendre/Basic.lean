/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.GaussLegendre

/-!
# Three- and four-point Gauss–Legendre rules

`QuadratureRule` is a list of `(weight, node)` pairs with nodes in `[0, 1]`, and
the rules here have weights summing to one, so `valueOn f a b` is the affine transport of
the rule to `[a, b]`. In that convention `three` and `four` are the three- and four-point
Gauss–Legendre rules in radicals, and `three_exact` and `four_exact` show that each is exact
through degree `2n - 1` (`ExactUpTo (2n - 1)`) by checking the monomial moments one degree at
a time.
`Legendre/Identification` transports them to `[-1, 1]` as `GaussianRule`s, together with
`midpointRule` and `gaussLegendreTwoRule`.

## References

* NIST Digital Library of Mathematical Functions, §3.5(v) Gauss Quadrature, Version 1.2.8
  (2026-09-15), <https://dlmf.nist.gov/3.5.v>.
* NIST Digital Library of Mathematical Functions, §18.3 Definitions of the classical orthogonal
  polynomials, Version 1.2.8 (2026-09-15), <https://dlmf.nist.gov/18.3>.
-/

@[expose] public section

namespace CAS.Continuum.Legendre

noncomputable section

/-- The outer node `√(3/5)` of the three-point rule on `[-1, 1]`. -/
def threeNode : ℝ := Real.sqrt (3 / 5)

/-- `threeNode ^ 2 = 3/5`. -/
theorem threeNode_sq : threeNode ^ 2 = (3 / 5 : ℝ) :=
  Real.sq_sqrt (by norm_num)

/-- `threeNode` lies in `[0, 1]`. -/
theorem threeNode_mem : threeNode ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.sqrt_nonneg _, by nlinarith [threeNode_sq]⟩

/-- The three-point Gauss–Legendre rule: nodes `(1 - √(3/5))/2`, `1/2`, `(1 + √(3/5))/2`
with weights `5/18`, `4/9`, `5/18`. -/
def three : QuadratureRule where
  terms := [(5 / 18, (1 - threeNode) / 2), (4 / 9, 1 / 2),
    (5 / 18, (1 + threeNode) / 2)]
  nodes_mem_unit := by
    intro term h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h <;> subst term <;>
      constructor <;> dsimp <;> nlinarith [threeNode_mem.1, threeNode_mem.2]

/-- The three-point rule is exact through degree five. -/
theorem three_exact : three.ExactUpTo 5 := by
  have hfour : threeNode ^ 4 = (9 / 25 : ℝ) := by
    linear_combination (threeNode ^ 2 + 3 / 5) * threeNode_sq
  intro k hk
  interval_cases k <;>
    norm_num [QuadratureRule.moment, QuadratureRule.normalizedValue, three, weightedSum] <;>
    ring_nf <;> nlinarith [threeNode_sq]

/-- The radical `√30` appearing in the four-point nodes and weights. -/
def fourRadical : ℝ := Real.sqrt 30

/-- `fourRadical ^ 2 = 30`. -/
theorem fourRadical_sq : fourRadical ^ 2 = 30 :=
  Real.sq_sqrt (by norm_num)

/-- The inner node `√((15 - 2√30)/35)` of the four-point rule on `[-1, 1]`. -/
def fourInner : ℝ := Real.sqrt ((15 - 2 * fourRadical) / 35)
/-- The outer node `√((15 + 2√30)/35)` of the four-point rule on `[-1, 1]`. -/
def fourOuter : ℝ := Real.sqrt ((15 + 2 * fourRadical) / 35)

/-- `0 ≤ √30 ≤ 6`. -/
theorem fourRadical_bounds : (0 : ℝ) ≤ fourRadical ∧ fourRadical ≤ 6 :=
  ⟨Real.sqrt_nonneg _, by nlinarith [fourRadical_sq]⟩

/-- `fourInner ^ 2 = (15 - 2√30)/35`. -/
theorem fourInner_sq : fourInner ^ 2 = (15 - 2 * fourRadical) / 35 :=
  Real.sq_sqrt (by nlinarith [fourRadical_bounds.2])

/-- `fourOuter ^ 2 = (15 + 2√30)/35`. -/
theorem fourOuter_sq : fourOuter ^ 2 = (15 + 2 * fourRadical) / 35 :=
  Real.sq_sqrt (by nlinarith [fourRadical_bounds.1])

/-- `fourInner` lies in `[0, 1]`. -/
theorem fourInner_mem : fourInner ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.sqrt_nonneg _, by nlinarith [fourInner_sq, fourRadical_bounds.1]⟩

/-- `fourOuter` lies in `[0, 1]`. -/
theorem fourOuter_mem : fourOuter ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.sqrt_nonneg _, by nlinarith [fourOuter_sq, fourRadical_bounds.2]⟩

/-- The four-point Gauss–Legendre rule with nodes in ascending order, `(1 ∓ fourOuter)/2` and
`(1 ∓ fourInner)/2`, with weights `(18 ∓ √30)/72`. -/
def four : QuadratureRule where
  terms := [((18 - fourRadical) / 72, (1 - fourOuter) / 2),
    ((18 + fourRadical) / 72, (1 - fourInner) / 2),
    ((18 + fourRadical) / 72, (1 + fourInner) / 2),
    ((18 - fourRadical) / 72, (1 + fourOuter) / 2)]
  nodes_mem_unit := by
    intro term h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;> subst term <;>
      constructor <;> dsimp <;>
      nlinarith [fourInner_mem.1, fourInner_mem.2, fourOuter_mem.1, fourOuter_mem.2]

/-- The four-point rule is exact through degree seven. -/
theorem four_exact : four.ExactUpTo 7 := by
  have hi4 : fourInner ^ 4 = ((15 - 2 * fourRadical) / 35) ^ 2 := by rw [← fourInner_sq, ← pow_mul]
  have ho4 : fourOuter ^ 4 = ((15 + 2 * fourRadical) / 35) ^ 2 := by rw [← fourOuter_sq, ← pow_mul]
  have hi6 : fourInner ^ 6 = ((15 - 2 * fourRadical) / 35) ^ 3 := by rw [← fourInner_sq, ← pow_mul]
  have ho6 : fourOuter ^ 6 = ((15 + 2 * fourRadical) / 35) ^ 3 := by rw [← fourOuter_sq, ← pow_mul]
  intro k hk
  interval_cases k <;>
    norm_num [QuadratureRule.moment, QuadratureRule.normalizedValue, four, weightedSum] <;>
    ring_nf <;>
    simp only [fourInner_sq, fourOuter_sq, hi4, ho4, hi6, ho6] <;>
    ring_nf <;> nlinarith [fourRadical_sq]

end
end CAS.Continuum.Legendre

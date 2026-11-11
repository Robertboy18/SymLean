/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.Rule

/-!
# Nodal quadrature rules and degree of exactness

A `NodalRule` is a finite family of nodes `xᵢ` and weights `wᵢ` on the real line, evaluated as
`Q(f) = ∑ wᵢ f(xᵢ)`.  Unlike `QuadratureRule`, which lives on the reference interval `[0,1]`
and is transported by `valueOn`, a nodal rule is attached to no interval: exactness is a
property relative to an interval `[a,b]` and a weight function `w`,

`Q(f) = ∫ₐᵇ f(x) w(x) dx`.

The rule has degree of exactness at least `d` for `(a, b, w)` when this holds for every
polynomial of degree at most `d`.  This is the setting of Gaussian, Newton-Cotes and weighted
rules alike.

## Main definitions

* `NodalRule.eval`: the value `∑ wᵢ f(xᵢ)`.
* `NodalRule.ExactFor`, `NodalRule.ExactToDegree`: exactness for one function, and for all
  polynomials of degree at most `d`, against `∫ₐᵇ · w`.
* `NodalRule.Positive`, `NodalRule.NodesIn`: nonnegative weights, and nodes in a given set.
* `NodalRule.transport`: the rule moved from `[a,b]` to `[c,d]` by the affine map
  `NodalRule.transportMap`.
* `QuadratureRule.toNodalRule`: a normalized rule transported to `[a,b]`.

## Main results

* `NodalRule.ExactFor.const_mul`, `NodalRule.ExactFor.finset_sum`: exactness is closed under
  linear combinations of integrable integrands.
* `NodalRule.exactToDegree_iff_monomial`: for a continuous weight, exactness to degree `d` is
  exactness on `1, x, …, x^d`.
* `NodalRule.ExactToDegree.transport`: affine transport preserves the degree of exactness,
  with the weight pulled back along the affine map.
* `QuadratureRule.toNodalRule_eval`, `QuadratureRule.toNodalRule_exactToDegree`: the
  transported normalized rule evaluates to `valueOn` and keeps its degree of exactness for the
  unit weight.

## Implementation notes

Two representations of a rule run through the library: `QuadratureRule`, whose degree of
exactness is stated through moments (`QuadratureRule.ExactUpTo`), and `NodalRule`.
`QuadratureRule.toNodalRule` passes from the first to the second without changing values.

* Panel rules and error control. A `PanelRule m` is a normalized rule with a one-panel error
  bound `M (b-a)^(m+1) / D` for `‖f^(m)‖ ≤ M`. Composite rules and adaptive search are built
  for every order `m` in `PanelRule`; tolerance planning requires `m > 0`.
  The trapezoidal and midpoint rules (`SecondOrder`) are the case `m = 2`; Simpson's rule and
  the two-point Gauss-Legendre rule (`simpsonRule.fourthOrder`, `gaussLegendreTwoRule.fourthOrder`)
  are the case `m = 4`.
* Positive rules.  A positive rule exact to degree `d` moves by at most a fixed multiple of
  `δ` between `f` and a polynomial of degree `d` within `δ` of `f`.  With the Weierstrass
  theorem this gives the Pólya-Steklov convergence theorem
  `NodalRule.tendsto_eval_of_positive` (`PositiveRule`).
* Gaussian rules.  For a continuous positive weight on `[a,b]` the monic orthogonal
  polynomials are built by projection (`Gaussian.Orthogonal`), satisfy the three-term
  recurrence (`Gaussian.Recurrence`) and have simple roots in `(a,b)` (`Gaussian.Roots`).
  For `n > 0`, their roots are the nodes of a positive rule exact to degree `2n - 1`
  (`exists_gaussian_quadrature`, `exists_nodalRule_gaussian`).  Exactness determines its
  nodes and weights (`Gaussian.Characterization`), and it has the classical remainder
  `f^(2n)(ξ) / (2n)! ∫ pₙ² w` (`Gaussian.Remainder`).  For the unit weight and two nodes it
  is `gaussLegendreTwoRule` (`Gaussian.GaussLegendreTwo`).
* Interpolatory rules. Integrating the Lagrange interpolant on `m ≥ 1` distinct nodes gives a
  rule exact to degree `m - 1`; on equispaced nodes including the endpoints this is the
  closed Newton-Cotes rule (`NewtonCotes`).

## References

* Philip J. Davis and Philip Rabinowitz, *Methods of Numerical Integration*, 2nd ed., Academic
  Press, Orlando, 1984, <https://doi.org/10.1016/C2013-0-10566-1>.
* Helmut Brass and Knut Petras, *Quadrature Theory: The Theory of Numerical Integration on a
  Compact Interval*, Mathematical Surveys and Monographs 178, American Mathematical Society,
  Providence, 2011, <https://doi.org/10.1090/surv/178>.
-/

@[expose] public section

open MeasureTheory Set Polynomial

namespace CAS.Continuum

/-- A quadrature rule given by finitely many real nodes and weights. -/
structure NodalRule where
  /-- The number of nodes. -/
  size : ℕ
  /-- The nodes `xᵢ`. -/
  node : Fin size → ℝ
  /-- The weights `wᵢ`. -/
  weight : Fin size → ℝ

namespace NodalRule

variable (Q : NodalRule)

/-- The value `∑ wᵢ f(xᵢ)` of the rule on `f`. -/
def eval (f : ℝ → ℝ) : ℝ :=
  ∑ i, Q.weight i * f (Q.node i)

/-- The rule integrates `f` exactly against the weight `w` on `a..b`.

As elsewhere in the library the integral is Mathlib's totalized interval integral, so this
equality does not assert integrability. -/
def ExactFor (a b : ℝ) (w f : ℝ → ℝ) : Prop :=
  Q.eval f = ∫ x in a..b, f x * w x

/-- The rule integrates every polynomial of degree at most `d` exactly against `w` on
`a..b`. -/
def ExactToDegree (a b : ℝ) (w : ℝ → ℝ) (d : ℕ) : Prop :=
  ∀ p : ℝ[X], p.natDegree ≤ d → Q.ExactFor a b w fun x ↦ p.eval x

/-- All weights are nonnegative.  Such rules are called positive quadrature rules. -/
def Positive : Prop :=
  ∀ i, 0 ≤ Q.weight i

/-- All nodes lie in `s`. -/
def NodesIn (s : Set ℝ) : Prop :=
  ∀ i, Q.node i ∈ s

/-! ### Linearity -/

/-- The value of the rule is additive in the integrand. -/
theorem eval_add (f g : ℝ → ℝ) :
    Q.eval (fun x ↦ f x + g x) = Q.eval f + Q.eval g := by
  simp only [eval, mul_add, Finset.sum_add_distrib]

/-- Scalars pull out of the value of the rule. -/
theorem eval_const_mul (c : ℝ) (f : ℝ → ℝ) :
    Q.eval (fun x ↦ c * f x) = c * Q.eval f := by
  simp only [eval, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The value of the rule is subtractive in the integrand. -/
theorem eval_sub (f g : ℝ → ℝ) :
    Q.eval (fun x ↦ f x - g x) = Q.eval f - Q.eval g := by
  simp only [eval, mul_sub, Finset.sum_sub_distrib]

/-- The value of the rule commutes with finite sums of integrands. -/
theorem eval_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) :
    Q.eval (fun x ↦ ∑ j ∈ s, f j x) = ∑ j ∈ s, Q.eval (f j) := by
  simp only [eval, Finset.mul_sum]
  exact Finset.sum_comm

/-- The value of the rule on a constant is the constant times the sum of the weights. -/
theorem eval_const (c : ℝ) : Q.eval (fun _ ↦ c) = c * ∑ i, Q.weight i := by
  rw [eval, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

variable {Q}

/-- Exactness is closed under scalar multiples. -/
theorem ExactFor.const_mul {a b : ℝ} {w f : ℝ → ℝ} (hf : Q.ExactFor a b w f) (c : ℝ) :
    Q.ExactFor a b w fun x ↦ c * f x := by
  unfold ExactFor at *
  rw [Q.eval_const_mul, hf, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun _ _ ↦ by simp only; ring

/-- Exactness is closed under finite sums of integrable integrands. -/
theorem ExactFor.finset_sum {ι : Type*} {a b : ℝ} {w : ℝ → ℝ} (s : Finset ι)
    {f : ι → ℝ → ℝ} (hf : ∀ j ∈ s, Q.ExactFor a b w (f j))
    (hfi : ∀ j ∈ s, IntervalIntegrable (fun x ↦ f j x * w x) volume a b) :
    Q.ExactFor a b w fun x ↦ ∑ j ∈ s, f j x := by
  unfold ExactFor at *
  rw [Q.eval_finset_sum, Finset.sum_congr rfl hf,
    ← intervalIntegral.integral_finsetSum hfi]
  exact intervalIntegral.integral_congr fun _ _ ↦ by simp only [Finset.sum_mul]

/-- A rule exact to any degree integrates constants, so its weights sum to `∫ₐᵇ w`. -/
theorem ExactToDegree.sum_weight {a b : ℝ} {w : ℝ → ℝ} {d : ℕ}
    (h : Q.ExactToDegree a b w d) : ∑ i, Q.weight i = ∫ x in a..b, w x := by
  have h1 := h 1 (by simp)
  simp only [ExactFor, eval_one, one_mul] at h1
  simpa [Q.eval_const] using h1

/-- For a continuous weight, exactness to degree `d` is exactness on the monomials
`1, x, …, x^d`. -/
theorem exactToDegree_iff_monomial {a b : ℝ} {w : ℝ → ℝ} (hw : ContinuousOn w (uIcc a b))
    (d : ℕ) :
    Q.ExactToDegree a b w d ↔ ∀ k ≤ d, Q.ExactFor a b w fun x ↦ x ^ k := by
  constructor
  · intro h k hk
    simpa using h (X ^ k) ((natDegree_X_pow_le k).trans hk)
  · intro h p hp
    rw [show (fun x ↦ p.eval x) = _ from funext fun x ↦ eval_eq_sum_range x]
    refine ExactFor.finset_sum _ (fun k hk ↦ (h k ?_).const_mul _) fun k _ ↦ ?_
    · exact (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans hp
    · exact ((continuous_const.mul (continuous_pow k)).continuousOn.mul hw).intervalIntegrable

/-! ### Affine transport -/

/-- The affine map `x ↦ c + (x - a) (d - c) / (b - a)`, sending `a` to `c` and, when
`a ≠ b`, sending `b` to `d`. -/
noncomputable def transportMap (a b c d x : ℝ) : ℝ :=
  c + (x - a) * ((d - c) / (b - a))

/-- `transportMap a b c d` sends `a` to `c`, for all real `a`, `b`, `c`, `d`. -/
@[simp]
theorem transportMap_left {a b c d : ℝ} : transportMap a b c d a = c := by
  simp [transportMap]

/-- For `a ≠ b`, `transportMap a b c d` sends `b` to `d`. -/
@[simp]
theorem transportMap_right {a b c d : ℝ} (hab : a ≠ b) : transportMap a b c d b = d := by
  have : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  simp only [transportMap]
  field_simp
  ring

/-- Change of variables along `transportMap`. -/
theorem integral_comp_transportMap {a b c d : ℝ} (hcd : c ≠ d) (g : ℝ → ℝ) :
    (∫ x in a..b, g (transportMap a b c d x)) = (b - a) / (d - c) * ∫ y in c..d, g y := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr hcd.symm
  set r := (d - c) / (b - a) with hr
  have hr0 : r ≠ 0 := div_ne_zero hdc hba
  have hmap : ∀ x, transportMap a b c d x = r * x + (c - a * r) := fun x ↦ by
    simp only [transportMap, ← hr]
    ring
  simp only [hmap]
  rw [intervalIntegral.integral_comp_mul_add g hr0, smul_eq_mul]
  have hlo : r * a + (c - a * r) = c := by ring
  have hhi : r * b + (c - a * r) = d := by
    rw [hr]
    field_simp
    ring
  rw [hlo, hhi, hr, inv_div]

variable (Q) in
/-- The rule moved from `[a,b]` to `[c,d]`: nodes are mapped by `transportMap` and weights are
scaled by `(d - c) / (b - a)`. -/
noncomputable def transport (a b c d : ℝ) : NodalRule where
  size := Q.size
  node i := transportMap a b c d (Q.node i)
  weight i := (d - c) / (b - a) * Q.weight i

/-- The transported value is the scaled value of the pulled-back integrand. -/
theorem eval_transport (a b c d : ℝ) (f : ℝ → ℝ) :
    (Q.transport a b c d).eval f =
      (d - c) / (b - a) * Q.eval fun x ↦ f (transportMap a b c d x) := by
  unfold eval transport
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- If the rule integrates the pullback of `f` against the pullback of `v` on `[a,b]`, the
transported rule integrates `f` against `v` on `[c,d]`. -/
theorem ExactFor.transport {a b c d : ℝ} (hab : a ≠ b) {v f : ℝ → ℝ}
    (h : Q.ExactFor a b (fun x ↦ v (transportMap a b c d x))
      fun x ↦ f (transportMap a b c d x)) :
    (Q.transport a b c d).ExactFor c d v f := by
  rcases eq_or_ne c d with rfl | hcd
  · unfold ExactFor
    rw [eval_transport]
    simp
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr hcd.symm
  unfold ExactFor at *
  have hchange := integral_comp_transportMap (a := a) (b := b) hcd fun y ↦ f y * v y
  rw [eval_transport, h, hchange, ← mul_assoc, div_mul_div_cancel₀ hba, div_self hdc, one_mul]

/-- The polynomial `C (c - a r) + C r X` with `r = (d - c) / (b - a)`, which evaluates to
`transportMap a b c d`. -/
private theorem transportMap_eq_eval (a b c d x : ℝ) :
    transportMap a b c d x =
      (C (c - a * ((d - c) / (b - a))) + C ((d - c) / (b - a)) * X).eval x := by
  rw [Polynomial.eval_add, eval_C, eval_mul, eval_C, eval_X]
  unfold transportMap
  ring

/-- Affine transport preserves the degree of exactness, with the weight pulled back along the
affine map. -/
theorem ExactToDegree.transport {a b c d : ℝ} (hab : a ≠ b) {v : ℝ → ℝ}
    {n : ℕ} (h : Q.ExactToDegree a b (fun x ↦ v (transportMap a b c d x)) n) :
    (Q.transport a b c d).ExactToDegree c d v n := by
  intro p hp
  apply ExactFor.transport hab
  set q : ℝ[X] := C (c - a * ((d - c) / (b - a))) + C ((d - c) / (b - a)) * X
  have hq : q.natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans
      (max_le ((natDegree_C _).le.trans zero_le_one) (natDegree_mul_le.trans (by simp)))
  have hfun : (fun x ↦ p.eval (transportMap a b c d x)) = fun x ↦ (p.comp q).eval x :=
    funext fun x ↦ by rw [eval_comp, transportMap_eq_eval]
  rw [hfun]
  exact h _ (natDegree_comp_le.trans ((Nat.mul_le_mul hp hq).trans (mul_one n).le))

end NodalRule

/-! ### Normalized rules as nodal rules -/

namespace QuadratureRule

/-- The normalized rule transported to `[a,b]`, as a nodal rule with nodes `a + tᵢ (b - a)`
and weights `(b - a) wᵢ`. -/
noncomputable def toNodalRule (rule : QuadratureRule) (a b : ℝ) : NodalRule where
  size := rule.terms.length
  node i := a + rule.terms[i].2 * (b - a)
  weight i := (b - a) * rule.terms[i].1

/-- The nodal form of a normalized rule evaluates to `valueOn`. -/
@[simp]
theorem toNodalRule_eval (rule : QuadratureRule) (a b : ℝ) (f : ℝ → ℝ) :
    (rule.toNodalRule a b).eval f = rule.valueOn f a b := by
  simp only [NodalRule.eval, toNodalRule, valueOn, termsOn, weightedSum, List.map_map]
  exact Fin.sum_univ_fun_getElem rule.terms fun term ↦ (b - a) * term.1 * f (a + term.2 * (b - a))

/-- On an ordered interval the nodes of the transported rule lie in `[a,b]`. -/
theorem toNodalRule_nodesIn (rule : QuadratureRule) {a b : ℝ} (hab : a ≤ b) :
    (rule.toNodalRule a b).NodesIn (Icc a b) := by
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, a + t * (b - a) ∈ Icc a b := fun t ht ↦ by
    constructor <;> nlinarith [ht.1, ht.2]
  exact fun i ↦ hmem _ (rule.nodes_mem_unit _ (List.getElem_mem _))

/-- A rule with nonnegative normalized weights is positive on an ordered interval. -/
theorem toNodalRule_positive {rule : QuadratureRule} {a b : ℝ} (hab : a ≤ b)
    (hpositive : ∀ term ∈ rule.terms, 0 ≤ term.1) : (rule.toNodalRule a b).Positive :=
  fun i ↦ mul_nonneg (sub_nonneg.mpr hab) (hpositive _ (List.getElem_mem i.2))

/-- Moment exactness through degree `d` is degree of exactness `d` of the transported rule for
the unit weight. -/
theorem toNodalRule_exactToDegree {rule : QuadratureRule} {d : ℕ} (hexact : rule.ExactUpTo d)
    (a b : ℝ) : (rule.toNodalRule a b).ExactToDegree a b (fun _ ↦ 1) d := by
  intro p hp
  simp only [NodalRule.ExactFor, toNodalRule_eval, mul_one]
  exact valueOn_eq_integral_of_natDegree_le hexact p hp a b

end QuadratureRule
end CAS.Continuum

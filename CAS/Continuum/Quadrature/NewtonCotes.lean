/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.Gaussian.Nodal
public import CAS.Continuum.Quadrature.SecondOrder

/-!
# Interpolatory rules and the closed Newton-Cotes rules

Given `m ≥ 1` distinct nodes `x₀, …, x_{m-1}` and a weight `w`, the interpolatory rule
integrates the Lagrange interpolant of `f`: its weights are `∫ₐᵇ ℓᵢ w`, where `ℓᵢ` is the `i`-th
Lagrange basis polynomial.  Since a polynomial of degree below `m` is its own interpolant, the
rule has degree of exactness at least `m - 1` for every continuous weight.

The closed Newton-Cotes rule with `n ≥ 2` points is the interpolatory rule for the unit weight
on the equispaced nodes `a + i (b - a)/(n - 1)`, `i = 0, …, n - 1`, which include both
endpoints.  With two points it is the trapezoidal rule.

## Main definitions

* `NodalRule.interpolatory`: the interpolatory rule for a weight and a family of nodes.
* `newtonCotesNodes`, `newtonCotes`: the equispaced nodes and the closed Newton-Cotes rule.

## Main results

* `NodalRule.interpolatory_exactToDegree`: an interpolatory rule on `m ≥ 1` distinct nodes is exact
  to degree `m - 1`.
* `newtonCotes_exactToDegree`: the `n`-point closed Newton-Cotes rule is exact to degree
  `n - 1`.
* `newtonCotes_two_eval`: the two-point rule is the trapezoidal rule.

## References

* NIST Digital Library of Mathematical Functions, §3.5 Quadrature, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/3.5>. §3.5(iv): an interpolatory rule with `n` nodes integrates every
  polynomial of degree at most `n - 1` exactly, its weights come from the Lagrange interpolation
  polynomial, and the Newton-Cotes formulas, the trapezoidal rule among them, are closed: the
  extreme nodes are the endpoints.
* Philip J. Davis and Philip Rabinowitz, *Methods of Numerical Integration*, 2nd ed., Academic
  Press, Orlando, 1984, <https://doi.org/10.1016/C2013-0-10566-1>.
* Helmut Brass and Knut Petras, *Quadrature Theory: The Theory of Numerical Integration on a
  Compact Interval*, Mathematical Surveys and Monographs 178, American Mathematical Society,
  Providence, 2011, <https://doi.org/10.1090/surv/178>.
-/

@[expose] public section

open MeasureTheory Set Polynomial

namespace CAS.Continuum

namespace NodalRule

/-- The interpolatory rule on the nodes `x` for the weight `w` on `a..b`: the weight at `xᵢ` is
the integral of the `i`-th Lagrange basis polynomial against `w`. -/
noncomputable def interpolatory (a b : ℝ) (w : ℝ → ℝ) (hw : ContinuousOn w (uIcc a b))
    {m : ℕ} (x : Fin m → ℝ) : NodalRule where
  size := m
  node := x
  weight := interpolatoryWeight (polynomialIntegral a b w hw) x

/-- An interpolatory rule on `m ≥ 1` distinct nodes has degree of exactness at least `m - 1`. -/
theorem interpolatory_exactToDegree {a b : ℝ} {w : ℝ → ℝ} (hw : ContinuousOn w (uIcc a b))
    {m : ℕ} (hm : 0 < m) {x : Fin m → ℝ} (hx : Function.Injective x) :
    (interpolatory a b w hw x).ExactToDegree a b w (m - 1) := fun p hp ↦
  interpolatory_exact (polynomialIntegral a b w hw) x hx p
    (degree_le_natDegree.trans_lt (by exact_mod_cast (show p.natDegree < m by omega)))

end NodalRule

/-- The `n` equispaced nodes `a + i (b - a)/(n - 1)` on `[a,b]`, including both endpoints when
`n ≥ 2`. -/
noncomputable def newtonCotesNodes (a b : ℝ) (n : ℕ) : Fin n → ℝ :=
  fun i ↦ a + i * (b - a) / ((n : ℝ) - 1)

/-- The interpolatory rule on `newtonCotesNodes`; for `n ≥ 2` these are the closed
Newton-Cotes nodes on `[a,b]`. -/
noncomputable def newtonCotes (a b : ℝ) (n : ℕ) : NodalRule :=
  NodalRule.interpolatory a b (fun _ ↦ 1) continuousOn_const (newtonCotesNodes a b n)

private theorem natCast_sub_one_ne_zero {n : ℕ} (hn : 2 ≤ n) : (n : ℝ) - 1 ≠ 0 :=
  sub_ne_zero.mpr (Nat.cast_ne_one.mpr (by omega))

/-- Distinct indices give distinct equispaced nodes on a nondegenerate interval. -/
theorem newtonCotesNodes_injective {a b : ℝ} (hab : a ≠ b) {n : ℕ} :
    Function.Injective (newtonCotesNodes a b n) := fun i j hij ↦ by
  rcases lt_or_ge n 2 with hn | hn
  · exact Fin.ext (by have := i.2; have := j.2; omega)
  simpa [newtonCotesNodes, natCast_sub_one_ne_zero hn, sub_ne_zero.mpr hab.symm, Fin.val_inj]
    using hij

/-- The equispaced nodes lie in `[a,b]`. -/
theorem newtonCotes_nodesIn {a b : ℝ} (hab : a ≤ b) {n : ℕ} (hn : 2 ≤ n) :
    (newtonCotes a b n).NodesIn (Icc a b) := by
  intro i
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (by omega : 1 < n))
  have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.2
  have hq : (i : ℝ) * (b - a) / ((n : ℝ) - 1) ≤ b - a := by
    rw [div_le_iff₀ hpos]
    nlinarith
  change a + (i : ℝ) * (b - a) / ((n : ℝ) - 1) ∈ Icc a b
  exact ⟨le_add_of_nonneg_right (by positivity), by linarith⟩

/-- The `n`-point closed Newton-Cotes rule, `n ≥ 2`, integrates every polynomial of degree at
most `n - 1` exactly on `[a,b]`. On a degenerate interval `a = b` every weight and every
integral is `0`. -/
theorem newtonCotes_exactToDegree {a b : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    (newtonCotes a b n).ExactToDegree a b (fun _ ↦ 1) (n - 1) := by
  rcases eq_or_ne a b with rfl | hab
  · intro p _
    simp [NodalRule.ExactFor, NodalRule.eval, newtonCotes, NodalRule.interpolatory,
      interpolatoryWeight, polynomialIntegral]
  exact NodalRule.interpolatory_exactToDegree _ (by omega) (newtonCotesNodes_injective hab)

/-- The two-point closed Newton-Cotes rule is the trapezoidal rule. -/
theorem newtonCotes_two_eval {a b : ℝ} (f : ℝ → ℝ) :
    (newtonCotes a b 2).eval f = trapezoidRule.valueOn f a b := by
  rcases eq_or_ne a b with rfl | hab
  · simp [NodalRule.eval, newtonCotes, NodalRule.interpolatory, interpolatoryWeight,
      polynomialIntegral, trapezoidRule_valueOn_eq_formula]
  have hexact := newtonCotes_exactToDegree (a := a) (b := b) le_rfl
  have h0 := hexact 1 (by simp)
  have h1 := hexact X (by simp)
  have hnode0 : newtonCotesNodes a b 2 0 = a := by simp [newtonCotesNodes]
  have hnode1 : newtonCotesNodes a b 2 1 = b := by norm_num [newtonCotesNodes]
  set W : Fin 2 → ℝ := (newtonCotes a b 2).weight
  change ∑ i : Fin 2, W i * eval (newtonCotesNodes a b 2 i) 1 = _ at h0
  change ∑ i : Fin 2, W i * eval (newtonCotesNodes a b 2 i) X = _ at h1
  change ∑ i : Fin 2, W i * f (newtonCotesNodes a b 2 i) = _
  simp only [Fin.sum_univ_two, eval_one, eval_X, mul_one, hnode0, hnode1,
    intervalIntegral.integral_const, smul_eq_mul, integral_id] at h0 h1 ⊢
  have hW1 : W 1 = (b - a) / 2 := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr hab.symm)
    linear_combination h1 - a * h0
  have hW0 : W 0 = (b - a) / 2 := by linarith
  rw [hW0, hW1, trapezoidRule_valueOn_eq_formula]
  ring

end CAS.Continuum

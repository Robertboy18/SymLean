/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Topology.ContinuousMap.Weierstrass
public import CAS.Continuum.Quadrature.Approximation
public import CAS.Continuum.Quadrature.NodalRule

/-!
# Convergence of positive quadrature rules

A positive rule, one with nonnegative weights, that is exact on constants has total weight
`∫ₐᵇ w`.  So if a polynomial `p` is within `δ` of `f` on `[a,b]` and the rule integrates `p`
exactly, then both the rule and the integral move by a multiple of `δ` between `p` and `f`,
with a constant that does not depend on the number of nodes.  With the Weierstrass
approximation theorem this gives the theorem of Pólya and Steklov: positive rules whose degree
of exactness tends to infinity converge for every continuous integrand.

## Main results

* `NodalRule.abs_eval_sub_integral_le_of_polynomial_approx`: the error of a positive rule on
  `f` is at most `δ (∫ w + ∫ |w|)` when a polynomial integrated exactly is `δ`-close to `f`.
* `NodalRule.tendsto_eval_of_positive`: the Pólya-Steklov theorem for a continuous weight on
  `[a,b]`.
* `QuadratureRule.tendsto_valueOn_of_nonneg`: the same for normalized rules transported to
  `[a,b]` by `valueOn`.

## Implementation notes

`ExactToDegree.sum_weight` turns exactness on constants into `∑ wᵢ = ∫ w`, so positivity bounds
the change of the rule by `δ ∫ w`, while the integral changes by at most `δ ∫ |w|`. Mathlib's
`exists_polynomial_near_of_continuousOn` supplies the polynomial, and `tendsto_eval_of_positive`
takes `|∫ w| + ∫ |w| + 1` as the constant shared by every rule of the sequence. The unit-weight
theorem applies the weighted one to `QuadratureRule.toNodalRule`.

## References

* George Pólya, "Über die Konvergenz von Quadraturverfahren", *Mathematische Zeitschrift* 37
  (1933), pp. 264-286, <https://doi.org/10.1007/BF01474574>. Satz I (p. 267): a procedure that
  converges for every polynomial converges for every continuous `f` on `[a, b]` if and only if
  the sums `∑ |λₙᵢ|` of the absolute values of the weights are bounded. Satz I has no weight
  function. For a positive rule exact on constants the sum is the total weight, and we prove the
  sufficiency directly, for a continuous weight.
* Philip J. Davis and Philip Rabinowitz, *Methods of Numerical Integration*, 2nd ed., Academic
  Press, Orlando, 1984, <https://doi.org/10.1016/C2013-0-10566-1>.
* Helmut Brass and Knut Petras, *Quadrature Theory: The Theory of Numerical Integration on a
  Compact Interval*, Mathematical Surveys and Monographs 178, American Mathematical Society,
  Providence, 2011, <https://doi.org/10.1090/surv/178>.
-/

@[expose] public section

open MeasureTheory Set Polynomial Filter Topology

namespace CAS.Continuum

namespace NodalRule

variable {Q : NodalRule}

/-- A positive rule with nodes in `s` moves by at most `δ ∑ wᵢ` between two integrands that are
`δ`-close on `s`. -/
theorem abs_eval_sub_le_of_positive (hpos : Q.Positive) {s : Set ℝ} (hnodes : Q.NodesIn s)
    {f g : ℝ → ℝ} {δ : ℝ} (hfg : ∀ x ∈ s, |f x - g x| ≤ δ) :
    |Q.eval f - Q.eval g| ≤ δ * ∑ i, Q.weight i := by
  rw [← Q.eval_sub, eval, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [abs_mul, abs_of_nonneg (hpos i), mul_comm]
  exact mul_le_mul_of_nonneg_right (hfg _ (hnodes i)) (hpos i)

/-- Error of a positive rule from uniform polynomial approximation.

If the rule is exact to degree `d` against a continuous weight `w`, its nodes lie in `[a,b]`,
and a polynomial of degree at most `d` is within `δ` of `f` on `[a,b]`, then the error on `f` is
at most `δ (∫ₐᵇ w + ∫ₐᵇ |w|)`. -/
theorem abs_eval_sub_integral_le_of_polynomial_approx {a b : ℝ} (hab : a ≤ b) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Icc a b)) (hpos : Q.Positive) (hnodes : Q.NodesIn (Icc a b))
    {d : ℕ} (hexact : Q.ExactToDegree a b w d) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (p : ℝ[X]) (hp : p.natDegree ≤ d) {δ : ℝ}
    (happrox : ∀ x ∈ Icc a b, |p.eval x - f x| ≤ δ) :
    |Q.eval f - ∫ x in a..b, f x * w x| ≤
      δ * ((∫ x in a..b, w x) + ∫ x in a..b, |w x|) := by
  have hrule : |Q.eval f - Q.eval fun x ↦ p.eval x| ≤ δ * ∫ x in a..b, w x := by
    rw [← hexact.sum_weight]
    exact abs_eval_sub_le_of_positive hpos hnodes fun x hx ↦
      (abs_sub_comm _ _).trans_le (happrox x hx)
  have hfw : IntervalIntegrable (fun x ↦ f x * w x) volume a b :=
    (hf.mul hw).intervalIntegrable_of_Icc hab
  have hpw : IntervalIntegrable (fun x ↦ p.eval x * w x) volume a b :=
    (p.continuous.continuousOn.mul hw).intervalIntegrable_of_Icc hab
  have hintegral :
      |(∫ x in a..b, p.eval x * w x) - ∫ x in a..b, f x * w x| ≤
        δ * ∫ x in a..b, |w x| := by
    rw [← intervalIntegral.integral_sub hpw hfw, ← intervalIntegral.integral_const_mul]
    refine (intervalIntegral.abs_integral_le_integral_abs hab).trans
      (intervalIntegral.integral_mono_on hab (hpw.sub hfw).abs
        ((hw.abs.const_smul δ).intervalIntegrable_of_Icc hab) fun x hx ↦ ?_)
    rw [← sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (happrox x hx) (abs_nonneg _)
  rw [hexact p hp] at hrule
  have htri := abs_sub_le (Q.eval f) (∫ x in a..b, p.eval x * w x) (∫ x in a..b, f x * w x)
  linarith

/-- **Pólya-Steklov theorem.**  Let `w` be continuous on `[a,b]` and let `Qₙ` be positive rules
with nodes in `[a,b]`, the `n`-th exact to degree `dₙ` against `w`, with `dₙ → ∞`.  Then
`Qₙ(f) → ∫ₐᵇ f w` for every `f` continuous on `[a,b]`. -/
theorem tendsto_eval_of_positive {Q : ℕ → NodalRule} {deg : ℕ → ℕ} {a b : ℝ} {w f : ℝ → ℝ}
    (hab : a ≤ b) (hw : ContinuousOn w (Icc a b)) (hpos : ∀ n, (Q n).Positive)
    (hnodes : ∀ n, (Q n).NodesIn (Icc a b)) (hexact : ∀ n, (Q n).ExactToDegree a b w (deg n))
    (hdeg : Tendsto deg atTop atTop) (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n ↦ (Q n).eval f) atTop (𝓝 (∫ x in a..b, f x * w x)) := by
  set K := |∫ x in a..b, w x| + (∫ x in a..b, |w x|) + 1
  have habs : 0 ≤ ∫ x in a..b, |w x| :=
    intervalIntegral.integral_nonneg hab fun _ _ ↦ abs_nonneg _
  have hK : 0 < K := by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / (2 * K)
  have hδ : 0 < δ := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f hf δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_atTop.mp hdeg p.natDegree)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hbound := abs_eval_sub_integral_le_of_polynomial_approx hab hw (hpos n) (hnodes n)
    (hexact n) hf p (hN n hn) fun x hx ↦ (hp x hx).le
  have hle : δ * ((∫ x in a..b, w x) + ∫ x in a..b, |w x|) ≤ δ * K :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self (∫ x in a..b, w x)]) hδ.le
  have hδK : δ * K = ε / 2 := by
    simp only [δ]
    field_simp
  rw [Real.dist_eq]
  linarith

end NodalRule

namespace QuadratureRule

/-- **Pólya-Steklov theorem for normalized rules.**  Rules with nonnegative weights on `[0,1]`,
the `n`-th exact through degree `dₙ` with `dₙ → ∞`, converge on every ordered interval to
`∫ₐᵇ f` for every continuous `f`.  This is `NodalRule.tendsto_eval_of_positive` for the unit
weight. -/
theorem tendsto_valueOn_of_nonneg (rules : ℕ → QuadratureRule) {deg : ℕ → ℕ}
    (hpositive : ∀ n, ∀ term ∈ (rules n).terms, 0 ≤ term.1)
    (hexact : ∀ n, (rules n).ExactUpTo (deg n)) (hdeg : Tendsto deg atTop atTop)
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n ↦ (rules n).valueOn f a b) atTop (𝓝 (∫ x in a..b, f x)) := by
  simpa using NodalRule.tendsto_eval_of_positive (Q := fun n ↦ (rules n).toNodalRule a b)
    (w := fun _ ↦ 1) hab continuousOn_const
    (fun n ↦ toNodalRule_positive hab (hpositive n))
    (fun n ↦ (rules n).toNodalRule_nodesIn hab)
    (fun n ↦ toNodalRule_exactToDegree (hexact n) a b) hdeg hf

end QuadratureRule
end CAS.Continuum

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import CAS.Calculus.Euclidean
public import CAS.Integration.Check

/-!
# Analytic semantics of checked antiderivatives

An `IntegrationCheck.AntiderivativeCert i integrand` (defined in
`CAS.Integration.Check`) is a primitive whose symbolic derivative in coordinate `i`
was checked to equal `integrand`. Read as one-dimensional calculus along the coordinate line
`t ↦ x + t • e_i`, at points where the certificate's domain requirements hold, it gives the
fundamental theorem of calculus on bounded intervals, on half-lines and on the whole line.

## Main results

* `hasDerivAt_eval_add_smul_single`: the primitive has the integrand as derivative along the
  line.
* `intervalIntegral_eq_sub_eval_add_smul_single`: the fundamental theorem of calculus on a
  bounded interval, and `intervalIntegral_eq_sub_of_line` the same theorem for the real
  functions that the integrand and the primitive evaluate to on a line of vectors.
* `integrableOn_Ioi_and_integral_eq`, `integrableOn_Iic_and_integral_eq`: the fundamental theorem
  on the half-lines `(a, +∞)` and `(-∞, a]`, where the primitive's limit at the infinite end
  replaces the endpoint. The integrand is assumed integrable, nonnegative or nonpositive on the
  half-line, and the conclusion is its integrability together with the value of its integral.
* `integrable_and_integral_eq`: the same on the whole line, with the limits at `+∞` and `-∞` and
  the three-way premise on each side of a split point, so the sign may change there.
* `CAS.integrableOn_Iic_deriv_of_nonneg'` and `CAS.integrableOn_Iic_deriv_of_nonpos'`: a
  derivative of constant sign on `(-∞, a]` is integrable there when the function has a limit at
  `-∞`, the counterparts of Mathlib's `integrableOn_Ioi_deriv_of_nonneg'` and
  `integrableOn_Ioi_deriv_of_nonpos'` on `(a, +∞)`.

## Implementation notes

We prove one derivative statement, `hasDerivAt_eval_add_smul_single`, from
`IntegrationCheck.AntiderivativeCert.eval_diff_eq` and the soundness of symbolic differentiation
along a coordinate line, `Verified.Expr.hasDerivAt_eval_add_smul_single`, and obtain the
integrals from Mathlib's one-variable theorems `intervalIntegral.integral_eq_sub_of_hasDerivAt`,
`integral_Ioi_of_hasDerivAt_of_tendsto'`, `integral_Iic_of_hasDerivAt_of_tendsto'` and
`integral_of_hasDerivAt_of_tendsto`. On a bounded interval the integrand is valid, hence
differentiable along the line and continuous, which gives its integrability. The primed
half-line theorems also differentiate at the endpoint, so the requirements are assumed on the
closed half-lines.

These statements do not depend on the antiderivative planner.
-/

@[expose] public section

namespace CAS

open MeasureTheory Filter Topology

namespace IntegrationCheck.AntiderivativeCert

/--
The certified primitive has the integrand as its derivative along the selected
coordinate line.
-/
theorem hasDerivAt_eval_add_smul_single
    {n : Nat} {i : Fin n} {integrand : Verified.Expr (Fin n)}
    (cert : IntegrationCheck.AntiderivativeCert i integrand)
    (x : ℝ^n) (t : ℝ)
    (hrequirements : cert.requirements.Holds
      (x + t • EuclideanSpace.single i (1 : ℝ))) :
    HasDerivAt
      (fun s : ℝ ↦ cert.candidate.eval
        (x + s • EuclideanSpace.single i (1 : ℝ)))
      (integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ))) t := by
  rw [← cert.eval_diff_eq (x + t • EuclideanSpace.single i (1 : ℝ)) hrequirements]
  exact Verified.Expr.hasDerivAt_eval_add_smul_single _ x i t
    (cert.candidate_validAt _ hrequirements)

/--
Fundamental theorem of calculus for a certified primitive along one coordinate
line.
-/
theorem intervalIntegral_eq_sub_eval_add_smul_single
    {n : Nat} {i : Fin n} {integrand : Verified.Expr (Fin n)}
    (cert : IntegrationCheck.AntiderivativeCert i integrand)
    (x : ℝ^n) (a b : ℝ)
    (hrequirements : ∀ t, t ∈ Set.uIcc a b →
      cert.requirements.Holds
        (x + t • EuclideanSpace.single i (1 : ℝ))) :
    (∫ t in a..b, integrand.eval
      (x + t • EuclideanSpace.single i (1 : ℝ))) =
      cert.candidate.eval (x + b • EuclideanSpace.single i (1 : ℝ)) -
        cert.candidate.eval (x + a • EuclideanSpace.single i (1 : ℝ)) := by
  refine _root_.intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ cert.hasDerivAt_eval_add_smul_single x t (hrequirements t ht))
    (ContinuousOn.intervalIntegrable fun t ht ↦ ?_)
  exact (Verified.Expr.hasDerivAt_eval_add_smul_single integrand x i t
    (cert.integrand_validAt _ (hrequirements t ht))).continuousAt.continuousWithinAt

/--
The fundamental theorem of calculus for a certified primitive, about real functions. Let `σ s` be
the point whose coordinate `i` is `s` and whose other coordinates are fixed, `f s` the value of
the integrand there, and `Fa` and `Fb` the values of the primitive at `σ a` and `σ b`. When the
requirements of the certificate are the lists `N` and `P` and hold at `σ s` for every `s` between
`a` and `b`, the integral of `f` from `a` to `b` is `Fb - Fa`.
-/
theorem intervalIntegral_eq_sub_of_line
    {n : Nat} {i : Fin n} {integrand : Verified.Expr (Fin n)}
    (cert : IntegrationCheck.AntiderivativeCert i integrand)
    {N P : List (Verified.Expr (Fin n))} (hrequirements : cert.requirements = ⟨N, P⟩)
    (σ : ℝ → Fin n → ℝ) (hσ : ∀ s, σ s = Function.update (σ 0) i s)
    {f : ℝ → ℝ} (hf : ∀ s, integrand.eval (σ s) = f s) (a b : ℝ) {Fa Fb : ℝ}
    (hFa : cert.candidate.eval (σ a) = Fa) (hFb : cert.candidate.eval (σ b) = Fb)
    (hholds : ∀ s ∈ Set.uIcc a b,
      (∀ d ∈ N, d.eval (σ s) ≠ 0) ∧ ∀ d ∈ P, 0 < d.eval (σ s)) :
    ∫ s in a..b, f s = Fb - Fa := by
  obtain ⟨x, hx⟩ : ∃ x : ℝ^n, x = WithLp.toLp 2 (Function.update (σ 0) i 0) := ⟨_, rfl⟩
  have hline : ∀ s : ℝ, (x + s • EuclideanSpace.single i (1 : ℝ) : Fin n → ℝ) = σ s := by
    intro s
    funext j
    rw [hσ s, hx]
    by_cases hj : j = i
    · rw [hj]
      simp
    · simp [hj]
  have hline' : ∀ s : ℝ, WithLp.ofLp (x + s • EuclideanSpace.single i (1 : ℝ)) = σ s :=
    fun s ↦ by simpa only [WithLp.ofLp_add, WithLp.ofLp_smul] using hline s
  have key := cert.intervalIntegral_eq_sub_eval_add_smul_single x a b fun s hs ↦ by
    rw [hrequirements, Verified.Expr.ValidityRequirements.Holds]
    simpa only [hline] using hholds s hs
  simpa only [hline', hf, hFa, hFb] using key

open Set in
/-- When a function has a limit at `-∞` and its derivative is nonnegative on `(-∞, a]`, the
derivative is integrable on `(-∞, a]`. This mirrors Mathlib's `integrableOn_Ioi_deriv_of_nonneg'`.
-/
theorem _root_.CAS.integrableOn_Iic_deriv_of_nonneg' {g g' : ℝ → ℝ} {a l : ℝ}
    (hderiv : ∀ x ∈ Iic a, HasDerivAt g (g' x) x)
    (g'pos : ∀ x ∈ Iic a, 0 ≤ g' x) (hg : Tendsto g atBot (𝓝 l)) :
    IntegrableOn g' (Iic a) := by
  have hcont : ContinuousOn g (Iic a) := fun x hx ↦
    (hderiv x hx).continuousAt.continuousWithinAt
  have hint : ∀ x ≤ a, IntegrableOn g' (Ioc x a) := fun x _ ↦
    intervalIntegral.integrableOn_deriv_of_nonneg (hcont.mono Icc_subset_Iic_self)
      (fun y hy ↦ hderiv y hy.2.le) (fun y hy ↦ g'pos y hy.2.le)
  refine integrableOn_Iic_of_intervalIntegral_norm_tendsto (g a - l) a (a := id)
    (fun x ↦ ?_) tendsto_id ?_
  · rcases le_or_gt x a with hx | hx
    · exact hint x hx
    · simp [Ioc_eq_empty_of_le hx.le]
  apply Tendsto.congr' _ (hg.const_sub (g a))
  filter_upwards [Iic_mem_atBot a] with x hx
  have hx : x ≤ a := hx
  calc
    g a - g x = ∫ y in x..a, g' y := by
      symm
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx
        (hcont.mono Icc_subset_Iic_self) fun y hy ↦ hderiv y hy.2.le
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
      exact hint x hx
    _ = ∫ y in x..id a, ‖g' y‖ := by
      simp_rw [id, intervalIntegral.integral_of_le hx]
      refine setIntegral_congr_fun measurableSet_Ioc fun y hy ↦ ?_
      dsimp
      rw [abs_of_nonneg (g'pos y hy.2)]

/-- When a function has a limit at `-∞` and its derivative is nonpositive on `(-∞, a]`, the
derivative is integrable on `(-∞, a]`. -/
theorem _root_.CAS.integrableOn_Iic_deriv_of_nonpos' {g g' : ℝ → ℝ} {a l : ℝ}
    (hderiv : ∀ x ∈ Set.Iic a, HasDerivAt g (g' x) x)
    (g'neg : ∀ x ∈ Set.Iic a, g' x ≤ 0) (hg : Tendsto g atBot (𝓝 l)) :
    IntegrableOn g' (Set.Iic a) := by
  apply integrable_neg_iff.1
  exact integrableOn_Iic_deriv_of_nonneg' (fun x hx ↦ (hderiv x hx).neg)
    (fun x hx ↦ neg_nonneg_of_nonpos (g'neg x hx)) hg.neg

/--
The fundamental theorem of calculus for a certified primitive `F` on the half-line `(a, +∞)`, along
one coordinate line, with the integrability of the integrand `f`. Let the requirements of the
certificate hold on `[a, +∞)` and `F` tend to `limit` at `+∞`. If `f` is integrable on `(a, +∞)`,
or nonnegative there, or nonpositive there, then `f` is integrable on `(a, +∞)` and its integral
is `limit - F a`. The requirements are needed at `a` because Mathlib's
`integral_Ioi_of_hasDerivAt_of_tendsto'` differentiates there; integrability follows from a sign
by Mathlib's `integrableOn_Ioi_deriv_of_nonneg'` and `integrableOn_Ioi_deriv_of_nonpos'`.
-/
theorem integrableOn_Ioi_and_integral_eq
    {n : Nat} {i : Fin n} {integrand : Verified.Expr (Fin n)}
    (cert : IntegrationCheck.AntiderivativeCert i integrand)
    (x : ℝ^n) (a limit : ℝ)
    (hrequirements : ∀ t, t ∈ Set.Ici a →
      cert.requirements.Holds (x + t • EuclideanSpace.single i (1 : ℝ)))
    (hlimit : Tendsto
      (fun t : ℝ ↦ cert.candidate.eval (x + t • EuclideanSpace.single i (1 : ℝ)))
      atTop (𝓝 limit))
    (hf : IntegrableOn
        (fun t : ℝ ↦ integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ))) (Set.Ioi a) ∨
      (∀ t, t ∈ Set.Ioi a → 0 ≤ integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ))) ∨
      ∀ t, t ∈ Set.Ioi a → integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ)) ≤ 0) :
    IntegrableOn (fun t : ℝ ↦ integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ)))
        (Set.Ioi a) ∧
      ∫ t in Set.Ioi a, integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ)) =
        limit - cert.candidate.eval (x + a • EuclideanSpace.single i (1 : ℝ)) := by
  have hderiv := fun t ht ↦ cert.hasDerivAt_eval_add_smul_single x t (hrequirements t ht)
  have hint : IntegrableOn
      (fun t : ℝ ↦ integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ))) (Set.Ioi a) := by
    rcases hf with h | h | h
    · exact h
    · exact integrableOn_Ioi_deriv_of_nonneg' hderiv h hlimit
    · exact integrableOn_Ioi_deriv_of_nonpos' hderiv h hlimit
  exact ⟨hint, integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlimit⟩

/--
The fundamental theorem of calculus for a certified primitive `F` on the half-line `(-∞, a]`, along
one coordinate line, with the integrability of the integrand `f`. Let the requirements of the
certificate hold on `(-∞, a]` and `F` tend to `limit` at `-∞`. If `f` is integrable on `(-∞, a]`,
or nonnegative there, or nonpositive there, then `f` is integrable on `(-∞, a]` and its integral
is `F a - limit`. Integrability follows from a sign by `CAS.integrableOn_Iic_deriv_of_nonneg'`
and `CAS.integrableOn_Iic_deriv_of_nonpos'`.
-/
theorem integrableOn_Iic_and_integral_eq
    {n : Nat} {i : Fin n} {integrand : Verified.Expr (Fin n)}
    (cert : IntegrationCheck.AntiderivativeCert i integrand)
    (x : ℝ^n) (a limit : ℝ)
    (hrequirements : ∀ t, t ∈ Set.Iic a →
      cert.requirements.Holds (x + t • EuclideanSpace.single i (1 : ℝ)))
    (hlimit : Tendsto
      (fun t : ℝ ↦ cert.candidate.eval (x + t • EuclideanSpace.single i (1 : ℝ)))
      atBot (𝓝 limit))
    (hf : IntegrableOn
        (fun t : ℝ ↦ integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ))) (Set.Iic a) ∨
      (∀ t, t ∈ Set.Iic a → 0 ≤ integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ))) ∨
      ∀ t, t ∈ Set.Iic a → integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ)) ≤ 0) :
    IntegrableOn (fun t : ℝ ↦ integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ)))
        (Set.Iic a) ∧
      ∫ t in Set.Iic a, integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ)) =
        cert.candidate.eval (x + a • EuclideanSpace.single i (1 : ℝ)) - limit := by
  have hderiv := fun t ht ↦ cert.hasDerivAt_eval_add_smul_single x t (hrequirements t ht)
  have hint : IntegrableOn
      (fun t : ℝ ↦ integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ))) (Set.Iic a) := by
    rcases hf with h | h | h
    · exact h
    · exact integrableOn_Iic_deriv_of_nonneg' hderiv h hlimit
    · exact integrableOn_Iic_deriv_of_nonpos' hderiv h hlimit
  exact ⟨hint, integral_Iic_of_hasDerivAt_of_tendsto' hderiv hint hlimit⟩

/--
The fundamental theorem of calculus for a certified primitive `F` on the whole line, along one
coordinate line, with the integrability of the integrand `f`. Let the requirements of the
certificate hold everywhere and `F` tend to `lower` at `-∞` and to `upper` at `+∞`. If, for a split
point `c`, `f` is integrable, nonnegative or nonpositive on `(-∞, c]`, and also integrable,
nonnegative or nonpositive on `(c, +∞)`, then `f` is integrable and its integral is
`upper - lower`. The sign may change at `c`; the two halves are
`integrableOn_Iic_and_integral_eq` and `integrableOn_Ioi_and_integral_eq`.
-/
theorem integrable_and_integral_eq
    {n : Nat} {i : Fin n} {integrand : Verified.Expr (Fin n)}
    (cert : IntegrationCheck.AntiderivativeCert i integrand)
    (x : ℝ^n) (lower upper c : ℝ)
    (hrequirements : ∀ t : ℝ,
      cert.requirements.Holds (x + t • EuclideanSpace.single i (1 : ℝ)))
    (hlower : Tendsto
      (fun t : ℝ ↦ cert.candidate.eval (x + t • EuclideanSpace.single i (1 : ℝ)))
      atBot (𝓝 lower))
    (hupper : Tendsto
      (fun t : ℝ ↦ cert.candidate.eval (x + t • EuclideanSpace.single i (1 : ℝ)))
      atTop (𝓝 upper))
    (hleft : IntegrableOn
        (fun t : ℝ ↦ integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ))) (Set.Iic c) ∨
      (∀ t, t ∈ Set.Iic c → 0 ≤ integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ))) ∨
      ∀ t, t ∈ Set.Iic c → integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ)) ≤ 0)
    (hright : IntegrableOn
        (fun t : ℝ ↦ integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ))) (Set.Ioi c) ∨
      (∀ t, t ∈ Set.Ioi c → 0 ≤ integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ))) ∨
      ∀ t, t ∈ Set.Ioi c → integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ)) ≤ 0) :
    Integrable (fun t : ℝ ↦ integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ))) ∧
      ∫ t : ℝ, integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ)) = upper - lower := by
  have hIic := (cert.integrableOn_Iic_and_integral_eq x c lower (fun t _ ↦ hrequirements t)
    hlower hleft).1
  have hIoi := (cert.integrableOn_Ioi_and_integral_eq x c upper (fun t _ ↦ hrequirements t)
    hupper hright).1
  have hint : Integrable
      (fun t : ℝ ↦ integrand.eval (x + t • EuclideanSpace.single i (1 : ℝ))) := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := c)]
    exact hIic.union hIoi
  exact ⟨hint, integral_of_hasDerivAt_of_tendsto
    (fun t ↦ cert.hasDerivAt_eval_add_smul_single x t (hrequirements t)) hint hlower hupper⟩

end IntegrationCheck.AntiderivativeCert

end CAS

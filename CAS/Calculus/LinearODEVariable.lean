/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.Antiderivative
public import CAS.Calculus.IteratedDifferentiation

/-!
# First-order linear equations with variable coefficients

For `y' + p y = q` with a primitive `P` of `p` and a primitive `Q` of `e ^ P q`, the
differentiable solutions on `ℝ` are exactly `y = (Q + C) e ^ (-P)` (`firstOrder_iff`), and
`y x₀ = y₀` fixes `C = y₀ e ^ (P x₀) - Q x₀` (`firstOrder_ivp`). The primitives come from the
checked integrator (`hasDerivAt_of_cert`).

## Main results

* `firstOrder_iff`: the general solution `y = (Q + C) e ^ (-P)`.
* `firstOrder_ivp`: the solution with `y x₀ = y₀`.
* `hasDerivAt_of_cert`: a certified primitive without domain requirements has the integrand as
  its derivative at every point.

## Implementation notes

The integrating factor `e ^ P` turns the equation into `(e ^ P y)' = e ^ P q`. For a solution
`y`, `e ^ P y - Q` therefore has derivative `0` and is constant (`is_const_of_deriv_eq_zero`);
the converse is a direct computation. Uniqueness needs no Picard-Lindelöf argument this way, and
it holds on all of `ℝ` because the primitives are global. `#cas [dsolve y x]` takes `P` and `Q`
from the checked integrator, and `hasDerivAt_of_cert` accepts a certificate only when its lists
of nonzero and positivity requirements are empty, so the derivative holds at every point.
Teschl's (1.40) is the same solution, written with integrals in place of the primitives.

## References

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, Graduate Studies in
  Mathematics 140, American Mathematical Society, Providence, 2012,
  <https://doi.org/10.1090/gsm/140>. §1.4, the linear equation (1.39) and its solution (1.40); we
  read them in the author's online version, <https://www.mat.univie.ac.at/~gerald/ftp/book-ode/>.
-/

@[expose] public section

namespace CAS.LinearODE

/-- The general solution of `y' + p y = q` by the integrating factor `e ^ P`. -/
theorem firstOrder_iff {p q P Q : ℝ → ℝ} (hP : ∀ x, HasDerivAt P (p x) x)
    (hQ : ∀ x, HasDerivAt Q (Real.exp (P x) * q x) x) {y : ℝ → ℝ} (hy : Differentiable ℝ y) :
    (∀ x, deriv y x + p x * y x = q x) ↔ ∃ C : ℝ, ∀ x, y x = (Q x + C) * Real.exp (-P x) := by
  constructor
  · intro h
    have hg (x : ℝ) : HasDerivAt (fun x ↦ Real.exp (P x) * y x - Q x) 0 x :=
      (((hP x).exp.mul (hy x).hasDerivAt).sub (hQ x)).congr_deriv
        (by linear_combination Real.exp (P x) * h x)
    refine ⟨Real.exp (P 0) * y 0 - Q 0, fun x ↦ ?_⟩
    rw [← is_const_of_deriv_eq_zero (fun x ↦ (hg x).differentiableAt) (fun x ↦ (hg x).deriv) x 0,
      Real.exp_neg]
    field_simp
    ring
  · rintro ⟨C, hC⟩ x
    have h1 : Real.exp (P x) * Real.exp (-P x) = 1 := by simp [← Real.exp_add]
    rw [funext hC, (((hQ x).add_const C).fun_mul (hP x).fun_neg.exp).deriv]
    linear_combination q x * h1

/-- The initial-value problem `y' + p y = q`, `y x₀ = y₀`. -/
theorem firstOrder_ivp {p q P Q : ℝ → ℝ} (hP : ∀ x, HasDerivAt P (p x) x)
    (hQ : ∀ x, HasDerivAt Q (Real.exp (P x) * q x) x) (x₀ y₀ : ℝ) {y : ℝ → ℝ}
    (hy : Differentiable ℝ y) :
    ((∀ x, deriv y x + p x * y x = q x) ∧ y x₀ = y₀) ↔
      ∀ x, y x = (Q x + (y₀ * Real.exp (P x₀) - Q x₀)) * Real.exp (-P x) := by
  rw [firstOrder_iff hP hQ hy]
  have h2 : Real.exp (P x₀) * Real.exp (-P x₀) = 1 := by simp [← Real.exp_add]
  constructor
  · rintro ⟨⟨C, hC⟩, h₀⟩ x
    have h1 : y₀ = (Q x₀ + C) * Real.exp (-P x₀) := by rw [← h₀, hC x₀]
    have : C = y₀ * Real.exp (P x₀) - Q x₀ := by
      linear_combination (-Real.exp (P x₀)) * h1 + (-(Q x₀ + C)) * h2
    rw [hC x, this]
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    rw [h x₀]
    linear_combination y₀ * h2

/-- In `EuclideanSpace ℝ (Fin 1)`, `0 + s • single 0 1` is the one-entry vector `!₂[s]`, for every
real `s`. -/
theorem zero_add_smul_single (s : ℝ) :
    (0 : EuclideanSpace ℝ (Fin 1)) + s • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) = !₂[s] := by
  ext i
  fin_cases i
  simp

/-- A certified primitive without domain requirements, along the real line. -/
theorem hasDerivAt_of_cert {integrand : Verified.Expr (Fin 1)}
    (cert : IntegrationCheck.AntiderivativeCert 0 integrand)
    (h : (cert.requirements.nonzero.isEmpty && cert.requirements.positive.isEmpty) = true)
    (t : ℝ) : HasDerivAt cert.candidate.univariateEval (integrand.univariateEval t) t := by
  simp only [Bool.and_eq_true, List.isEmpty_iff] at h
  have := cert.hasDerivAt_eval_add_smul_single 0 t ⟨by simp [h.1], by simp [h.2]⟩
  simp only [zero_add_smul_single] at this
  exact this

end CAS.LinearODE

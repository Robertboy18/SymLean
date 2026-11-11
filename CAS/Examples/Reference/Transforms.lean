/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Integral transforms

The compiled examples of the docstrings of the Transforms family: Laplace transforms and their
inverses, Fourier coefficients on `[-π, π]`, sine and cosine series on `[0, L]`, and Fourier
transforms of Gaussians. Each section pins the report lines that a docstring shows and proves its
theorem, and checks the axioms of that proof.
-/

@[expose] public section

namespace CAS.Examples.Reference.Transforms

set_option linter.hashCommand false

/-! ## laplace -/

/--
Output (Laplace transform): 1/(s + 1)^2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [laplace t s] (t * exp (-t))

/--
Output (Laplace transform): 4*s/(s^2 + 4)^2
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [laplace t s] (t * sin (2 * t))

/--
Output (Laplace transform): 6/(s - 2)^3 + s/(s^2 + 25)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [laplace t s] (3 * t ^ 2 * exp (2 * t) + cos (5 * t))

theorem laplace_one (s : ℝ) (hs : 0 < s) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s * t)) * 1 = 1 / s := by
  cas

/--
info: 'CAS.Examples.Reference.Transforms.laplace_one' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms laplace_one

/--
laplace: expected a sum of terms c tⁿ e ^ (a t) g (b t) with g one of cos, sin, cosh, sinh, or
c tⁿ e ^ (a t), with rational a, b, c and b ≠ 0 (parameters are not supported)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [laplace t s] (cosh t * cos t)

/--
laplace accepts powers t ^ n with n ≤ 8
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [laplace t s] (t ^ 9)

/-! ## inverseLaplace -/

/--
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)):
1/2*sin(2*t)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [inverseLaplace s t] (1 / (s ^ 2 + 4))

/--
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)):
1/3*exp(t) - 1/3*exp(-2*t)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [inverseLaplace s t] (1 / ((s - 1) * (s + 2)))

/--
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)):
1/4*exp(-t) - 1/4*exp(-t)*cos(2*t) + exp(-t)*sin(2*t)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [inverseLaplace s t] ((2 * s + 3) / ((s + 1) * (s ^ 2 + 2 * s + 5)))

/--
Domain: s > √(1/2)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [inverseLaplace s t] (1 / (s ^ 2 - 1/2))

theorem inverseLaplace_at_one
    (h : ∀ s : ℝ, 0 < s → ∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(s * t)) * (1 / 2 * Real.sin (2 * t)) = 1 / (s ^ 2 + 4)) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(1 * t)) * (1 / 2 * Real.sin (2 * t)) = 1 / 5 := by
  rw [h 1 one_pos]
  norm_num

/--
info: 'CAS.Examples.Reference.Transforms.inverseLaplace_at_one' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms inverseLaplace_at_one

/--
inverseLaplace: F is not proper; its polynomial part (Dirac deltas and their derivatives) is not
supported
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [inverseLaplace s t] (s ^ 2 / (s + 1))

/--
inverseLaplace: expected a proper rational function of s with rational coefficients (parameters
are not supported)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [inverseLaplace s t] (exp (-s) / s)

/-! ## fourier -/

/--
Output (Fourier coefficients): a₀ = 0, aₙ = 0, bₙ = 2*(-1)^(n + 1)/n
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fourier x n] (x)

/--
Output (Fourier coefficients): a₀ = 2/3*pi^2, aₙ = 4*(-1)^n/n^2, bₙ = 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fourier x n] (x^2)

/--
Output (Fourier coefficients): a₀ = 2, aₙ = if n = 1 then -(1/2) else
2*(-1)^(n + 1)/((n + 1)*(n - 1)), bₙ = 0
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fourier x n] (x * sin x)

theorem fourier_b_one : 1 / Real.pi * ∫ x in -Real.pi..Real.pi, x * Real.sin x = 2 := by
  cas

/--
info: 'CAS.Examples.Reference.Transforms.fourier_b_one' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fourier_b_one

/--
fourier: the function must be a sum of products of polynomials, exponentials, sines and cosines
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fourier x n] (exp (x ^ 2))

/--
fourier: trigonometric frequencies must be integers on [-π, π]
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fourier x n] (sin (x / 2))

/-! ## fourierSin -/

/--
Output (sine series coefficients): bₙ = 4*(1 - (-1)^n)/(n^3*pi)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fourierSin x n pi] (x * (pi - x))

/--
Output (sine series coefficients): bₙ = 2*(-1)^(n + 1)/(n*pi)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fourierSin x n 1] (x)

theorem fourierSin_b_one : ∫ x in (0 : ℝ)..Real.pi, x * (Real.pi - x) * Real.sin x = 4 := by
  cas

/--
info: 'CAS.Examples.Reference.Transforms.fourierSin_b_one' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fourierSin_b_one

/--
fourierSin: L must be positive
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fourierSin x n 0] (x)

/--
fourierSin: on [0, L] the function must be a sum of terms c x ^ j e ^ (a x)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fourierSin x n pi] (exp (x ^ 2))

/-! ## fourierCos -/

/--
Output (cosine series coefficients): a₀ = 1, aₙ = -(2*(1 - (-1)^n)/(n^2*pi^2))
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fourierCos x n 1] (x)

/--
Output (cosine series coefficients): a₀ = 8/3, aₙ = 16*(-1)^n/(n^2*pi^2)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fourierCos x n 2] (x ^ 2)

theorem fourierCos_a_one :
    ∫ x in (0 : ℝ)..1, x * Real.cos (Real.pi * x) = -(2 / Real.pi ^ 2) := by
  cas

/--
info: 'CAS.Examples.Reference.Transforms.fourierCos_a_one' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fourierCos_a_one

/--
fourierCos: on [0, L] the function must be a sum of terms c x ^ j e ^ (a x)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fourierCos x n pi] (sin x)

/--
fourierCos: L must be a positive rational number or a rational multiple of π
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fourierCos x n (sqrt 2)] (x)

/-! ## fourierTransform -/

/--
Output (Fourier transform 𝓕 f ξ = ∫ e ^ (-2 π i x ξ) f x dx (Mathlib)):
sqrt(pi)*exp(-(pi^2*ξ^2))
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fourierTransform x ξ] (exp (-x ^ 2))

/--
Output (Fourier transform 𝓕 f ξ = ∫ e ^ (-2 π i x ξ) f x dx (Mathlib)):
3*sqrt(pi)*exp(1 - pi^2*ξ^2)*exp(-(2*pi*ξ)*i)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fourierTransform x ξ] (3 * exp (-(x ^ 2) + 2 * x))

theorem fourierTransform_at_zero
    (h : ∀ ξ : ℝ, FourierTransform.fourier (fun x : ℝ ↦ ((Real.exp (-x ^ 2) : ℝ) : ℂ)) ξ =
      ((√Real.pi * Real.exp (-(Real.pi ^ 2 * ξ ^ 2)) : ℝ) : ℂ)) :
    FourierTransform.fourier (fun x : ℝ ↦ ((Real.exp (-x ^ 2) : ℝ) : ℂ)) 0 = (√Real.pi : ℂ) := by
  rw [h 0]
  simp

/--
info: 'CAS.Examples.Reference.Transforms.fourierTransform_at_zero' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fourierTransform_at_zero

/--
fourierTransform: expected c * exp (-α x ^ 2 + β x + γ) with rational c, α, β, γ and α > 0
(parameters are not supported)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fourierTransform x ξ] (exp (-pi * x ^ 2))

/--
fourierTransform: expected c * exp (-α x ^ 2 + β x + γ) with rational c, α, β, γ and α > 0
(parameters are not supported)
-/
#guard_msgs (whitespace := lax, substring := true) in
#cas [fourierTransform x ξ] (exp (x ^ 2))

end CAS.Examples.Reference.Transforms

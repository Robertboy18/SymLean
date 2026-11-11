/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import CASOracle.DSolve
import CASOracle.Factor
import CASOracle.Ideal
import CASOracle.Numeric
import CASOracle.Sos
import CASOracle.Sum

/-!
# One positive per oracle and task

Run by `tests/oracle/run.sh` with the oracles installed (it calls them); not part of the library
build. Each command's headline is checked with `#guard_msgs`; the report beneath it holds the
kernel-checked theorem. The rows follow the commands of `CASOracle`.
-/

set_option linter.hashCommand false
set_option maxHeartbeats 1000000

/-- Output (scalar ℝ; antiderivative): -(x^2*cos(x)) + 2*x*sin(x) + 2*cos(x) -/
#guard_msgs (info, substring := true) in
#cas [integrate x, oracle := sympy] (x ^ 2 * sin x)

/-- Output (scalar ℝ; antiderivative): atan(x) -/
#guard_msgs (info, substring := true) in
#cas [integrate x, oracle := sage] (1 / (1 + x ^ 2))

/-- Output (scalar ℝ; antiderivative): exp(x)*(x - 1) -/
#guard_msgs (info, substring := true) in
#cas [integrate x, oracle := maxima] (x * exp x)

/-- Output (scalar ℝ; the identity is checked, irreducibility is not): (x^2 - 2*x + 2)*(x^2 + 2*x + 2) -/
#guard_msgs (info, substring := true) in
#cas [factor, oracle := sympy] (x ^ 4 + 4)

/-- Output (scalar ℝ; the identity is checked, irreducibility is not): (x - y)*(x^2 + x*y + y^2) -/
#guard_msgs (info, substring := true) in
#cas [factor, oracle := sage] (x ^ 3 - y ^ 3)

/-- Output (scalar ℝ; the identity is checked, irreducibility is not): (x - 1)*(x + 1)*(x^2 - x + 1)*(x^2 + x + 1) -/
#guard_msgs (info, substring := true) in
#cas [factor, oracle := pari] (x ^ 6 - 1)

/-- Output (scalar ℝ; the identity is checked, irreducibility is not): y*(x - y)*(x + y) -/
#guard_msgs (info, substring := true) in
#cas [factor, oracle := flint] (x ^ 2 * y - y ^ 3)

/-- Output (scalar ℝ; the identity is checked, irreducibility is not): 1/2*((x - 1)^2*x) -/
#guard_msgs (info, substring := true) in
#cas [factor, oracle := maxima] (x ^ 3 / 2 - x ^ 2 + x / 2)

/-- Output (Gröbner basis of the same ideal (checked)): 2*x + y^3 - 5*y, y^4 - 5*y^2 + 4 -/
#guard_msgs (info, substring := true) in
#cas [groebner x, y, oracle := sympy] [x ^ 2 + y ^ 2 - 5, x * y - 2]

-- The zero ideal: the basis is empty, and the theorems use the set `{0}`.
/-- Output (Gröbner basis of the same ideal (checked)): 0 -/
#guard_msgs (info, substring := true) in
#cas [groebner x, y, oracle := sympy] [x - x]

/-- Output (Gröbner basis of the same ideal (checked)): 2*x + y^3 - 5*y, y^4 - 5*y^2 + 4 -/
#guard_msgs (info, substring := true) in
#cas [groebner x, y, oracle := sage] [x ^ 2 + y ^ 2 - 5, x * y - 2]

/-- Output (solutions checked by substitution; completeness not checked): (x = -2, y = -1) ∨ (x = -1, y = -2) ∨ (x = 1, y = 2) ∨ (x = 2, y = 1) -/
#guard_msgs (info, substring := true) in
#cas [solve x, y, oracle := sympy] (x ^ 2 + y ^ 2 = 5 ∧ x * y = 2)

/-- Output (solutions checked by substitution; completeness not checked): (x = 1 - sqrt(2)) ∨ (x = 1 + sqrt(2)) -/
#guard_msgs (info, substring := true) in
#cas [solve x, oracle := sage] (x ^ 2 - 2 * x - 1 = 0)

/-- Output (a root in each interval (existence checked)): 0.739085 ± 10^-6 -/
#guard_msgs (info, substring := true) in
#cas [nsolve x in [0, 1], oracle := sympy] (cos x = x)

/-- Output (a root in each interval (existence checked)): 1.167304 ± 10^-6 -/
#guard_msgs (info, substring := true) in
#cas [nsolve x, oracle := pari] (x ^ 5 - x - 1 = 0)

/-- Output (a root in each interval (existence checked)): 1.25992105 ± 10^-8 -/
#guard_msgs (info, substring := true) in
#cas (digits := 8) [nsolve x, oracle := flint] (x ^ 3 = 2)

/-- Output (certified value of the integral): 0.746824 ± 10^-6 -/
#guard_msgs (info, substring := true) in
#cas [nintegrate x in [0, 1], oracle := sympy] (exp (-x ^ 2))

/-- Output (certified value of the integral): 0.459698 ± 10^-6 -/
#guard_msgs (info, substring := true) in
#cas [nintegrate x in [0, 1], oracle := sage] (sin x)

/-- Output (certified value of the integral): 0.785398 ± 10^-6 -/
#guard_msgs (info, substring := true) in
#cas [nintegrate x in [0, 1], oracle := pari] (1 / (1 + x ^ 2))

/-- Output (certified value of the integral): 8.389056 ± 10^-6 -/
#guard_msgs (info, substring := true) in
#cas [nintegrate x in [0, 2], oracle := flint] (x * exp x)

/-- Output (a real eigenvalue in each interval (existence checked)): 1.267949 ± 10^-6, 3.000000 ± 10^-6, 4.732051 ± 10^-6 -/
#guard_msgs (info, substring := true) in
#cas [eigenvalues, oracle := sympy] !![2, 1, 0; 1, 3, 1; 0, 1, 4]

/-- Output (a real eigenvalue in each interval (existence checked)): 1.381966 ± 10^-6, 3.618034 ± 10^-6 -/
#guard_msgs (info, substring := true) in
#cas [eigenvalues, oracle := sage] !![2, 1; 1, 3]

/-- Output (a real eigenvalue in each interval (existence checked)): -1.000000 ± 10^-6, 3.000000 ± 10^-6 -/
#guard_msgs (info, substring := true) in
#cas [eigenvalues, oracle := pari] !![1, 2; 2, 1]

/-- Output (a real eigenvalue in each interval (existence checked)): 2.000000 ± 10^-6, 5.000000 ± 10^-6 -/
#guard_msgs (info, substring := true) in
#cas [eigenvalues, oracle := flint] !![4, 1; 2, 3]

/-- Output (enclosure on the box, checked by cega): [0.192450, 1.060661] -/
#guard_msgs (info, substring := true) in
#cas [enclose x in [1/3, 2], oracle := gappa] (sqrt x / (1 + x))

/-- Output (a family of solutions (checked); that it is the general solution is not): y(x) = c1/x -/
#guard_msgs (info, substring := true) in
#cas [dsolve y x, oracle := sympy] (x * y' + y = 0)

/-- Output (a family of solutions (checked); that it is the general solution is not): y(x) = c1*sin(x) + c2*cos(x) -/
#guard_msgs (info, substring := true) in
#cas [dsolve y x, oracle := sage] (y'' + y = 0)

/-- Output (closed form, checked by induction for n ≥ 1): n/(n + 1) -/
#guard_msgs (info, substring := true) in
#cas [sum k 1 n, oracle := sympy] (1 / (k * (k + 1)))

/-- Output (closed form, checked by induction for n ≥ 1): n^4/4 + n^3/2 + n^2/4 -/
#guard_msgs (info, substring := true) in
#cas [sum k 1 n, oracle := sage] (k ^ 3)

-- The tactics, and the oracle-free calls they suggest.

/-- cas [integrate primitive := fun x => (x - 1) * Real.exp x] -/
#guard_msgs (info, substring := true) in
theorem integral_by_oracle : ∫ x in (0 : ℝ)..1, x * Real.exp x = 1 := by
  cas [oracle := sympy]

/-- linear_combination h1 + x * h2 -/
#guard_msgs (info, substring := true) in
theorem combination_by_sympy (x y : ℝ) (h1 : x * y = 1) (h2 : x = y) : x ^ 2 = 1 := by
  cas [oracle := sympy]

/-- linear_combination (a + b + c) * h₁ + (-2) * h₂ -/
#guard_msgs (info, substring := true) in
theorem combination_by_sage (a b c : ℚ) (h₁ : a + b + c = 0)
    (h₂ : a * b + b * c + c * a = 0) : a ^ 2 + b ^ 2 + c ^ 2 = 0 := by
  cas [oracle := sage]

open MvPolynomial in
theorem membership_by_oracle :
    (X 0 ^ 2 - 1 : MvPolynomial (Fin 2) ℚ) ∈ Ideal.span {X 0 * X 1 - 1, X 0 - X 1} := by
  cas [oracle := sympy]

-- Inequalities between polynomials, by a sum of squares that `ring` and `positivity` check.
-- The pins stop before the sum, which depends on the numerical solver.

/-- (rw [show x ^ 4 + y ^ 4 - 4 * x * y + 2 = -/
#guard_msgs (info, whitespace := lax, substring := true) in
theorem sos_quartic (x y : ℝ) : 0 ≤ x ^ 4 + y ^ 4 - 4 * x * y + 2 := by
  cas [oracle := sympy]

/-- (rw [ge_iff_le, ← sub_nonneg, show (x ^ 2 + y ^ 2) ^ 2 - 4 * x ^ 2 * y ^ 2 = -/
#guard_msgs (info, whitespace := lax, substring := true) in
theorem sos_square (x y : ℝ) : (x ^ 2 + y ^ 2) ^ 2 ≥ 4 * x ^ 2 * y ^ 2 := by
  cas [oracle := sympy]

/--
(intro h₁ h₂; rw [ge_iff_le, ← sub_nonneg, show x ^ 3 + y ^ 3 - (x ^ 2 * y + x * y ^ 2) =
-/
#guard_msgs (info, whitespace := lax, substring := true) in
theorem sos_cubic (x y : ℝ) : x ≥ 0 → y ≥ 0 → x ^ 3 + y ^ 3 ≥ x ^ 2 * y + x * y ^ 2 := by
  cas [oracle := sympy]

/-- (intro x y; rw [show x ^ 2 + x * y + y ^ 2 = -/
#guard_msgs (info, whitespace := lax, substring := true) in
theorem sos_forall : ∀ x y : ℝ, 0 ≤ x ^ 2 + x * y + y ^ 2 := by
  cas [oracle := sympy]

-- A hypothesis `x ≤ 1` multiplies a square as `0 ≤ 1 - x`.
/-- (have h₁ := sub_nonneg.mpr h; rw [← sub_nonneg, show x ^ 2 - x ^ 3 = -/
#guard_msgs (info, whitespace := lax, substring := true) in
theorem sos_hypothesis (x : ℝ) (h : x ≤ 1) : x ^ 3 ≤ x ^ 2 := by
  cas [oracle := sympy]

/-- Output (sum of squares (checked)) -/
#guard_msgs (info, substring := true) in
#cas [sos x, y, oracle := sympy] (x ^ 4 + y ^ 4 - 4 * x * y + 2)

-- Motzkin's polynomial is nonnegative but not a sum of squares; the refusal says nothing more.
/-- no positive semidefinite Gram matrix -/
#guard_msgs (error, substring := true) in
example (x y : ℝ) : 0 ≤ x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1 := by
  cas [oracle := sympy]

-- Strict inequalities: the sum has a positive term, a positive constant or a positive constant
-- times hypotheses `0 < h`. When the oracle finds no such sum equal to the polynomial, it tries a
-- multiplier of degree at most 2, then at most 4.

/-- (intro x; rw [show x ^ 4 - x + 1 = -/
#guard_msgs (info, whitespace := lax, substring := true) in
theorem sos_strict_quartic : ∀ x : ℝ, 0 < x ^ 4 - x + 1 := by
  cas [oracle := sympy]

/-- (intro x y; rw [← sub_pos, show x ^ 2 + y ^ 2 + 2 - (x * y + x + y) = -/
#guard_msgs (info, whitespace := lax, substring := true) in
theorem sos_strict_lt : ∀ x y : ℝ, x * y + x + y < x ^ 2 + y ^ 2 + 2 := by
  cas [oracle := sympy]

/-- (intro x h₁; rw [show x ^ 3 + x = -/
#guard_msgs (info, whitespace := lax, substring := true) in
theorem sos_strict_hypothesis : ∀ x : ℝ, 0 < x → 0 < x ^ 3 + x := by
  cas [oracle := sympy]

-- Without premises the positive term would be a constant, and this polynomial takes values below
-- every positive constant (at `x = 1 / y` for large `y`), so it is proved with a multiplier.
/-- (intro x y; refine pos_of_mul_pos_right (a := -/
#guard_msgs (info, whitespace := lax, substring := true) in
theorem sos_not_attained : ∀ x y : ℝ, 0 < (x * y - 1) ^ 2 + x ^ 2 := by
  cas [oracle := sympy]

/-- Output (sum of squares with a positive term (checked)) -/
#guard_msgs (info, substring := true) in
#cas [sos x, oracle := sympy] (x ^ 4 - x + 1 > 0)

/-- Output (multiplier and sum of squares with a positive term (checked)) -/
#guard_msgs (info, substring := true) in
#cas [sos x, y, oracle := sympy] ((x * y - 1) ^ 2 + x ^ 2 > 0)

-- `0 < x ^ 2` fails at `0`. Under `x ≠ 0` it holds, but that premise is not an inequality, and
-- the oracle finds no certificate without it. Neither refusal says anything about the inequality.
/-- no sum of squares with a positive term -/
#guard_msgs (error, substring := true) in
example (x : ℝ) : 0 < x ^ 2 := by
  cas [oracle := sympy]

/-- no sum of squares with a positive term -/
#guard_msgs (error, substring := true) in
example : ∀ x : ℝ, x ≠ 0 → 0 < x ^ 2 := by
  cas [oracle := sympy]

-- An atom printed as `x✝` cannot be written back, so the script as printed does not check: the
-- goal is proved from the same certificate over the elaborated atom, and the suggestion is the
-- call itself.
/--
info: cas [oracle := sympy]: the script as printed does not check here, so no oracle-free script
is suggested; the goal is proved from the same certificate over the elaborated atoms
---
info: Try this:
  [apply] cas [oracle := sympy]
-/
#guard_msgs (info, whitespace := lax) in
theorem sos_hidden_atom : ∀ x : ℝ, 0 ≤ x ^ 2 + 1 := by
  intro
  cas [oracle := sympy]

/-! ## Axioms

The tactic proofs, and every evidence theorem the commands above added, depend on no axiom
beyond the standard three. -/

/-- info: 'integral_by_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms integral_by_oracle

/-- info: 'combination_by_sympy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms combination_by_sympy

/-- info: 'membership_by_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms membership_by_oracle

/-- info: 'sos_quartic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sos_quartic

/-- info: 'sos_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sos_square

/-- info: 'sos_cubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sos_cubic

/-- info: 'sos_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sos_forall

/-- info: 'sos_hypothesis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sos_hypothesis

/-- info: 'sos_strict_quartic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sos_strict_quartic

/-- info: 'sos_strict_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sos_strict_lt

/-- info: 'sos_strict_hypothesis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sos_strict_hypothesis

/-- info: 'sos_not_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sos_not_attained

/-- info: 'sos_hidden_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sos_hidden_atom

open Lean Elab Command in
/-- info: every evidence theorem uses only propext, Classical.choice and Quot.sound -/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let evidence := env.constants.map₂.foldl (init := #[]) fun acc name _ ↦
    if (name.toString.splitOn "_evidence").length > 1 then acc.push name else acc
  let (found, unknown) ← liftTermElabM <|
    CAS.Tactic.ProofCarrier.axiomAudit (evidence.map fun name ↦ mkConst name)
  unless found.isEmpty && unknown.isEmpty do
    throwError "nonstandard axioms: {found.map (·.1)} {unknown}"
  unless evidence.size ≥ 32 do throwError "only {evidence.size} evidence theorems"
  logInfo m!"every evidence theorem uses only propext, Classical.choice and Quot.sound"

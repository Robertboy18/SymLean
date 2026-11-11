/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Bare `cas` on the statements of the algebra, matrix and number theory commands

Bare `cas` reads these goals with `CAS.Command.AlgebraGoals`, computes as the corresponding
`#cas` command does and builds the same proof against the goal's own terms: polynomial gcds,
lcms, quotients, remainders, coefficients and degrees in `ℚ[X]`; inverses, ranks,
characteristic polynomials and other equations of literal matrices over `ℚ`; modular powers of
any size; finite sums and products by induction. A false statement is refused, with the computed
value where there is one.
-/

open Polynomial

namespace CAS.Examples.AlgebraGoals

/-! ## Polynomials in `ℚ[X]` -/

example : gcd (X ^ 2 - 1 : ℚ[X]) (X ^ 2 - 2 * X + 1) = X - 1 := by cas

example : lcm (X ^ 2 - 1 : ℚ[X]) (X ^ 2 - 2 * X + 1) = X ^ 3 - X ^ 2 - X + 1 := by cas

/-- The equation may be written either way round. -/
example : X - 1 = gcd (X ^ 2 - 1 : ℚ[X]) (X ^ 2 - 2 * X + 1) := by cas

example : (X ^ 3 + 1 : ℚ[X]) % (2 * X - 1) = C (9 / 8) := by cas

example : (X ^ 4 - 1 : ℚ[X]) / (X ^ 2 + 1) = X ^ 2 - 1 := by cas

example : ((X + 1) ^ 5 : ℚ[X]).coeff 2 = 10 := by cas

example : ((X + 1) ^ 3 - X ^ 3 : ℚ[X]).natDegree = 2 := by cas

/-! ## Matrices over `ℚ` -/

example : (!![(1 : ℚ), 2; 3, 4])⁻¹ = !![-2, 1; 3 / 2, -1 / 2] := by cas

example : Matrix.rank !![(1 : ℚ), 2; 2, 4] = 1 := by cas

example : Matrix.charpoly !![(1 : ℚ), 2; 3, 4] = X ^ 2 - 5 * X - 2 := by cas

example : (!![(1 : ℚ), 2; 3, 4]).transpose = !![1, 3; 2, 4] := by cas

/-! ## Modular powers, sums and products -/

/-- The exponent has 27 digits: repeated squaring, checked by `Nat.pow_mod` steps. -/
example : (2 : ℕ) ^ 123456789123456789123456789 % 1000000007 = 612059118 := by cas

/-- Stated with the computed side on the right. -/
example : 612059118 = (2 : ℕ) ^ 123456789123456789123456789 % 1000000007 := by cas

example (n : ℕ) : ∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 3 = (n * (n + 1) / 2) ^ 2 := by cas

/-- A quantified polynomial inequality is not an algebra goal: the sign route proves it, the
unused binder notwithstanding. -/
example : ∀ (_ : ℝ) (x : ℝ), 0 ≤ x ^ 4 - x ^ 3 + 1 := by cas

example : ∀ n : ℕ, ∏ k ∈ Finset.Icc 1 n, ((k : ℝ) + 1) / k = n + 1 := by cas

/-! ## Refusals -/

example : True := by
  fail_if_success have : gcd (X ^ 2 - 1 : ℚ[X]) (X - 1) = X + 1 := by cas
  fail_if_success have : ((X + 1) ^ 5 : ℚ[X]).coeff 2 = 5 := by cas
  fail_if_success have : (X ^ 3 + 1 : ℚ[X]).natDegree = 2 := by cas
  fail_if_success have : (!![(1 : ℚ), 2; 3, 4])⁻¹ = !![-2, 1; 3 / 2, 1 / 2] := by cas
  fail_if_success have : Matrix.rank !![(1 : ℚ), 2; 2, 4] = 2 := by cas
  fail_if_success have : (!![(1 : ℚ), 2; 3, 4]).transpose = !![1, 2; 3, 4] := by cas
  fail_if_success have : (2 : ℕ) ^ 1000 % 7 = 3 := by cas
  -- Refuted at once, without evaluating the power by other routes.
  fail_if_success have : (2 : ℕ) ^ 123456789123456789123456789 % 1000000007 = 1 := by cas
  fail_if_success have : 1 = (2 : ℕ) ^ 123456789123456789123456789 % 1000000007 := by cas
  fail_if_success have :
    ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), (k : ℝ) = n * n / 2 := by cas
  trivial

end CAS.Examples.AlgebraGoals

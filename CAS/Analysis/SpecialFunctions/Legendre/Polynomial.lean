/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination

/-!
# Legendre polynomials

The Legendre polynomial `P_n` is Mathlib's shifted Legendre polynomial `P̃_n` in the variable
`(1 - x) / 2`. It has degree `n`, takes the value `1` at `x = 1` and has the parity
`P_n (-x) = (-1)ⁿ P_n (x)`. The coefficients of `P̃_n` satisfy the two-term recurrence of the
hypergeometric equation, so `P̃_n` solves `(y (1 - y) P̃_n')' + n (n + 1) P̃_n = 0` and `P_n`
solves the Legendre equation `((1 - x²) P_n')' + n (n + 1) P_n = 0`, both as a polynomial
identity and at every real argument.

Since `P_n` has degree `n`, the polynomials `P_0, …, P_{m-1}` span the polynomials of degree
less than `m`; the derivatives `P_1', …, P_m'` span them as well. The coefficients `cᵢ` of `P_l`
vanish unless `l - i` is even and satisfy `(i + 2) (i + 1) c_{i+2} + (l - i) (l + i + 1) cᵢ = 0`.

## References

* NIST Digital Library of Mathematical Functions, §18.5 Explicit Representations, Version 1.2.8
  (2026-09-15), <https://dlmf.nist.gov/18.5>. (18.5.7) at `α = β = 0` is the expansion of `P_n`
  in powers of `(x - 1) / 2` that defines `legendre` through `P̃_n`.
* NIST Digital Library of Mathematical Functions, §18.6 Symmetry, Special Values, and Limits to
  Monomials, Version 1.2.8 (2026-09-15), <https://dlmf.nist.gov/18.6>. Table 18.6.1 for
  `P_n (1) = 1` and the parity.
* NIST Digital Library of Mathematical Functions, §18.8 Differential Equations, Version 1.2.8
  (2026-09-15), <https://dlmf.nist.gov/18.8>. Table 18.8.1 for the Legendre equation.
-/

@[expose] public noncomputable section

namespace CAS.Analysis.SpecialFunctions

open _root_.Polynomial

/-- Multiplying the derivative by `X` multiplies the `k`-th coefficient by `k`. -/
theorem coeff_X_mul_derivative {R : Type*} [Semiring R] (p : R[X]) (k : ℕ) :
    (X * derivative p).coeff k = p.coeff k * k := by
  cases k with
  | zero => simp
  | succ k => rw [coeff_X_mul, coeff_derivative, Nat.cast_succ]

/-- The shifted Legendre polynomial solves the hypergeometric equation
`(y (1 - y) P̃_n')' + n (n + 1) P̃_n = 0`. -/
theorem shiftedLegendre_equation (n : ℕ) :
    derivative (X * (1 - X) * derivative (shiftedLegendre n)) =
      -C ((n : ℤ) * (n + 1)) * shiftedLegendre n := by
  ext k
  have hsplit : X * (1 - X) * derivative (shiftedLegendre n) =
      X * derivative (shiftedLegendre n) - X * (X * derivative (shiftedLegendre n)) := by ring
  rw [hsplit, coeff_derivative, coeff_sub, coeff_X_mul, coeff_X_mul, coeff_X_mul_derivative,
    coeff_derivative, neg_mul, coeff_neg, coeff_C_mul, coeff_shiftedLegendre,
    coeff_shiftedLegendre]
  have h₁ : ((n.choose (k + 1) : ℕ) : ℤ) * (k + 1) = (n.choose k : ℤ) * ((n : ℤ) - k) := by
    rcases le_or_gt k n with hk | hk
    · rw [← Nat.cast_sub hk]
      exact_mod_cast Nat.choose_succ_right_eq n k
    · rw [Nat.choose_eq_zero_of_lt hk, Nat.choose_eq_zero_of_lt (by omega)]
      simp
  have h₂ : (((n + (k + 1)).choose n : ℕ) : ℤ) * (k + 1) =
      ((n + k).choose n : ℤ) * (n + k + 1) := by
    have h := Nat.add_one_mul_choose_eq (n + k) k
    rw [← Nat.choose_symm_add, show n + k + 1 = n + (k + 1) by omega,
      ← Nat.choose_symm_add] at h
    exact_mod_cast h.symm.trans (mul_comm _ _)
  rw [pow_succ]
  linear_combination
    (-(-1 : ℤ) ^ k * (((n + (k + 1)).choose n : ℕ) : ℤ) * (k + 1)) * h₁ +
      (-(-1 : ℤ) ^ k * (n.choose k : ℤ) * ((n : ℤ) - k)) * h₂

/-- The Legendre polynomial `P_n (x) = P̃_n ((1 - x) / 2)`, where `P̃_n` is Mathlib's shifted
Legendre polynomial. -/
def legendre (n : ℕ) : ℝ[X] :=
  ((shiftedLegendre n).map (Int.castRingHom ℝ)).comp (C (1 / 2) * (1 - X))

/-- The Legendre polynomial at `x` is the shifted Legendre polynomial at `(1 - x) / 2`. -/
theorem legendre_eval (n : ℕ) (x : ℝ) :
    (legendre n).eval x = aeval ((1 - x) / 2) (shiftedLegendre n) := by
  rw [legendre, eval_comp, ← algebraMap_int_eq, eval_map_algebraMap, eval_mul, eval_C, eval_sub,
    eval_one, eval_X, one_div, inv_mul_eq_div]

/-- The Legendre polynomial takes the value `1` at `x = 1`. -/
@[simp]
theorem legendre_eval_one (n : ℕ) : (legendre n).eval 1 = 1 := by
  rw [legendre_eval, sub_self, zero_div, ← coeff_zero_eq_aeval_zero', coeff_shiftedLegendre]
  simp

/-- The Legendre polynomial has the parity of its degree: `P_n (-x) = (-1)ⁿ P_n (x)`. -/
theorem legendre_eval_neg (n : ℕ) (x : ℝ) :
    (legendre n).eval (-x) = (-1) ^ n * (legendre n).eval x := by
  rw [legendre_eval, legendre_eval, shiftedLegendre_eval_symm,
    show 1 - (1 - -x) / 2 = (1 - x) / 2 by ring]

/-- The Legendre polynomial takes the value `(-1)ⁿ` at `x = -1`. -/
@[simp]
theorem legendre_eval_neg_one (n : ℕ) : (legendre n).eval (-1) = (-1) ^ n := by
  rw [legendre_eval_neg, legendre_eval_one, mul_one]

/-- The Legendre polynomial is not zero. -/
theorem legendre_ne_zero (n : ℕ) : legendre n ≠ 0 := fun h ↦ by
  simpa [h] using legendre_eval_one n

/-- The Legendre polynomial `P_n` has degree `n`. -/
@[simp]
theorem natDegree_legendre (n : ℕ) : (legendre n).natDegree = n := by
  have hq : (C (1 / 2 : ℝ) * (1 - X)).natDegree = 1 := by
    rw [natDegree_C_mul (by norm_num), natDegree_sub_eq_right_of_natDegree_lt (by simp)]
    exact natDegree_X
  rw [legendre, natDegree_comp, hq, mul_one,
    natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℝ)),
    natDegree_shiftedLegendre]

/-- The Legendre polynomial `P_n` has degree `n`. -/
@[simp]
theorem degree_legendre (n : ℕ) : (legendre n).degree = n := by
  rw [degree_eq_natDegree (legendre_ne_zero n), natDegree_legendre]

/-- The Legendre equation `((1 - x²) P_n')' + n (n + 1) P_n = 0` as a polynomial identity. -/
theorem legendre_equation (n : ℕ) :
    derivative ((1 - X ^ 2) * derivative (legendre n)) =
      -C ((n : ℝ) * (n + 1)) * legendre n := by
  set p : ℝ[X] := (shiftedLegendre n).map (Int.castRingHom ℝ)
  set q : ℝ[X] := C (1 / 2) * (1 - X) with hq_def
  have hp : derivative (X * (1 - X) * derivative p) = -C ((n : ℝ) * (n + 1)) * p := by
    have h := congrArg (Polynomial.map (Int.castRingHom ℝ)) (shiftedLegendre_equation n)
    rw [← derivative_map, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_one, Polynomial.map_X, ← derivative_map, Polynomial.map_mul,
      Polynomial.map_neg, Polynomial.map_C] at h
    rw [h]
    congr 3
    simp
  have hhalf : (2 : ℝ[X]) * C (1 / 2) = 1 := by
    rw [← C_ofNat, ← C_mul]
    norm_num
  have hdq : derivative q = -C (1 / 2) := by
    rw [hq_def, derivative_C_mul, derivative_sub, derivative_one, derivative_X]
    ring
  have hweight : (1 - X ^ 2 : ℝ[X]) = 4 * (q * (1 - q)) := by
    rw [hq_def]
    linear_combination
      (-(2 * (1 - X)) + (2 + (2 * C (1 / 2) - 1)) * (1 - X) ^ 2) * hhalf
  have hcomp : (1 - X ^ 2) * derivative (legendre n) =
      -2 * (X * (1 - X) * derivative p).comp q := by
    rw [legendre, derivative_comp, hdq, hweight, mul_comp, mul_comp, sub_comp, one_comp, X_comp]
    linear_combination (-2 * q * (1 - q) * (derivative p).comp q) * hhalf
  rw [hcomp, derivative_mul, derivative_comp, hp, hdq, derivative_neg, derivative_ofNat,
    neg_zero, zero_mul, zero_add, mul_comp, neg_comp, C_comp,
    show legendre n = p.comp q from rfl]
  linear_combination (-C ((n : ℝ) * (n + 1)) * p.comp q) * hhalf

/-- The Legendre equation at every real argument, `(1 - x²) Q'' - 2x Q' + μ Q = 0`, is the
polynomial identity `((1 - X²) Q')' = -μ Q`. -/
theorem derivative_one_sub_sq_mul_derivative_of_eval {Q : ℝ[X]} {μ : ℝ}
    (h : ∀ x : ℝ, (1 - x ^ 2) * Q.derivative.derivative.eval x - 2 * x * Q.derivative.eval x +
      μ * Q.eval x = 0) :
    derivative ((1 - X ^ 2) * derivative Q) = -C μ * Q := by
  refine Polynomial.funext fun x ↦ ?_
  simp only [derivative_mul, derivative_sub, derivative_one, derivative_X_pow, eval_add,
    eval_mul, eval_sub, eval_neg, eval_C, eval_one, eval_pow, eval_X, zero_sub,
    Nat.cast_ofNat]
  linear_combination h x

/-- The first Legendre polynomial is `P_0 = 1`. -/
@[simp]
theorem legendre_zero : legendre 0 = 1 := by
  simp [legendre, shiftedLegendre]

/-- The second Legendre polynomial is `P_1 = X`. -/
@[simp]
theorem legendre_one : legendre 1 = X := by
  refine Polynomial.funext fun x ↦ ?_
  rw [legendre_eval]
  simp [shiftedLegendre, Finset.sum_range_succ]
  ring

/-- The Legendre polynomials as a polynomial sequence: `P_n` has degree `n`. -/
def legendreSequence : Polynomial.Sequence ℝ where
  elems' := legendre
  degree_eq' := degree_legendre

/-- The Legendre polynomials span all real polynomials. -/
theorem span_legendre : Submodule.span ℝ (Set.range legendre) = ⊤ :=
  legendreSequence.span fun n ↦ isUnit_iff_ne_zero.mpr
    (leadingCoeff_ne_zero.mpr (legendre_ne_zero n))

/-- A polynomial of degree less than `m` is a combination of `P_0, …, P_{m-1}`. -/
theorem mem_span_legendre_of_degree_lt {q : ℝ[X]} {m : ℕ} (hq : q.degree < m) :
    q ∈ Submodule.span ℝ (legendre '' Set.Iio m) := by
  have h := legendreSequence.span_degreeLT (m := m) fun n _ ↦ isUnit_iff_ne_zero.mpr
    (leadingCoeff_ne_zero.mpr (legendre_ne_zero n))
  change q ∈ Submodule.span ℝ (legendreSequence '' Set.Iio m)
  rwa [h, mem_degreeLT]

/-- The derivative `P_{l+1}'` has degree `l`. -/
theorem degree_derivative_legendre_succ (l : ℕ) : (derivative (legendre (l + 1))).degree = l := by
  rw [degree_derivative (by simp), natDegree_legendre, Nat.add_sub_cancel]

/-- The derivatives `P_1', P_2', …` as a polynomial sequence: `P_{l+1}'` has degree `l`. -/
def derivativeLegendreSequence : Polynomial.Sequence ℝ where
  elems' l := derivative (legendre (l + 1))
  degree_eq' := degree_derivative_legendre_succ

/-- The derivative `P_{l+1}'` is not zero. -/
theorem derivative_legendre_succ_ne_zero (l : ℕ) : derivative (legendre (l + 1)) ≠ 0 :=
  derivativeLegendreSequence.ne_zero l

/-- The derivatives `P_1', P_2', …` span all real polynomials. -/
theorem span_derivative_legendre :
    Submodule.span ℝ (Set.range fun l ↦ derivative (legendre (l + 1))) = ⊤ :=
  derivativeLegendreSequence.span fun l ↦ isUnit_iff_ne_zero.mpr
    (leadingCoeff_ne_zero.mpr (derivative_legendre_succ_ne_zero l))

/-- The parity `P_n (-X) = (-1)ⁿ P_n` as a polynomial identity. -/
theorem legendre_comp_neg_X (n : ℕ) : (legendre n).comp (-X) = C ((-1) ^ n) * legendre n :=
  Polynomial.funext fun x ↦ by rw [eval_comp, eval_neg, eval_X, legendre_eval_neg, eval_mul, eval_C]

/-- The derivative of a Legendre polynomial has the opposite parity:
`P_n' (-x) = (-1)ⁿ⁺¹ P_n' (x)`. -/
theorem derivative_legendre_eval_neg (n : ℕ) (x : ℝ) :
    (derivative (legendre n)).eval (-x) = (-1) ^ (n + 1) * (derivative (legendre n)).eval x := by
  have h := congrArg (fun p : ℝ[X] ↦ (derivative p).eval x) (legendre_comp_neg_X n)
  simp only [derivative_comp, derivative_neg, derivative_X, derivative_C_mul, eval_mul,
    eval_neg, eval_one, eval_comp, eval_X, eval_C] at h
  rw [pow_succ]
  linear_combination -h

/-! ### Coefficients of the Legendre polynomials -/

/-- The coefficients `cᵢ` of `P_l` satisfy `(-1)ⁱ cᵢ = (-1)ˡ cᵢ`. -/
theorem neg_one_pow_mul_coeff_legendre (l i : ℕ) :
    (-1) ^ i * (legendre l).coeff i = (-1) ^ l * (legendre l).coeff i := by
  have h := congrArg (fun p : Polynomial ℝ ↦ p.coeff i) (legendre_comp_neg_X l)
  rw [show (-Polynomial.X : Polynomial ℝ) = Polynomial.C (-1) * Polynomial.X by simp,
    Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_C_mul] at h
  linear_combination h

/-- A coefficient `cᵢ` of `P_l` vanishes unless `l - i` is even, that is unless
`i + 2 ((l - i) / 2) = l`. -/
theorem coeff_legendre_eq_zero_or (l i : ℕ) :
    (legendre l).coeff i = 0 ∨ i + 2 * ((l - i) / 2) = l := by
  rcases lt_or_ge l i with hli | hil
  · exact .inl (Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_legendre]))
  rcases Nat.even_or_odd (l - i) with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact .inr (by omega)
  · have hl : (-1 : ℝ) ^ l = -(-1) ^ i := by
      rw [show l = i + (2 * k + 1) by omega, pow_add, pow_succ, pow_mul]
      norm_num
    have h := neg_one_pow_mul_coeff_legendre l i
    rw [hl] at h
    exact .inl (by simpa [CharZero.eq_neg_self_iff] using h)

/-- The coefficients `cᵢ` of `P_l` satisfy `(i + 2) (i + 1) c_{i+2} + (l - i) (l + i + 1) cᵢ = 0`,
the recursion read off from the Legendre equation. -/
theorem coeff_legendre_recursion (l i : ℕ) :
    ((i : ℝ) + 2) * (i + 1) * (legendre l).coeff (i + 2) +
      ((l : ℝ) - i) * (l + i + 1) * (legendre l).coeff i = 0 := by
  have h := congrArg (fun p : Polynomial ℝ ↦ p.coeff i) (legendre_equation l)
  have hsplit : (1 - Polynomial.X ^ 2) * Polynomial.derivative (legendre l) =
      Polynomial.derivative (legendre l) -
        Polynomial.X * (Polynomial.X * Polynomial.derivative (legendre l)) := by
    ring
  rw [hsplit, Polynomial.coeff_derivative, Polynomial.coeff_sub, Polynomial.coeff_X_mul,
    coeff_X_mul_derivative, Polynomial.coeff_derivative, neg_mul, Polynomial.coeff_neg,
    Polynomial.coeff_C_mul] at h
  push_cast at h
  linear_combination h

end CAS.Analysis.SpecialFunctions

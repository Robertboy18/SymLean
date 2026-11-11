/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.SpecialFunctions.Legendre.Polynomial
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Monomial coefficients of the Legendre polynomials

The Legendre polynomial `P_n (x) = P̃_n ((1 - x) / 2)` expands in monomials as
`P_n (x) = ∑ j ≤ n, c_{n,j} x ^ j` with the rational coefficients

`c_{n,j} = ∑ k ≤ n, (-1) ^ (k + j) C(n, k) C(n + k, n) C(k, j) / 2 ^ k`

(`legendreMonomialCoeff`), from the binomial expansion of `(1 - x) ^ k` in the shifted
polynomial. `legendreCoeff` computes the same numbers by a faster sum.

## Main results

* `legendre_eval_eq_sum_coeff`: `P_n (x) = ∑ j ≤ n, c_{n,j} x ^ j`.
* `legendre_eval_ratCast`: the exact value at a rational point.
* `legendreMonomialCoeff_eq_legendreCoeff`: the coefficients by the faster sum.

## Implementation notes

The binomial coefficients of `legendreMonomialCoeff` are computed from factorials (`chooseRat`),
so the coefficients are closed rational computations that the kernel evaluates directly.
`legendreCoeff` is the same sum from `k = j` on, where the terms below `j` vanish, with each of
the three binomial coefficients updated by one multiplication and one division per term instead
of computed from factorials (`legendreMonomialCoeff_eq_legendreCoeff`). The commands evaluate it,
in the kernel and to state the coefficients. The expansion is classical: it is the explicit
representation of the Jacobi polynomials at `α = β = 0`, multiplied out.

## References

* NIST Digital Library of Mathematical Functions, §18.5 Explicit Representations, Version 1.2.8
  (2026-09-15), <https://dlmf.nist.gov/18.5>. (18.5.7) at `α = β = 0` gives
  `P_n (x) = ∑ ℓ ≤ n, C(n, ℓ) C(n + ℓ, ℓ) ((x - 1) / 2) ^ ℓ`.
* NIST Digital Library of Mathematical Functions, §18.7 Interrelations and Limit Relations,
  Version 1.2.8 (2026-09-15), <https://dlmf.nist.gov/18.7>. `P_n = P_n^(0,0)` is (18.7.9).
-/

@[expose] public section

namespace CAS.Analysis.SpecialFunctions

open _root_.Polynomial Finset Nat

/-- The binomial coefficient as a rational number, from factorials. -/
def chooseRat (n k : ℕ) : ℚ :=
  if k ≤ n then (n ! : ℚ) / ((k ! : ℚ) * ((n - k)! : ℚ)) else 0

/-- `chooseRat n k` is the binomial coefficient `n.choose k` cast to `ℚ`, for all `n` and `k` (both
are `0` when `n < k`). -/
theorem chooseRat_eq (n k : ℕ) : chooseRat n k = (n.choose k : ℚ) := by
  unfold chooseRat
  split_ifs with h
  · rw [Nat.cast_choose ℚ h]
  · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge h), Nat.cast_zero]

/-- The coefficient of `x ^ j` in the Legendre polynomial `P_n`. -/
def legendreMonomialCoeff (n j : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1), (-1) ^ (k + j) * chooseRat n k * chooseRat (n + k) n *
    chooseRat k j / 2 ^ k

/-- The Legendre polynomial is the sum of its monomials with the coefficients
`legendreMonomialCoeff`. -/
theorem legendre_eval_eq_sum_coeff (n : ℕ) (x : ℝ) :
    (legendre n).eval x = ∑ j ∈ range (n + 1), (legendreMonomialCoeff n j : ℝ) * x ^ j := by
  have hshift : (legendre n).eval x = ∑ k ∈ range (n + 1),
      ((-1 : ℝ) ^ k * n.choose k * (n + k).choose n) * ((1 - x) / 2) ^ k := by
    rw [legendre_eval, shiftedLegendre, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp [map_mul, map_pow]
  have hbin (k : ℕ) (hk : k ≤ n) : ((1 - x) / 2) ^ k = ∑ j ∈ range (n + 1),
      ((-1 : ℝ) ^ j * k.choose j / 2 ^ k) * x ^ j := by
    have h := add_pow (-x) (1 : ℝ) k
    have hsub : ∑ j ∈ range (k + 1), (-x) ^ j * 1 ^ (k - j) * (k.choose j : ℝ) =
        ∑ j ∈ range (n + 1), (-x) ^ j * 1 ^ (k - j) * (k.choose j : ℝ) := by
      apply Finset.sum_subset (range_subset_range.mpr (by omega))
      intro j _ hj
      rw [mem_range, not_lt] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
    rw [div_pow, show 1 - x = -x + 1 by ring, h, hsub, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [one_pow, mul_one, neg_pow]
    ring
  rw [hshift]
  have hrw : ∑ k ∈ range (n + 1), ((-1 : ℝ) ^ k * n.choose k * (n + k).choose n) *
      ((1 - x) / 2) ^ k = ∑ k ∈ range (n + 1), ∑ j ∈ range (n + 1),
        ((-1 : ℝ) ^ k * n.choose k * (n + k).choose n) *
          (((-1 : ℝ) ^ j * k.choose j / 2 ^ k) * x ^ j) := by
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [hbin k (by simpa [Nat.lt_succ_iff] using hk), Finset.mul_sum]
  rw [hrw, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [legendreMonomialCoeff, Rat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [chooseRat_eq, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
    Rat.cast_natCast, Rat.cast_ofNat, pow_add]
  ring

/-- The exact value of `P_n` at a rational point. -/
theorem legendre_eval_ratCast (n : ℕ) (q : ℚ) :
    (legendre n).eval (q : ℝ) =
      ((∑ j ∈ range (n + 1), legendreMonomialCoeff n j * q ^ j : ℚ) : ℝ) := by
  rw [legendre_eval_eq_sum_coeff]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_pow]


/-- `∑ i < m, (-1) ^ (k + i + j) C(n, k + i) C(n + k + i, n) C(k + i, j) / 2 ^ (k + i)`, given
`a = C(n, k)`, `b = C(n + k, n)`, `c = C(k, j)` and `s = (-1) ^ (k + j) / 2 ^ k`, for `j ≤ k`. -/
def legendreCoeffFrom (n j : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℚ → ℚ
  | 0, _, _, _, _, _ => 0
  | m + 1, k, a, b, c, s => s * ((a * b * c : ℕ) : ℚ) +
      legendreCoeffFrom n j m (k + 1) (a * (n - k) / (k + 1)) (b * (n + k + 1) / (k + 1))
        (c * (k + 1) / (k + 1 - j)) (-s / 2)

/-- The coefficient of `x ^ j` in `P_n`, the sum of `legendreMonomialCoeff` from `k = j` on; the
binomial coefficients at `k = j` come from factorials. -/
def legendreCoeff (n j : ℕ) : ℚ :=
  legendreCoeffFrom n j (n + 1 - j) j (n ! / (j ! * (n - j)!)) ((n + j)! / (n ! * j !)) 1
    (1 / 2 ^ j)

/-- For `j ≤ k`, `legendreCoeffFrom n j m k` started at `a = C(n, k)`, `b = C(n + k, n)`,
`c = C(k, j)` and `s = (-1) ^ (k + j) / 2 ^ k` equals
`∑ i < m, (-1) ^ (k + i + j) C(n, k + i) C(n + k + i, n) C(k + i, j) / 2 ^ (k + i)`. -/
theorem legendreCoeffFrom_eq (n j m k : ℕ) (hjk : j ≤ k) :
    legendreCoeffFrom n j m k (n.choose k) ((n + k).choose n) (k.choose j)
        ((-1) ^ (k + j) / 2 ^ k) =
      ∑ i ∈ range m, (-1) ^ (k + i + j) * ((n.choose (k + i) * (n + k + i).choose n *
        (k + i).choose j : ℕ) : ℚ) / 2 ^ (k + i) := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
    have ha : n.choose k * (n - k) / (k + 1) = n.choose (k + 1) := by
      rw [← Nat.choose_succ_right_eq, Nat.mul_div_cancel _ (Nat.succ_pos k)]
    have hb : (n + k).choose n * (n + k + 1) / (k + 1) = (n + (k + 1)).choose n := by
      rw [Nat.choose_mul_succ_eq, show n + k + 1 - n = k + 1 by omega,
        Nat.mul_div_cancel _ (Nat.succ_pos k), Nat.add_assoc]
    have hc : k.choose j * (k + 1) / (k + 1 - j) = (k + 1).choose j := by
      rw [Nat.choose_mul_succ_eq, Nat.mul_div_cancel _ (by omega)]
    have hs : -((-1 : ℚ) ^ (k + j) / 2 ^ k) / 2 = (-1) ^ (k + 1 + j) / 2 ^ (k + 1) := by
      rw [show k + 1 + j = k + j + 1 by omega, pow_succ, pow_succ]
      ring
    rw [legendreCoeffFrom, ha, hb, hc, hs, ih (k + 1) (by omega), sum_range_succ']
    simp only [add_zero, Nat.add_assoc, Nat.add_comm 1]
    ring

/-- `legendreMonomialCoeff n j` is `legendreCoeff n j`, which the kernel evaluates faster. -/
theorem legendreMonomialCoeff_eq_legendreCoeff (n j : ℕ) :
    legendreMonomialCoeff n j = legendreCoeff n j := by
  rcases lt_or_ge n j with hnj | hjn
  · rw [legendreCoeff, show n + 1 - j = 0 by omega, legendreCoeffFrom, legendreMonomialCoeff]
    refine sum_eq_zero fun k hk ↦ ?_
    rw [chooseRat_eq k j, Nat.choose_eq_zero_of_lt (by simp at hk; omega)]
    simp
  · have h := legendreCoeffFrom_eq n j (n + 1 - j) j le_rfl
    rw [Nat.choose_self, ← two_mul, pow_mul, neg_one_sq, one_pow,
      Nat.choose_eq_factorial_div_factorial hjn,
      Nat.choose_eq_factorial_div_factorial (Nat.le_add_right n j), Nat.add_sub_cancel_left] at h
    rw [legendreCoeff, h, legendreMonomialCoeff, range_eq_Ico,
      ← sum_Ico_consecutive _ (Nat.zero_le j) (by omega : j ≤ n + 1)]
    rw [sum_eq_zero (s := Ico 0 j) fun k hk ↦ by
      rw [chooseRat_eq k j, Nat.choose_eq_zero_of_lt (by simp at hk; omega)]; simp, zero_add,
      sum_Ico_eq_sum_range]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [chooseRat_eq, ← Nat.add_assoc]
    push_cast
    ring

end CAS.Analysis.SpecialFunctions

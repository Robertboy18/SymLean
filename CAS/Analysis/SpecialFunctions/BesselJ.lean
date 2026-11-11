/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Certified values of the Bessel function `J_n` at rational points

Mathlib defines `Complex.besselJ a x` through the regularized hypergeometric function. For a natural
order `n`, `J_n` is the sum of its power series (`hasSum_besselJ_nat`), satisfies the geometric tail
bound `‖J_n x - ∑_{k<N} t_k‖ ≤ 2 ‖t_N‖` once `2 ‖x / 2‖² ≤ (N + 1) (n + N + 1)`
(`besselJ_tail_bound`), and is real at a real point (`besselJ_ofReal_enclosure`).
`besselJ_int_enclosure` is the statement that `#cas [N d] (BesselJ n q)` proves: an enclosure of
`J_n q` for an integer order `n` and a rational point `q`.

## Main results

* `hasSum_besselJ_nat`: `J_n x = ∑ (-1)^k (x/2)^(2k+n) / (k! (n+k)!)`.
* `besselJ_tail_bound`: the tail bound above.
* `besselCheck_sound`, `besselJ_int_enclosure`: `J_n q` is a real number in `[lo, hi]`.

## Implementation notes

We read the power series off the hypergeometric series `regularizedHGFunSeries` of Mathlib's
definition, with `Complex.Gamma_nat_eq_factorial` for the Gamma factor. Under the tail condition
the terms shrink by a factor `1/2` from `N` on, so the tail is at most twice the `N`-th term
(`norm_tsum_tail_le_of_ratio`). `besselCheck` is a Boolean checker over `ℚ` that the kernel
evaluates: the tail condition, and `[lo, hi]` contains the partial sum widened by twice the next
term; `besselCheck_sound` turns it into the enclosure. The command chooses `N` and the interval
outside the kernel. `besselCheckInt` extends the check to integer orders through Mathlib's
`Complex.besselJ_neg_int` (`J_{-m} = (-1)^m J_m`).

## References

* NIST Digital Library of Mathematical Functions, §10.2 Definitions, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/10.2>. The power series is (10.2.2).
* NIST Digital Library of Mathematical Functions, §10.4 Connection Formulas, Version 1.2.8
  (2026-09-15), <https://dlmf.nist.gov/10.4>. `J_{-n} = (-1)^n J_n` is (10.4.1).
-/

@[expose] public section

open Complex

namespace CAS.Analysis.SpecialFunctions.Bessel

/-- The power series of `J_n` at natural order `n`. -/
theorem hasSum_besselJ_nat (n : ℕ) (x : ℂ) :
    HasSum (fun k : ℕ ↦ (-1) ^ k * (x / 2) ^ (2 * k + n) / ((k.factorial : ℂ) * (n + k).factorial))
      (besselJ n x) := by
  have hs := (regularizedHGFunSeries 0 {(n : ℂ) + 1}).hasSum
    (x := -(x / 2) ^ 2) (by simp)
  simp only [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq] at hs
  have h := hs.mul_left ((x / 2) ^ n)
  rw [besselJ, Complex.cpow_natCast]
  convert h using 1
  · funext k
    simp only [regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero,
      Multiset.map_singleton, Multiset.prod_singleton, smul_eq_mul]
    rw [show (n : ℂ) + 1 + k = ((n + k : ℕ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
    rw [neg_eq_neg_one_mul ((x / 2) ^ 2), mul_pow, ← pow_mul, pow_add]
    ring
  · rfl

/-- Geometric tail bound: if the terms from `N` on shrink by a factor `r < 1`, the series is
summable and its tail from `N` is at most `‖f N‖ / (1 - r)`. -/
theorem norm_tsum_tail_le_of_ratio {f : ℕ → ℂ} {r : ℝ} (N : ℕ) (hr0 : 0 ≤ r) (hr : r < 1)
    (h : ∀ k, N ≤ k → ‖f (k + 1)‖ ≤ r * ‖f k‖) :
    Summable f ∧ ‖∑' k, f (k + N)‖ ≤ ‖f N‖ / (1 - r) := by
  have hle : ∀ k, ‖f (k + N)‖ ≤ ‖f N‖ * r ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show k + 1 + N = k + N + 1 by omega]
      calc ‖f (k + N + 1)‖ ≤ r * ‖f (k + N)‖ := h (k + N) (by omega)
        _ ≤ r * (‖f N‖ * r ^ k) := by gcongr
        _ = ‖f N‖ * r ^ (k + 1) := by ring
  have hs : Summable (fun k ↦ ‖f N‖ * r ^ k) :=
    (summable_geometric_of_lt_one hr0 hr).mul_left _
  have hsn : Summable (fun k ↦ ‖f (k + N)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle hs
  refine ⟨(summable_nat_add_iff N).1 hsn.of_norm, ?_⟩
  calc ‖∑' k, f (k + N)‖ ≤ ∑' k, ‖f (k + N)‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' k, ‖f N‖ * r ^ k := hsn.tsum_le_tsum hle hs
    _ = ‖f N‖ / (1 - r) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr, div_eq_mul_inv]

/-- The `k`-th term of the series of `J_n`. -/
noncomputable def besselTerm (n : ℕ) (x : ℂ) (k : ℕ) : ℂ :=
  (-1) ^ k * (x / 2) ^ (2 * k + n) / ((k.factorial : ℂ) * (n + k).factorial)

/-- Consecutive terms of the series of `J_n`: term `k + 1` is term `k` times
`-(x / 2)² / ((k + 1) (n + k + 1))`, for every natural order `n` and complex `x`. -/
theorem besselTerm_succ (n : ℕ) (x : ℂ) (k : ℕ) :
    besselTerm n x (k + 1) =
      besselTerm n x k * (-(x / 2) ^ 2 / (((k + 1) * (n + k + 1) : ℕ) : ℂ)) := by
  unfold besselTerm
  rw [Nat.factorial_succ k, show n + (k + 1) = (n + k) + 1 by omega, Nat.factorial_succ (n + k)]
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- The norm form of `besselTerm_succ`: `‖besselTerm n x (k + 1)‖` equals
`‖besselTerm n x k‖ ‖x / 2‖² / ((k + 1) (n + k + 1))`. -/
theorem norm_besselTerm_succ (n : ℕ) (x : ℂ) (k : ℕ) :
    ‖besselTerm n x (k + 1)‖ =
      ‖besselTerm n x k‖ * (‖x / 2‖ ^ 2 / (((k + 1) * (n + k + 1) : ℕ) : ℝ)) := by
  rw [besselTerm_succ, norm_mul, norm_div, norm_neg, norm_pow, Complex.norm_natCast]

/-- The partial sum of `N` terms of the series of `J_n` is within twice the `N`-th term of
`J_n x`, once `2 ‖x / 2‖² ≤ (N + 1) (n + N + 1)`. -/
theorem besselJ_tail_bound (n N : ℕ) (x : ℂ)
    (h : 2 * ‖x / 2‖ ^ 2 ≤ ((N : ℝ) + 1) * (n + N + 1)) :
    ‖besselJ n x - ∑ k ∈ Finset.range N, besselTerm n x k‖ ≤ 2 * ‖besselTerm n x N‖ := by
  have hratio : ∀ k, N ≤ k → ‖besselTerm n x (k + 1)‖ ≤ 1 / 2 * ‖besselTerm n x k‖ := by
    intro k hk
    rw [norm_besselTerm_succ, mul_comm (1 / 2 : ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [div_le_iff₀ (by positivity)]
    have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
    have hNk : ((N : ℝ) + 1) * (n + N + 1) ≤ (k + 1) * (n + k + 1) := by gcongr
    push_cast
    linarith
  obtain ⟨hsum, htail⟩ :=
    norm_tsum_tail_le_of_ratio (f := besselTerm n x) N (by norm_num) (by norm_num) hratio
  have hJ : besselJ n x = ∑' k, besselTerm n x k := (hasSum_besselJ_nat n x).tsum_eq.symm
  rw [hJ, ← hsum.sum_add_tsum_nat_add N, add_sub_cancel_left]
  calc _ ≤ ‖besselTerm n x N‖ / (1 - 1 / 2) := htail
    _ = 2 * ‖besselTerm n x N‖ := by ring

/-- The `k`-th term of the series of `J_n` at a real point. -/
noncomputable def besselTermReal (n : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  (-1) ^ k * (x / 2) ^ (2 * k + n) / ((k.factorial : ℝ) * (n + k).factorial)

/-- At a real point `x`, the complex series term `besselTerm n x k` is the cast of the real term
`besselTermReal n x k`. -/
theorem besselTerm_ofReal (n : ℕ) (x : ℝ) (k : ℕ) :
    besselTerm n (x : ℂ) k = (besselTermReal n x k : ℂ) := by
  unfold besselTerm besselTermReal
  push_cast
  try ring

/-- At a real point `J_n` is real, within twice the `N`-th term of its partial sum of `N` terms,
once `2 (x / 2)² ≤ (N + 1) (n + N + 1)`. -/
theorem besselJ_ofReal_enclosure (n N : ℕ) (x : ℝ)
    (h : 2 * (x / 2) ^ 2 ≤ ((N : ℝ) + 1) * (n + N + 1)) :
    ∃ r : ℝ, besselJ n (x : ℂ) = r ∧
      |r - ∑ k ∈ Finset.range N, besselTermReal n x k| ≤ 2 * |besselTermReal n x N| := by
  have hx : ‖(x : ℂ) / 2‖ ^ 2 = (x / 2) ^ 2 := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
  have hb := besselJ_tail_bound n N (x : ℂ) (by rw [hx]; exact h)
  have hs : HasSum (fun k ↦ (besselTermReal n x k : ℂ)) (besselJ n (x : ℂ)) := by
    have := hasSum_besselJ_nat n (x : ℂ)
    convert this using 1
    funext k
    exact (besselTerm_ofReal n x k).symm
  have hJ : besselJ n (x : ℂ) = ((∑' k, besselTermReal n x k : ℝ) : ℂ) := by
    rw [← hs.tsum_eq, Complex.ofReal_tsum]
  refine ⟨_, hJ, ?_⟩
  have hS : ∑ k ∈ Finset.range N, besselTerm n (x : ℂ) k =
      ((∑ k ∈ Finset.range N, besselTermReal n x k : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun k _ ↦ besselTerm_ofReal n x k
  rw [hJ, hS, besselTerm_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs] at hb
  exact hb

/-- The `k`-th term of the series of `J_n` at a rational point, computed in `ℚ`. -/
def besselTermQ (n : ℕ) (q : ℚ) (k : ℕ) : ℚ :=
  (-1) ^ k * (q / 2) ^ (2 * k + n) / ((k.factorial : ℚ) * (n + k).factorial)

/-- The partial sum of `N` terms, in `ℚ`. -/
def besselPartialQ (n : ℕ) (q : ℚ) : ℕ → ℚ
  | 0 => 0
  | N + 1 => besselPartialQ n q N + besselTermQ n q N

/-- The checker: the tail condition, and `[lo, hi]` contains the partial sum widened by twice
the next term. -/
def besselCheck (n N : ℕ) (q lo hi : ℚ) : Bool :=
  decide (2 * (q / 2) ^ 2 ≤ ((N : ℚ) + 1) * (n + N + 1)) &&
    decide (lo ≤ besselPartialQ n q N - 2 * |besselTermQ n q N|) &&
    decide (besselPartialQ n q N + 2 * |besselTermQ n q N| ≤ hi)

/-- The real cast of the rational term `besselTermQ n q k` is the real term
`besselTermReal n q k`. -/
theorem besselTermQ_cast (n : ℕ) (q : ℚ) (k : ℕ) :
    ((besselTermQ n q k : ℚ) : ℝ) = besselTermReal n q k := by
  unfold besselTermQ besselTermReal
  push_cast
  try ring

/-- The real cast of the rational partial sum `besselPartialQ n q N` is the real partial sum
`∑ k < N, besselTermReal n q k`. -/
theorem besselPartialQ_cast (n : ℕ) (q : ℚ) (N : ℕ) :
    ((besselPartialQ n q N : ℚ) : ℝ) = ∑ k ∈ Finset.range N, besselTermReal n q k := by
  induction N with
  | zero => simp [besselPartialQ]
  | succ N ih => rw [besselPartialQ, Rat.cast_add, ih, besselTermQ_cast, Finset.sum_range_succ]

/-- Soundness of the checker: `J_n q` is a real number in `[lo, hi]`. -/
theorem besselCheck_sound (n N : ℕ) (q lo hi : ℚ) (h : besselCheck n N q lo hi = true) :
    ∃ r : ℝ, besselJ n ((q : ℝ) : ℂ) = r ∧ (lo : ℝ) ≤ r ∧ r ≤ hi := by
  simp only [besselCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hN, hlo⟩, hhi⟩ := h
  have hNR : 2 * ((q : ℝ) / 2) ^ 2 ≤ ((N : ℝ) + 1) * (n + N + 1) := by
    exact_mod_cast hN
  obtain ⟨r, hr, hb⟩ := besselJ_ofReal_enclosure n N (q : ℝ) hNR
  have hloR : (lo : ℝ) ≤ (besselPartialQ n q N : ℝ) - 2 * |(besselTermQ n q N : ℝ)| := by
    exact_mod_cast hlo
  have hhiR : (besselPartialQ n q N : ℝ) + 2 * |(besselTermQ n q N : ℝ)| ≤ hi := by
    exact_mod_cast hhi
  rw [besselPartialQ_cast, besselTermQ_cast] at hloR hhiR
  have hab := abs_sub_le_iff.1 hb
  exact ⟨r, hr, by linarith [hab.1, hab.2], by linarith [hab.1, hab.2]⟩

/-- The checker at an integer order `n`: for `n ≥ 0` or an even `n`, `besselCheck` at `|n|`;
for an odd negative `n`, `J_n = -J_{|n|}`, so `besselCheck` at `|n|` on `[-hi, -lo]`. -/
def besselCheckInt (n : ℤ) (N : ℕ) (q lo hi : ℚ) : Bool :=
  if 0 ≤ n ∨ n.natAbs % 2 = 0 then besselCheck n.natAbs N q lo hi
  else besselCheck n.natAbs N q (-hi) (-lo)

/-- Soundness of the integer-order checker: `J_n q` is a real number in `[lo, hi]`. -/
theorem besselJ_int_enclosure (n : ℤ) (N : ℕ) (q lo hi : ℚ)
    (h : besselCheckInt n N q lo hi = true) :
    ∃ r : ℝ, besselJ ((n : ℤ) : ℂ) ((q : ℚ) : ℂ) = r ∧ (lo : ℝ) ≤ r ∧ r ≤ hi := by
  have hq : ((q : ℚ) : ℂ) = (((q : ℚ) : ℝ) : ℂ) := (Complex.ofReal_ratCast q).symm
  rw [hq]
  have hneg : n < 0 → besselJ ((n : ℤ) : ℂ) (((q : ℚ) : ℝ) : ℂ) =
      (-1) ^ ((n.natAbs : ℕ) : ℤ) * besselJ ((n.natAbs : ℕ) : ℂ) (((q : ℚ) : ℝ) : ℂ) := by
    intro hn
    have hm : n = -((n.natAbs : ℕ) : ℤ) := by omega
    have hc : ((n : ℤ) : ℂ) = -(((n.natAbs : ℕ) : ℤ) : ℂ) := by rw [← Int.cast_neg, ← hm]
    have := Complex.besselJ_neg_int ((n.natAbs : ℕ) : ℤ) (((q : ℚ) : ℝ) : ℂ)
    rw [hc]
    simpa only [Int.cast_natCast] using this
  unfold besselCheckInt at h
  split_ifs at h with hcase
  · rcases le_or_gt 0 n with hn | hn
    · have hc : ((n : ℤ) : ℂ) = ((n.natAbs : ℕ) : ℂ) := by
        rw [← Int.cast_natCast, Int.natAbs_of_nonneg hn]
      rw [hc]
      exact besselCheck_sound n.natAbs N q lo hi h
    · have he : n.natAbs % 2 = 0 := by omega
      rw [hneg hn]
      obtain ⟨r, hr, h1, h2⟩ := besselCheck_sound n.natAbs N q lo hi h
      have hev : Even ((n.natAbs : ℕ) : ℤ) := by
        rw [Int.even_coe_nat]; exact Nat.even_iff.2 he
      refine ⟨r, ?_, h1, h2⟩
      rw [hr, hev.neg_one_zpow, one_mul]
  · have hn : n < 0 := by omega
    rw [hneg hn]
    obtain ⟨r, hr, h1, h2⟩ := besselCheck_sound n.natAbs N q (-hi) (-lo) h
    have hod : Odd ((n.natAbs : ℕ) : ℤ) := by
      rw [Int.odd_coe_nat]; exact Nat.odd_iff.2 (by omega)
    refine ⟨-r, ?_, ?_, ?_⟩
    · rw [hr, hod.neg_one_zpow]; push_cast; ring
    · push_cast at h2; linarith
    · push_cast at h1; linarith

end CAS.Analysis.SpecialFunctions.Bessel

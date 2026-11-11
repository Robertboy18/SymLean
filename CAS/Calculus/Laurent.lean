/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.Series
public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Data.List.GetD
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Laurent expansions of quotients

Let `g` and `h` have the Taylor expansions `∑ k ≤ n + m, cN_k (x - a) ^ k + o ((x - a) ^ (n + m))`
and `∑ k ≤ n + 2m, cD_k (x - a) ^ k + o ((x - a) ^ (n + 2m))` at `a`, where `h` vanishes to
order exactly `m` (`cD_k = 0` for `k < m`, `cD_m ≠ 0`). If the coefficients `cs` solve the
triangular system `cN_j = ∑ i ≤ j, cs_i cD_(m + j - i)` for `j ≤ n + m` (the division of the
two series), then

`g / h = ∑ k ≤ n + m, cs_k (x - a) ^ (k - m) + o ((x - a) ^ n)` as `x → a`, `x ≠ a`,

the Laurent expansion with a pole of order `m` (`laurent_of_isLittleO`). The check
`laurentCheck` is the triangular system on rational lists, and `laurent_of_check` takes the two
Taylor expansions from `series_of_check`.

## Main definitions

* `laurentCheck`: the Boolean check of the triangular system and of the order of the zero of `h`.

## Main results

* `laurent_of_isLittleO`: the Laurent expansion from the two Taylor expansions and the check.
* `laurent_of_check`: the same for two checked expressions, from `seriesCheck` and validity at
  `a`.

## Implementation notes

The search of `#cas [series x a n]` at a pole (`CAS.Command.Laurent`) computes `cN` and `cD` as
exact values of the symbolic derivatives, finds `m` as the order of the first nonzero
coefficient of `cD`, and solves the triangular system by forward substitution,
`cs_j = (cN_j - ∑ i < j, cs_i cD_(m + j - i)) / cD_m`. The kernel decides the two `seriesCheck`s
and `laurentCheck`, so the division itself is only checked, never trusted.

The proof of `laurent_of_isLittleO` writes `g - L h` as
`(g - P_N) + (P_N - C D̂) - C (h - P_D) / (x - a) ^ m`, with `P_D = (x - a) ^ m D̂` and
`L = C / (x - a) ^ m`. The middle term is a polynomial divisible by `(x - a) ^ (n + m + 1)`
because of the check, and `h / (x - a) ^ m → cD_m ≠ 0` bounds `1 / h`, so dividing by `h` loses
exactly the `m` orders of the pole. Only finitely many coefficients are ever checked, so the
proof needs polynomials (Mathlib's `Polynomial.ofCoeffList`, mapped to `ℝ`) and Mathlib's `=o`
calculus, and no formal Laurent series.
-/

@[expose] public section

namespace CAS.Verified.Expr

open Filter Asymptotics Topology Set Polynomial

/-- The triangular system of the series division, with the order `m` of the pole. -/
def laurentCheck (cN cD cs : List ℚ) (m n : ℕ) : Bool :=
  cN.length == n + m + 1 && cD.length == n + 2 * m + 1 && cs.length == n + m + 1 &&
    (List.range m).all (fun k ↦ cD.getD k 0 == 0) && cD.getD m 0 != 0 &&
    (List.range (n + m + 1)).all fun j ↦
      cN.getD j 0 == ((List.range (j + 1)).map fun i ↦ cs.getD i 0 * cD.getD (m + (j - i)) 0).sum

private theorem list_sum_map_range (f : ℕ → ℚ) (j : ℕ) :
    (((List.range j).map f).sum : ℚ) = ∑ i ∈ Finset.range j, f i := by
  rw [Finset.sum, Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]

private theorem getD_drop (l : List ℚ) (m k : ℕ) : (l.drop m).getD k 0 = l.getD (m + k) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **Laurent expansions.** The series division of two Taylor expansions, the denominator with a
zero of order `m` at `a`, gives the Laurent expansion of the quotient. -/
theorem laurent_of_isLittleO {g h : ℝ → ℝ} {a : ℝ} {m n : ℕ} {cN cD cs : List ℚ}
    (hg : (fun x ↦ g x - ∑ k ∈ Finset.range (n + m + 1), (cN.getD k 0 : ℝ) * (x - a) ^ k)
      =o[𝓝 a] fun x ↦ (x - a) ^ (n + m))
    (hh : (fun x ↦ h x - ∑ k ∈ Finset.range (n + 2 * m + 1), (cD.getD k 0 : ℝ) * (x - a) ^ k)
      =o[𝓝 a] fun x ↦ (x - a) ^ (n + 2 * m))
    (hcheck : laurentCheck cN cD cs m n = true) :
    (fun x ↦ g x / h x -
        ∑ k ∈ Finset.range (n + m + 1), (cs.getD k 0 : ℝ) * (x - a) ^ ((k : ℤ) - m))
      =o[𝓝[≠] a] fun x ↦ (x - a) ^ n := by
  unfold laurentCheck at hcheck
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, bne_iff_ne,
    ne_eq] at hcheck
  obtain ⟨⟨⟨⟨⟨hlN, hlD⟩, hls⟩, hlow⟩, hlead⟩, hsys⟩ := hcheck
  -- The real polynomial `P l` with the coefficients `l`; the proof uses only its coefficients and
  -- its values.
  obtain ⟨P, hPc, hPe⟩ : ∃ P : List ℚ → ℝ[X], (∀ l k, (P l).coeff k = (l.getD k 0 : ℝ)) ∧
      ∀ l y, (P l).eval y = ∑ k ∈ Finset.range l.length, (l.getD k 0 : ℝ) * y ^ k := by
    refine ⟨fun l ↦ (ofCoeffList l).map (algebraMap ℚ ℝ), fun l k ↦ by simp, fun l y ↦ ?_⟩
    have hdeg : ((ofCoeffList l).map (algebraMap ℚ ℝ)).natDegree < l.length + 1 :=
      Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ by
        rw [coeff_map, coeff_ofCoeffList, List.getD_eq_default _ _ hN.le, map_zero])
    rw [eval_eq_sum_range' hdeg, Finset.sum_range_succ, coeff_map, coeff_ofCoeffList,
      List.getD_eq_default _ _ le_rfl, map_zero, zero_mul, add_zero]
    simp
  have hle : 𝓝[≠] a ≤ 𝓝 a := nhdsWithin_le_nhds
  have hne : ∀ᶠ x in 𝓝[≠] a, x - a ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact sub_ne_zero.mpr hx
  -- The denominator polynomial is `(x - a) ^ m D̂`.
  have hPD : P cD = X ^ m * P (cD.drop m) := by
    ext k
    rw [coeff_X_pow_mul', hPc, hPc]
    split_ifs with hk
    · rw [getD_drop, Nat.add_sub_cancel' hk]
    · rw [hlow k (by omega), Rat.cast_zero]
  -- The polynomial `P_N - C D̂` is divisible by `X ^ (n + m + 1)`.
  have hE : X ^ (n + m + 1) ∣ P cN - P cs * P (cD.drop m) := by
    rw [X_pow_dvd_iff]
    intro d hd
    rw [coeff_sub, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hPc,
      hsys d hd, list_sum_map_range]
    simp only [Rat.cast_sum, Rat.cast_mul, hPc, getD_drop, Nat.succ_eq_add_one,
      sub_self]
  obtain ⟨Q, hQ⟩ := hE
  have hevalPN : ∀ x, ∑ k ∈ Finset.range (n + m + 1), (cN.getD k 0 : ℝ) * (x - a) ^ k =
      (P cN).eval (x - a) := fun x ↦ by rw [hPe, hlN]
  have hevalPD : ∀ x, ∑ k ∈ Finset.range (n + 2 * m + 1), (cD.getD k 0 : ℝ) * (x - a) ^ k =
      (x - a) ^ m * (P (cD.drop m)).eval (x - a) := fun x ↦ by
    rw [← hlD, ← hPe, hPD, eval_mul, eval_pow, eval_X]
  -- Continuity of the polynomial parts.
  have hcont (p : ℝ[X]) : Tendsto (fun x ↦ p.eval (x - a)) (𝓝 a) (𝓝 (p.eval 0)) :=
    (p.continuous.comp (continuous_sub_right a)).tendsto' a _ (by simp)
  have hbounded (p : ℝ[X]) : (fun x ↦ p.eval (x - a)) =O[𝓝 a] fun _ ↦ (1 : ℝ) :=
    (hcont p).isBigO_one ℝ
  -- `(h - P_D) / (x - a) ^ m = o ((x - a) ^ (n + m))`.
  have hhm : (fun x ↦ (h x - (x - a) ^ m * (P (cD.drop m)).eval (x - a)) / (x - a) ^ m)
      =o[𝓝[≠] a] fun x ↦ (x - a) ^ (n + m) := by
    refine ((hh.mono hle).mul_isBigO (isBigO_refl (fun x ↦ ((x - a) ^ m)⁻¹) _)).congr'
      (.of_forall fun x ↦ by simp only [hevalPD, div_eq_mul_inv]) ?_
    filter_upwards [hne] with x hx
    rw [show n + 2 * m = n + m + m by ring, pow_add, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hx), mul_one]
  -- `h / (x - a) ^ m → cD_m`.
  have hlim : Tendsto (fun x ↦ h x / (x - a) ^ m) (𝓝[≠] a) (𝓝 (cD.getD m 0 : ℝ)) := by
    have hD : Tendsto (fun x ↦ (P (cD.drop m)).eval (x - a)) (𝓝[≠] a)
        (𝓝 (cD.getD m 0 : ℝ)) := by
      have := (hcont (P (cD.drop m))).mono_left hle
      rwa [← coeff_zero_eq_eval_zero, hPc, getD_drop, add_zero] at this
    have hrest := (isLittleO_one_iff ℝ).mp (hhm.trans_isBigO
      ((((continuous_sub_right a).pow (n + m)).tendsto a).isBigO_one ℝ |>.mono hle))
    have := hD.add hrest
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [hne] with x hx
    field_simp
    ring
  have hlead' : (cD.getD m 0 : ℝ) ≠ 0 := by exact_mod_cast hlead
  have hhne : ∀ᶠ x in 𝓝[≠] a, h x ≠ 0 := by
    filter_upwards [hlim.eventually_ne hlead'] with x hx h0
    simp [h0] at hx
  -- `1 / h = O (1 / (x - a) ^ m)`.
  have hinv : (fun x ↦ (h x)⁻¹) =O[𝓝[≠] a] fun x ↦ ((x - a) ^ m)⁻¹ := by
    have hq : Tendsto (fun x ↦ (x - a) ^ m / h x) (𝓝[≠] a) (𝓝 (cD.getD m 0 : ℝ)⁻¹) :=
      (hlim.inv₀ hlead').congr fun x ↦ inv_div _ _
    refine ((hq.isBigO_one ℝ).mul (isBigO_refl _ _)).congr' ?_ (.of_forall fun x ↦ one_mul _)
    filter_upwards [hne, hhne] with x hx hx'
    field_simp
  -- `g - L h = o ((x - a) ^ (n + m))`.
  have hR : (fun x ↦ g x - (P cs).eval (x - a) / (x - a) ^ m * h x)
      =o[𝓝[≠] a] fun x ↦ (x - a) ^ (n + m) := by
    have h1 : (fun x ↦ g x - (P cN).eval (x - a)) =o[𝓝[≠] a] fun x ↦ (x - a) ^ (n + m) :=
      (hg.mono hle).congr_left fun x ↦ by rw [hevalPN x]
    have h2 : (fun x ↦ (P cN - P cs * P (cD.drop m)).eval (x - a))
        =o[𝓝[≠] a] fun x ↦ (x - a) ^ (n + m) := by
      have hpow : (fun x ↦ (x - a) ^ (n + m + 1)) =o[𝓝 a] fun x ↦ (x - a) ^ (n + m) :=
        (isLittleO_pow_pow (𝕜 := ℝ) (by omega : n + m < n + m + 1)).comp_tendsto
          (tendsto_sub_nhds_zero_iff.mpr tendsto_id)
      refine ((hbounded Q).mul_isLittleO hpow).mono hle |>.congr (fun x ↦ ?_) fun x ↦ one_mul _
      rw [hQ, eval_mul, eval_pow, eval_X, mul_comm]
    have h3 : (fun x ↦ (P cs).eval (x - a) *
        ((h x - (x - a) ^ m * (P (cD.drop m)).eval (x - a)) / (x - a) ^ m))
        =o[𝓝[≠] a] fun x ↦ (x - a) ^ (n + m) :=
      (((hbounded (P cs)).mono hle).mul_isLittleO hhm).congr_right fun x ↦ one_mul _
    refine ((h1.add h2).sub h3).congr' ?_ (by filter_upwards with x; rfl)
    filter_upwards [hne] with x hx
    rw [eval_sub, eval_mul]
    field_simp
    ring
  -- Divide by `h`.
  refine (hR.mul_isBigO hinv).congr' ?_ ?_
  · filter_upwards [hne, hhne] with x hx hx'
    have hL : ∑ k ∈ Finset.range (n + m + 1), (cs.getD k 0 : ℝ) * (x - a) ^ ((k : ℤ) - m) =
        (P cs).eval (x - a) / (x - a) ^ m := by
      rw [hPe, hls, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [zpow_sub₀ hx, zpow_natCast, zpow_natCast, mul_div_assoc]
    rw [hL]
    field_simp
  · filter_upwards [hne] with x hx
    rw [pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx), mul_one]

/-- The Laurent expansion of a quotient of two expressions at `a`. -/
theorem laurent_of_check (num den : Verified.Expr (Fin 1)) (m n : ℕ) (a : ℚ)
    (hnum : num.ValidIteratesOn (n + m + 1) {(a : ℝ)})
    (hden : den.ValidIteratesOn (n + 2 * m + 1) {(a : ℝ)})
    (cN cD cs : List ℚ)
    (h : (seriesCheck num (n + m) a cN && seriesCheck den (n + 2 * m) a cD &&
      laurentCheck cN cD cs m n) = true) :
    (fun x ↦ num.univariateEval x / den.univariateEval x -
        ∑ k ∈ Finset.range (n + m + 1), (cs.getD k 0 : ℝ) * (x - a) ^ ((k : ℤ) - m))
      =o[𝓝[≠] (a : ℝ)] fun x ↦ (x - a) ^ n := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hN, hD⟩, hcheck⟩ := h
  exact laurent_of_isLittleO (series_of_check num (n + m) a hnum cN hN)
    (series_of_check den (n + 2 * m) a hden cD hD) hcheck

end CAS.Verified.Expr

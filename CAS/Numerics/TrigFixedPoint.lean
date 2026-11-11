/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.AtanProof
public import FloatLib.Numerics.Enclosure.Trigonometric.SinCosProof

/-!
# Fixed-point π, sine and cosine with a priori error bounds

Every quantity here is an integer at the scale `2 ^ w`, computed with natural-number floor
division only. `piFixed w` approximates `2 ^ w π` by Machin's formula, and `trigTaylorCos` and
`trigTaylorSin` evaluate the Taylor polynomials of cosine and sine with floored terms. The error
bounds hold for every working precision `w`, so they are proved once rather than checked for
each table.

## Main definitions

* `piFixed w`: Machin's formula `π = 16 arctan (1/5) - 4 arctan (1/239)` with `w / 4 + 2`
  floored terms of each arctangent series (`atanInvFixed`).
* `trigTaylorCos (2 ^ w) X d`, `trigTaylorSin (2 ^ w) X d`: the Taylor polynomials of degree `d`
  of cosine and sine at `X / 2 ^ w`, summed from the floored terms of `trigTaylorLoop`, which
  computes each term from the previous one by one product and two floor divisions.
* `trigDegree w`: the least degree `d ≤ w` with `2 ^ w ≤ (d + 1)!`.

## Main results

* `abs_piFixed_sub_le`: `piFixed w` is within `5 w + 41` of `2 ^ w π`.
* `taylorTermFixed_mem`: for `X ≤ 2 ^ w` every floored term lies at most `2` below the exact
  term and never above it.
* `abs_trigTaylorCos_sub_le`, `abs_trigTaylorSin_sub_le`: for `X ≤ 2 ^ w` the sums lie within
  `2 (d + 1) + 2 ^ w / (d + 1)!` of `2 ^ w cos (X / 2 ^ w)` and `2 ^ w sin (X / 2 ^ w)`.

## Implementation notes

We compute π from Machin's formula because its two arctangent series need only divisions by
small natural numbers and converge fast: the terms at `1/5` shrink by `25` and those at `1/239`
by `239 ^ 2`, so `n = w / 4 + 2` terms bring both tails below `2 ^ w / 25 ^ n ≤ 1 / 32`.
`atanInvLoop` keeps `⌊2 ^ w / m ^ (2 i + 1)⌋` and divides it by `m ^ 2` at each step. Nested
floor divisions are one floor division, so every term is the floor of the exact term, and the
terms of even and of odd index go into two separate natural numbers, which keeps signs out of
the loop. With the weights `16` and `4` of the formula the floors cost `20 n ≤ 5 w + 40` and the
tails less than `1`. The Taylor loops floor a product that already carries the error of the
previous term. The first term is exact, and every later error is multiplied by
`X / (2 ^ w (i + 1)) ≤ 1 / 2` before the next floor, so no term is off by more than `2`.

The truncation bounds of the series are FloatLib's `abs_atan_sub_atanTaylor_le`,
`abs_cos_sub_cosTaylor_le` and `abs_sin_sub_sinTaylor_le`, and Machin's identity is Mathlib's
`Real.four_mul_arctan_inv_5_sub_arctan_inv_239`; the fixed-point loops and their error budgets
are ours. Nothing here is a certificate. The bounds are theorems for every `w`, and a kernel check
that uses the values, such as the comparison of a stored table with `trigTable` in
`TrigTableWords`, only evaluates the loops. They call `Nat.div`, `Nat.mul`, `Nat.add` and
`Nat.mod` directly, so that this evaluation uses the kernel's natural-number literal arithmetic.

## References

* David H. Bailey, Jonathan M. Borwein, Peter B. Borwein and Simon Plouffe, "The Quest for Pi",
  *The Mathematical Intelligencer* 19 (1997), pp. 50-57, <https://doi.org/10.1007/BF03024340>.
  Section 2 gives the arctangent series and Machin's formula
  `π / 4 = 4 arctan (1/5) - arctan (1/239)`, evaluated through that series as here.
* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>.
* The mathlib Community, "The Lean Mathematical Library", in *Proceedings of the 9th ACM SIGPLAN
  International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020,
  pp. 367-381, <https://doi.org/10.1145/3372885.3373824>.
-/

@[expose] public section

namespace CAS.Numerics

open FloatLib.Numerics.Enclosure

/-- Floor division of natural numbers lies within one of the real quotient. -/
theorem natCast_div_mem (a b : ℕ) :
    ((a / b : ℕ) : ℝ) ∈ Set.Ioc ((a : ℝ) / b - 1) ((a : ℝ) / b) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  refine ⟨?_, Nat.cast_div_le⟩
  have h : (a : ℝ) < ((a / b : ℕ) : ℝ) * b + b := by exact_mod_cast Nat.lt_div_mul_add hb
  rw [sub_lt_iff_lt_add, div_lt_iff₀ (by exact_mod_cast hb)]
  linarith

/-! ### Machin's formula in fixed point -/

/-- The arctangent series at `1 / m` in fixed point, with natural-number operations only.
After `i` steps the state is `⌊W / m ^ (2 i + 1)⌋` and the sums of the floored terms
`⌊W / (m ^ (2 j + 1) (2 j + 1))⌋`, `j < i`, over even and over odd `j`. -/
def atanInvLoop (W m : ℕ) : ℕ → ℕ × ℕ × ℕ
  | 0 => (Nat.div W m, 0, 0)
  | i + 1 =>
    match atanInvLoop W m i with
    | (u, se, so) =>
      match Nat.mod i 2 with
      | 0 => (Nat.div u (Nat.mul m m), Nat.add se (Nat.div u (Nat.succ (Nat.mul 2 i))), so)
      | _ => (Nat.div u (Nat.mul m m), se, Nat.add so (Nat.div u (Nat.succ (Nat.mul 2 i))))

/-- `atanInvLoop W m i` is `(W / m ^ (2 * i + 1), Se, So)`, where `Se` and `So` are the sums over
the even and over the odd `j < i` of the natural quotients `W / (m ^ (2 * j + 1) * (2 * j + 1))`. -/
theorem atanInvLoop_eq (W m i : ℕ) :
    atanInvLoop W m i = (W / m ^ (2 * i + 1),
      ∑ j ∈ Finset.range i, (if j % 2 = 0 then W / (m ^ (2 * j + 1) * (2 * j + 1)) else 0),
      ∑ j ∈ Finset.range i, (if j % 2 = 0 then 0 else W / (m ^ (2 * j + 1) * (2 * j + 1)))) := by
  induction i with
  | zero =>
    simp only [atanInvLoop, Finset.range_zero, Finset.sum_empty, mul_zero, zero_add, pow_one]
    rfl
  | succ i ih =>
    have hu : W / m ^ (2 * i + 1) / (m * m) = W / m ^ (2 * (i + 1) + 1) := by
      rw [Nat.div_div_eq_div_mul]
      congr 1
      ring
    have hm : Nat.mod i 2 = i % 2 := rfl
    rw [atanInvLoop, ih, Finset.sum_range_succ, Finset.sum_range_succ, ← hu,
      ← Nat.div_div_eq_div_mul W (m ^ (2 * i + 1)) (2 * i + 1)]
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · simp only [hm, h, ite_true]
      rfl
    · simp only [hm, h, one_ne_zero, ite_false, add_zero]
      rfl

/-- An approximation of `W arctan (1 / m)` by `n` floored terms of the arctangent series. -/
def atanInvFixed (W m n : ℕ) : ℤ :=
  let r := atanInvLoop W m n
  (r.2.1 : ℤ) - r.2.2

/-- `atanInvFixed W m n` is the alternating sum over `j < n` of the natural quotients
`W / (m ^ (2 * j + 1) * (2 * j + 1))`, with sign `(-1) ^ j`. -/
theorem atanInvFixed_eq (W m n : ℕ) :
    atanInvFixed W m n =
      ∑ j ∈ Finset.range n, (-1 : ℤ) ^ j * ((W / (m ^ (2 * j + 1) * (2 * j + 1)) : ℕ) : ℤ) := by
  rw [atanInvFixed, atanInvLoop_eq]
  dsimp only
  push_cast [Nat.cast_sum, Nat.cast_ite]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · simp [h, Even.neg_one_pow (Nat.even_iff.mpr h)]
  · simp [h, Odd.neg_one_pow (Nat.odd_iff.mpr h)]

/-- The floored series lies within `n` of `W` times the exact partial sum, and FloatLib's
geometric tail bound covers the truncation. -/
theorem abs_atanInvFixed_sub_le (W m n : ℕ) (hm : 2 ≤ m) :
    |(atanInvFixed W m n : ℝ) - W * Real.arctan (m : ℝ)⁻¹| ≤
      n + W * (atanRadius (1 / m : ℚ) n : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hx : |(1 / m : ℚ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by exact_mod_cast (show 0 < m by omega))]
    exact_mod_cast (show 1 < m by omega)
  have htail := abs_atan_sub_atanTaylor_le (1 / m : ℚ) n hx
  have hcast : (((1 / m : ℚ)) : ℝ) = (m : ℝ)⁻¹ := by push_cast; ring
  rw [hcast] at htail
  have hseries : |(atanInvFixed W m n : ℝ) - W * (atanTaylor (1 / m : ℚ) n : ℝ)| ≤ n := by
    rw [atanInvFixed_eq, cast_atanTaylor, Finset.mul_sum, hcast]
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_card_nsmul _ _ 1 fun j _ ↦ ?_).trans (by simp))
    obtain ⟨hlo, hhi⟩ := natCast_div_mem W (m ^ (2 * j + 1) * (2 * j + 1))
    have hexact : W * ((-1 : ℝ) ^ j * ((m : ℝ)⁻¹) ^ (2 * j + 1) / (2 * j + 1)) =
        (-1 : ℝ) ^ j * ((W : ℝ) / ((m ^ (2 * j + 1) * (2 * j + 1) : ℕ) : ℝ)) := by
      rw [inv_pow]
      push_cast
      field_simp
    rw [hexact, ← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_le]
    constructor <;> linarith
  refine (abs_sub_le _ (W * (atanTaylor (1 / m : ℚ) n : ℝ)) _).trans (add_le_add hseries ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg W)]
  exact mul_le_mul_of_nonneg_left (by rwa [abs_sub_comm]) (Nat.cast_nonneg W)

/-- For `5 ≤ m`, FloatLib's arctangent tail radius `atanRadius (1 / m) n`, cast to `ℝ`, is at most
`25 / 24 / m * (1 / 25) ^ n`. -/
theorem atanRadius_inv_le (m n : ℕ) (hm : 5 ≤ m) :
    (atanRadius (1 / m : ℚ) n : ℝ) ≤ 25 / 24 / m * (1 / 25) ^ n := by
  have hm0 : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  rw [cast_atanRadius]
  push_cast
  rw [abs_of_pos (by positivity)]
  have hsq : (1 / (m : ℝ)) ^ 2 ≤ 1 / 25 := by
    rw [div_pow, one_pow, one_div_le_one_div (by positivity) (by norm_num)]
    nlinarith
  calc 1 / (m : ℝ) * ((1 / (m : ℝ)) ^ 2) ^ n / (1 - (1 / (m : ℝ)) ^ 2)
      ≤ 1 / (m : ℝ) * (1 / 25) ^ n / (24 / 25) := by
        gcongr
        linarith
    _ = 25 / 24 / m * (1 / 25) ^ n := by ring

/-- `2 ^ w π` to within `5 w + 41`, by Machin's formula with `w / 4 + 2` terms per series. -/
def piFixed (w : ℕ) : ℤ :=
  4 * (4 * atanInvFixed (2 ^ w) 5 (w / 4 + 2) - atanInvFixed (2 ^ w) 239 (w / 4 + 2))

/-- `piFixed w` is within `5 w + 41` of `2 ^ w π`: each floored arctangent series is within
its number of terms of the exact partial sum, and the tails are below `2 ^ w / 25 ^ n`. -/
theorem abs_piFixed_sub_le (w : ℕ) : |(piFixed w : ℝ) - 2 ^ w * Real.pi| ≤ 5 * w + 41 := by
  set n := w / 4 + 2 with hn
  have h5 := abs_atanInvFixed_sub_le (2 ^ w) 5 n (by norm_num)
  have h239 := abs_atanInvFixed_sub_le (2 ^ w) 239 n (by norm_num)
  have r5 := atanRadius_inv_le 5 n le_rfl
  have r239 := atanRadius_inv_le 239 n (by norm_num)
  push_cast at h5 h239 r5 r239
  have hpow : (2 : ℝ) ^ w * (1 / 25) ^ n ≤ 1 / 32 := by
    have h16 : (2 : ℝ) ^ (w + 5) ≤ 25 ^ n := by
      calc (2 : ℝ) ^ (w + 5) ≤ 2 ^ (4 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 16 ^ n := by rw [pow_mul]; norm_num
        _ ≤ 25 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    rw [one_div_pow, ← div_eq_mul_one_div, div_le_iff₀ (by positivity)]
    rw [pow_add] at h16
    linarith
  have hmachin := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have hW : (0 : ℝ) ≤ 2 ^ w := by positivity
  have hnw : (n : ℝ) ≤ w / 4 + 2 := by
    have : (4 * n : ℝ) ≤ w + 8 := by exact_mod_cast (show 4 * n ≤ w + 8 by omega)
    linarith
  have hsplit : (piFixed w : ℝ) - 2 ^ w * Real.pi =
      16 * ((atanInvFixed (2 ^ w) 5 n : ℝ) - 2 ^ w * Real.arctan 5⁻¹) -
        4 * ((atanInvFixed (2 ^ w) 239 n : ℝ) - 2 ^ w * Real.arctan 239⁻¹) := by
    rw [piFixed, ← hn]
    push_cast
    linear_combination (4 * 2 ^ w : ℝ) * hmachin
  obtain ⟨h5l, h5u⟩ := abs_le.1 h5
  obtain ⟨h239l, h239u⟩ := abs_le.1 h239
  have := mul_le_mul_of_nonneg_left r5 hW
  have := mul_le_mul_of_nonneg_left r239 hW
  rw [hsplit, abs_le]
  constructor <;> linarith

/-! ### Taylor polynomials of cosine and sine in fixed point -/

/-- The floored Taylor terms of the exponential series at `X / 2 ^ w`, scaled by `2 ^ w`;
each term is the previous one times `X / 2 ^ w`, divided by the index, and floored. -/
def taylorTermFixed (w X : ℕ) : ℕ → ℕ
  | 0 => 2 ^ w
  | i + 1 => taylorTermFixed w X i * X / 2 ^ w / (i + 1)

/-- The sign of the `i`-th Taylor coefficient of cosine. -/
def cosTaylorSign (i : ℕ) : ℤ := if i % 4 = 0 then 1 else if i % 4 = 2 then -1 else 0

/-- The sign of the `i`-th Taylor coefficient of sine. -/
def sinTaylorSign (i : ℕ) : ℤ := if i % 4 = 1 then 1 else if i % 4 = 3 then -1 else 0

/-- One pass over the floored terms through degree `j`, with natural-number operations only.
The state is the last term and the sums of the terms whose Taylor sign is `+1` and `-1` for
cosine (degrees `0` and `2` modulo `4`) and for sine (degrees `1` and `3` modulo `4`). -/
def trigTaylorLoop (W X : ℕ) : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ
  | 0 => (W, W, 0, 0, 0)
  | j + 1 =>
    match trigTaylorLoop W X j with
    | (t, cp, cn, sp, sn) =>
      let u := Nat.div (Nat.div (Nat.mul t X) W) (Nat.succ j)
      match Nat.mod (Nat.succ j) 4 with
      | 0 => (u, Nat.add cp u, cn, sp, sn)
      | 1 => (u, cp, cn, Nat.add sp u, sn)
      | 2 => (u, cp, Nat.add cn u, sp, sn)
      | _ => (u, cp, cn, sp, Nat.add sn u)

/-- `trigTaylorLoop (2 ^ w) X j` is the term `taylorTermFixed w X j` followed by the four sums over
`i ≤ j` of `taylorTermFixed w X i` with `i % 4` equal to `0`, `2`, `1` and `3`, in that order. -/
theorem trigTaylorLoop_eq (w X j : ℕ) :
    trigTaylorLoop (2 ^ w) X j = (taylorTermFixed w X j,
      ∑ i ∈ Finset.range (j + 1), (if i % 4 = 0 then taylorTermFixed w X i else 0),
      ∑ i ∈ Finset.range (j + 1), (if i % 4 = 2 then taylorTermFixed w X i else 0),
      ∑ i ∈ Finset.range (j + 1), (if i % 4 = 1 then taylorTermFixed w X i else 0),
      ∑ i ∈ Finset.range (j + 1), (if i % 4 = 3 then taylorTermFixed w X i else 0)) := by
  induction j with
  | zero => simp [trigTaylorLoop, taylorTermFixed]
  | succ j ih =>
    rw [trigTaylorLoop, ih]
    simp only [Finset.sum_range_succ _ (j + 1)]
    have hterm : Nat.div (Nat.div (Nat.mul (taylorTermFixed w X j) X) (2 ^ w)) (Nat.succ j) =
        taylorTermFixed w X (j + 1) := rfl
    rcases (by omega : (j + 1) % 4 = 0 ∨ (j + 1) % 4 = 1 ∨ (j + 1) % 4 = 2 ∨ (j + 1) % 4 = 3)
      with h | h | h | h
    all_goals
      have hm : Nat.mod (Nat.succ j) 4 = (j + 1) % 4 := rfl
      simp only [hm, h, hterm]
      simp [Nat.add_eq]

/-- The fixed-point Taylor sum of cosine through degree `d` at `X / W`. -/
def trigTaylorCos (W X d : ℕ) : ℤ :=
  let r := trigTaylorLoop W X d
  (r.2.1 : ℤ) - r.2.2.1

/-- The fixed-point Taylor sum of sine through degree `d` at `X / W`. -/
def trigTaylorSin (W X d : ℕ) : ℤ :=
  let r := trigTaylorLoop W X d
  (r.2.2.2.1 : ℤ) - r.2.2.2.2

/-- `trigTaylorCos (2 ^ w) X d` is the sum over `i ≤ d` of
`cosTaylorSign i * taylorTermFixed w X i`. -/
theorem trigTaylorCos_eq (w X d : ℕ) :
    trigTaylorCos (2 ^ w) X d =
      ∑ i ∈ Finset.range (d + 1), cosTaylorSign i * (taylorTermFixed w X i : ℤ) := by
  rw [trigTaylorCos, trigTaylorLoop_eq]
  dsimp only
  push_cast [Nat.cast_sum, Nat.cast_ite]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h | h | h | h <;>
    simp [h, cosTaylorSign]

/-- `trigTaylorSin (2 ^ w) X d` is the sum over `i ≤ d` of
`sinTaylorSign i * taylorTermFixed w X i`. -/
theorem trigTaylorSin_eq (w X d : ℕ) :
    trigTaylorSin (2 ^ w) X d =
      ∑ i ∈ Finset.range (d + 1), sinTaylorSign i * (taylorTermFixed w X i : ℤ) := by
  rw [trigTaylorSin, trigTaylorLoop_eq]
  dsimp only
  push_cast [Nat.cast_sum, Nat.cast_ite]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h | h | h | h <;>
    simp [h, sinTaylorSign]

/-- FloatLib's cosine coefficients are the signs `cosTaylorSign`. -/
theorem cast_cosCoefficient_eq (i : ℕ) : (cosCoefficient i : ℝ) = cosTaylorSign i := by
  rw [cosCoefficient, cosTaylorSign]
  by_cases h0 : i % 4 = 0
  · have he : Even (i / 2) := Nat.even_iff.mpr (by omega)
    simp [show i % 2 = 0 by omega, h0, he.neg_one_pow]
  · by_cases h2 : i % 4 = 2
    · have ho : Odd (i / 2) := Nat.odd_iff.mpr (by omega)
      simp [show i % 2 = 0 by omega, h2, ho.neg_one_pow]
    · simp [show i % 2 = 1 by omega, h0, h2]

/-- FloatLib's sine coefficients are the signs `sinTaylorSign`. -/
theorem cast_sinCoefficient_eq (i : ℕ) : (sinCoefficient i : ℝ) = sinTaylorSign i := by
  rw [sinCoefficient, sinTaylorSign]
  by_cases h1 : i % 4 = 1
  · have he : Even (i / 2) := Nat.even_iff.mpr (by omega)
    simp [show i % 2 = 1 by omega, h1, he.neg_one_pow]
  · by_cases h3 : i % 4 = 3
    · have ho : Odd (i / 2) := Nat.odd_iff.mpr (by omega)
      simp [show i % 2 = 1 by omega, h3, ho.neg_one_pow]
    · simp [show i % 2 = 0 by omega, h1, h3]

/-- For `X ≤ 2 ^ w` every floored term lies at most `2` below the exact term
`2 ^ w (X / 2 ^ w) ^ i / i!`, and never above it; the first term is exact. -/
theorem taylorTermFixed_mem (w X : ℕ) (hX : X ≤ 2 ^ w) (i : ℕ) :
    (taylorTermFixed w X i : ℝ) ∈ Set.Icc
      (2 ^ w * ((X : ℝ) / 2 ^ w) ^ i / i.factorial - (if i = 0 then 0 else 2))
      (2 ^ w * ((X : ℝ) / 2 ^ w) ^ i / i.factorial) := by
  have hs : (0 : ℝ) < 2 ^ w := by positivity
  set a : ℝ := (X : ℝ) / 2 ^ w with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := (div_le_one hs).2 (by exact_mod_cast hX)
  induction i with
  | zero => simp [taylorTermFixed]
  | succ i ih =>
    obtain ⟨hlow, hup⟩ := ih
    have hstep : (taylorTermFixed w X (i + 1) : ℝ) =
        ((taylorTermFixed w X i * X / (2 ^ w * (i + 1)) : ℕ) : ℝ) := by
      rw [taylorTermFixed, Nat.div_div_eq_div_mul]
    obtain ⟨hlo, hhi⟩ :=
      natCast_div_mem (taylorTermFixed w X i * X) (2 ^ w * (i + 1))
    have hq : ((taylorTermFixed w X i * X : ℕ) : ℝ) / ((2 ^ w * (i + 1) : ℕ) : ℝ) =
        (taylorTermFixed w X i : ℝ) * (a / (i + 1)) := by
      rw [ha]
      push_cast
      field_simp
    rw [hq, ← hstep] at hlo hhi
    have hexact : 2 ^ w * a ^ (i + 1) / ((i + 1).factorial : ℝ) =
        2 ^ w * a ^ i / (i.factorial : ℝ) * (a / (i + 1)) := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    have hfac : (0 : ℝ) ≤ a / (i + 1) := by positivity
    rw [hexact]
    refine ⟨?_, hhi.trans (mul_le_mul_of_nonneg_right hup hfac)⟩
    have herr : (if i = 0 then (0 : ℝ) else 2) * (a / (i + 1)) ≤ 1 := by
      split_ifs with hi
      · norm_num
      · have hi1 : (2 : ℝ) ≤ i + 1 := by norm_cast; omega
        rw [mul_div_assoc', div_le_one (by positivity)]
        linarith
    have := mul_le_mul_of_nonneg_right hlow hfac
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
    nlinarith

/-- A signed sum of the floored terms with coefficients of absolute value at most one lies
within `2 (d + 1)` of `2 ^ w` times the matching exact polynomial. -/
theorem abs_signedTaylorSum_sub_le (w X d : ℕ) (hX : X ≤ 2 ^ w) (σ : ℕ → ℤ)
    (hσ : ∀ i, |(σ i : ℝ)| ≤ 1) :
    |∑ i ∈ Finset.range (d + 1), (σ i : ℝ) * taylorTermFixed w X i -
        2 ^ w * ∑ i ∈ Finset.range (d + 1), (σ i : ℝ) * ((X : ℝ) / 2 ^ w) ^ i /
          i.factorial| ≤ 2 * (d + 1) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_card_nsmul _ _ 2 fun i _ ↦ ?_).trans_eq (by simp; ring))
  obtain ⟨hlow, hup⟩ := taylorTermFixed_mem w X hX i
  have h2 : |(taylorTermFixed w X i : ℝ) - 2 ^ w * ((X : ℝ) / 2 ^ w) ^ i / i.factorial| ≤ 2 :=
    abs_le.2 ⟨by split_ifs at hlow <;> linarith, by linarith⟩
  rw [show (σ i : ℝ) * taylorTermFixed w X i -
      2 ^ w * ((σ i : ℝ) * ((X : ℝ) / 2 ^ w) ^ i / i.factorial) = (σ i : ℝ) *
        (taylorTermFixed w X i - 2 ^ w * ((X : ℝ) / 2 ^ w) ^ i / i.factorial) by ring, abs_mul]
  exact (mul_le_mul (hσ i) h2 (abs_nonneg _) zero_le_one).trans_eq (one_mul 2)

/-- `|cosTaylorSign i| ≤ 1` in `ℝ`, for every `i`. -/
theorem abs_cast_cosTaylorSign_le (i : ℕ) : |(cosTaylorSign i : ℝ)| ≤ 1 := by
  unfold cosTaylorSign
  split_ifs <;> norm_num

/-- `|sinTaylorSign i| ≤ 1` in `ℝ`, for every `i`. -/
theorem abs_cast_sinTaylorSign_le (i : ℕ) : |(sinTaylorSign i : ℝ)| ≤ 1 := by
  unfold sinTaylorSign
  split_ifs <;> norm_num

/-- For `X ≤ 2 ^ w`, so that `X / 2 ^ w` lies in `[0, 1]`, FloatLib's Taylor remainder bound
satisfies `2 ^ w * trigRadius (X / 2 ^ w) d ≤ 2 ^ w / (d + 1)!` in `ℝ`, for every degree `d`. -/
theorem two_pow_mul_trigRadius_le (w X d : ℕ) (hX : X ≤ 2 ^ w) :
    2 ^ w * (trigRadius ((X : ℚ) / 2 ^ w) d : ℝ) ≤ 2 ^ w / (d + 1).factorial := by
  have hs : (0 : ℝ) < 2 ^ w := by positivity
  rw [trigRadius]
  push_cast
  have ha : |(X : ℝ) / 2 ^ w| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), div_le_one hs]
    exact_mod_cast hX
  have hp : |(X : ℝ) / 2 ^ w| ^ (d + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) ha
  rw [mul_div_assoc']
  gcongr
  exact mul_le_of_le_one_right hs.le hp

/-- For `X ≤ 2 ^ w`, the fixed-point cosine sum `trigTaylorCos (2 ^ w) X d` through degree `d`
lies within `2 * (d + 1) + 2 ^ w / (d + 1)!` of `2 ^ w * cos (X / 2 ^ w)` in `ℝ`. -/
theorem abs_trigTaylorCos_sub_le (w X d : ℕ) (hX : X ≤ 2 ^ w) :
    |(trigTaylorCos (2 ^ w) X d : ℝ) - 2 ^ w * Real.cos ((X : ℝ) / 2 ^ w)| ≤
      2 * (d + 1) + 2 ^ w / (d + 1).factorial := by
  have htail := abs_cos_sub_cosTaylor_le ((X : ℚ) / 2 ^ w) d
  have hcast : ((((X : ℚ) / 2 ^ w : ℚ)) : ℝ) = (X : ℝ) / 2 ^ w := by push_cast; ring
  rw [hcast] at htail
  have hpoly : (cosTaylor ((X : ℚ) / 2 ^ w) d : ℝ) =
      ∑ i ∈ Finset.range (d + 1), (cosTaylorSign i : ℝ) * ((X : ℝ) / 2 ^ w) ^ i /
        i.factorial := by
    rw [cosTaylor]
    push_cast [cast_cosCoefficient_eq]
    rfl
  have hsum := abs_signedTaylorSum_sub_le w X d hX cosTaylorSign abs_cast_cosTaylorSign_le
  rw [← hpoly] at hsum
  have hrad := two_pow_mul_trigRadius_le w X d hX
  have hs : (0 : ℝ) ≤ 2 ^ w := by positivity
  rw [trigTaylorCos_eq]
  push_cast
  refine (abs_sub_le _ (2 ^ w * (cosTaylor ((X : ℚ) / 2 ^ w) d : ℝ)) _).trans
    (add_le_add hsum ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg hs]
  exact (mul_le_mul_of_nonneg_left (by rwa [abs_sub_comm]) hs).trans hrad

/-- For `X ≤ 2 ^ w`, the fixed-point sine sum `trigTaylorSin (2 ^ w) X d` through degree `d`
lies within `2 * (d + 1) + 2 ^ w / (d + 1)!` of `2 ^ w * sin (X / 2 ^ w)` in `ℝ`. -/
theorem abs_trigTaylorSin_sub_le (w X d : ℕ) (hX : X ≤ 2 ^ w) :
    |(trigTaylorSin (2 ^ w) X d : ℝ) - 2 ^ w * Real.sin ((X : ℝ) / 2 ^ w)| ≤
      2 * (d + 1) + 2 ^ w / (d + 1).factorial := by
  have htail := abs_sin_sub_sinTaylor_le ((X : ℚ) / 2 ^ w) d
  have hcast : ((((X : ℚ) / 2 ^ w : ℚ)) : ℝ) = (X : ℝ) / 2 ^ w := by push_cast; ring
  rw [hcast] at htail
  have hpoly : (sinTaylor ((X : ℚ) / 2 ^ w) d : ℝ) =
      ∑ i ∈ Finset.range (d + 1), (sinTaylorSign i : ℝ) * ((X : ℝ) / 2 ^ w) ^ i /
        i.factorial := by
    rw [sinTaylor]
    push_cast [cast_sinCoefficient_eq]
    rfl
  have hsum := abs_signedTaylorSum_sub_le w X d hX sinTaylorSign abs_cast_sinTaylorSign_le
  rw [← hpoly] at hsum
  have hrad := two_pow_mul_trigRadius_le w X d hX
  have hs : (0 : ℝ) ≤ 2 ^ w := by positivity
  rw [trigTaylorSin_eq]
  push_cast
  refine (abs_sub_le _ (2 ^ w * (sinTaylor ((X : ℚ) / 2 ^ w) d : ℝ)) _).trans
    (add_le_add hsum ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg hs]
  exact (mul_le_mul_of_nonneg_left (by rwa [abs_sub_comm]) hs).trans hrad

/-! ### The Taylor degree -/

/-- Search for the least `d` from the start value with `t ≤ (d + 1)!`, using `fuel` steps;
`f` carries `(d + 1)!`. -/
def factorialDegree (t : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, d, _ => d
  | fuel + 1, d, f => if t ≤ f then d else factorialDegree t fuel (d + 1) (f * (d + 2))

/-- The search `factorialDegree t fuel d (d + 1)!` returns at most `d + fuel`, and its result `e`
satisfies `t ≤ (e + 1)!` or `e = d + fuel`. -/
theorem factorialDegree_spec (t fuel d : ℕ) :
    factorialDegree t fuel d (d + 1).factorial ≤ d + fuel ∧
      (t ≤ (factorialDegree t fuel d (d + 1).factorial + 1).factorial ∨
        factorialDegree t fuel d (d + 1).factorial = d + fuel) := by
  induction fuel generalizing d with
  | zero => simp [factorialDegree]
  | succ fuel ih =>
    rw [factorialDegree]
    split_ifs with h
    · exact ⟨by omega, Or.inl h⟩
    · rw [show (d + 1).factorial * (d + 2) = (d + 1 + 1).factorial by
        rw [Nat.factorial_succ (d + 1)]; ring]
      obtain ⟨h1, h2⟩ := ih (d + 1)
      exact ⟨by omega, h2.imp_right fun h ↦ by omega⟩

/-- The Taylor degree at working precision `w`: `factorialDegree (2 ^ w) w 0 1` tests
`2 ^ w ≤ (d + 1)!` for `d = 0, 1, …, w - 1` in turn and returns the first `d` that passes, or
`w` when none does. `trigDegree_le` and `two_pow_le_factorial_trigDegree` prove
`trigDegree w ≤ w` and `2 ^ w ≤ (trigDegree w + 1)!`. -/
def trigDegree (w : ℕ) : ℕ := factorialDegree (2 ^ w) w 0 1

/-- `trigDegree w ≤ w`. -/
theorem trigDegree_le (w : ℕ) : trigDegree w ≤ w := by
  have h := (factorialDegree_spec (2 ^ w) w 0).1
  simpa [trigDegree] using h

/-- `2 ^ w ≤ (trigDegree w + 1)!`. -/
theorem two_pow_le_factorial_trigDegree (w : ℕ) : 2 ^ w ≤ (trigDegree w + 1).factorial := by
  have h := (factorialDegree_spec (2 ^ w) w 0).2
  simp only [zero_add, Nat.factorial_one] at h
  rcases h with h | h
  · exact h
  · rw [trigDegree, h]
    simpa [add_comm] using Nat.factorial_mul_pow_le_factorial (m := 1) (n := w)

end CAS.Numerics

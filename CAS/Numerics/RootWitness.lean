/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Positivity

/-!
# Verified rational powers

`rootBounds N q s` encloses `N ^ (1/q)` for a rational `N ≥ 0` between two dyadic rationals of
denominator `2 ^ s`. `rpowBounds R e bits` encloses `R ^ e` for rational `R ≥ 0` and rational
`e` (`rpowBounds_mem`): through `(R ^ e.num) ^ (1 / e.den)` with about `bits` correct bits when
the denominator of `e` is at most `64`; through the product of two such roots, met with the next
route, when the denominator is the product of two coprime factors at most `64` (such as
`237/160 = 41/32 + 1/5`), so that it is never wider than the next route; and otherwise
through the split `e = e₀ + t` with `e₀` the nearest multiple of `1/12`, with
`1 - Λ |t| ≤ R ^ t ≤ 1 + Λ |t|` for `2 ^ (-Λ) ≤ R ≤ 2 ^ Λ` and `Λ |t| ≤ 1` (Bernoulli's
inequality). The last route serves exponents such as `1/6 ± 5 · 10⁻⁹`, for which a direct root
is out of reach; its relative width is about `2 Λ |t|`.

## Main definitions

* `rootBounds`: dyadic bounds of `N ^ (1/q)` with denominator `2 ^ s` from a checked Newton root.
* `log2Bound`: an exponent `Λ` with `2 ^ (-Λ) < R < 2 ^ Λ` for `R > 0`.
* `rpowNearBounds`: bounds of `R ^ e` through the nearest multiple of `1/12` and Bernoulli's
  inequality.
* `rpowBounds`: lower and upper bounds of `R ^ e` for rational `R ≥ 0` and rational `e`.

## Main results

* `rootBounds_mem`: `rootBounds N q s` encloses `N ^ (1/q)` for `N ≥ 0` and `q ≥ 1`.
* `rootBounds_fst_nonneg`: the lower bound of `rootBounds N q s` is nonnegative.
* `rpow_rat_eq_root`: `R ^ e = (R ^ e.num) ^ (1 / e.den)` for `R ≥ 0`.
* `log2Bound_mem`: `2 ^ (-Λ) ≤ R ≤ 2 ^ Λ` for `Λ = log2Bound R` and `R > 0`.
* `rpowNearBounds_mem`: `rpowNearBounds R e bits` encloses `R ^ e` for `R > 0`.
* `rpowBounds_mem`: `rpowBounds R e bits` encloses `R ^ e` for rational `R ≥ 0` and rational `e`.
* `rpowBounds_fst_nonneg`: the lower bound of `rpowBounds R e bits` is nonnegative.

## Implementation notes

We compute a candidate `m` for `⌊(N 2^{qs})^{1/q}⌋` by Newton's iteration on natural numbers and
then check `m ^ q ≤ M < (m + 1) ^ q` for `M = ⌊N 2^{qs}⌋`, so the soundness theorem
`rootBounds_mem` uses only the check, never the iteration. When the check fails (as it can when
the fixed number of Newton steps does not reach the root, for large `q`), the bounds fall back
to `0` and `max 1 N`; widths and precisions refer to successful checks. All functions use
rational and natural arithmetic only, so a check built from them reduces both in compiled code
and in the kernel.
-/

@[expose] public section

namespace CAS.Numerics

/-! ### Integer roots -/

/-- One Newton step `((k - 1) x + n / x ^ (k - 1)) / k` for the `k`-th root of `n`. -/
def natRootStep (n k x : ℕ) : ℕ :=
  ((k - 1) * x + n / x ^ (k - 1)) / k

/-- Newton's iteration from `x`, stopped when the iterate no longer decreases or the fuel ends. -/
def natRootIter (n k : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | fuel + 1, x =>
    let y := natRootStep n k x
    if y < x then natRootIter n k fuel y else x

/-- A candidate for `⌊n ^ (1/k)⌋`: Newton's iteration from `2 ^ (⌊log₂ n⌋ / k + 1)`, which is at
least the root. Nothing is proved about it; `rootBounds` checks it. -/
def natRootCandidate (n k : ℕ) : ℕ :=
  if n = 0 then 0 else natRootIter n k 400 (2 ^ (Nat.log2 n / k + 1))

/-! ### Roots of rationals -/

/-- The integer `⌊N 2^{qs}⌋` (as a natural number) of `rootBounds`. -/
def rootScaled (N : ℚ) (q s : ℕ) : ℕ :=
  (⌊N * 2 ^ (q * s)⌋).toNat

/-- The check `m ^ q ≤ M < (m + 1) ^ q` of the candidate root. -/
def rootCheck (M q m : ℕ) : Bool :=
  decide (m ^ q ≤ M) && decide (M < (m + 1) ^ q)

/-- Dyadic bounds of `N ^ (1/q)` with denominator `2 ^ s`: `(m / 2^s, (m + 1) / 2^s)` for the
checked candidate `m`, else `(0, max 1 N)`. -/
def rootBounds (N : ℚ) (q s : ℕ) : ℚ × ℚ :=
  let M := rootScaled N q s
  let m := natRootCandidate M q
  if rootCheck M q m then ((m : ℚ) / 2 ^ s, ((m : ℚ) + 1) / 2 ^ s) else (0, max 1 N)

/-- `⌊N 2^{qs}⌋ ≤ N 2^{qs}` for `N ≥ 0`. -/
theorem rootScaled_le {N : ℚ} (hN : 0 ≤ N) (q s : ℕ) :
    ((rootScaled N q s : ℕ) : ℝ) ≤ (N : ℝ) * 2 ^ (q * s) := by
  have h0 : (0 : ℤ) ≤ ⌊N * 2 ^ (q * s)⌋ := Int.floor_nonneg.2 (by positivity)
  have h : ((⌊N * 2 ^ (q * s)⌋.toNat : ℤ) : ℚ) ≤ N * 2 ^ (q * s) := by
    rw [Int.toNat_of_nonneg h0]
    exact Int.floor_le _
  unfold rootScaled
  exact_mod_cast h

/-- `N 2^{qs} < ⌊N 2^{qs}⌋ + 1` for `N ≥ 0`. -/
theorem lt_rootScaled_add_one {N : ℚ} (hN : 0 ≤ N) (q s : ℕ) :
    (N : ℝ) * 2 ^ (q * s) < ((rootScaled N q s : ℕ) : ℝ) + 1 := by
  have h0 : (0 : ℤ) ≤ ⌊N * 2 ^ (q * s)⌋ := Int.floor_nonneg.2 (by positivity)
  have h : N * 2 ^ (q * s) < ((⌊N * 2 ^ (q * s)⌋.toNat : ℤ) : ℚ) + 1 := by
    rw [Int.toNat_of_nonneg h0]
    exact Int.lt_floor_add_one _
  unfold rootScaled
  exact_mod_cast h

/-- **Verified roots**: `rootBounds N q s` encloses `N ^ (1/q)` for `N ≥ 0` and `q ≥ 1`. -/
theorem rootBounds_mem {N : ℚ} (hN : 0 ≤ N) {q : ℕ} (hq : q ≠ 0) (s : ℕ) :
    ((rootBounds N q s).1 : ℝ) ≤ (N : ℝ) ^ ((q : ℝ)⁻¹) ∧
      (N : ℝ) ^ ((q : ℝ)⁻¹) ≤ ((rootBounds N q s).2 : ℝ) := by
  have hNr : (0 : ℝ) ≤ N := by exact_mod_cast hN
  unfold rootBounds
  simp only
  split_ifs with hc
  · simp only [rootCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    set M := rootScaled N q s
    set m := natRootCandidate M q
    have h2 : (0 : ℝ) < 2 ^ s := by positivity
    have hpow : ((2 : ℝ) ^ s) ^ q = 2 ^ (q * s) := by rw [← pow_mul, mul_comm]
    have hlo : ((m : ℝ) / 2 ^ s) ^ q ≤ N := by
      rw [div_pow, hpow, div_le_iff₀ (by positivity)]
      have : ((m ^ q : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hc.1
      push_cast at this
      exact this.trans (rootScaled_le hN q s)
    have hhi : (N : ℝ) ≤ (((m : ℝ) + 1) / 2 ^ s) ^ q := by
      rw [div_pow, hpow, le_div_iff₀ (by positivity)]
      have h1 : ((M + 1 : ℕ) : ℝ) ≤ (((m + 1) ^ q : ℕ) : ℝ) := by exact_mod_cast hc.2
      push_cast at h1
      exact (lt_rootScaled_add_one hN q s).le.trans h1
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.2 (Nat.pos_of_ne_zero hq)
    refine ⟨?_, ?_⟩
    · push_cast
      exact (Real.le_rpow_inv_iff_of_pos (by positivity) hNr hq0).2 (by rwa [Real.rpow_natCast])
    · push_cast
      exact (Real.rpow_inv_le_iff_of_pos hNr (by positivity) hq0).2 (by rwa [Real.rpow_natCast])
  · refine ⟨by simpa using Real.rpow_nonneg hNr _, ?_⟩
    push_cast
    rcases le_total (N : ℝ) 1 with h1 | h1
    · exact (Real.rpow_le_one hNr h1 (by positivity)).trans (le_max_left _ _)
    · exact ((Real.rpow_le_rpow_of_exponent_le h1 (inv_le_one_of_one_le₀ (by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 hq))).trans_eq (Real.rpow_one _)).trans
          (le_max_right _ _)

/-- The lower bound of `rootBounds N q s` is nonnegative. -/
theorem rootBounds_fst_nonneg (N : ℚ) (q s : ℕ) : 0 ≤ (rootBounds N q s).1 := by
  unfold rootBounds
  simp only
  split_ifs <;> positivity

/-! ### Rational powers -/

/-- An exponent `Λ` with `2 ^ (-Λ) < R < 2 ^ Λ` for `R > 0`, from the binary lengths of the
numerator and the denominator. -/
def log2Bound (R : ℚ) : ℕ :=
  max (Nat.log2 R.num.natAbs + 1 - Nat.log2 R.den) (Nat.log2 R.den + 1 - Nat.log2 R.num.natAbs)

/-- Bounds of `R ^ e` for a rational `R > 0` through `R ^ e₀` for the nearest multiple `e₀` of
`1/12`, times the bounds `1 - Λ |t|` and `1 + Λ |t|` of `R ^ t`, `t = e - e₀`, with
`2 ^ (-Λ) ≤ R ≤ 2 ^ Λ` (`log2Bound`), or `0` and `max R R⁻¹` when `Λ |t| > 1`. -/
def rpowNearBounds (R e : ℚ) (bits : ℕ) : ℚ × ℚ :=
  let e₀ : ℚ := (⌊e * 12 + 1 / 2⌋ : ℚ) / 12
  let N := R ^ e₀.num
  let B := rootBounds N e₀.den (bits + Nat.log2 N.den / e₀.den)
  let u := (log2Bound R : ℚ) * |e - e₀|
  if u ≤ 1 then (B.1 * (1 - u), B.2 * (1 + u)) else (0, B.2 * max R R⁻¹)

/-- A splitting `e = e₁ + e₂` with denominators `d₁ d₂ = e.den`, `gcd d₁ d₂ = 1` and
`d₁, d₂ ≤ 64`, if the denominator of `e` factors so: `e₁ = a/d₁` with `a ≡ e.num d₂⁻¹ (mod d₁)`.
Nothing is proved about it; `rpowBounds` checks `e₁ + e₂ = e`. -/
def rpowSplit (e : ℚ) : Option (ℚ × ℚ) :=
  match (List.range' 2 63).find? fun d₁ ↦
      e.den % d₁ == 0 && e.den / d₁ ≤ 64 && Nat.gcd d₁ (e.den / d₁) == 1 with
  | none => none
  | some d₁ =>
    let d₂ := e.den / d₁
    let a : ℤ := (e.num * Nat.gcdA d₂ d₁) % (d₁ : ℤ)
    some ((a : ℚ) / d₁, ((e.num - a * d₂) / (d₁ : ℤ) : ℤ) / (d₂ : ℚ))

/-- Lower and upper bounds of `R ^ e` for a rational `R ≥ 0`: exactly `1` for `e = 0`; Mathlib's
`0 ^ e = 0` at `R = 0` otherwise; the root of `R ^ e.num` of order `e.den` when `e.den ≤ 64`;
the product of the roots for the two parts of a checked splitting `e = e₁ + e₂` (`rpowSplit`),
met with `rpowNearBounds`, when the denominator factors into coprime parts at most `64`;
otherwise `rpowNearBounds`. -/
def rpowBounds (R e : ℚ) (bits : ℕ) : ℚ × ℚ :=
  if e = 0 then (1, 1)
  else if R = 0 then (0, 0)
  else if e.den ≤ 64 then
    let N := R ^ e.num
    rootBounds N e.den (bits + Nat.log2 N.den / e.den)
  else
    match rpowSplit e with
    | some (e₁, e₂) =>
      if e₁ + e₂ = e then
        let N₁ := R ^ e₁.num
        let N₂ := R ^ e₂.num
        let B₁ := rootBounds N₁ e₁.den (bits + Nat.log2 N₁.den / e₁.den)
        let B₂ := rootBounds N₂ e₂.den (bits + Nat.log2 N₂.den / e₂.den)
        let C := rpowNearBounds R e bits
        (max (B₁.1 * B₂.1) C.1, min (B₁.2 * B₂.2) C.2)
      else rpowNearBounds R e bits
    | none => rpowNearBounds R e bits

/-- `R ^ e = (R ^ e.num) ^ (1 / e.den)` for `R ≥ 0`. -/
theorem rpow_rat_eq_root {R : ℝ} (hR : 0 ≤ R) (e : ℚ) :
    R ^ (e : ℝ) = (R ^ e.num) ^ (((e.den : ℕ) : ℝ)⁻¹) := by
  rw [← Real.rpow_intCast, ← Real.rpow_mul hR, Rat.cast_def, div_eq_mul_inv]

/-- The root route of `rpowBounds`. -/
theorem rootBounds_zpow_mem {R : ℚ} (hR : 0 < R) (e : ℚ) (s : ℕ) :
    ((rootBounds (R ^ e.num) e.den s).1 : ℝ) ≤ (R : ℝ) ^ (e : ℝ) ∧
      (R : ℝ) ^ (e : ℝ) ≤ ((rootBounds (R ^ e.num) e.den s).2 : ℝ) := by
  have h := rootBounds_mem (zpow_nonneg hR.le e.num) (q := e.den) e.den_nz s
  rw [rpow_rat_eq_root (by exact_mod_cast hR.le)]
  exact_mod_cast h

/-- `2 ^ (-Λ) ≤ R ≤ 2 ^ Λ` for `Λ = log2Bound R` and `R > 0`. -/
theorem log2Bound_mem {R : ℚ} (hR : 0 < R) :
    ((2 : ℝ) ^ log2Bound R)⁻¹ ≤ R ∧ (R : ℝ) ≤ 2 ^ log2Bound R := by
  have two_pow_div_le : ∀ a b : ℕ, (2 : ℝ) ^ a / 2 ^ b ≤ 2 ^ (a - b) := by
    intro a b
    rcases le_total b a with hab | hab
    · rw [div_le_iff₀ (by positivity), ← pow_add, Nat.sub_add_cancel hab]
    · rw [Nat.sub_eq_zero_of_le hab, pow_zero, div_le_one (by positivity)]
      exact pow_le_pow_right₀ (by norm_num) hab
  set n := R.num.natAbs
  set d := R.den
  have hnum : (0 : ℤ) < R.num := Rat.num_pos.2 hR
  have hn0 : n ≠ 0 := Int.natAbs_ne_zero.2 hnum.ne'
  have hd0 : d ≠ 0 := R.den_nz
  have hRnd : (R : ℝ) = (n : ℝ) / d := by
    rw [Rat.cast_def, Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hnum)]
  have hnlt : (n : ℝ) < 2 ^ (Nat.log2 n + 1) := by exact_mod_cast Nat.lt_log2_self
  have hdlt : (d : ℝ) < 2 ^ (Nat.log2 d + 1) := by exact_mod_cast Nat.lt_log2_self
  have hnge : (2 : ℝ) ^ Nat.log2 n ≤ n := by exact_mod_cast Nat.log2_self_le hn0
  have hdge : (2 : ℝ) ^ Nat.log2 d ≤ d := by exact_mod_cast Nat.log2_self_le hd0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have hΛ₁ : Nat.log2 n + 1 - Nat.log2 d ≤ log2Bound R := le_max_left _ _
  have hΛ₂ : Nat.log2 d + 1 - Nat.log2 n ≤ log2Bound R := le_max_right _ _
  constructor
  · rw [hRnd, inv_le_comm₀ (by positivity) (by positivity), inv_div]
    calc (d : ℝ) / n ≤ 2 ^ (Nat.log2 d + 1) / 2 ^ Nat.log2 n :=
          div_le_div₀ (by positivity) hdlt.le (by positivity) hnge
      _ ≤ 2 ^ (Nat.log2 d + 1 - Nat.log2 n) := two_pow_div_le _ _
      _ ≤ 2 ^ log2Bound R := pow_le_pow_right₀ (by norm_num) hΛ₂
  · rw [hRnd]
    calc (n : ℝ) / d ≤ 2 ^ (Nat.log2 n + 1) / 2 ^ Nat.log2 d :=
          div_le_div₀ (by positivity) hnlt.le (by positivity) hdge
      _ ≤ 2 ^ (Nat.log2 n + 1 - Nat.log2 d) := two_pow_div_le _ _
      _ ≤ 2 ^ log2Bound R := pow_le_pow_right₀ (by norm_num) hΛ₁

/-- `rpowNearBounds R e bits` encloses `R ^ e` for `R > 0`. -/
theorem rpowNearBounds_mem {R : ℚ} (hpos : 0 < R) (e : ℚ) (bits : ℕ) :
    ((rpowNearBounds R e bits).1 : ℝ) ≤ (R : ℝ) ^ (e : ℝ) ∧
      (R : ℝ) ^ (e : ℝ) ≤ ((rpowNearBounds R e bits).2 : ℝ) := by
  have hRr : (0 : ℝ) < R := by exact_mod_cast hpos
  unfold rpowNearBounds
  simp only
  set e₀ : ℚ := (⌊e * 12 + 1 / 2⌋ : ℚ) / 12 with he₀
  set t := e - e₀ with ht
  have hB := rootBounds_zpow_mem hpos e₀ (bits + Nat.log2 (R ^ e₀.num).den / e₀.den)
  set B := rootBounds (R ^ e₀.num) e₀.den (bits + Nat.log2 (R ^ e₀.num).den / e₀.den)
  have hB0 : 0 ≤ B.1 := rootBounds_fst_nonneg _ _ _
  have ht1 : |t| ≤ 1 := by
    have h1 : (⌊e * 12 + 1 / 2⌋ : ℚ) ≤ e * 12 + 1 / 2 := Int.floor_le _
    have h2 : e * 12 + 1 / 2 < (⌊e * 12 + 1 / 2⌋ : ℚ) + 1 := Int.lt_floor_add_one _
    rw [abs_le, ht, he₀]; constructor <;> linarith
  have ht1r : |(t : ℝ)| ≤ 1 := by exact_mod_cast ht1
  have hsplit : (R : ℝ) ^ (e : ℝ) = (R : ℝ) ^ (e₀ : ℝ) * (R : ℝ) ^ (t : ℝ) := by
    rw [← Real.rpow_add hRr]; congr 1; rw [ht]; push_cast; ring
  have hRe : 0 ≤ (R : ℝ) ^ (e₀ : ℝ) := Real.rpow_nonneg hRr.le _
  have hRt : 0 ≤ (R : ℝ) ^ (t : ℝ) := Real.rpow_nonneg hRr.le _
  have hΛ := log2Bound_mem hpos
  set Λ := log2Bound R
  have hτ0 : 0 ≤ |(t : ℝ)| := abs_nonneg _
  rw [hsplit]
  split_ifs with hu
  · -- `R ^ t = S ^ |t|` with `S = R` or `S = R⁻¹`, both within `[2 ^ (-Λ), 2 ^ Λ]`
    obtain ⟨S, hS0, hSlo, hShi, hSt⟩ : ∃ S : ℝ, 0 < S ∧ ((2 : ℝ) ^ Λ)⁻¹ ≤ S ∧ S ≤ 2 ^ Λ ∧
        (R : ℝ) ^ (t : ℝ) = S ^ |(t : ℝ)| := by
      rcases le_or_gt 0 (t : ℝ) with htp | htn
      · exact ⟨R, hRr, hΛ.1, hΛ.2, by rw [abs_of_nonneg htp]⟩
      · refine ⟨(R : ℝ)⁻¹, inv_pos.2 hRr, ?_, ?_, ?_⟩
        · exact inv_anti₀ hRr hΛ.2
        · rw [inv_le_comm₀ hRr (by positivity)]; exact hΛ.1
        · rw [abs_of_neg htn, Real.inv_rpow hRr.le, ← Real.rpow_neg hRr.le, neg_neg]
    rw [hSt]
    have hu' : (Λ : ℝ) * |(t : ℝ)| ≤ 1 := by exact_mod_cast (hu : ((Λ : ℚ) * |t| : ℚ) ≤ 1)
    have hpow : ((2 : ℝ) ^ Λ) ^ |(t : ℝ)| = (2 : ℝ) ^ ((Λ : ℝ) * |(t : ℝ)|) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have hbern : (2 : ℝ) ^ ((Λ : ℝ) * |(t : ℝ)|) ≤ 1 + (Λ : ℝ) * |(t : ℝ)| := by
      have h := rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num)
        (p := (Λ : ℝ) * |(t : ℝ)|) (by positivity) hu'
      norm_num at h ⊢
      linarith
    have hlo : 1 - (Λ : ℝ) * |(t : ℝ)| ≤ S ^ |(t : ℝ)| := by
      rcases le_total (1 : ℝ) S with h1 | h1
      · have := Real.one_le_rpow h1 hτ0
        have : (0 : ℝ) ≤ (Λ : ℝ) * |(t : ℝ)| := by positivity
        linarith
      · have hmono := Real.rpow_le_rpow (by positivity) hSlo hτ0
        rw [Real.inv_rpow (by positivity), hpow] at hmono
        have hx0 : (0 : ℝ) ≤ (Λ : ℝ) * |(t : ℝ)| := by positivity
        have h1x : 1 - (Λ : ℝ) * |(t : ℝ)| ≤ (1 + (Λ : ℝ) * |(t : ℝ)|)⁻¹ := by
          rw [← one_div, le_div_iff₀ (by positivity)]
          nlinarith
        exact h1x.trans ((inv_anti₀ (by positivity) hbern).trans hmono)
    have hhi : S ^ |(t : ℝ)| ≤ 1 + (Λ : ℝ) * |(t : ℝ)| := by
      rcases le_total (1 : ℝ) S with h1 | h1
      · have hmono := Real.rpow_le_rpow hS0.le hShi hτ0
        rw [hpow] at hmono
        linarith
      · have := Real.rpow_le_one hS0.le h1 hτ0
        have : (0 : ℝ) ≤ (Λ : ℝ) * |(t : ℝ)| := by positivity
        linarith
    simp only [Rat.cast_mul, Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_natCast,
      Rat.cast_abs]
    have hu0 : (0 : ℝ) ≤ 1 - (Λ : ℝ) * |(t : ℝ)| := by linarith
    exact ⟨mul_le_mul hB.1 hlo hu0 hRe,
      mul_le_mul hB.2 hhi (Real.rpow_nonneg hS0.le _) (hRe.trans hB.2)⟩
  · -- the fallback `R ^ t ≤ max R R⁻¹` for `|t| ≤ 1`
    have ht1' := abs_le.1 ht1r
    have hmax : (R : ℝ) ^ (t : ℝ) ≤ max (R : ℝ) (R : ℝ)⁻¹ := by
      rcases le_total (1 : ℝ) R with h1 | h1
      · rcases le_total 0 (t : ℝ) with htp | htn
        · exact ((Real.rpow_le_rpow_of_exponent_le h1 ht1'.2).trans_eq (Real.rpow_one _)).trans
            (le_max_left _ _)
        · exact (Real.rpow_le_one_of_one_le_of_nonpos h1 htn).trans (h1.trans (le_max_left _ _))
      · have hRi : 1 ≤ (R : ℝ)⁻¹ := (one_le_inv₀ hRr).2 h1
        rcases le_total 0 (t : ℝ) with htp | htn
        · exact (Real.rpow_le_one hRr.le h1 htp).trans (hRi.trans (le_max_right _ _))
        · rw [← neg_neg (t : ℝ), Real.rpow_neg hRr.le, ← Real.inv_rpow hRr.le]
          exact ((Real.rpow_le_rpow_of_exponent_le hRi (by linarith)).trans_eq
            (Real.rpow_one _)).trans (le_max_right _ _)
    simp only [Rat.cast_mul, Rat.cast_max, Rat.cast_inv, Rat.cast_zero]
    exact ⟨mul_nonneg hRe hRt, mul_le_mul hB.2 hmax hRt (hRe.trans hB.2)⟩

/-- **Verified rational powers**: `rpowBounds R e bits` encloses `R ^ e` for rational `R ≥ 0` and
rational `e`. -/
theorem rpowBounds_mem {R : ℚ} (hR : 0 ≤ R) (e : ℚ) (bits : ℕ) :
    ((rpowBounds R e bits).1 : ℝ) ≤ (R : ℝ) ^ (e : ℝ) ∧
      (R : ℝ) ^ (e : ℝ) ≤ ((rpowBounds R e bits).2 : ℝ) := by
  unfold rpowBounds
  by_cases he : e = 0
  · simp [he]
  simp only [he, ↓reduceIte]
  by_cases h0 : R = 0
  · subst h0
    have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he
    simp [Real.zero_rpow he']
  have hpos : 0 < R := lt_of_le_of_ne hR (Ne.symm h0)
  have hRr : (0 : ℝ) < R := by exact_mod_cast hpos
  simp only [h0, ↓reduceIte]
  by_cases hden : e.den ≤ 64
  · simp only [hden, ↓reduceIte]
    exact rootBounds_zpow_mem hpos e _
  · simp only [hden, ↓reduceIte]
    split
    · rename_i e₁ e₂ _
      split_ifs with hsum
      · set s₁ := bits + Nat.log2 (R ^ e₁.num).den / e₁.den
        set s₂ := bits + Nat.log2 (R ^ e₂.num).den / e₂.den
        have h₁ := rootBounds_zpow_mem hpos e₁ s₁
        have h₂ := rootBounds_zpow_mem hpos e₂ s₂
        have h0₁ : (0 : ℝ) ≤ (rootBounds (R ^ e₁.num) e₁.den s₁).1 := by
          exact_mod_cast rootBounds_fst_nonneg _ _ _
        have h0₂ : (0 : ℝ) ≤ (rootBounds (R ^ e₂.num) e₂.den s₂).1 := by
          exact_mod_cast rootBounds_fst_nonneg _ _ _
        have hpow : (R : ℝ) ^ (e : ℝ) = (R : ℝ) ^ (e₁ : ℝ) * (R : ℝ) ^ (e₂ : ℝ) := by
          rw [← Real.rpow_add hRr, ← hsum]; push_cast; ring_nf
        have hC := rpowNearBounds_mem hpos e bits
        rw [hpow] at hC ⊢
        push_cast
        exact ⟨max_le (mul_le_mul h₁.1 h₂.1 h0₂ (Real.rpow_nonneg hRr.le _)) hC.1,
          le_min (mul_le_mul h₁.2 h₂.2 (Real.rpow_nonneg hRr.le _) ((h0₁.trans h₁.1).trans h₁.2))
            hC.2⟩
      · exact rpowNearBounds_mem hpos e bits
    · exact rpowNearBounds_mem hpos e bits

/-- The lower bound of `rpowBounds R e bits` is nonnegative. -/
theorem rpowBounds_fst_nonneg (R e : ℚ) (bits : ℕ) : 0 ≤ (rpowBounds R e bits).1 := by
  have hnear : 0 ≤ (rpowNearBounds R e bits).1 := by
    unfold rpowNearBounds
    simp only
    split_ifs with hu
    · exact mul_nonneg (rootBounds_fst_nonneg _ _ _) (by linarith)
    · exact le_rfl
  rw [rpowBounds]
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact rootBounds_fst_nonneg _ _ _
  · split
    · split_ifs
      · exact le_max_of_le_left
          (mul_nonneg (rootBounds_fst_nonneg _ _ _) (rootBounds_fst_nonneg _ _ _))
      · exact hnear
    · exact hnear

end CAS.Numerics

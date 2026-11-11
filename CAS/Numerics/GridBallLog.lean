/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.GridBallSeries
public import CAS.Numerics.GridBallJoin
public import CAS.Continuum.Interval.Rational.LogPrimitive
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Balls for FloatLib's exact rational logarithm

FloatLib's `Enclosure.log x n` is an exact rational interval: `x` (inverted first when `x < 1`,
the interval then negated) is reduced to `x' ∈ [1, 2)` by a power of two, the series
`log x' = log (1 + t) - log (1 - t)` with `t = (x' - 1) / (x' + 1)` is truncated after `n` terms
with the remainder `|t| ^ (n + 1) / (1 - |t|)`, and the removed multiple of `log 2` is added
back. Its endpoints are rationals of thousands of bits, which balls on the grid `2 ^ -P` enclose
with natural-number operations only.

The two truncated series combine into twice the odd part,
`logOneSubTaylor t n - logOneSubTaylor (-t) n = 2 ∑ k < (n + 1) / 2, t ^ (2k + 1) / (2k + 1)`
(`logOneSubTaylor_sub_neg`), which `nonnegLoop` evaluates in `(n + 1) / 2` steps with one error
bound for the whole sum (`oddLogLoop_spec`).

* `logSeriesFrac P n a b` encloses the endpoints of `Enclosure.logSeries x n` when
  `(x - 1) / (x + 1) = a / b` (`logSeriesFrac_encloses`).
* `logLargeFrac P n u v` and `logFrac P n u v` enclose `Enclosure.logLarge` and
  `Enclosure.log` at the exact rational `u / v`, computing the scale and the series argument from
  `u` and `v` with natural operations (`logFrac_encloses`).
* `logBall P n B` encloses `Enclosure.log q n` for every `q` enclosed by the ball `B`: the odd
  series is evaluated at the center of the ball of the series argument and widened by twice its
  radius, its Lipschitz constant (`abs_oddLogSum_sub_le`). On `(1/2, 2)` FloatLib's two branches
  give the same series (`log_eq_logSeries`), so a ball there, on either side of one, takes the
  series of either sign directly (`logSeriesSignedBall`); elsewhere the ball must decide whether
  `q < 1`, and where it straddles a power of two the enclosures with the two neighbouring binary
  scales are joined (`logLargeBall`).
* `logPointFrac`, `logAbsPointFrac` and `logRangeFrac` mirror the interval logarithms
  `RationalInterval.logPointIntervalWith`, `logAbsPointIntervalWith` and `logRangeWith` (and so
  `logPointInterval` and `logRange`, at `logSeriesTerms`) at exact rational points, and
  `logPointBall` and `logRangeBall` mirror `logPointIntervalWith` and `logRangeWith` at balls.

## Implementation notes

We do not reimplement the logarithm: the intervals are FloatLib's, and the balls only enclose
their exact endpoints. The odd series is summed by `nonnegLoop`, which truncates the term and the
sum at every step; `oddLogLoop_spec` bounds the accumulated error a priori by `3 m` units for
`m` steps, and that bound is the radius.

At `P = 160` the logarithm of a rational point with series degree 96 (48 loop steps) costs about
0.8 ms in the kernel, the logarithm of a ball 1.5 ms; for arguments in `[2 ^ -10, 2 ^ 10]` the
endpoint balls have radius below `2 ^ 12` units. A panel of `translatedLogPanelInterval` with
four coefficients, two endpoint logarithms of degree 96 and the outward rounding to `2 ^ -100`
costs about 4.5 ms, and its rounded endpoints come out with radius zero, equal to the exact ones.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>. The enclosed
  intervals are those of `FloatLib.Numerics.Enclosure.log`, with its inversion below one, its
  reduction by a power of two and its series in `t = (x - 1) / (x + 1)`.
* Joris van der Hoeven, "Ball arithmetic", *Logical approaches to Barriers in Computing and
  Complexity*, Preprint-Reihe Mathematik 6, Ernst-Moritz-Arndt-Universität Greifswald, 2010,
  pp. 179-208, <https://www.texmacs.org/joris/ball/ball-abs.html>. Section 3.6, (15), for the
  enclosure `B(f(c), M r)` with `M` a bound of `|f'|` over the ball, used for the odd series.
* NIST Digital Library of Mathematical Functions, §4.6 Power Series, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/4.6>. Equation (4.6.4), the series of `ln z` in `(z - 1) / (z + 1)`;
  `oddLogSum` is half of its partial sum.
-/

@[expose] public section

namespace CAS.Numerics

open FloatLib.Numerics CAS.Continuum

/-! ### The odd part of the logarithm series -/

/-- The odd series `∑ k < m, t ^ (2k + 1) / (2k + 1)`. -/
def oddLogSum (t : ℚ) (m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range m, t ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℚ)

/-- The two truncated series of `log (1 - x)` at `t` and `-t` differ by twice the odd part. -/
theorem logOneSubTaylor_sub_neg (t : ℚ) (n : ℕ) :
    Enclosure.logOneSubTaylor t n - Enclosure.logOneSubTaylor (-t) n =
      2 * oddLogSum t ((n + 1) / 2) := by
  induction n with
  | zero => simp [Enclosure.logOneSubTaylor, oddLogSum]
  | succ n ih =>
    unfold Enclosure.logOneSubTaylor at ih ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
    · have h1 : (n + 1 + 1) / 2 = (n + 1) / 2 + 1 := by omega
      have h2 : 2 * ((n + 1) / 2) + 1 = n + 1 := by omega
      rw [h1, oddLogSum, Finset.sum_range_succ, ← oddLogSum, h2,
        Odd.neg_pow ⟨j, by omega⟩]
      linear_combination ih
    · have h1 : (n + 1 + 1) / 2 = (n + 1) / 2 := by omega
      rw [h1, Even.neg_pow ⟨j + 1, by omega⟩]
      linear_combination ih

/-- The logarithm remainder is even in its argument. -/
theorem logOneSubRadius_neg (t : ℚ) (n : ℕ) :
    Enclosure.logOneSubRadius (-t) n = Enclosure.logOneSubRadius t n := by
  simp [Enclosure.logOneSubRadius]

/-- The lower endpoint of `logSeries x n` through the odd series. -/
theorem logSeries_lo (x : ℚ) (n : ℕ) :
    (Enclosure.logSeries x n).lo =
      2 * oddLogSum ((x - 1) / (x + 1)) ((n + 1) / 2) -
        2 * Enclosure.logOneSubRadius ((x - 1) / (x + 1)) n := by
  simp only [Enclosure.logSeries, Enclosure.logOneSub, FloatLib.Numerics.RationalInterval.around,
    FloatLib.Numerics.RationalInterval.sub, FloatLib.Numerics.RationalInterval.add,
    FloatLib.Numerics.RationalInterval.neg, logOneSubRadius_neg]
  linear_combination logOneSubTaylor_sub_neg ((x - 1) / (x + 1)) n

/-- The upper endpoint of `logSeries x n` through the odd series. -/
theorem logSeries_hi (x : ℚ) (n : ℕ) :
    (Enclosure.logSeries x n).hi =
      2 * oddLogSum ((x - 1) / (x + 1)) ((n + 1) / 2) +
        2 * Enclosure.logOneSubRadius ((x - 1) / (x + 1)) n := by
  simp only [Enclosure.logSeries, Enclosure.logOneSub, FloatLib.Numerics.RationalInterval.around,
    FloatLib.Numerics.RationalInterval.sub, FloatLib.Numerics.RationalInterval.add,
    FloatLib.Numerics.RationalInterval.neg, logOneSubRadius_neg]
  linear_combination logOneSubTaylor_sub_neg ((x - 1) / (x + 1)) n

/-- `m` steps of the odd series at `t = a / b`: the term `t ^ (2k + 1) 2 ^ P` is multiplied by
`a ^ 2 / b ^ 2` and divided by `2k + 1`. -/
def oddLogLoop (P a b m : ℕ) : NonnegState :=
  nonnegLoop (Nat.mul a a) (fun _ ↦ Nat.mul b b) (fun k ↦ Nat.add (Nat.add k k) 1)
    (Nat.div (Nat.shiftLeft a P) b) m

/-- The fraction `a / b` is defined and its square is at most `1 / 2`. -/
def oddLogOk (a b : ℕ) : Bool :=
  Nat.blt 0 b && Nat.ble (Nat.mul 2 (Nat.mul a a)) (Nat.mul b b)

/-- For `oddLogOk a b` (`0 < b` and `2 * a ^ 2 ≤ b ^ 2`), the sum of `oddLogLoop P a b m` lies
within `3 m` units of `oddLogSum (a / b) m * 2 ^ P`, and its term within `2` units of
`(a / b) ^ (2 m + 1) * 2 ^ P`. -/
theorem oddLogLoop_spec {P a b : ℕ} (h : oddLogOk a b = true) (m : ℕ) :
    |oddLogSum ((a : ℚ) / b) m * 2 ^ P - (oddLogLoop P a b m).s| ≤ 3 * m ∧
      |((a : ℚ) / b) ^ (2 * m + 1) * 2 ^ P - (oddLogLoop P a b m).z| ≤ 2 := by
  simp only [oddLogOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.mul_eq] at h
  obtain ⟨hb, hab⟩ := h
  have hr : ((a : ℚ) / b) ^ 2 ≤ 1 / 2 := by
    rw [div_pow, div_le_div_iff₀ (by positivity) two_pos, sq, sq]
    exact_mod_cast (by omega : a * a * 2 ≤ 1 * (b * b))
  have key := nonnegLoop_spec (c := a * a) (d := fun _ ↦ b * b) (w := fun k ↦ k + k + 1)
    (z₀ := a * 2 ^ P / b) (X := fun k ↦ ((a : ℚ) / b) ^ (2 * k + 1) * 2 ^ P)
    (B := fun _ ↦ 2)
    (fun k ↦ by push_cast; ring)
    (fun _ ↦ by
      rw [Nat.cast_mul, Nat.cast_mul, ← div_mul_div_comm, ← sq, abs_sq]
      linarith)
    (by
      obtain ⟨h1, h2⟩ := GridBall.natDiv_bounds (a * 2 ^ P) b hb
      push_cast [← div_mul_eq_mul_div] at h1 h2
      rw [pow_one, abs_le]
      constructor <;> linarith) m
  have hloop : oddLogLoop P a b m = nonnegLoop (a * a) (fun _ ↦ b * b) (fun k ↦ k + k + 1)
      (a * 2 ^ P / b) m := by
    simp only [oddLogLoop, Nat.mul_eq, Nat.add_eq, GridBall.natDiv_eq_div,
      Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  rw [hloop]
  refine ⟨?_, key.1⟩
  have hsum : (∑ k ∈ Finset.range m, ((a : ℚ) / b) ^ (2 * k + 1) * 2 ^ P / ((k + k + 1 : ℕ) : ℚ)) =
      oddLogSum ((a : ℚ) / b) m * 2 ^ P := by
    simp only [oddLogSum, Finset.sum_mul, two_mul]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have h3 : ∀ k ∈ Finset.range m, (2 : ℚ) / ((k + k + 1 : ℕ) : ℚ) + 1 ≤ 3 := fun k _ ↦ by
    have : (1 : ℚ) ≤ (k + k + 1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 (k + k)
    linarith [div_le_self (zero_le_two (α := ℚ)) this]
  have h := key.2
  rw [hsum] at h
  have := Finset.sum_le_card_nsmul _ _ _ h3
  simp only [Finset.card_range, nsmul_eq_mul] at this
  linarith

/-- Two steps of the odd series loop per iteration, with the multiplier `c / d`: `j` iterations
compute the terms of index below `2 j`. -/
def oddLogLoop2 (c d z₀ j : ℕ) : NonnegState :=
  Nat.rec (motive := fun _ ↦ NonnegState) ⟨z₀, 0⟩
    (fun i st ↦ ⟨Nat.div (Nat.mul (Nat.div (Nat.mul st.z c) d) c) d,
      Nat.add (Nat.add st.s (Nat.div st.z (Nat.add (Nat.add (Nat.add i i) (Nat.add i i)) 1)))
        (Nat.div (Nat.div (Nat.mul st.z c) d)
          (Nat.add (Nat.add (Nat.add (Nat.add i i) 1) (Nat.add (Nat.add i i) 1)) 1))⟩) j

/-- The recursion equation of `oddLogLoop2` at `j + 1`: two steps of the odd series loop from the
state after `j` iterations. -/
theorem oddLogLoop2_succ (c d z₀ j : ℕ) :
    oddLogLoop2 c d z₀ (j + 1) =
      ⟨Nat.div (Nat.mul (Nat.div (Nat.mul (oddLogLoop2 c d z₀ j).z c) d) c) d,
      Nat.add (Nat.add (oddLogLoop2 c d z₀ j).s (Nat.div (oddLogLoop2 c d z₀ j).z
          (Nat.add (Nat.add (Nat.add j j) (Nat.add j j)) 1)))
        (Nat.div (Nat.div (Nat.mul (oddLogLoop2 c d z₀ j).z c) d)
          (Nat.add (Nat.add (Nat.add (Nat.add j j) 1) (Nat.add (Nat.add j j) 1)) 1))⟩ := rfl

/-- The loop with two steps per iteration computes the loop with one step at even counts. -/
theorem oddLogLoop2_eq (c d z₀ j : ℕ) :
    oddLogLoop2 c d z₀ j =
      nonnegLoop c (fun _ ↦ d) (fun k ↦ Nat.add (Nat.add k k) 1) z₀ (2 * j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, nonnegLoop_succ, nonnegLoop_succ,
      oddLogLoop2_succ, ← ih]
    simp only [Nat.add_eq, two_mul]

/-- `oddLogLoop` with two steps per iteration, about a third faster in the kernel. -/
def oddLogLoopFast (P a b m : ℕ) : NonnegState :=
  Bool.rec
    ⟨Nat.div (Nat.mul (oddLogLoop2 (Nat.mul a a) (Nat.mul b b) (Nat.div (Nat.shiftLeft a P) b)
        (Nat.div m 2)).z (Nat.mul a a)) (Nat.mul b b),
      Nat.add (oddLogLoop2 (Nat.mul a a) (Nat.mul b b) (Nat.div (Nat.shiftLeft a P) b)
          (Nat.div m 2)).s
        (Nat.div (oddLogLoop2 (Nat.mul a a) (Nat.mul b b) (Nat.div (Nat.shiftLeft a P) b)
          (Nat.div m 2)).z (Nat.add (Nat.add (Nat.sub m 1) (Nat.sub m 1)) 1))⟩
    (oddLogLoop2 (Nat.mul a a) (Nat.mul b b) (Nat.div (Nat.shiftLeft a P) b) (Nat.div m 2))
    (Nat.beq (Nat.mod m 2) 0)

/-- `oddLogLoopFast P a b m` equals `oddLogLoop P a b m`, for all arguments. -/
theorem oddLogLoopFast_eq (P a b m : ℕ) : oddLogLoopFast P a b m = oddLogLoop P a b m := by
  unfold oddLogLoopFast oddLogLoop
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have hb : Nat.beq (Nat.mod m 2) 0 = true := by rw [GridBall.natMod_eq_mod, h]; rfl
    rw [hb]
    change oddLogLoop2 _ _ _ (Nat.div m 2) = _
    rw [oddLogLoop2_eq, GridBall.natDiv_eq_div m 2, show 2 * (m / 2) = m by omega]
  · have hb : Nat.beq (Nat.mod m 2) 0 = false := by rw [GridBall.natMod_eq_mod, h]; rfl
    rw [hb]
    change (⟨_, _⟩ : NonnegState) = _
    rw [oddLogLoop2_eq, GridBall.natDiv_eq_div m 2]
    conv_rhs => rw [show m = 2 * (m / 2) + 1 by omega, nonnegLoop_succ]
    have hm : Nat.sub m 1 = 2 * (m / 2) := by simp only [Nat.sub_eq]; omega
    rw [hm]

/-- The ball of `oddLogSum (a / b) m`. -/
def oddLogSumBall (P a b m : ℕ) : GridBall :=
  ⟨(oddLogLoopFast P a b m).s, 0, Nat.mul 3 m, oddLogOk a b⟩

/-- The ball of `(a / b) ^ (2m + 1)`. -/
def oddLogPowBall (P a b m : ℕ) : GridBall :=
  ⟨(oddLogLoopFast P a b m).z, 0, 2, oddLogOk a b⟩

/-- `oddLogSumBall P a b m` encloses `oddLogSum (a / b) m` at precision `P`, for all arguments; the
ball is valid only when `oddLogOk a b`. -/
theorem oddLogSumBall_encloses (P a b m : ℕ) :
    (oddLogSumBall P a b m).Encloses P (oddLogSum ((a : ℚ) / b) m) := fun h ↦ by
  simpa [oddLogSumBall, oddLogLoopFast_eq, GridBall.cast_center] using
    (oddLogLoop_spec (P := P) h m).1

/-- `oddLogPowBall P a b m` encloses `(a / b) ^ (2 m + 1)` at precision `P`, for all arguments; the
ball is valid only when `oddLogOk a b`. -/
theorem oddLogPowBall_encloses (P a b m : ℕ) :
    (oddLogPowBall P a b m).Encloses P (((a : ℚ) / b) ^ (2 * m + 1)) := fun h ↦ by
  simpa [oddLogPowBall, oddLogLoopFast_eq, GridBall.cast_center] using
    (oddLogLoop_spec (P := P) h m).2

/-- `oddLogOk a b` gives `0 < b` and `a < b`. -/
theorem lt_of_oddLogOk {a b : ℕ} (h : oddLogOk a b = true) : 0 < b ∧ a < b := by
  simp only [oddLogOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.mul_eq] at h
  have := Nat.mul_pos h.1 h.1
  exact ⟨h.1, Nat.mul_self_lt_mul_self_iff.mp (by omega)⟩

/-- The ball of the remainder `logOneSubRadius (a / b) n`: from the last term of the odd loop
when `n` is even, by ball arithmetic otherwise. -/
def logRadiusFrac (P n a b : ℕ) : GridBall :=
  Bool.rec
    (GridBall.divPos P (GridBall.powNonneg P (GridBall.ofFrac P false a b) (Nat.add n 1))
      (GridBall.sub (GridBall.ofNat P 1) (GridBall.ofFrac P false a b)))
    (GridBall.mulFrac b (Nat.sub b a) (oddLogPowBall P a b (Nat.div (Nat.add n 1) 2)))
    (Nat.beq (Nat.mod n 2) 0)

/-- `logRadiusFrac P n a b` encloses `Enclosure.logOneSubRadius (a / b) n` at precision `P`, for all
arguments. -/
theorem logRadiusFrac_encloses (P n a b : ℕ) :
    (logRadiusFrac P n a b).Encloses P (Enclosure.logOneSubRadius ((a : ℚ) / b) n) := by
  have ht : (0 : ℚ) ≤ (a : ℚ) / b := by positivity
  rw [Enclosure.logOneSubRadius, abs_of_nonneg ht]
  unfold logRadiusFrac
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · rw [show Nat.beq (Nat.mod n 2) 0 = true by rw [GridBall.natMod_eq_mod, hn]; rfl]
    intro hok
    obtain ⟨hb0, hab⟩ := lt_of_oddLogOk (a := a) (b := b) hok
    have h := GridBall.mulFrac_encloses (a := b) (b := Nat.sub b a)
      (oddLogPowBall_encloses P a b (Nat.div (Nat.add n 1) 2)) hok
    rw [show 2 * Nat.div (Nat.add n 1) 2 + 1 = n + 1 by
      simp only [Nat.add_eq, GridBall.natDiv_eq_div]; omega, Nat.sub_eq, Nat.cast_sub hab.le] at h
    rwa [one_sub_div (Nat.cast_ne_zero.mpr hb0.ne'), div_div_eq_mul_div, mul_div_assoc]
  · rw [show Nat.beq (Nat.mod n 2) 0 = false by rw [GridBall.natMod_eq_mod, hn]; rfl]
    exact GridBall.divPos_encloses
      (GridBall.powNonneg_encloses (GridBall.ofFrac_encloses P a b).1 ht _)
      (GridBall.sub_encloses (by simpa using GridBall.ofNat_encloses P 1)
        (GridBall.ofFrac_encloses P a b).1)

/-- Balls of the endpoints of `Enclosure.logSeries x n` when `(x - 1) / (x + 1) = a / b`. -/
def logSeriesFrac (P n a b : ℕ) : IntervalBalls :=
  ⟨GridBall.sub (GridBall.scaleNat 2 (oddLogSumBall P a b (Nat.div (Nat.add n 1) 2)))
      (GridBall.scaleNat 2 (logRadiusFrac P n a b)),
    GridBall.add (GridBall.scaleNat 2 (oddLogSumBall P a b (Nat.div (Nat.add n 1) 2)))
      (GridBall.scaleNat 2 (logRadiusFrac P n a b))⟩

/-- If `(x - 1) / (x + 1) = a / b`, then `logSeriesFrac P n a b` encloses the endpoints of
`Enclosure.logSeries x n` at precision `P`. -/
theorem logSeriesFrac_encloses {P : ℕ} {x : ℚ} (n : ℕ) {a b : ℕ}
    (ht : (x - 1) / (x + 1) = (a : ℚ) / b) :
    (logSeriesFrac P n a b).EnclosesEnds P (Enclosure.logSeries x n).lo
      (Enclosure.logSeries x n).hi := by
  have hO := GridBall.scaleNat_encloses (c := 2) (oddLogSumBall_encloses P a b ((n + 1) / 2))
  have hR := GridBall.scaleNat_encloses (c := 2) (logRadiusFrac_encloses P n a b)
  push_cast at hO hR
  rw [logSeries_lo, logSeries_hi, ht, mul_comm 2, mul_comm 2]
  exact ⟨GridBall.sub_encloses hO hR, GridBall.add_encloses hO hR⟩

/-- Balls of `Enclosure.logLarge (u / v) n` with the scale `s` given: series argument
`(u - v 2 ^ s) / (u + v 2 ^ s)`, valid when `0 < v` and `v 2 ^ s ≤ u`. -/
def logLargeCore (P n u v s : ℕ) : IntervalBalls :=
  IntervalBalls.guard (Nat.blt 0 v && Nat.ble (Nat.shiftLeft v s) u)
    ⟨GridBall.add
        (logSeriesFrac P n (Nat.sub u (Nat.shiftLeft v s)) (Nat.add u (Nat.shiftLeft v s))).lo
        (GridBall.scaleNat s (logSeriesFrac P n 1 3).lo),
      GridBall.add
        (logSeriesFrac P n (Nat.sub u (Nat.shiftLeft v s)) (Nat.add u (Nat.shiftLeft v s))).hi
        (GridBall.scaleNat s (logSeriesFrac P n 1 3).hi)⟩

/-- Balls of `Enclosure.logLarge (u / v) n`, with the scale `log2 ⌊u / v⌋`. -/
def logLargeFrac (P n u v : ℕ) : IntervalBalls := logLargeCore P n u v (Nat.log2 (Nat.div u v))

/-- `logLargeFrac P n u v` encloses the endpoints of `Enclosure.logLarge (u / v) n` at precision
`P`, for all naturals `u` and `v`. -/
theorem logLargeFrac_encloses (P n u v : ℕ) :
    (logLargeFrac P n u v).EnclosesEnds P (Enclosure.logLarge ((u : ℚ) / v) n).lo
      (Enclosure.logLarge ((u : ℚ) / v) n).hi := by
  unfold logLargeFrac logLargeCore
  refine IntervalBalls.guard_enclosesEnds fun hok ↦ ?_
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hok
  obtain ⟨hv, hW⟩ := hok
  set s := Nat.log2 (Nat.div u v)
  have hscale : Enclosure.logScale ((u : ℚ) / v) = s := by
    simp only [Enclosure.logScale, Nat.floor_div_eq_div, s, GridBall.natDiv_eq_div]
  have ht : ((u : ℚ) / v / 2 ^ s - 1) / ((u : ℚ) / v / 2 ^ s + 1) =
      ((Nat.sub u (Nat.shiftLeft v s) : ℕ) : ℚ) / ((Nat.add u (Nat.shiftLeft v s) : ℕ) : ℚ) := by
    have : (0 : ℚ) < v := by exact_mod_cast hv
    rw [Nat.sub_eq, Nat.add_eq, Nat.cast_sub hW, Nat.cast_add, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
    push_cast
    field_simp
  have hL := logSeriesFrac_encloses (P := P) n ht
  have h2 := logSeriesFrac_encloses (P := P) n
    (by norm_num : ((2 : ℚ) - 1) / (2 + 1) = ((1 : ℕ) : ℚ) / ((3 : ℕ) : ℚ))
  simp only [Enclosure.logLarge, hscale, FloatLib.Numerics.RationalInterval.add,
    FloatLib.Numerics.RationalInterval.scaleNonnegative, mul_comm (s : ℚ)]
  exact ⟨GridBall.add_encloses hL.1 (GridBall.scaleNat_encloses h2.1),
    GridBall.add_encloses hL.2 (GridBall.scaleNat_encloses h2.2)⟩

/-- With denominator zero the balls of `logLargeFrac` are invalid. -/
theorem logLargeFrac_ok_zero (P n u : ℕ) :
    (logLargeFrac P n u 0).lo.ok = false ∧ (logLargeFrac P n u 0).hi.ok = false := by
  simp [logLargeFrac, logLargeCore, IntervalBalls.guard, GridBall.guard]

/-- Balls of `Enclosure.log (u / v) n`: arguments below one are inverted and the result negated,
as in FloatLib. -/
def logFrac (P n u v : ℕ) : IntervalBalls :=
  Bool.rec (logLargeFrac P n u v) (IntervalBalls.neg (logLargeFrac P n v u)) (Nat.blt u v)

/-- `logFrac P n u v` encloses the endpoints of `Enclosure.log (u / v) n` at precision `P`, for all
naturals `u` and `v`. -/
theorem logFrac_encloses (P n u v : ℕ) :
    (logFrac P n u v).EnclosesEnds P (Enclosure.log ((u : ℚ) / v) n).lo
      (Enclosure.log ((u : ℚ) / v) n).hi := by
  unfold logFrac
  by_cases huv : u < v
  · rw [Nat.blt_eq.mpr huv]
    have hlt : (u : ℚ) / v < 1 := by
      rw [div_lt_one (by exact_mod_cast (Nat.zero_le u).trans_lt huv)]
      exact_mod_cast huv
    have h := logLargeFrac_encloses P n v u
    simp only [Enclosure.log, hlt, ↓reduceIte, inv_div, FloatLib.Numerics.RationalInterval.neg]
    exact ⟨GridBall.neg_encloses h.2, GridBall.neg_encloses h.1⟩
  · rw [Bool.eq_false_iff.mpr fun h ↦ huv (Nat.blt_eq.mp h)]
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · have hz := logLargeFrac_ok_zero P n u
      exact ⟨fun h ↦ by simp [hz.1] at h, fun h ↦ by simp [hz.2] at h⟩
    · have hge : ¬ (u : ℚ) / v < 1 := by
        rw [div_lt_one (by exact_mod_cast hv)]
        exact_mod_cast huv
      simpa only [Enclosure.log, hge, ↓reduceIte] using logLargeFrac_encloses P n u v

/-! ### Logarithms of balls -/

/-- The odd series is Lipschitz with constant two where `2 t ^ 2 ≤ 1`. -/
theorem abs_oddLogSum_sub_le {t s : ℚ} (ht : 2 * t ^ 2 ≤ 1) (hs : 2 * s ^ 2 ≤ 1) (m : ℕ) :
    |oddLogSum t m - oddLogSum s m| ≤ 2 * |t - s| := by
  set M := max |t| |s|
  have hM0 : 0 ≤ M := (abs_nonneg t).trans (le_max_left _ _)
  have hM2 : M ^ 2 ≤ 1 / 2 := by
    rcases max_cases |t| |s| with ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [M, h, sq_abs] <;> linarith
  have hterm : ∀ k : ℕ, |t ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℚ) -
      s ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℚ)| ≤ |t - s| * (M ^ 2) ^ k := by
    intro k
    have hk : (0 : ℚ) < ((2 * k + 1 : ℕ) : ℚ) := by positivity
    rw [← sub_div, abs_div, abs_of_pos hk, div_le_iff₀ hk]
    calc |t ^ (2 * k + 1) - s ^ (2 * k + 1)|
        ≤ |t - s| * ((2 * k + 1 : ℕ) : ℚ) * M ^ (2 * k + 1 - 1) :=
          abs_pow_sub_pow_le (a := t) (b := s) (n := 2 * k + 1)
      _ = |t - s| * (M ^ 2) ^ k * ((2 * k + 1 : ℕ) : ℚ) := by
          rw [Nat.add_sub_cancel, ← pow_mul]; ring
  rw [oddLogSum, oddLogSum, ← Finset.sum_sub_distrib, mul_comm]
  refine (Finset.abs_sum_le_sum_abs _ _).trans <| (Finset.sum_le_sum fun k _ ↦ hterm k).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (geom_sum_le_two (by positivity) hM2 m) (abs_nonneg _)

/-- `oddLogOk a (2 ^ P)` bounds the square of `a / 2 ^ P`. -/
theorem sq_le_of_oddLogOk {P a : ℕ} (h : oddLogOk a (Nat.shiftLeft 1 P) = true) :
    2 * ((a : ℚ) / 2 ^ P) ^ 2 ≤ 1 := by
  simp only [oddLogOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.mul_eq,
    Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at h
  rw [div_pow, mul_div_assoc', div_le_one (by positivity), sq, sq]
  exact_mod_cast h.2

/-! ### Logarithms of balls of either side of one -/

/-- The odd series is odd. -/
theorem oddLogSum_neg (t : ℚ) (m : ℕ) : oddLogSum (-t) m = -oddLogSum t m := by
  simp only [oddLogSum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Odd.neg_pow ⟨k, rfl⟩, neg_div]

/-- If `oddLogOk a' b` and `a ≤ a'`, then `oddLogOk a b`. -/
theorem oddLogOk_mono {a a' b : ℕ} (h : oddLogOk a' b = true) (ha : a ≤ a') :
    oddLogOk a b = true := by
  simp only [oddLogOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.mul_eq] at h ⊢
  exact ⟨h.1, le_trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul ha ha)) h.2⟩

/-- The ball of `oddLogSum t m` from a ball `T` of `t` of either sign: the loop at the absolute
value of the center, with the sign of the center, widened by twice the radius. -/
def oddLogSumOfSignedBall (P m : ℕ) (T : GridBall) : GridBall :=
  Bool.rec
    ⟨(oddLogLoopFast P T.mag (Nat.shiftLeft 1 P) m).s, 0,
      Nat.add (Nat.mul 3 m) (Nat.add T.e T.e),
      T.ok && oddLogOk (Nat.add T.mag T.e) (Nat.shiftLeft 1 P)⟩
    ⟨0, (oddLogLoopFast P T.mag (Nat.shiftLeft 1 P) m).s,
      Nat.add (Nat.mul 3 m) (Nat.add T.e T.e),
      T.ok && oddLogOk (Nat.add T.mag T.e) (Nat.shiftLeft 1 P)⟩
    (Nat.blt T.p T.n)

/-- If `T` encloses `t` at precision `P`, then `oddLogSumOfSignedBall P m T` encloses
`oddLogSum t m`, for `t` of either sign. -/
theorem oddLogSumOfSignedBall_encloses {P m : ℕ} {T : GridBall} {t : ℚ} (hT : T.Encloses P t) :
    (oddLogSumOfSignedBall P m T).Encloses P (oddLogSum t m) := by
  intro hok
  have hP : (0 : ℚ) < 2 ^ P := by positivity
  obtain ⟨hTok, hbig⟩ : T.ok = true ∧ oddLogOk (T.mag + T.e) (Nat.shiftLeft 1 P) = true := by
    unfold oddLogSumOfSignedBall at hok
    cases h : Nat.blt T.p T.n <;> simpa [h, Nat.add_eq] using hok
  have hsmall := oddLogOk_mono hbig (Nat.le_add_right _ _)
  have hloop := (oddLogLoop_spec (P := P) hsmall m).1
  rw [show ((Nat.shiftLeft 1 P : ℕ) : ℚ) = 2 ^ P by simp [Nat.shiftLeft_eq', Nat.shiftLeft_eq]]
    at hloop
  have hmag := GridBall.cast_mag T
  -- the center of `T` as a rational `z` with `|z| = mag / 2 ^ P`, and the loop's value there
  obtain ⟨z, hz, hzu, hval⟩ : ∃ z : ℚ, z * 2 ^ P = T.center ∧
      z ^ 2 = ((T.mag : ℚ) / 2 ^ P) ^ 2 ∧
      |oddLogSum z m * 2 ^ P - (oddLogSumOfSignedBall P m T).center| ≤ 3 * m := by
    unfold oddLogSumOfSignedBall
    cases h : Nat.blt T.p T.n
    · have hc : (0 : ℚ) ≤ T.center := by
        rw [GridBall.cast_center, sub_nonneg]
        exact_mod_cast not_lt.mp (Bool.eq_false_iff.mp h ∘ Nat.blt_eq.mpr)
      refine ⟨_, by rw [div_mul_cancel₀ _ hP.ne', hmag, abs_of_nonneg hc], rfl, ?_⟩
      simpa [GridBall.cast_center, oddLogLoopFast_eq] using hloop
    · have hc : (T.center : ℚ) < 0 := by
        rw [GridBall.cast_center, sub_neg]
        exact_mod_cast Nat.blt_eq.mp h
      refine ⟨-(T.mag / 2 ^ P), by rw [neg_mul, div_mul_cancel₀ _ hP.ne', hmag, abs_of_neg hc,
        neg_neg], by ring, ?_⟩
      rw [GridBall.cast_center, oddLogSum_neg, ← abs_neg]
      simpa [oddLogLoopFast_eq, sub_eq_add_neg, add_comm] using hloop
  have he : ((oddLogSumOfSignedBall P m T).e : ℚ) = 3 * m + (T.e + T.e) := by
    unfold oddLogSumOfSignedBall
    cases Nat.blt T.p T.n <;> simp
  have ht2 : 2 * t ^ 2 ≤ 1 := by
    have habs : |t| ≤ ((T.mag + T.e : ℕ) : ℚ) / 2 ^ P := by
      rw [le_div_iff₀ hP, ← abs_of_pos hP, ← abs_mul]
      push_cast
      linarith [abs_sub_abs_le_abs_sub (t * 2 ^ P) (T.center : ℚ), hT hTok]
    have := pow_le_pow_left₀ (abs_nonneg t) habs 2
    rw [sq_abs] at this
    linarith [sq_le_of_oddLogOk (P := P) hbig]
  have hlip := abs_oddLogSum_sub_le ht2 (by rw [hzu]; exact sq_le_of_oddLogOk hsmall) m
  have hdist : |t - z| * 2 ^ P ≤ T.e := by
    rw [← abs_of_pos hP, ← abs_mul, sub_mul, hz]
    exact hT hTok
  have h3 := abs_sub_le (oddLogSum t m * 2 ^ P) (oddLogSum z m * 2 ^ P)
    (oddLogSumOfSignedBall P m T).center
  rw [← sub_mul, abs_mul, abs_of_pos hP] at h3
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right hlip hP.le]

/-- Balls of the endpoints of `Enclosure.logSeries x n` from a ball `T` of
`t = (x - 1) / (x + 1)` of either sign. -/
def logSeriesSignedBall (P n : ℕ) (T : GridBall) : IntervalBalls :=
  ⟨GridBall.sub (GridBall.scaleNat 2 (oddLogSumOfSignedBall P (Nat.div (Nat.add n 1) 2) T))
      (GridBall.scaleNat 2 (GridBall.divPos P (GridBall.powNonneg P T.abs (Nat.add n 1))
        (GridBall.sub (GridBall.ofNat P 1) T.abs))),
    GridBall.add (GridBall.scaleNat 2 (oddLogSumOfSignedBall P (Nat.div (Nat.add n 1) 2) T))
      (GridBall.scaleNat 2 (GridBall.divPos P (GridBall.powNonneg P T.abs (Nat.add n 1))
        (GridBall.sub (GridBall.ofNat P 1) T.abs)))⟩

/-- If `T` encloses `(x - 1) / (x + 1)` at precision `P`, then `logSeriesSignedBall P n T` encloses
the endpoints of `Enclosure.logSeries x n`. -/
theorem logSeriesSignedBall_encloses {P : ℕ} {x : ℚ} (n : ℕ) {T : GridBall}
    (hT : T.Encloses P ((x - 1) / (x + 1))) :
    (logSeriesSignedBall P n T).EnclosesEnds P (Enclosure.logSeries x n).lo
      (Enclosure.logSeries x n).hi := by
  have hTa := GridBall.abs_encloses hT
  have hO := GridBall.scaleNat_encloses (c := 2)
    (oddLogSumOfSignedBall_encloses (m := (n + 1) / 2) hT)
  have hR := GridBall.scaleNat_encloses (c := 2) (GridBall.divPos_encloses
    (GridBall.powNonneg_encloses hTa (abs_nonneg _) (n + 1))
    (GridBall.sub_encloses (GridBall.ofNat_encloses P 1) hTa))
  push_cast at hO hR
  rw [logSeries_lo, logSeries_hi, Enclosure.logOneSubRadius, mul_comm 2, mul_comm 2]
  exact ⟨GridBall.sub_encloses hO hR, GridBall.add_encloses hO hR⟩

/-- `logSeries (y / 2 ^ s) + s · logSeries 2`: `Enclosure.logLarge y n` when `logScale y = s`. -/
def logScaled (y : ℚ) (n s : ℕ) : FloatLib.Numerics.RationalInterval :=
  (Enclosure.logSeries (y / 2 ^ s) n).add ((Enclosure.logSeries 2 n).scaleNonnegative s)

/-- FloatLib's `Enclosure.logLarge y n` is `logScaled y n (Enclosure.logScale y)`, by definition. -/
theorem logLarge_eq_logScaled (y : ℚ) (n : ℕ) :
    Enclosure.logLarge y n = logScaled y n (Enclosure.logScale y) := rfl

/-- Balls of `logScaled y n s` from a ball `Y` of `y ≥ 0`. -/
def logScaledBall (P n s : ℕ) (Y : GridBall) : IntervalBalls :=
  ⟨GridBall.add
      (logSeriesSignedBall P n (GridBall.divPos P
        (GridBall.sub (GridBall.mulFrac 1 (Nat.shiftLeft 1 s) Y) (GridBall.ofNat P 1))
        (GridBall.add (GridBall.mulFrac 1 (Nat.shiftLeft 1 s) Y) (GridBall.ofNat P 1)))).lo
      (GridBall.scaleNat s (logSeriesFrac P n 1 3).lo),
    GridBall.add
      (logSeriesSignedBall P n (GridBall.divPos P
        (GridBall.sub (GridBall.mulFrac 1 (Nat.shiftLeft 1 s) Y) (GridBall.ofNat P 1))
        (GridBall.add (GridBall.mulFrac 1 (Nat.shiftLeft 1 s) Y) (GridBall.ofNat P 1)))).hi
      (GridBall.scaleNat s (logSeriesFrac P n 1 3).hi)⟩

/-- If `Y` encloses `y` at precision `P`, then `logScaledBall P n s Y` encloses the endpoints of
`logScaled y n s`, for every `s`. -/
theorem logScaledBall_encloses {P n s : ℕ} {Y : GridBall} {y : ℚ} (hY : Y.Encloses P y) :
    (logScaledBall P n s Y).EnclosesEnds P (logScaled y n s).lo (logScaled y n s).hi := by
  have hone : (GridBall.ofNat P 1).Encloses P 1 := by simpa using GridBall.ofNat_encloses P 1
  have hY' := GridBall.mulFrac_encloses (a := 1) (b := Nat.shiftLeft 1 s) hY
  rw [show y * (((1 : ℕ) : ℚ) / ((Nat.shiftLeft 1 s : ℕ) : ℚ)) = y / 2 ^ s by
    simp [Nat.shiftLeft_eq', Nat.shiftLeft_eq, div_eq_mul_inv]] at hY'
  have hL := logSeriesSignedBall_encloses (P := P) n
    (GridBall.divPos_encloses (GridBall.sub_encloses hY' hone) (GridBall.add_encloses hY' hone))
  have h2 := logSeriesFrac_encloses (P := P) n
    (by norm_num : ((2 : ℚ) - 1) / (2 + 1) = ((1 : ℕ) : ℚ) / ((3 : ℕ) : ℚ))
  simp only [logScaled, FloatLib.Numerics.RationalInterval.add,
    FloatLib.Numerics.RationalInterval.scaleNonnegative, mul_comm (s : ℚ)]
  exact ⟨GridBall.add_encloses hL.1 (GridBall.scaleNat_encloses h2.1),
    GridBall.add_encloses hL.2 (GridBall.scaleNat_encloses h2.2)⟩

/-- The floor of the lower end `(Y.p - Y.n - Y.e) / 2 ^ P` of the ball `Y`, or `0` when that end
is negative: `Nat.shiftRight (Nat.sub Y.p (Nat.add Y.n Y.e)) P`, which is
`⌊(Y.p - (Y.n + Y.e)) / 2 ^ P⌋` with truncated subtraction. -/
def floorLow (P : ℕ) (Y : GridBall) : ℕ := Nat.shiftRight (Nat.sub Y.p (Nat.add Y.n Y.e)) P

/-- The floor of the upper end `(Y.p + Y.e - Y.n) / 2 ^ P` of the ball `Y`, or `0` when that end
is negative: `Nat.shiftRight (Nat.sub (Nat.add Y.p Y.e) Y.n) P`, which is
`⌊(Y.p + Y.e - Y.n) / 2 ^ P⌋` with truncated subtraction. -/
def floorHigh (P : ℕ) (Y : GridBall) : ℕ := Nat.shiftRight (Nat.sub (Nat.add Y.p Y.e) Y.n) P

/-- If `Y` encloses `y` at precision `P`, `Y.ok` and `Y.n + Y.e ≤ Y.p`, then `0 ≤ y` and
`floorLow P Y ≤ ⌊y⌋₊ ≤ floorHigh P Y`. -/
theorem floor_mem_of_encloses {P : ℕ} {Y : GridBall} {y : ℚ} (hY : Y.Encloses P y)
    (hok : Y.ok = true) (hnn : Y.n + Y.e ≤ Y.p) :
    0 ≤ y ∧ floorLow P Y ≤ ⌊y⌋₊ ∧ ⌊y⌋₊ ≤ floorHigh P Y := by
  have hP : (0 : ℚ) < 2 ^ P := by positivity
  have h1 := abs_le.mp (hY hok)
  rw [GridBall.cast_center] at h1
  have hnn' : (Y.n : ℚ) + Y.e ≤ Y.p := by exact_mod_cast hnn
  refine ⟨nonneg_of_mul_nonneg_left (by linarith) hP, ?_, ?_⟩
  · simp only [floorLow, Nat.add_eq, Nat.sub_eq, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow,
      ← Nat.floor_div_eq_div (K := ℚ)]
    refine Nat.floor_le_floor ?_
    rw [div_le_iff₀ (by positivity), Nat.cast_sub hnn]
    push_cast
    linarith
  · simp only [floorHigh, Nat.add_eq, Nat.sub_eq, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow,
      ← Nat.floor_div_eq_div (K := ℚ)]
    refine Nat.floor_le_floor ?_
    rw [le_div_iff₀ (by positivity), Nat.cast_sub (by omega)]
    push_cast
    linarith

/-- Balls of `Enclosure.logLarge y n` from a ball `Y` of `y ≥ 0`: the binary scale of the lower
end when the ball decides it, the join of the two neighbouring scales when the ball straddles a
power of two. -/
def logLargeBall (P n : ℕ) (Y : GridBall) : IntervalBalls :=
  IntervalBalls.guard (Y.ok && Nat.ble (Nat.add Y.n Y.e) Y.p)
    (Bool.rec
      (Bool.rec IntervalBalls.invalid
        (IntervalBalls.join (logScaledBall P n (Nat.log2 (floorLow P Y)) Y)
          (logScaledBall P n (Nat.add (Nat.log2 (floorLow P Y)) 1) Y))
        (Nat.beq (Nat.log2 (floorHigh P Y)) (Nat.add (Nat.log2 (floorLow P Y)) 1)))
      (logScaledBall P n (Nat.log2 (floorLow P Y)) Y)
      (Nat.beq (Nat.log2 (floorHigh P Y)) (Nat.log2 (floorLow P Y))))

/-- If `Y` encloses `y` at precision `P`, then `logLargeBall P n Y` encloses the endpoints of
`Enclosure.logLarge y n`. -/
theorem logLargeBall_encloses {P n : ℕ} {Y : GridBall} {y : ℚ} (hY : Y.Encloses P y) :
    (logLargeBall P n Y).EnclosesEnds P (Enclosure.logLarge y n).lo
      (Enclosure.logLarge y n).hi := by
  unfold logLargeBall
  refine IntervalBalls.guard_enclosesEnds fun hg ↦ ?_
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at hg
  obtain ⟨hy0, hlow, hhigh⟩ := floor_mem_of_encloses hY hg.1 hg.2
  set s := Nat.log2 (floorLow P Y)
  have hmono : ∀ {a b : ℕ}, a ≤ b → Nat.log2 a ≤ Nat.log2 b := fun h ↦ by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]; exact Nat.log_mono_right h
  have hs1 : s ≤ Enclosure.logScale y := hmono hlow
  have hs2 : Enclosure.logScale y ≤ Nat.log2 (floorHigh P Y) := hmono hhigh
  rw [logLarge_eq_logScaled]
  cases h1 : Nat.beq (Nat.log2 (floorHigh P Y)) s
  · cases h2 : Nat.beq (Nat.log2 (floorHigh P Y)) (Nat.add s 1)
    · exact ⟨GridBall.invalid_encloses P _, GridBall.invalid_encloses P _⟩
    · have h2' : Nat.log2 (floorHigh P Y) = s + 1 := Nat.eq_of_beq_eq_true h2
      have hj := IntervalBalls.join_enclosesEnds_ite
        (logScaledBall_encloses (n := n) (s := s) hY)
        (logScaledBall_encloses (n := n) (s := s + 1) hY) (Enclosure.logScale y = s)
      by_cases hs : Enclosure.logScale y = s
      · simpa [hs] using hj
      · simpa [hs, show Enclosure.logScale y = s + 1 by omega] using hj
  · rw [le_antisymm (Nat.eq_of_beq_eq_true h1 ▸ hs2) hs1]
    exact logScaledBall_encloses hY

/-- On `(1/2, 2)` FloatLib's logarithm is the series enclosure, on either side of one. -/
theorem log_eq_logSeries {q : ℚ} (h1 : 1 / 2 < q) (h2 : q < 2) (n : ℕ) :
    Enclosure.log q n = Enclosure.logSeries q n := by
  have hq0 : 0 < q := by linarith
  unfold Enclosure.log
  split_ifs with hq
  · have hinv1 : 1 < q⁻¹ := (one_lt_inv₀ hq0).mpr hq
    have hinv2 : q⁻¹ < 2 := by
      rw [inv_lt_comm₀ hq0 (by norm_num)]; linarith
    have hscale : Enclosure.logScale q⁻¹ = 0 := by
      have : ⌊q⁻¹⌋₊ = 1 := by
        rw [Nat.floor_eq_iff (by positivity)]; constructor <;> push_cast <;> linarith
      simp [Enclosure.logScale, this]
    have ht : (q⁻¹ - 1) / (q⁻¹ + 1) = -((q - 1) / (q + 1)) := by
      field_simp; ring
    simp only [Enclosure.logLarge, hscale, pow_zero, div_one, Enclosure.logSeries, ht, neg_neg,
      FloatLib.Numerics.RationalInterval.add, FloatLib.Numerics.RationalInterval.sub,
      FloatLib.Numerics.RationalInterval.neg, FloatLib.Numerics.RationalInterval.scaleNonnegative,
      Nat.cast_zero, zero_mul, add_zero]
    congr 1 <;> ring
  · have hscale : Enclosure.logScale q = 0 := by
      have : ⌊q⌋₊ = 1 := by
        rw [Nat.floor_eq_iff hq0.le]; constructor <;> push_cast <;> linarith
      simp [Enclosure.logScale, this]
    simp only [Enclosure.logLarge, hscale, pow_zero, div_one,
      FloatLib.Numerics.RationalInterval.add, FloatLib.Numerics.RationalInterval.scaleNonnegative,
      Nat.cast_zero, zero_mul, add_zero]

/-- Every rational enclosed by `B` lies strictly between `1/2` and `2`. -/
def nearOneCertain (P : ℕ) (B : GridBall) : Bool :=
  B.ok && Nat.blt (Nat.add (Nat.shiftLeft 1 P) (Nat.add (Nat.add B.n B.e) (Nat.add B.n B.e)))
      (Nat.add B.p B.p) &&
    Nat.blt (Nat.add B.p B.e) (Nat.add B.n (Nat.shiftLeft 1 (Nat.add P 1)))

/-- If `B` encloses `q` at precision `P` and `nearOneCertain P B`, then `1 / 2 < q` and `q < 2`. -/
theorem mem_of_nearOneCertain {P : ℕ} {B : GridBall} {q : ℚ} (hB : B.Encloses P q)
    (h : nearOneCertain P B = true) : 1 / 2 < q ∧ q < 2 := by
  simp only [nearOneCertain, Bool.and_eq_true, Nat.blt_eq, Nat.add_eq,
    Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at h
  obtain ⟨⟨hok, h1⟩, h2⟩ := h
  have hP : (0 : ℚ) < 2 ^ P := by positivity
  have hb := abs_le.mp (hB hok)
  rw [GridBall.cast_center] at hb
  have h1' : (2 : ℚ) ^ P + (B.n + B.e + (B.n + B.e)) < B.p + B.p := by exact_mod_cast h1
  have h2' : (B.p : ℚ) + B.e < B.n + 2 ^ (P + 1) := by exact_mod_cast h2
  rw [pow_succ] at h2'
  exact ⟨lt_of_mul_lt_mul_right (by linarith) hP.le, lt_of_mul_lt_mul_right (by linarith) hP.le⟩

/-- Balls of `Enclosure.log q n` from a ball `B` of `q > 0`: the series directly when the ball lies
in `(1/2, 2)`, which covers balls on both sides of one; otherwise the reduction of FloatLib's
`log`, which needs the ball to decide whether `q < 1`. -/
def logBall (P n : ℕ) (B : GridBall) : IntervalBalls :=
  Bool.rec
    (Bool.rec
      (Bool.rec IntervalBalls.invalid (logLargeBall P n B)
        (B.ok && Nat.ble (Nat.add (Nat.shiftLeft 1 P) (Nat.add B.n B.e)) B.p))
      (IntervalBalls.neg (logLargeBall P n (GridBall.inv P B)))
      (B.ok && Nat.blt (Nat.add B.p B.e) (Nat.add B.n (Nat.shiftLeft 1 P))))
    (logSeriesSignedBall P n (GridBall.divPos P (GridBall.sub B (GridBall.ofNat P 1))
      (GridBall.add B (GridBall.ofNat P 1))))
    (nearOneCertain P B)

/-- If `B` encloses `q` at precision `P`, then `logBall P n B` encloses the endpoints of
`Enclosure.log q n`. -/
theorem logBall_encloses {P n : ℕ} {B : GridBall} {q : ℚ} (hB : B.Encloses P q) :
    (logBall P n B).EnclosesEnds P (Enclosure.log q n).lo (Enclosure.log q n).hi := by
  have hP : (0 : ℚ) < 2 ^ P := by positivity
  unfold logBall
  cases h0 : nearOneCertain P B
  · cases h1 : (B.ok && Nat.blt (Nat.add B.p B.e) (Nat.add B.n (Nat.shiftLeft 1 P)))
    · cases h2 : (B.ok && Nat.ble (Nat.add (Nat.shiftLeft 1 P) (Nat.add B.n B.e)) B.p)
      · exact ⟨GridBall.invalid_encloses P _, GridBall.invalid_encloses P _⟩
      · simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq,
          one_mul] at h2
        have hb := abs_le.mp (hB h2.1)
        rw [GridBall.cast_center] at hb
        have h2' : (2 : ℚ) ^ P + (B.n + B.e) ≤ B.p := by exact_mod_cast h2.2
        have hq : ¬ q < 1 := not_lt.mpr (le_of_mul_le_mul_right (by linarith) hP)
        simpa only [Enclosure.log, hq, ↓reduceIte] using logLargeBall_encloses (n := n) hB
    · simp only [Bool.and_eq_true, Nat.blt_eq, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq,
        one_mul] at h1
      have hb := abs_le.mp (hB h1.1)
      rw [GridBall.cast_center] at hb
      have h1' : (B.p : ℚ) + B.e < B.n + 2 ^ P := by exact_mod_cast h1.2
      have hq : q < 1 := lt_of_mul_lt_mul_right (by linarith) hP.le
      have h := logLargeBall_encloses (n := n) (GridBall.inv_encloses hB)
      simp only [Enclosure.log, hq, ↓reduceIte, FloatLib.Numerics.RationalInterval.neg]
      exact ⟨GridBall.neg_encloses h.2, GridBall.neg_encloses h.1⟩
  · obtain ⟨hq1, hq2⟩ := mem_of_nearOneCertain hB h0
    rw [log_eq_logSeries hq1 hq2]
    have hone : (GridBall.ofNat P 1).Encloses P 1 := by simpa using GridBall.ofNat_encloses P 1
    exact logSeriesSignedBall_encloses n
      (GridBall.divPos_encloses (GridBall.sub_encloses hB hone) (GridBall.add_encloses hB hone))

/-! ### The interval logarithms `RationalInterval.logPointIntervalWith` and `logRangeWith` -/

/-- The lower endpoint of `logRangeWith I terms hpos` is FloatLib's at `I.lo`. -/
theorem logRangeWith_lo (I : Continuum.RationalInterval) (terms : ℕ) (hpos : 0 < I.lo) :
    (Continuum.RationalInterval.logRangeWith I terms hpos).lo =
      (Enclosure.log I.lo (Continuum.RationalInterval.logFloatLibDegree terms)).lo := by
  unfold Continuum.RationalInterval.logRangeWith
  split
  next J hJ =>
    have hp : 0 < I.toFloatLib.lo := hpos
    simp only [Interval.logBounds?, hp, ↓reduceIte, Option.some.injEq] at hJ
    subst hJ
    simp only [Continuum.RationalInterval.ofFloatLib, Interval.monotoneBounds]
    split_ifs <;> rfl
  next h => simp [Interval.logBounds?, hpos] at h

/-- The upper endpoint of `logRangeWith I terms hpos` is FloatLib's at `I.hi`. -/
theorem logRangeWith_hi (I : Continuum.RationalInterval) (terms : ℕ) (hpos : 0 < I.lo) :
    (Continuum.RationalInterval.logRangeWith I terms hpos).hi =
      (Enclosure.log I.hi (Continuum.RationalInterval.logFloatLibDegree terms)).hi := by
  unfold Continuum.RationalInterval.logRangeWith
  split
  next J hJ =>
    have hp : 0 < I.toFloatLib.lo := hpos
    simp only [Interval.logBounds?, hp, ↓reduceIte, Option.some.injEq] at hJ
    subst hJ
    simp only [Continuum.RationalInterval.ofFloatLib, Interval.monotoneBounds]
    split_ifs with heq
    · change (Enclosure.log I.lo _).hi = _
      rw [show I.lo = I.hi from heq]
    · rfl
  next h => simp [Interval.logBounds?, hpos] at h

namespace IntervalBalls

/-- Balls of `logPointIntervalWith terms (u / v) h`. -/
def logPointFrac (P terms u v : ℕ) : IntervalBalls :=
  logFrac P (Continuum.RationalInterval.logFloatLibDegree terms) u v

/-- For `h : 0 < u / v`, `logPointFrac P terms u v` encloses `logPointIntervalWith terms (u / v) h`
at precision `P`. -/
theorem logPointFrac_encloses (P terms u v : ℕ) (h : 0 < (u : ℚ) / v) :
    (logPointFrac P terms u v).Encloses P
      (Continuum.RationalInterval.logPointIntervalWith terms ((u : ℚ) / v) h) := by
  unfold Continuum.RationalInterval.logPointIntervalWith
  rw [IntervalBalls.Encloses, logRangeWith_lo (.const _) terms h,
    logRangeWith_hi (.const _) terms h]
  exact logFrac_encloses P _ u v

/-- Balls of `logAbsPointIntervalWith terms (±u / v)`. -/
def logAbsPointFrac (P terms u v : ℕ) : IntervalBalls :=
  Bool.rec (logPointFrac P terms u v) (const P 0) (Nat.beq u 0)

/-- `logAbsPointFrac P terms u v` encloses `logAbsPointIntervalWith terms (signedFrac neg u v)` at
precision `P`, for either sign `neg` and all naturals `u` and `v`. -/
theorem logAbsPointFrac_encloses (P terms : ℕ) (neg : Bool) (u v : ℕ) :
    (logAbsPointFrac P terms u v).Encloses P
      (Continuum.RationalInterval.logAbsPointIntervalWith terms
        (signedFrac neg u v)) := by
  unfold logAbsPointFrac Continuum.RationalInterval.logAbsPointIntervalWith
  have habs : |signedFrac neg u v| = (u : ℚ) / v := by cases neg <;> simp [abs_div]
  rcases eq_or_ne u 0 with rfl | hu
  · have : signedFrac neg 0 v = 0 := by cases neg <;> simp
    simpa only [this, ↓reduceDIte, Nat.beq_refl] using const_encloses 0
  · rw [Bool.eq_false_iff.mpr fun h ↦ hu (Nat.eq_of_beq_eq_true h)]
    split
    · next hq =>
      -- `±u / v = 0` forces `v = 0`, where the balls are invalid
      have : (u : ℚ) / v = 0 := by rw [← habs, hq, abs_zero]
      obtain rfl : v = 0 := by simpa [hu] using this
      have hz := logLargeFrac_ok_zero P
        (Continuum.RationalInterval.logFloatLibDegree terms) u
      change IntervalBalls.Encloses P
        (logLargeFrac P (Continuum.RationalInterval.logFloatLibDegree terms) u 0) _
      exact ⟨fun h ↦ by simp [hz.1] at h, fun h ↦ by simp [hz.2] at h⟩
    · next hq =>
      convert logPointFrac_encloses P terms u v (habs ▸ abs_pos.mpr hq) using 2

/-- `(±u / v) ^ (n + 1) / d` as a signed fraction of natural numbers. -/
theorem signedFrac_pow_div (neg : Bool) (u v n d : ℕ) :
    (signedFrac neg u v) ^ (n + 1) / (d : ℚ) =
      signedFrac (neg && Nat.beq (Nat.mod n 2) 0) (u ^ (n + 1)) (v ^ (n + 1) * d) := by
  rcases Nat.even_or_odd n with hn | hn
  · rw [show Nat.beq (Nat.mod n 2) 0 = true by rw [GridBall.natMod_eq_mod, Nat.even_iff.mp hn]; rfl,
      Bool.and_true]
    cases neg <;> simp [hn.add_one.neg_pow, div_pow, div_div, neg_div]
  · rw [show Nat.beq (Nat.mod n 2) 0 = false by rw [GridBall.natMod_eq_mod, Nat.odd_iff.mp hn]; rfl,
      Bool.and_false]
    cases neg <;> simp [hn.add_one.neg_pow, div_pow, div_div]

/-- Balls of `logRangeWith I terms h` for `I.lo = u₁ / v₁` and `I.hi = u₂ / v₂`. -/
def logRangeFrac (P terms u₁ v₁ u₂ v₂ : ℕ) : IntervalBalls :=
  ⟨(logPointFrac P terms u₁ v₁).lo, (logPointFrac P terms u₂ v₂).hi⟩

/-- For `I.lo = u₁ / v₁`, `I.hi = u₂ / v₂` and `h : 0 < I.lo`, the balls
`logRangeFrac P terms u₁ v₁ u₂ v₂` enclose `logRangeWith I terms h` at precision `P`. -/
theorem logRangeFrac_encloses {P terms u₁ v₁ u₂ v₂ : ℕ}
    {I : Continuum.RationalInterval}
    (hlo : I.lo = (u₁ : ℚ) / v₁) (hhi : I.hi = (u₂ : ℚ) / v₂) (h : 0 < I.lo) :
    (logRangeFrac P terms u₁ v₁ u₂ v₂).Encloses P
      (Continuum.RationalInterval.logRangeWith I terms h) := by
  rw [IntervalBalls.Encloses, logRangeWith_lo, logRangeWith_hi, hlo, hhi]
  exact ⟨(logFrac_encloses P (Continuum.RationalInterval.logFloatLibDegree terms) u₁ v₁).1,
    (logFrac_encloses P (Continuum.RationalInterval.logFloatLibDegree terms) u₂ v₂).2⟩

/-- Balls of `logPointIntervalWith terms q h` from a ball `B` of `q`. -/
def logPointBall (P terms : ℕ) (B : GridBall) : IntervalBalls :=
  logBall P (Continuum.RationalInterval.logFloatLibDegree terms) B

/-- If `B` encloses `q` at precision `P` and `h : 0 < q`, then `logPointBall P terms B` encloses
`logPointIntervalWith terms q h`. -/
theorem logPointBall_encloses {P terms : ℕ} {B : GridBall} {q : ℚ} (hB : B.Encloses P q)
    (h : 0 < q) : (logPointBall P terms B).Encloses P
      (Continuum.RationalInterval.logPointIntervalWith terms q h) := by
  unfold Continuum.RationalInterval.logPointIntervalWith
  rw [IntervalBalls.Encloses, logRangeWith_lo (.const _) terms h,
    logRangeWith_hi (.const _) terms h]
  exact logBall_encloses hB

/-- Balls of `logRangeWith I terms h` from balls `S` of `I`. -/
def logRangeBall (P terms : ℕ) (S : IntervalBalls) : IntervalBalls :=
  ⟨(logBall P (Continuum.RationalInterval.logFloatLibDegree terms) S.lo).lo,
    (logBall P (Continuum.RationalInterval.logFloatLibDegree terms) S.hi).hi⟩

/-- If `S` encloses `I` at precision `P` and `h : 0 < I.lo`, then `logRangeBall P terms S` encloses
`logRangeWith I terms h`. -/
theorem logRangeBall_encloses {P terms : ℕ} {S : IntervalBalls}
    {I : Continuum.RationalInterval} (hS : S.Encloses P I) (h : 0 < I.lo) :
    (logRangeBall P terms S).Encloses P
      (Continuum.RationalInterval.logRangeWith I terms h) := by
  rw [IntervalBalls.Encloses, logRangeWith_lo, logRangeWith_hi]
  exact ⟨(logBall_encloses (n := Continuum.RationalInterval.logFloatLibDegree terms) hS.1).1,
    (logBall_encloses (n := Continuum.RationalInterval.logFloatLibDegree terms) hS.2).2⟩

end IntervalBalls

end CAS.Numerics

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.GridBallLog
public import CAS.Continuum.Interval.Elementary.Atan

/-!
# Balls for FloatLib's exact rational arctangent

FloatLib's `Enclosure.atan x d` reduces `x` by oddness to `x ≥ 0`, by `atan x = π / 2 - atan x⁻¹`
to `x ≤ 1`, and by `atan x = π / 4 + atan ((x - 1) / (x + 1))` to `x ≤ 1 / 2`, and encloses the
arctangent of the reduced argument `t` by the Taylor sum `∑ k < d + 1, (-1) ^ k t ^ (2k + 1) /
(2k + 1)` with the geometric remainder `|t| ^ (2d + 3) / (1 - t ^ 2)` (`atanSmall`); `π / 4` is
Machin's `4 atan (1 / 5) - atan (1 / 239)` with the same degree. Its exact rational endpoints
are enclosed by balls on the grid `2 ^ -P`:

* `atanLoop` evaluates the Taylor sum at a fraction by the signed `seriesLoop` with one error
  bound for the whole sum (`atanLoop_spec`); `atanSmallOfBall P d Y` evaluates it at the center of
  a ball `Y` and widens it by twice the radius, the Lipschitz constant of the sum where
  `2 t ^ 2 ≤ 1` (`abs_atanTaylor_sub_le`).
* `atanBall P d X` encloses both endpoints of `Enclosure.atan x d` for every `x` enclosed by `X`
  (`atanBall_encloses`). A ball inside `[-1/2, 1/2]` goes to `atanSmall` directly, because
  `atan x d = atanSmall x d` there for either sign (`atan_eq_atanSmall`). Where the ball does not
  decide a comparison of a reduction (`x ≤ 1/2`, `x ≤ 1`), both branches are evaluated and
  joined (`GridBall.join`), so that exact cell endpoints such as `x = 1/2` or `x = 1` need no
  special treatment.
* `IntervalBalls.atanRangeBall P terms S` encloses `atanRangeWith I terms` when `S` encloses `I`
  (`atanRangeBall_encloses`).

## Main results

* `atanLoop_spec`: when `(a / b) ^ 2 ≤ 1 / 2` the loop approximates `2 ^ P` times the Taylor sum
  within `3 n`.
* `abs_atanTaylor_sub_le`: the arctangent Taylor sum is Lipschitz with constant two where
  `2 t ^ 2 ≤ 1`.
* `piQuarterBalls_encloses`: `piQuarterBalls P d` encloses both endpoints of Machin's
  `piQuarter d`.
* `atan_eq_atanSmall`: on `[-1/2, 1/2]` FloatLib's arctangent is the series enclosure.
* `atanBall_encloses`: `atanBall P d X` encloses both endpoints of `atan x d` for every `x`
  enclosed by `X`.
* `IntervalBalls.atanRangeBall_encloses`: `atanRangeBall P terms S` encloses
  `atanRangeWith I terms` when `S` encloses `I`.

## Implementation notes

We do not reimplement the arctangent: the intervals are FloatLib's, Machin's enclosure of `π / 4`
included, and the balls only enclose their exact endpoints. The loop truncates the term and the
sum at every step, and the a priori bound `3 n` of `atanLoop_spec` is the radius of the sum.

The degree `d` sums `d + 1` terms, so the analytic error at the reduced argument `|t| ≤ 1/2` is
about `2 ^ -(2d + 3)` whatever the precision `P`. At `P = 200` and `d = 40` an arctangent of a
ball costs about 2.7 ms in the fast profile and 1 ms in the kernel, where the Machin balls are
shared within a declaration.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>. The enclosed
  intervals are those of `FloatLib.Numerics.Enclosure.atan`, with its reductions, its geometric
  remainder and Machin's identity for `π / 4`.
* Joris van der Hoeven, "Ball arithmetic", *Logical approaches to Barriers in Computing and
  Complexity*, Preprint-Reihe Mathematik 6, Ernst-Moritz-Arndt-Universität Greifswald, 2010,
  pp. 179-208, <https://www.texmacs.org/joris/ball/ball-abs.html>. Section 3.6, (15), for the
  enclosure `B(f(c), M r)` with `M` a bound of `|f'|` over the ball, used for the Taylor sum.
* NIST Digital Library of Mathematical Functions, §4.24 Inverse Trigonometric Functions: Further
  Properties, Version 1.2.8 (2026-09-15), <https://dlmf.nist.gov/4.24>. Equation (4.24.3), the
  arctangent series, whose partial sums `atanLoop` approximates on the grid.
* David H. Bailey, Jonathan M. Borwein, Peter B. Borwein and Simon Plouffe, "The Quest for Pi",
  *The Mathematical Intelligencer* 19 (1997), pp. 50-57, <https://doi.org/10.1007/BF03024340>.
  Section 2 for Machin's formula, the `π / 4` of `piQuarterBalls`.
-/

@[expose] public section

namespace CAS.Numerics

open FloatLib.Numerics

/-! ### The arctangent series -/

/-- `n` steps of the arctangent series at `±a / b`: from the term `±a 2 ^ P / b`, multiplied by
`-a ^ 2 / b ^ 2` and divided by `2k + 1` at step `k`. -/
def atanLoop (P n : ℕ) (neg : Bool) (a b : ℕ) : SeriesState :=
  seriesLoop 0 (Nat.mul a a) (fun _ ↦ Nat.mul b b) (fun k ↦ Nat.add (Nat.add k k) 1)
    (Bool.rec ⟨Nat.div (Nat.shiftLeft a P) b, 0, 0, 0⟩ ⟨0, Nat.div (Nat.shiftLeft a P) b, 0, 0⟩
      neg) n

/-- When `(a / b) ^ 2 ≤ 1 / 2` (`oddLogOk a b`), the loop approximates `2 ^ P` times the Taylor sum
`atanTaylor (±a / b) n` within `3 n` and the next term within `2`. -/
theorem atanLoop_spec {P n : ℕ} {neg : Bool} {a b : ℕ} (h : oddLogOk a b = true) :
    |Enclosure.atanTaylor (signedFrac neg a b) n * 2 ^ P - (atanLoop P n neg a b).sum| ≤
        3 * n ∧
      |(-1) ^ n * (signedFrac neg a b) ^ (2 * n + 1) * 2 ^ P - (atanLoop P n neg a b).term| ≤
        2 := by
  simp only [oddLogOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.mul_eq] at h
  obtain ⟨hb, hab⟩ := h
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  set t := signedFrac neg a b
  have ht2 : t ^ 2 = (a : ℚ) ^ 2 / (b : ℚ) ^ 2 := by
    cases neg <;> simp [t, div_pow]
  have hr : (a : ℚ) ^ 2 / (b : ℚ) ^ 2 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 * (a * a) : ℚ) ≤ b * b := by exact_mod_cast hab
    nlinarith
  have hinit : |t * 2 ^ P -
      (Bool.rec (motive := fun _ ↦ SeriesState) ⟨a * 2 ^ P / b, 0, 0, 0⟩
        ⟨0, a * 2 ^ P / b, 0, 0⟩ neg).term| ≤ 2 := by
    have hd := GridBall.natDiv_bounds (a * 2 ^ P) b hb
    have hfr : ((a * 2 ^ P : ℕ) : ℚ) / b = (a : ℚ) / b * 2 ^ P := by push_cast; ring
    rw [hfr] at hd
    cases neg <;> simp only [t, signedFrac_false, signedFrac_true, SeriesState.term,
      Nat.cast_zero, sub_zero, zero_sub, Int.cast_neg, Int.cast_natCast, abs_le] <;>
      constructor <;> linarith [hd.1, hd.2]
  have key := seriesLoop_spec (cp := 0) (cn := a * a) (d := fun _ ↦ b * b)
    (w := fun k ↦ k + k + 1)
    (init := Bool.rec (motive := fun _ ↦ SeriesState) ⟨a * 2 ^ P / b, 0, 0, 0⟩
      ⟨0, a * 2 ^ P / b, 0, 0⟩ neg)
    (X := fun i ↦ (-1) ^ i * t ^ (2 * i + 1) * 2 ^ P) (B := fun _ ↦ 2)
    (fun i ↦ by
      push_cast
      have : t ^ (2 * (i + 1) + 1) = t ^ (2 * i + 1) * t ^ 2 := by ring
      rw [this, ht2]; field_simp; ring)
    (fun i ↦ by
      push_cast
      rw [show ((0 : ℚ) - a * a) / (b * b) = -((a : ℚ) ^ 2 / (b : ℚ) ^ 2) by ring, abs_neg,
        abs_of_nonneg (by positivity)]
      linarith)
    (by simpa using hinit) (by cases neg <;> exact ⟨rfl, rfl⟩) n
  have hloop : atanLoop P n neg a b = seriesLoop 0 (a * a) (fun _ ↦ b * b) (fun k ↦ k + k + 1)
      (Bool.rec (motive := fun _ ↦ SeriesState) ⟨a * 2 ^ P / b, 0, 0, 0⟩
        ⟨0, a * 2 ^ P / b, 0, 0⟩ neg) n := by
    simp only [atanLoop, Nat.mul_eq, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq,
        GridBall.natDiv_eq_div]
  rw [hloop]
  refine ⟨?_, key.1⟩
  have hsum : (∑ i ∈ Finset.range n, (-1) ^ i * t ^ (2 * i + 1) * 2 ^ P /
      ((i + i + 1 : ℕ) : ℚ)) = Enclosure.atanTaylor t n * 2 ^ P := by
    rw [Enclosure.atanTaylor, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by push_cast; ring
  have hbound : (∑ i ∈ Finset.range n, ((2 : ℚ) / ((i + i + 1 : ℕ) : ℚ) + 1)) ≤ 3 * n := by
    refine (Finset.sum_le_card_nsmul _ _ 3 fun i _ ↦ ?_).trans_eq (by simp [mul_comm])
    have : (2 : ℚ) / ((i + i + 1 : ℕ) : ℚ) ≤ 2 :=
      div_le_self (by norm_num) (by exact_mod_cast Nat.le_add_left 1 (i + i))
    linarith
  have := key.2
  rw [hsum] at this
  linarith

/-- The arctangent Taylor sum is Lipschitz with constant two where `2 t ^ 2 ≤ 1`. -/
theorem abs_atanTaylor_sub_le {t s : ℚ} (ht : 2 * t ^ 2 ≤ 1) (hs : 2 * s ^ 2 ≤ 1) (m : ℕ) :
    |Enclosure.atanTaylor t m - Enclosure.atanTaylor s m| ≤ 2 * |t - s| := by
  set M := max |t| |s|
  have hM2 : M ^ 2 ≤ 1 / 2 := by
    rcases max_cases |t| |s| with ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [M, h, sq_abs] <;> linarith
  have hterm : ∀ k : ℕ, |(-1) ^ k * t ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℚ) -
      (-1) ^ k * s ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℚ)| ≤ |t - s| * (M ^ 2) ^ k := by
    intro k
    have hk : (0 : ℚ) < ((2 * k + 1 : ℕ) : ℚ) := by positivity
    rw [← sub_div, ← mul_sub, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos hk, div_le_iff₀ hk]
    calc |t ^ (2 * k + 1) - s ^ (2 * k + 1)|
        ≤ |t - s| * ((2 * k + 1 : ℕ) : ℚ) * M ^ (2 * k + 1 - 1) :=
          abs_pow_sub_pow_le (a := t) (b := s) (n := 2 * k + 1)
      _ = |t - s| * (M ^ 2) ^ k * ((2 * k + 1 : ℕ) : ℚ) := by
          rw [Nat.add_sub_cancel, ← pow_mul]; ring
  rw [Enclosure.atanTaylor, Enclosure.atanTaylor, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ k ∈ Finset.range m, |t - s| * (M ^ 2) ^ k :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ hterm k)
    _ ≤ |t - s| * 2 := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (geom_sum_le_two (by positivity) hM2 m) (abs_nonneg _)
    _ = 2 * |t - s| := by ring

/-! ### Arctangents of balls in `[-1 / √2, 1 / √2]` -/

/-- The value `±|p - n| / 2 ^ P` of the center of a ball, as a signed fraction. -/
theorem signedFrac_center (Y : GridBall) (P : ℕ) :
    signedFrac (Nat.blt Y.p Y.n) Y.mag (Nat.shiftLeft 1 P) * 2 ^ P = Y.center := by
  have hP : (0 : ℚ) < 2 ^ P := by positivity
  have hm := GridBall.cast_mag Y
  rw [GridBall.cast_center] at hm ⊢
  simp only [signedFrac, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  cases h : Nat.blt Y.p Y.n
  · have : (Y.n : ℚ) ≤ Y.p := by exact_mod_cast (by simpa [Bool.eq_false_iff] using h : Y.n ≤ Y.p)
    rw [Bool.cond_false, div_mul_cancel₀ _ hP.ne', hm, abs_of_nonneg (by linarith)]
  · have : (Y.p : ℚ) < Y.n := by exact_mod_cast Nat.blt_eq.mp h
    rw [Bool.cond_true, neg_mul, div_mul_cancel₀ _ hP.ne', hm, abs_of_neg (by linarith), neg_neg]

/-- The ball of `atanTaylor y n` from a ball `Y` of `y`: the loop at the center, widened by
twice the radius; valid when `2 (|c| + e) ^ 2 ≤ 2 ^ (2P)` for the center `c` and radius `e`. -/
def atanTaylorOfBall (P n : ℕ) (Y : GridBall) : GridBall :=
  ⟨(atanLoop P n (Nat.blt Y.p Y.n) Y.mag (Nat.shiftLeft 1 P)).sp,
    (atanLoop P n (Nat.blt Y.p Y.n) Y.mag (Nat.shiftLeft 1 P)).sn,
    Nat.add (Nat.mul 3 n) (Nat.add Y.e Y.e),
    Y.ok && oddLogOk (Nat.add Y.mag Y.e) (Nat.shiftLeft 1 P)⟩

/-- `atanTaylorOfBall P n Y` encloses `atanTaylor y n` when `Y` encloses `y`. -/
theorem atanTaylorOfBall_encloses {P n : ℕ} {Y : GridBall} {y : ℚ} (hY : Y.Encloses P y) :
    (atanTaylorOfBall P n Y).Encloses P (Enclosure.atanTaylor y n) := by
  intro hok
  simp only [atanTaylorOfBall, Bool.and_eq_true, Nat.add_eq] at hok
  obtain ⟨hYok, hbig⟩ := hok
  have hP : (0 : ℚ) < 2 ^ P := by positivity
  set z := signedFrac (Nat.blt Y.p Y.n) Y.mag (Nat.shiftLeft 1 P)
  have hzc := signedFrac_center Y P
  have hsmall : oddLogOk Y.mag (Nat.shiftLeft 1 P) = true :=
    oddLogOk_mono hbig (Nat.le_add_right _ _)
  have hloop := (atanLoop_spec (P := P) (n := n) (neg := Nat.blt Y.p Y.n) hsmall).1
  have hyz : |y - z| * 2 ^ P ≤ Y.e := by
    rw [← abs_of_pos hP, ← abs_mul, sub_mul, hzc]; exact hY hYok
  have hmag : |z| * 2 ^ P = Y.mag := by
    rw [← abs_of_pos hP, ← abs_mul, hzc, GridBall.cast_mag]
  have hz2 : 2 * z ^ 2 ≤ 1 := by
    have := sq_le_of_oddLogOk (P := P) hsmall
    rwa [show ((Y.mag : ℕ) : ℚ) / 2 ^ P = |z| by rw [← hmag]; field_simp, sq_abs] at this
  have hy2 : 2 * y ^ 2 ≤ 1 := by
    have hyabs : |y| ≤ ((Y.mag + Y.e : ℕ) : ℚ) / 2 ^ P := by
      rw [le_div_iff₀ hP]
      push_cast
      nlinarith [abs_sub_abs_le_abs_sub y z]
    nlinarith [sq_le_of_oddLogOk (P := P) hbig, sq_abs y,
      pow_le_pow_left₀ (abs_nonneg y) hyabs 2]
  have hlip := abs_atanTaylor_sub_le hy2 hz2 n
  have hcen : ((atanTaylorOfBall P n Y).center : ℚ) =
      ((atanLoop P n (Nat.blt Y.p Y.n) Y.mag (Nat.shiftLeft 1 P)).sum : ℚ) := by
    rw [GridBall.cast_center]; simp [atanTaylorOfBall, SeriesState.sum]
  have he : ((atanTaylorOfBall P n Y).e : ℚ) = 3 * n + (Y.e + Y.e) := by
    simp [atanTaylorOfBall]
  rw [hcen, he]
  have h2 := abs_sub_le (Enclosure.atanTaylor y n * 2 ^ P) (Enclosure.atanTaylor z n * 2 ^ P)
    ((atanLoop P n (Nat.blt Y.p Y.n) Y.mag (Nat.shiftLeft 1 P)).sum : ℚ)
  rw [← sub_mul, abs_mul, abs_of_pos hP] at h2
  linarith [mul_le_mul_of_nonneg_right hlip hP.le]

/-- The ball of the remainder `atanRadius y n = |y| (y ^ 2) ^ n / (1 - y ^ 2)`. -/
def atanRadiusOfBall (P n : ℕ) (Y : GridBall) : GridBall :=
  GridBall.divPos P
    (GridBall.mulNonneg P Y.abs (GridBall.powNonneg P (GridBall.sqNonneg P Y.abs) n))
    (GridBall.sub (GridBall.ofNat P 1) (GridBall.sqNonneg P Y.abs))

/-- `atanRadiusOfBall P n Y` encloses the remainder `atanRadius y n` when `Y` encloses `y`. -/
theorem atanRadiusOfBall_encloses {P n : ℕ} {Y : GridBall} {y : ℚ} (hY : Y.Encloses P y) :
    (atanRadiusOfBall P n Y).Encloses P (Enclosure.atanRadius y n) := by
  have hA := GridBall.abs_encloses hY
  have hS := GridBall.sqNonneg_encloses hA (abs_nonneg y)
  have hone := GridBall.ofNat_encloses P 1
  rw [Nat.cast_one] at hone
  have h := GridBall.divPos_encloses (GridBall.mulNonneg_encloses hA (abs_nonneg y)
    (GridBall.powNonneg_encloses hS (sq_nonneg _) n) (by positivity))
    (GridBall.sub_encloses hone hS)
  rwa [sq_abs] at h

/-- Balls of the endpoints of `Enclosure.atanSmall y d` from a ball `Y` of `y`. -/
def atanSmallOfBall (P d : ℕ) (Y : GridBall) : IntervalBalls :=
  ⟨GridBall.sub (atanTaylorOfBall P (Nat.add d 1) Y) (atanRadiusOfBall P (Nat.add d 1) Y),
    GridBall.add (atanTaylorOfBall P (Nat.add d 1) Y) (atanRadiusOfBall P (Nat.add d 1) Y)⟩

/-- `atanSmallOfBall P d Y` encloses both endpoints of `atanSmall y d` when `Y` encloses `y`. -/
theorem atanSmallOfBall_encloses {P d : ℕ} {Y : GridBall} {y : ℚ} (hY : Y.Encloses P y) :
    (atanSmallOfBall P d Y).EnclosesEnds P (Enclosure.atanSmall y d).lo
      (Enclosure.atanSmall y d).hi :=
  ⟨GridBall.sub_encloses (atanTaylorOfBall_encloses hY) (atanRadiusOfBall_encloses hY),
    GridBall.add_encloses (atanTaylorOfBall_encloses hY) (atanRadiusOfBall_encloses hY)⟩

/-- Balls of the endpoints of Machin's `Enclosure.piQuarter d`. -/
def piQuarterBalls (P d : ℕ) : IntervalBalls :=
  ⟨GridBall.sub (GridBall.scaleNat 4 (atanSmallOfBall P d (GridBall.ofFrac P false 1 5)).lo)
      (atanSmallOfBall P d (GridBall.ofFrac P false 1 239)).hi,
    GridBall.sub (GridBall.scaleNat 4 (atanSmallOfBall P d (GridBall.ofFrac P false 1 5)).hi)
      (atanSmallOfBall P d (GridBall.ofFrac P false 1 239)).lo⟩

/-- `piQuarterBalls P d` encloses both endpoints of Machin's `piQuarter d`. -/
theorem piQuarterBalls_encloses (P d : ℕ) :
    (piQuarterBalls P d).EnclosesEnds P (Enclosure.piQuarter d).lo (Enclosure.piQuarter d).hi := by
  have h5 := atanSmallOfBall_encloses (d := d) (GridBall.ofFrac_encloses P 1 5).1
  have h239 := atanSmallOfBall_encloses (d := d) (GridBall.ofFrac_encloses P 1 239).1
  simp only [Nat.cast_one, Nat.cast_ofNat] at h5 h239
  refine ⟨?_, ?_⟩ <;> simp only [piQuarterBalls, Enclosure.piQuarter, RationalInterval.sub,
    RationalInterval.add, RationalInterval.neg, RationalInterval.scaleNonnegative]
  · convert GridBall.sub_encloses (GridBall.scaleNat_encloses (c := 4) h5.1) h239.2 using 1
    ring
  · convert GridBall.sub_encloses (GridBall.scaleNat_encloses (c := 4) h5.2) h239.1 using 1
    ring

/-! ### Argument reduction -/

/-- On `[-1/2, 1/2]` FloatLib's arctangent is the series enclosure, for either sign. -/
theorem atan_eq_atanSmall {x : ℚ} (hx : |x| ≤ 1 / 2) (d : ℕ) :
    Enclosure.atan x d = Enclosure.atanSmall x d := by
  have hx' := abs_le.mp hx
  unfold Enclosure.atan
  split_ifs with hneg
  · simp only [Enclosure.atanNonnegative, show -x ≤ 1 by linarith, ↓reduceIte,
      Enclosure.atanUnit, show -x ≤ 1 / 2 by linarith]
    have hT : Enclosure.atanTaylor (-x) (d + 1) = -Enclosure.atanTaylor x (d + 1) := by
      simp only [Enclosure.atanTaylor, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Odd.neg_pow ⟨i, rfl⟩]; ring
    have hR : Enclosure.atanRadius (-x) (d + 1) = Enclosure.atanRadius x (d + 1) := by
      simp [Enclosure.atanRadius]
    simp only [Enclosure.atanSmall, RationalInterval.around, RationalInterval.neg, hT, hR]
    congr 1 <;> ring
  · simp only [Enclosure.atanNonnegative, show x ≤ 1 by linarith, ↓reduceIte, Enclosure.atanUnit,
      show x ≤ 1 / 2 by linarith]

/-- Balls of `Enclosure.atanUnit x d` from a ball `X` of `x`: the series when the ball decides
`x ≤ 1/2`, the reduction by `π/4` when it decides `x > 1/2`, the join of both otherwise. -/
def atanUnitBall (P d : ℕ) (X : GridBall) : IntervalBalls :=
  let half := GridBall.ofFrac P false 1 2
  let one := GridBall.ofNat P 1
  let small := atanSmallOfBall P d X
  let large := IntervalBalls.add (piQuarterBalls P d)
    (atanSmallOfBall P d (GridBall.divPos P (GridBall.sub X one) (GridBall.add X one)))
  Bool.rec (Bool.rec (IntervalBalls.join small large) large (GridBall.ltCertain half X)) small
    (GridBall.leCertain X half)

/-- `atanUnitBall P d X` encloses both endpoints of `atanUnit x d` when `X` encloses `x`. -/
theorem atanUnitBall_encloses {P d : ℕ} {X : GridBall} {x : ℚ} (hX : X.Encloses P x) :
    (atanUnitBall P d X).EnclosesEnds P (Enclosure.atanUnit x d).lo
      (Enclosure.atanUnit x d).hi := by
  have hhalf := (GridBall.ofFrac_encloses P 1 2).1
  simp only [Nat.cast_one, Nat.cast_ofNat] at hhalf
  have hone := GridBall.ofNat_encloses P 1
  rw [Nat.cast_one] at hone
  have hsmall := atanSmallOfBall_encloses (d := d) hX
  have hred := atanSmallOfBall_encloses (d := d)
    (GridBall.divPos_encloses (GridBall.sub_encloses hX hone) (GridBall.add_encloses hX hone))
  have hpi := piQuarterBalls_encloses P d
  have hlarge : (IntervalBalls.add (piQuarterBalls P d) _).EnclosesEnds P
      ((Enclosure.piQuarter d).add (Enclosure.atanSmall ((x - 1) / (x + 1)) d)).lo
      ((Enclosure.piQuarter d).add (Enclosure.atanSmall ((x - 1) / (x + 1)) d)).hi :=
    ⟨GridBall.add_encloses hpi.1 hred.1, GridBall.add_encloses hpi.2 hred.2⟩
  unfold atanUnitBall
  dsimp only
  cases h1 : GridBall.leCertain X (GridBall.ofFrac P false 1 2)
  · cases h2 : GridBall.ltCertain (GridBall.ofFrac P false 1 2) X
    · simpa only [Enclosure.atanUnit] using
        IntervalBalls.join_enclosesEnds_ite hsmall hlarge (x ≤ 1 / 2)
    · simpa only [Enclosure.atanUnit, (GridBall.lt_of_ltCertain hhalf hX h2).not_ge, ↓reduceIte]
        using hlarge
  · simpa only [Enclosure.atanUnit, GridBall.le_of_leCertain hX hhalf h1, ↓reduceIte]
      using hsmall

/-- Balls of `Enclosure.atanNonnegative x d` from a ball `X` of `x ≥ 0`: the unit reduction when
the ball decides `x ≤ 1`, the inversion when it decides `x > 1`, the join of both otherwise. -/
def atanNonnegBall (P d : ℕ) (X : GridBall) : IntervalBalls :=
  let one := GridBall.ofNat P 1
  let unit := atanUnitBall P d X
  let inv := IntervalBalls.sub
    ⟨GridBall.scaleNat 2 (piQuarterBalls P d).lo, GridBall.scaleNat 2 (piQuarterBalls P d).hi⟩
    (atanUnitBall P d (GridBall.inv P X))
  Bool.rec (Bool.rec (IntervalBalls.join unit inv) inv (GridBall.ltCertain one X)) unit
    (GridBall.leCertain X one)

/-- `atanNonnegBall P d X` encloses both endpoints of `atanNonnegative x d` when `X` encloses
`x`. -/
theorem atanNonnegBall_encloses {P d : ℕ} {X : GridBall} {x : ℚ} (hX : X.Encloses P x) :
    (atanNonnegBall P d X).EnclosesEnds P (Enclosure.atanNonnegative x d).lo
      (Enclosure.atanNonnegative x d).hi := by
  have hone := GridBall.ofNat_encloses P 1
  rw [Nat.cast_one] at hone
  have hunit := atanUnitBall_encloses (d := d) hX
  have hinvu := atanUnitBall_encloses (d := d) (GridBall.inv_encloses hX)
  have hpi := piQuarterBalls_encloses P d
  have hinv : (IntervalBalls.sub
      ⟨GridBall.scaleNat 2 (piQuarterBalls P d).lo, GridBall.scaleNat 2 (piQuarterBalls P d).hi⟩
      (atanUnitBall P d (GridBall.inv P X))).EnclosesEnds P
      (((Enclosure.piQuarter d).scaleNonnegative 2).sub (Enclosure.atanUnit x⁻¹ d)).lo
      (((Enclosure.piQuarter d).scaleNonnegative 2).sub (Enclosure.atanUnit x⁻¹ d)).hi := by
    refine ⟨?_, ?_⟩ <;> simp only [IntervalBalls.sub, RationalInterval.sub, RationalInterval.add,
      RationalInterval.neg, RationalInterval.scaleNonnegative]
    · convert GridBall.sub_encloses (GridBall.scaleNat_encloses (c := 2) hpi.1) hinvu.2 using 1
      push_cast
      ring
    · convert GridBall.sub_encloses (GridBall.scaleNat_encloses (c := 2) hpi.2) hinvu.1 using 1
      push_cast
      ring
  unfold atanNonnegBall
  dsimp only
  cases h1 : GridBall.leCertain X (GridBall.ofNat P 1)
  · cases h2 : GridBall.ltCertain (GridBall.ofNat P 1) X
    · simpa only [Enclosure.atanNonnegative] using
        IntervalBalls.join_enclosesEnds_ite hunit hinv (x ≤ 1)
    · simpa only [Enclosure.atanNonnegative, (GridBall.lt_of_ltCertain hone hX h2).not_ge,
        ↓reduceIte] using hinv
  · simpa only [Enclosure.atanNonnegative, GridBall.le_of_leCertain hX hone h1, ↓reduceIte]
      using hunit

/-- Every rational enclosed by `X` lies in `[-1/2, 1/2]`. -/
def halfCertain (P : ℕ) (X : GridBall) : Bool :=
  X.ok && Nat.ble (Nat.mul 2 (Nat.add X.mag X.e)) (Nat.shiftLeft 1 P)

/-- A rational enclosed by a ball with `halfCertain P X` satisfies `|x| ≤ 1 / 2`. -/
theorem abs_le_half_of_halfCertain {P : ℕ} {X : GridBall} {x : ℚ} (hX : X.Encloses P x)
    (h : halfCertain P X = true) : |x| ≤ 1 / 2 := by
  simp only [halfCertain, Bool.and_eq_true, Nat.ble_eq, Nat.mul_eq, Nat.add_eq,
    Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at h
  have hP : (0 : ℚ) < 2 ^ P := by positivity
  have hb : (2 * (X.mag + X.e) : ℚ) ≤ 2 ^ P := by exact_mod_cast h.2
  have := abs_sub_abs_le_abs_sub (x * 2 ^ P) (X.center : ℚ)
  rw [abs_mul, abs_of_pos hP, ← GridBall.cast_mag] at this
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 2)]
  nlinarith [hX h.1]

/-- Balls of `Enclosure.atan x d` from a ball `X` of `x`. -/
def atanBall (P d : ℕ) (X : GridBall) : IntervalBalls :=
  Bool.rec
    (Bool.rec
      (Bool.rec IntervalBalls.invalid (IntervalBalls.neg (atanNonnegBall P d X.neg))
        (GridBall.negCertain X))
      (atanNonnegBall P d X) (GridBall.nonnegCertain X))
    (atanSmallOfBall P d X) (halfCertain P X)

/-- **Arctangent balls.** `atanBall P d X` encloses both endpoints of FloatLib's `atan x d` for
every `x` enclosed by `X`. -/
theorem atanBall_encloses {P d : ℕ} {X : GridBall} {x : ℚ} (hX : X.Encloses P x) :
    (atanBall P d X).EnclosesEnds P (Enclosure.atan x d).lo (Enclosure.atan x d).hi := by
  unfold atanBall
  cases h1 : halfCertain P X
  · cases h2 : GridBall.nonnegCertain X
    · cases h3 : GridBall.negCertain X
      · exact ⟨GridBall.invalid_encloses P _, GridBall.invalid_encloses P _⟩
      have h := atanNonnegBall_encloses (d := d) (GridBall.neg_encloses hX)
      simp only [Enclosure.atan, GridBall.neg_of_negCertain hX h3, ↓reduceIte, RationalInterval.neg]
      exact ⟨GridBall.neg_encloses h.2, GridBall.neg_encloses h.1⟩
    · simpa only [Enclosure.atan, (GridBall.nonneg_of_nonnegCertain hX h2).not_gt, ↓reduceIte]
        using atanNonnegBall_encloses (d := d) hX
  · rw [atan_eq_atanSmall (abs_le_half_of_halfCertain hX h1)]
    exact atanSmallOfBall_encloses hX

/-! ### The interval arctangents `RationalInterval.atanRangeWith` and `atanRange` -/

/-- The lower end of `atanRangeWith I terms` is the lower end of `atan I.lo terms`. -/
theorem atanRangeWith_lo (I : Continuum.RationalInterval) (terms : ℕ) :
    (Continuum.RationalInterval.atanRangeWith I terms).lo =
      (Enclosure.atan I.lo terms).lo := by
  simp only [Continuum.RationalInterval.atanRangeWith, Continuum.AtanSplit.bounds_eq,
    Continuum.RationalInterval.ofFloatLib, Interval.atanBounds, Interval.monotoneBounds]
  split_ifs <;> rfl

/-- The upper end of `atanRangeWith I terms` is the upper end of `atan I.hi terms`. -/
theorem atanRangeWith_hi (I : Continuum.RationalInterval) (terms : ℕ) :
    (Continuum.RationalInterval.atanRangeWith I terms).hi =
      (Enclosure.atan I.hi terms).hi := by
  simp only [Continuum.RationalInterval.atanRangeWith, Continuum.AtanSplit.bounds_eq,
    Continuum.RationalInterval.ofFloatLib, Interval.atanBounds, Interval.monotoneBounds]
  split_ifs with heq
  · change (Enclosure.atan I.lo _).hi = _
    rw [show I.lo = I.hi from heq]
  · rfl

namespace IntervalBalls

/-- Balls of `atanRangeWith I terms` from balls `S` of `I`. -/
def atanRangeBall (P terms : ℕ) (S : IntervalBalls) : IntervalBalls :=
  ⟨(atanBall P terms S.lo).lo, (atanBall P terms S.hi).hi⟩

/-- `atanRangeBall P terms S` encloses `atanRangeWith I terms` when `S` encloses `I`. -/
theorem atanRangeBall_encloses {P terms : ℕ} {S : IntervalBalls}
    {I : Continuum.RationalInterval} (hS : S.Encloses P I) :
    (atanRangeBall P terms S).Encloses P
      (Continuum.RationalInterval.atanRangeWith I terms) :=
  ⟨by rw [atanRangeWith_lo]; exact (atanBall_encloses (d := terms) hS.1).1,
    by rw [atanRangeWith_hi]; exact (atanBall_encloses (d := terms) hS.2).2⟩

end IntervalBalls

end CAS.Numerics

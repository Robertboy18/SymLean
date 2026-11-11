/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.IntervalBalls
public import CAS.Numerics.GridBallSeries
public import CAS.Continuum.Interval.Elementary.Exp
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Balls for FloatLib's exact rational exponential

FloatLib's `Enclosure.exp x d` divides `x` by `2 ^ s`, `s = expScale x`, encloses the
exponential of the reduced argument `y` by the Taylor sum `∑ i ≤ d, y ^ i / i!` with the
remainder `|y| ^ (d + 1) (d + 2) / ((d + 1)! (d + 1))` (`expSmall`), and squares the interval
`s` times (`squareRepeat`). Its exact rational endpoints are enclosed by balls on the grid
`2 ^ -P`:

* `expTaylorBall P n neg a b` evaluates the Taylor sum at `±a / b` by the signed loop
  `seriesLoop`, with one error bound `3 n` for the whole sum (`expLoop_spec`);
* `expSmallFrac`, `squareRepeatBall` and `expFrac P d neg u v` mirror `expSmall`,
  `squareRepeat` and `Enclosure.exp` at the exact rational `±u / v` (`expFrac_encloses`);
* `expBall P d B` encloses `Enclosure.exp q d` for every `q` enclosed by the ball `B`, with the
  Lipschitz bound `abs_expTaylor_sub_le` of the Taylor sum on `[-1, 1]`;
* `expRangeFrac`, `expPointFrac` and `expRangeBall` mirror the interval exponential
  `RationalInterval.expRangeWith` of `CAS.Continuum.Interval.Elementary.Exp`.

## Implementation notes

We do not reimplement the exponential: the intervals are FloatLib's, and the balls only enclose
their exact endpoints, whose numerators and denominators grow quickly with the degree and the
number of squarings. The Taylor sum is evaluated by `seriesLoop`, which truncates the term and
the sum at every step; `expLoop_spec` bounds the accumulated error a priori by `3 n` units, and
that bound is the radius. For a ball argument the loop runs once, at the center, and the result
is widened by eight times the radius, since the Taylor sum is Lipschitz with constant eight on
`[-1, 1]` (`abs_expTaylor_sub_le`). The scale `expScale q` must be the same for every enclosed
`q`: `expBall` reads it off the upper end of `|q|`, and the ball is invalid unless it decides it.

At `P = 160` and degree 16 the exponential of a rational point costs about 0.8 ms in the kernel
when its absolute value is at most one, 1.1 ms near ten (four squarings), and the exponential of
a ball 1.1 ms.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>. The enclosed
  intervals are those of `FloatLib.Numerics.Enclosure.exp`, with its reduction by a power of
  two, its Taylor remainder and its repeated squaring.
* Joris van der Hoeven, "Ball arithmetic", *Logical approaches to Barriers in Computing and
  Complexity*, Preprint-Reihe Mathematik 6, Ernst-Moritz-Arndt-Universität Greifswald, 2010,
  pp. 179-208, <https://www.texmacs.org/joris/ball/ball-abs.html>. Section 3.6, (15), for the
  enclosure `B(f(c), M r)` with `M` a bound of `|f'|` over the ball, used for the Taylor sum.
* NIST Digital Library of Mathematical Functions, §4.2 Definitions, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/4.2>. Equation (4.2.19), the exponential series, whose partial sums
  `expLoop` approximates on the grid.
-/

@[expose] public section

namespace CAS.Numerics

open FloatLib.Numerics

/-- The Taylor loop of the exponential at `±a / b`: `n` steps from `2 ^ P`, the term multiplied
by `±a / (b (i + 1))` at step `i`. -/
def expLoop (P n : ℕ) (neg : Bool) (a b : ℕ) : SeriesState :=
  seriesLoop (Bool.rec a 0 neg) (Bool.rec 0 a neg) (fun i ↦ Nat.mul b (Nat.add i 1)) (fun _ ↦ 1)
    ⟨Nat.shiftLeft 1 P, 0, 0, 0⟩ n

/-- For `unitFracOk a b` (`0 < b` and `a ≤ b`), the sum of `expLoop P n neg a b` lies within `3 n`
units of `expTaylor (signedFrac neg a b) n * 2 ^ P`, and its term within `2` units of
`(signedFrac neg a b) ^ n / n! * 2 ^ P`. -/
theorem expLoop_spec {P n : ℕ} {neg : Bool} {a b : ℕ} (h : unitFracOk a b = true) :
    |Enclosure.expTaylor (signedFrac neg a b) n * 2 ^ P - (expLoop P n neg a b).sum| ≤ 3 * n ∧
      |(signedFrac neg a b) ^ n / (n.factorial : ℚ) * 2 ^ P - (expLoop P n neg a b).term| ≤ 2 := by
  simp only [unitFracOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨hb, hab⟩ := h
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  set x := signedFrac neg a b
  have hx : |x| ≤ 1 := by
    have : |x| = (a : ℚ) / b := by
      cases neg <;> simp [x, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (a : ℚ) / b)]
    rw [this, div_le_one hbq]; exact_mod_cast hab
  have hc : ((Bool.rec a 0 neg : ℕ) : ℚ) - ((Bool.rec 0 a neg : ℕ) : ℚ) = x * b := by
    cases neg <;> simp [x] <;> field_simp
  have key := seriesLoop_spec (cp := Bool.rec a 0 neg) (cn := Bool.rec 0 a neg)
    (d := fun i ↦ b * (i + 1)) (w := fun _ ↦ 1) (init := ⟨2 ^ P, 0, 0, 0⟩)
    (X := fun i ↦ x ^ i / (i.factorial : ℚ) * 2 ^ P)
    (B := fun i ↦ if i = 0 then 0 else 2)
    (fun i ↦ by
      rw [hc, Nat.factorial_succ]; push_cast
      field_simp; ring)
    (fun i ↦ by
      rw [hc]
      rcases eq_or_ne i 0 with rfl | hi
      · simp
      have hi1 : (1 : ℚ) ≤ i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
      have hd : (0 : ℚ) < ((b * (i + 1) : ℕ) : ℚ) := by positivity
      rw [ite_eq_right hi, ite_eq_right i.succ_ne_zero, abs_div, abs_mul, abs_of_pos hbq,
        abs_of_pos hd, ← le_sub_iff_add_le, div_mul_eq_mul_div, div_le_iff₀ hd]
      push_cast
      nlinarith [abs_nonneg x])
    (by simp [SeriesState.term]) ⟨rfl, rfl⟩ n
  have hloop : expLoop P n neg a b = seriesLoop (Bool.rec a 0 neg) (Bool.rec 0 a neg)
      (fun i ↦ b * (i + 1)) (fun _ ↦ 1) ⟨2 ^ P, 0, 0, 0⟩ n := by
    simp only [expLoop, Nat.mul_eq, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]
  rw [hloop]
  refine ⟨?_, ?_⟩
  · have hsum : (∑ i ∈ Finset.range n, x ^ i / (i.factorial : ℚ) * 2 ^ P / ((1 : ℕ) : ℚ)) =
        Enclosure.expTaylor x n * 2 ^ P := by
      rw [Enclosure.expTaylor, Finset.sum_mul]
      simp
    have hbound : (∑ i ∈ Finset.range n, ((if i = 0 then (0 : ℚ) else 2) / ((1 : ℕ) : ℚ) + 1)) ≤
        3 * n := (Finset.sum_le_card_nsmul _ _ 3 fun i _ ↦ by split_ifs <;> norm_num).trans_eq
          (by simp [mul_comm])
    have := key.2
    rw [hsum] at this
    linarith
  · have := key.1
    split_ifs at this <;> linarith

/-- The ball of the Taylor sum `expTaylor (±a / b) n`. -/
def expTaylorBall (P n : ℕ) (neg : Bool) (a b : ℕ) : GridBall :=
  ⟨(expLoop P n neg a b).sp, (expLoop P n neg a b).sn, Nat.mul 3 n, unitFracOk a b⟩

/-- The ball of the remainder `expRadius (±a / b) n`, from the last term of the loop. -/
def expRadiusBall (P n : ℕ) (neg : Bool) (a b : ℕ) : GridBall :=
  GridBall.mulFrac (Nat.add n 1) n
    (GridBall.abs ⟨(expLoop P n neg a b).zp, (expLoop P n neg a b).zn, 2, unitFracOk a b⟩)

/-- `expTaylorBall P n neg a b` encloses `Enclosure.expTaylor (signedFrac neg a b) n` at precision
`P`, for all arguments; the ball is valid only when `unitFracOk a b`. -/
theorem expTaylorBall_encloses (P n : ℕ) (neg : Bool) (a b : ℕ) :
    (expTaylorBall P n neg a b).Encloses P (Enclosure.expTaylor (signedFrac neg a b) n) := by
  intro h
  have := (expLoop_spec (P := P) (n := n) (neg := neg) h).1
  rw [GridBall.cast_center]
  simpa [expTaylorBall, SeriesState.sum] using this

/-- `expRadiusBall P n neg a b` encloses `Enclosure.expRadius (signedFrac neg a b) n` at precision
`P`, for all arguments; the ball is valid only when `unitFracOk a b`. -/
theorem expRadiusBall_encloses (P n : ℕ) (neg : Bool) (a b : ℕ) :
    (expRadiusBall P n neg a b).Encloses P (Enclosure.expRadius (signedFrac neg a b) n) := by
  have hz : GridBall.Encloses P ⟨(expLoop P n neg a b).zp, (expLoop P n neg a b).zn, 2,
      unitFracOk a b⟩ ((signedFrac neg a b) ^ n / (n.factorial : ℚ)) := fun h ↦ by
    rw [GridBall.cast_center]
    simpa [SeriesState.term] using (expLoop_spec (P := P) (n := n) (neg := neg) h).2
  have h := GridBall.mulFrac_encloses (a := Nat.add n 1) (b := n) (GridBall.abs_encloses hz)
  rwa [abs_div, abs_pow, Nat.abs_cast, div_mul_div_comm] at h

/-- Balls of the endpoints of `Enclosure.expSmall (±a / b) d`. -/
def expSmallFrac (P d : ℕ) (neg : Bool) (a b : ℕ) : IntervalBalls :=
  ⟨GridBall.sub (expTaylorBall P (Nat.add d 1) neg a b) (expRadiusBall P (Nat.add d 1) neg a b),
    GridBall.add (expTaylorBall P (Nat.add d 1) neg a b) (expRadiusBall P (Nat.add d 1) neg a b)⟩

/-- `expSmallFrac P d neg a b` encloses the endpoints of `Enclosure.expSmall (signedFrac neg a b) d`
at precision `P`, for all arguments. -/
theorem expSmallFrac_encloses (P d : ℕ) (neg : Bool) (a b : ℕ) :
    (expSmallFrac P d neg a b).EnclosesEnds P (Enclosure.expSmall (signedFrac neg a b) d).lo
      (Enclosure.expSmall (signedFrac neg a b) d).hi :=
  ⟨GridBall.sub_encloses (expTaylorBall_encloses P _ neg a b) (expRadiusBall_encloses P _ neg a b),
    GridBall.add_encloses (expTaylorBall_encloses P _ neg a b)
      (expRadiusBall_encloses P _ neg a b)⟩

/-- `s` squarings of balls of an interval known to contain a nonnegative value, mirroring
`RationalInterval.squareRepeat`: the lower endpoint is clamped at zero before squaring. -/
def squareRepeatBall (P : ℕ) (S : IntervalBalls) (s : ℕ) : IntervalBalls :=
  Nat.rec (motive := fun _ ↦ IntervalBalls) S
    (fun _ T ↦ ⟨GridBall.sqNonneg P T.lo.clamp, GridBall.sqNonneg P T.hi.abs⟩) s

/-- If `S` encloses the endpoints of `J` at precision `P`, then `squareRepeatBall P S s` encloses
the endpoints of `J.squareRepeat s`, for every `s`. -/
theorem squareRepeatBall_encloses {P : ℕ} {S : IntervalBalls} {J : RationalInterval}
    (hS : S.EnclosesEnds P J.lo J.hi) (s : ℕ) :
    (squareRepeatBall P S s).EnclosesEnds P (J.squareRepeat s).lo (J.squareRepeat s).hi := by
  induction s with
  | zero => exact hS
  | succ s ih =>
    have h := GridBall.sqNonneg_encloses (GridBall.abs_encloses ih.2) (abs_nonneg _)
    rw [sq_abs] at h
    exact ⟨GridBall.sqNonneg_encloses (GridBall.clamp_encloses_max ih.1) (le_max_left _ _), h⟩

/-- `q.num.natAbs / q.den` is the floor of `|q|`. -/
theorem natAbs_num_div_den (q : ℚ) : q.num.natAbs / q.den = ⌊|q|⌋₊ := by
  rw [Rat.abs_def, Rat.divInt_eq_div, Int.cast_natCast, Int.cast_natCast, Nat.floor_div_eq_div]

/-- Balls of `Enclosure.exp (±u / v) d` with the scale `s` given; valid when `0 < v` and
`u ≤ v 2 ^ s`. -/
def expCore (P d s : ℕ) (neg : Bool) (u v : ℕ) : IntervalBalls :=
  IntervalBalls.guard (Nat.blt 0 v && Nat.ble u (Nat.shiftLeft v s))
    (squareRepeatBall P (expSmallFrac P d neg u (Nat.shiftLeft v s)) s)

/-- Balls of `Enclosure.exp (±u / v) d`, with the scale `log2 ⌊u / v⌋ + 1`. -/
def expFrac (P d : ℕ) (neg : Bool) (u v : ℕ) : IntervalBalls :=
  expCore P d (Nat.add (Nat.log2 (Nat.div u v)) 1) neg u v

/-- `expFrac P d neg u v` encloses the endpoints of `Enclosure.exp (signedFrac neg u v) d` at
precision `P`, for all arguments. -/
theorem expFrac_encloses (P d : ℕ) (neg : Bool) (u v : ℕ) :
    (expFrac P d neg u v).EnclosesEnds P (Enclosure.exp (signedFrac neg u v) d).lo
      (Enclosure.exp (signedFrac neg u v) d).hi := by
  refine IntervalBalls.guard_enclosesEnds fun hok ↦ ?_
  have hv : 0 < v := Nat.blt_eq.mp (Bool.and_eq_true_iff.mp hok).1
  set s := Nat.add (Nat.log2 (Nat.div u v)) 1
  have hscale : Enclosure.expScale (signedFrac neg u v) = s := by
    have habs : |signedFrac neg u v| = (u : ℚ) / v := by
      cases neg <;> simp [abs_of_nonneg (by positivity : (0 : ℚ) ≤ (u : ℚ) / v)]
    simp only [Enclosure.expScale, natAbs_num_div_den, habs, Nat.floor_div_eq_div, s,
      Nat.add_eq, GridBall.natDiv_eq_div]
  have hy : signedFrac neg u v / 2 ^ s = signedFrac neg u (Nat.shiftLeft v s) := by
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
    have hvq : (0 : ℚ) < v := by exact_mod_cast hv
    cases neg <;> simp [signedFrac] <;> field_simp
  simp only [Enclosure.exp, hscale, hy]
  exact squareRepeatBall_encloses (expSmallFrac_encloses P d neg u (Nat.shiftLeft v s)) s

/-! ### Exponentials of balls -/

/-- `i 2 ^ i ≤ 4 i!`. -/
theorem mul_two_pow_le_factorial (i : ℕ) : i * 2 ^ i ≤ 4 * i.factorial := by
  induction i with
  | zero => simp
  | succ i ih =>
    rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i <;> simp [Nat.factorial]
    rw [Nat.factorial_succ, pow_succ]
    nlinarith [Nat.mul_le_mul_left (i + 1) ih,
      Nat.mul_le_mul_left (i + 1) (Nat.mul_le_mul_right (2 ^ i) hi)]

/-- The Taylor sum of the exponential is Lipschitz with constant eight on `[-1, 1]`. -/
theorem abs_expTaylor_sub_le {y z : ℚ} (hy : |y| ≤ 1) (hz : |z| ≤ 1) (n : ℕ) :
    |Enclosure.expTaylor y n - Enclosure.expTaylor z n| ≤ 8 * |y - z| := by
  have hterm : ∀ i : ℕ, |y ^ i / (i.factorial : ℚ) - z ^ i / (i.factorial : ℚ)| ≤
      |y - z| * (4 * (1 / 2) ^ i) := by
    intro i
    have hf : (0 : ℚ) < i.factorial := by exact_mod_cast Nat.factorial_pos i
    rw [← sub_div, abs_div, abs_of_pos hf, div_le_iff₀ hf]
    have h4 : |y ^ i - z ^ i| ≤ |y - z| * i := (abs_pow_sub_pow_le y z i).trans
      (mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by positivity) (max_le hy hz)))
    have h5 : (i : ℚ) ≤ 4 * (1 / 2) ^ i * i.factorial := by
      rw [one_div, inv_pow, mul_comm 4, mul_assoc, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
      exact_mod_cast mul_two_pow_le_factorial i
    calc |y ^ i - z ^ i| ≤ |y - z| * i := h4
      _ ≤ |y - z| * (4 * (1 / 2) ^ i * i.factorial) := by gcongr
      _ = |y - z| * (4 * (1 / 2) ^ i) * i.factorial := by ring
  rw [Enclosure.expTaylor, Enclosure.expTaylor, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ i ∈ Finset.range n, |y - z| * (4 * (1 / 2) ^ i) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ hterm i)
    _ = |y - z| * 4 * ∑ i ∈ Finset.range n, (1 / 2 : ℚ) ^ i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ ≤ |y - z| * 4 * 2 :=
        mul_le_mul_of_nonneg_left (geom_sum_le_two (by norm_num) (by norm_num) n) (by positivity)
    _ = 8 * |y - z| := by ring

/-- The ball of `expTaylor y n` from a ball `Y` of `y` with `|y| ≤ 1`: the loop at the center,
widened by eight times the radius. -/
def expTaylorOfBall (P n : ℕ) (Y : GridBall) : GridBall :=
  GridBall.guard (Y.ok && Nat.ble (Nat.add Y.mag Y.e) (Nat.shiftLeft 1 P))
    (GridBall.add (expTaylorBall P n (Nat.blt Y.p Y.n) Y.mag (Nat.shiftLeft 1 P))
      ⟨0, 0, Nat.mul 8 Y.e, true⟩)

/-- If `Y` encloses `y` at precision `P`, then `expTaylorOfBall P n Y` encloses
`Enclosure.expTaylor y n`; the result is valid only when the magnitude of the center plus the radius
is at most `2 ^ P`, which gives `|y| ≤ 1`. -/
theorem expTaylorOfBall_encloses {P n : ℕ} {Y : GridBall} {y : ℚ} (hY : Y.Encloses P y) :
    (expTaylorOfBall P n Y).Encloses P (Enclosure.expTaylor y n) := by
  refine GridBall.guard_encloses fun hchk ↦ ?_
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq,
    one_mul] at hchk
  obtain ⟨hok, hb⟩ := hchk
  have hP : (0 : ℚ) < 2 ^ P := by positivity
  set z := signedFrac (Nat.blt Y.p Y.n) Y.mag (Nat.shiftLeft 1 P)
  have hzc : z * 2 ^ P = Y.center := by
    have hm := GridBall.cast_mag Y
    rw [GridBall.cast_center] at hm ⊢
    simp only [z, signedFrac, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.cast_pow,
      Nat.cast_ofNat]
    cases h : Nat.blt Y.p Y.n
    · have : (Y.n : ℚ) ≤ Y.p := by exact_mod_cast (by simpa [Bool.eq_false_iff] using h : Y.n ≤ Y.p)
      rw [Bool.cond_false, div_mul_cancel₀ _ hP.ne', hm, abs_of_nonneg (by linarith)]
    · have : (Y.p : ℚ) < Y.n := by exact_mod_cast Nat.blt_eq.mp h
      rw [Bool.cond_true, neg_mul, div_mul_cancel₀ _ hP.ne', hm, abs_of_neg (by linarith), neg_neg]
  have hyz : |y - z| * 2 ^ P ≤ Y.e := by
    rw [← abs_of_pos hP, ← abs_mul, sub_mul, hzc]; exact hY hok
  have hbq : ((Y.mag + Y.e : ℕ) : ℚ) ≤ 2 ^ P := by exact_mod_cast hb
  push_cast at hbq
  have hmag : |z| * 2 ^ P = Y.mag := by
    rw [← abs_of_pos hP, ← abs_mul, hzc, GridBall.cast_mag]
  have hz1 : |z| ≤ 1 :=
    (mul_le_iff_le_one_left hP).mp (by rw [hmag]; linarith [Nat.cast_nonneg (α := ℚ) Y.e])
  have hy1 : |y| ≤ 1 :=
    (mul_le_iff_le_one_left hP).mp (by nlinarith [abs_sub_abs_le_abs_sub y z])
  have hlip := abs_expTaylor_sub_le hy1 hz1 n
  have hW : GridBall.Encloses P ⟨0, 0, Nat.mul 8 Y.e, true⟩
      (Enclosure.expTaylor y n - Enclosure.expTaylor z n) := by
    intro _
    simp only [GridBall.center, Nat.cast_zero, sub_zero, Int.cast_zero, Nat.mul_eq]
    push_cast
    rw [abs_mul, abs_of_pos hP]
    nlinarith
  have := GridBall.add_encloses
    (expTaylorBall_encloses P n (Nat.blt Y.p Y.n) Y.mag (Nat.shiftLeft 1 P)) hW
  rwa [add_sub_cancel] at this

/-- The ball of `expRadius y n` from a ball `Y` of `y`. -/
def expRadiusOfBall (P n : ℕ) (Y : GridBall) : GridBall :=
  GridBall.mulFrac (Nat.add n 1) (Nat.mul n.factorial n) (GridBall.powNonneg P Y.abs n)

/-- If `Y` encloses `y` at precision `P`, then `expRadiusOfBall P n Y` encloses
`Enclosure.expRadius y n`. -/
theorem expRadiusOfBall_encloses {P n : ℕ} {Y : GridBall} {y : ℚ} (hY : Y.Encloses P y) :
    (expRadiusOfBall P n Y).Encloses P (Enclosure.expRadius y n) := by
  have h := GridBall.mulFrac_encloses (a := Nat.add n 1) (b := Nat.mul n.factorial n)
    (GridBall.powNonneg_encloses (GridBall.abs_encloses hY) (abs_nonneg y) n)
  have hval : |y| ^ n * (((Nat.add n 1 : ℕ) : ℚ) / ((Nat.mul n.factorial n : ℕ) : ℚ)) =
      Enclosure.expRadius y n := by
    rw [Enclosure.expRadius, Nat.add_eq, Nat.mul_eq]; push_cast; ring
  rwa [hval] at h

/-- Balls of the endpoints of `Enclosure.expSmall y d` from a ball `Y` of `y`. -/
def expSmallOfBall (P d : ℕ) (Y : GridBall) : IntervalBalls :=
  ⟨GridBall.sub (expTaylorOfBall P (Nat.add d 1) Y) (expRadiusOfBall P (Nat.add d 1) Y),
    GridBall.add (expTaylorOfBall P (Nat.add d 1) Y) (expRadiusOfBall P (Nat.add d 1) Y)⟩

/-- If `Y` encloses `y` at precision `P`, then `expSmallOfBall P d Y` encloses the endpoints of
`Enclosure.expSmall y d`. -/
theorem expSmallOfBall_encloses {P d : ℕ} {Y : GridBall} {y : ℚ} (hY : Y.Encloses P y) :
    (expSmallOfBall P d Y).EnclosesEnds P (Enclosure.expSmall y d).lo
      (Enclosure.expSmall y d).hi :=
  ⟨GridBall.sub_encloses (expTaylorOfBall_encloses hY) (expRadiusOfBall_encloses hY),
    GridBall.add_encloses (expTaylorOfBall_encloses hY) (expRadiusOfBall_encloses hY)⟩

/-- Balls of `Enclosure.exp q d` from a ball `B` of `q`, with the scale `s` given; valid when
the ball decides `expScale q = s`. -/
def expBallCore (P d s : ℕ) (B : GridBall) : IntervalBalls :=
  IntervalBalls.guard
    (B.ok && Nat.blt (Nat.add B.mag B.e) (Nat.shiftLeft 1 (Nat.add s P)) &&
      (Nat.beq s 1 ||
        Nat.ble (Nat.add (Nat.shiftLeft 1 (Nat.add (Nat.sub s 1) P)) B.e) B.mag))
    (squareRepeatBall P (expSmallOfBall P d (GridBall.mulFrac 1 (Nat.shiftLeft 1 s) B)) s)

/-- Balls of `Enclosure.exp q d` from a ball `B` of `q`, the scale read off the upper end of
`|q|`. -/
def expBall (P d : ℕ) (B : GridBall) : IntervalBalls :=
  expBallCore P d (Nat.add (Nat.log2 (Nat.shiftRight (Nat.add B.mag B.e) P)) 1) B

/-- If `B` encloses `q` at precision `P`, then `expBallCore P d s B` encloses the endpoints of
`Enclosure.exp q d`, for every `s`; the result is valid only when the ball decides
`expScale q = s`. -/
theorem expBallCore_encloses {P d s : ℕ} {B : GridBall} {q : ℚ} (hB : B.Encloses P q) :
    (expBallCore P d s B).EnclosesEnds P (Enclosure.exp q d).lo (Enclosure.exp q d).hi := by
  refine IntervalBalls.guard_enclosesEnds fun hchk ↦ ?_
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq,
    Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at hchk
  obtain ⟨⟨hok, hup⟩, hlow⟩ := hchk
  have hP : (0 : ℚ) < 2 ^ P := by positivity
  have h1 := abs_le.mp (GridBall.abs_encloses hB hok)
  simp only [GridBall.abs, GridBall.cast_center, Nat.cast_zero, sub_zero] at h1
  have hup' : (B.mag + B.e : ℚ) < 2 ^ s * 2 ^ P := by rw [← pow_add]; exact_mod_cast hup
  have hq2 : |q| < 2 ^ s := lt_of_mul_lt_mul_right (by linarith : |q| * 2 ^ P < _) hP.le
  have hfl2 : ⌊|q|⌋₊ < 2 ^ s := (Nat.floor_lt (abs_nonneg q)).mpr (by exact_mod_cast hq2)
  have hscale : Enclosure.expScale q = s := by
    rw [Enclosure.expScale, natAbs_num_div_den]
    rcases hlow with rfl | hlow
    · interval_cases h : ⌊|q|⌋₊ <;> rfl
    have hlow' : (2 ^ (s - 1) * 2 ^ P + B.e : ℚ) ≤ B.mag := by
      rw [← pow_add]; exact_mod_cast hlow
    have hq1 : (2 : ℚ) ^ (s - 1) ≤ |q| :=
      le_of_mul_le_mul_right (by linarith : 2 ^ (s - 1) * 2 ^ P ≤ |q| * 2 ^ P) hP
    have hfl1 : 2 ^ (s - 1) ≤ ⌊|q|⌋₊ := Nat.le_floor (by exact_mod_cast hq1)
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp only [zero_tsub, pow_zero] at hfl1 hfl2
      omega
    have := (Nat.log2_eq_iff (Nat.ne_of_gt ((Nat.two_pow_pos _).trans_le hfl1))).mpr
      ⟨hfl1, by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hs0)]; exact hfl2⟩
    omega
  have hY := GridBall.mulFrac_encloses (a := 1) (b := Nat.shiftLeft 1 s) hB
  rw [show q * (((1 : ℕ) : ℚ) / ((Nat.shiftLeft 1 s : ℕ) : ℚ)) = q / 2 ^ s by
    simp [Nat.shiftLeft_eq, div_eq_mul_inv]] at hY
  simp only [Enclosure.exp, hscale]
  exact squareRepeatBall_encloses (expSmallOfBall_encloses (d := d) hY) s

/-- If `B` encloses `q` at precision `P`, then `expBall P d B` encloses the endpoints of
`Enclosure.exp q d`. -/
theorem expBall_encloses {P d : ℕ} {B : GridBall} {q : ℚ} (hB : B.Encloses P q) :
    (expBall P d B).EnclosesEnds P (Enclosure.exp q d).lo (Enclosure.exp q d).hi :=
  expBallCore_encloses hB

/-! ### The interval exponential `RationalInterval.expRangeWith` -/

/-- The lower endpoint of `expRangeWith I order`. -/
theorem expRangeWith_lo (I : Continuum.RationalInterval) (order : ℕ) :
    (Continuum.RationalInterval.expRangeWith I order).lo =
      max 0 (Enclosure.exp I.lo (max order 1)).lo := by
  simp only [Continuum.RationalInterval.expRangeWith,
    Continuum.RationalInterval.ofFloatLib, Interval.expBounds, Interval.monotoneBounds]
  split_ifs <;> rfl

/-- The upper endpoint of `expRangeWith I order`. -/
theorem expRangeWith_hi (I : Continuum.RationalInterval) (order : ℕ) :
    (Continuum.RationalInterval.expRangeWith I order).hi =
      (Enclosure.exp I.hi (max order 1)).hi := by
  simp only [Continuum.RationalInterval.expRangeWith,
    Continuum.RationalInterval.ofFloatLib, Interval.expBounds, Interval.monotoneBounds]
  split_ifs with heq
  · change (Enclosure.exp I.lo _).hi = _
    rw [show I.lo = I.hi from heq]
  · rfl

namespace IntervalBalls

/-- Balls of `expRangeWith I order` for `I.lo = ±u₁ / v₁` and `I.hi = ±u₂ / v₂`. -/
def expRangeFrac (P order : ℕ) (neg₁ : Bool) (u₁ v₁ : ℕ) (neg₂ : Bool) (u₂ v₂ : ℕ) :
    IntervalBalls :=
  ⟨(expFrac P (Nat.max order 1) neg₁ u₁ v₁).lo.clamp, (expFrac P (Nat.max order 1) neg₂ u₂ v₂).hi⟩

/-- For `I.lo = signedFrac neg₁ u₁ v₁` and `I.hi = signedFrac neg₂ u₂ v₂`, the balls
`expRangeFrac P order neg₁ u₁ v₁ neg₂ u₂ v₂` enclose `expRangeWith I order` at precision `P`. -/
theorem expRangeFrac_encloses {P order : ℕ} {neg₁ neg₂ : Bool} {u₁ v₁ u₂ v₂ : ℕ}
    {I : Continuum.RationalInterval}
    (hlo : I.lo = signedFrac neg₁ u₁ v₁) (hhi : I.hi = signedFrac neg₂ u₂ v₂) :
    (expRangeFrac P order neg₁ u₁ v₁ neg₂ u₂ v₂).Encloses P
      (Continuum.RationalInterval.expRangeWith I order) := by
  rw [Encloses, expRangeWith_lo, expRangeWith_hi, hlo, hhi]
  exact ⟨GridBall.clamp_encloses_max (expFrac_encloses P (Nat.max order 1) neg₁ u₁ v₁).1,
    (expFrac_encloses P (Nat.max order 1) neg₂ u₂ v₂).2⟩

/-- Balls of `expRangeWith (const (±u / v)) order`. -/
def expPointFrac (P order : ℕ) (neg : Bool) (u v : ℕ) : IntervalBalls :=
  ⟨(expFrac P (Nat.max order 1) neg u v).lo.clamp, (expFrac P (Nat.max order 1) neg u v).hi⟩

/-- `expPointFrac P order neg u v` encloses `expRangeWith (const (signedFrac neg u v)) order` at
precision `P`, for all arguments. -/
theorem expPointFrac_encloses (P order : ℕ) (neg : Bool) (u v : ℕ) :
    (expPointFrac P order neg u v).Encloses P
      (Continuum.RationalInterval.expRangeWith
        (Continuum.RationalInterval.const (signedFrac neg u v)) order) :=
  expRangeFrac_encloses (P := P) (order := order) rfl rfl

/-- Balls of `expRangeWith I order` from balls `S` of `I`. -/
def expRangeBall (P order : ℕ) (S : IntervalBalls) : IntervalBalls :=
  ⟨(expBall P (Nat.max order 1) S.lo).lo.clamp, (expBall P (Nat.max order 1) S.hi).hi⟩

/-- If `S` encloses `I` at precision `P`, then `expRangeBall P order S` encloses
`expRangeWith I order`. -/
theorem expRangeBall_encloses {P order : ℕ} {S : IntervalBalls}
    {I : Continuum.RationalInterval} (hS : S.Encloses P I) :
    (expRangeBall P order S).Encloses P
      (Continuum.RationalInterval.expRangeWith I order) := by
  rw [Encloses, expRangeWith_lo, expRangeWith_hi]
  exact ⟨GridBall.clamp_encloses_max (expBall_encloses (d := Nat.max order 1) hS.1).1,
    (expBall_encloses (d := Nat.max order 1) hS.2).2⟩

end IntervalBalls

end CAS.Numerics

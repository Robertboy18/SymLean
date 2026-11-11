/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.IntervalBalls
public import CAS.Continuum.Interval.Elementary.Sqrt

/-!
# Balls for the rational square-root enclosures

The interval square root `RationalInterval.sqrtPointInterval q steps` of
`CAS.Continuum.Interval.Elementary.Sqrt` encloses `√q` for `q ≥ 0` by
`⌊√(q.num q.den 4 ^ steps)⌋` divided by `q.den 2 ^ steps`, and one grid step higher unless the
root is exact; it depends on the reduced denominator of `q`.

From a ball of `q` alone the reduced denominator of `q` is unknown, but both endpoints lie within
`2 ^ -steps` of `√q`; `sqrtPointBall` and `sqrtRangeBall` enclose them on that account
(`sqrtPointBall_encloses`). Their radius is `2 ^ (P - steps)` units plus the smaller of
`√(e 2 ^ P)` and `e 2 ^ P / m` for a ball of radius `e` whose root center is `m`: the first bound
holds near zero, the second, the Lipschitz bound of the root, keeps the precision of the ball
away from zero, so that iterated roots do not halve the number of correct bits at each step.

## Implementation notes

We compute the center and both radius bounds with natural-number operations, the roots with
`Nat.sqrt` of the scaled center and radius. At `P = 160` the square root of a ball costs about
7 ms in the kernel, two integer square roots of 320-bit numbers.
-/

@[expose] public section

namespace CAS.Numerics

/-! ### Square roots of balls -/

/-- `|√x - √y| ≤ √|x - y|` for nonnegative `x` and `y`. -/
theorem abs_sqrt_sub_sqrt_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
  wlog hxy : y ≤ x generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x]; exact this hy hx (le_of_not_ge hxy)
  have hs : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt hxy
  rw [abs_of_nonneg (sub_nonneg.mpr hs), abs_of_nonneg (sub_nonneg.mpr hxy)]
  rw [Real.le_sqrt (sub_nonneg.mpr hs) (sub_nonneg.mpr hxy)]
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  have h3 : Real.sqrt y * Real.sqrt y ≤ Real.sqrt x * Real.sqrt y :=
    mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg y)
  nlinarith

/-- `|√x - √y| ≤ |x - y| / √y` for nonnegative `x` and positive `y`. -/
theorem abs_sqrt_sub_sqrt_le_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    |Real.sqrt x - Real.sqrt y| ≤ |x - y| / Real.sqrt y := by
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hsum : 0 < Real.sqrt x + Real.sqrt y := by positivity
  have hdiff : Real.sqrt x - Real.sqrt y = (x - y) / (Real.sqrt x + Real.sqrt y) := by
    rw [eq_div_iff hsum.ne']
    have h1 := Real.sq_sqrt hx
    have h2 := Real.sq_sqrt hy.le
    nlinarith
  rw [hdiff, abs_div, abs_of_pos hsum]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hsy (by linarith [Real.sqrt_nonneg x])

/-- The radius term of `sqrtEndBall` from the Lipschitz bound `|√x - √y| ≤ |x - y| / √y`, in units
of `2 ^ -P`, for a ball of radius `e` whose root center is `m`; it falls back to `r` when `m = 0`.
-/
def sqrtLipschitzRadius (P e m r : ℕ) : ℕ :=
  Bool.rec (Nat.add (Nat.div (Nat.shiftLeft e P) m) 2) r (Nat.beq m 0)

/-- The ball of an endpoint of `sqrtPointInterval q steps` from a ball `B` of `q ≥ 0`: center
`m = ⌊√(c 2 ^ P)⌋` for the clamped center `c`, radius `min (⌊√(e 2 ^ P)⌋ + 2) (⌊e 2 ^ P / m⌋ + 2)`
plus `2 ^ (P - steps)`. The first bound holds near zero, the second, from the Lipschitz constant
of the root away from zero, keeps the full precision of the ball. -/
def sqrtEndBall (P steps : ℕ) (B : GridBall) : GridBall :=
  let m := Nat.sqrt (Nat.shiftLeft (Nat.sub B.p B.n) P)
  let r := Nat.add (Nat.sqrt (Nat.shiftLeft B.e P)) 2
  ⟨m, 0, Nat.add (Nat.sub r (Nat.sub r (sqrtLipschitzRadius P B.e m r)))
      (Nat.shiftLeft 1 (Nat.sub P steps)), B.ok && Nat.ble steps P⟩

/-- If `B` encloses `q` at precision `P`, `0 ≤ q`, and the rational `w` satisfies
`|w - √q| ≤ 1 / 2 ^ steps` in `ℝ`, then `sqrtEndBall P steps B` encloses `w`. -/
theorem sqrtEndBall_encloses {P steps : ℕ} {B : GridBall} {q : ℚ} (hB : B.Encloses P q)
    (hq : 0 ≤ q) {w : ℚ} (hw : |(w : ℝ) - Real.sqrt q| ≤ 1 / 2 ^ steps) :
    (sqrtEndBall P steps B).Encloses P w := by
  intro hok
  simp only [sqrtEndBall, Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨hBok, hsP⟩ := hok
  have hc := GridBall.clamp_encloses hB hq hBok
  rw [GridBall.clamp_center] at hc
  simp only [GridBall.clamp] at hc
  set c := B.p - B.n
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hcR : |(q : ℝ) * 2 ^ P - c| ≤ B.e := by exact_mod_cast hc
  set m := Nat.sqrt (Nat.shiftLeft c P)
  set r := Nat.sqrt (Nat.shiftLeft B.e P) + 2
  have hcP : ((Nat.shiftLeft c P : ℕ) : ℝ) = c * 2 ^ P := by
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]; push_cast; ring
  have heP : ((Nat.shiftLeft B.e P : ℕ) : ℝ) = B.e * 2 ^ P := by
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]; push_cast; ring
  have hm1 : (m : ℝ) ≤ Real.sqrt (c * 2 ^ P) := by
    rw [← hcP]; exact Real.nat_sqrt_le_real_sqrt
  have hm2 : Real.sqrt (c * 2 ^ P) < m + 1 := by
    rw [← hcP]; exact Real.real_sqrt_lt_nat_sqrt_succ
  have he1 : Real.sqrt (B.e * 2 ^ P) < Nat.sqrt (Nat.shiftLeft B.e P) + 1 := by
    rw [← heP]; exact Real.real_sqrt_lt_nat_sqrt_succ
  have hsq : Real.sqrt q * 2 ^ P = Real.sqrt ((q : ℝ) * 2 ^ P * 2 ^ P) := by
    rw [mul_assoc, Real.sqrt_mul (by exact_mod_cast hq), Real.sqrt_mul_self hP.le]
  have hdist : |(q : ℝ) * 2 ^ P * 2 ^ P - c * 2 ^ P| ≤ B.e * 2 ^ P := by
    rw [← sub_mul, abs_mul, abs_of_pos hP]
    exact mul_le_mul_of_nonneg_right hcR hP.le
  have htri := abs_sub_le (Real.sqrt ((q : ℝ) * 2 ^ P * 2 ^ P)) (Real.sqrt (c * 2 ^ P)) m
  have h3 : |Real.sqrt (c * 2 ^ P) - m| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  have hroot1 : |Real.sqrt q * 2 ^ P - m| < (r : ℝ) := by
    have h1 := (abs_sqrt_sub_sqrt_le (x := (q : ℝ) * 2 ^ P * 2 ^ P) (y := c * 2 ^ P)
      (by positivity) (by positivity)).trans (Real.sqrt_le_sqrt hdist)
    rw [hsq]
    simp only [r]
    push_cast
    linarith
  have hroot2 : |Real.sqrt q * 2 ^ P - m| < (sqrtLipschitzRadius P B.e m r : ℝ) := by
    unfold sqrtLipschitzRadius
    cases hb : Nat.beq m 0
    · have hmpos := Nat.pos_of_ne_zero (Nat.ne_of_beq_eq_false hb)
      have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
      have hcpos : 0 < (c : ℝ) * 2 ^ P := Real.sqrt_pos.mp (hmR.trans_le hm1)
      have hL := (abs_sqrt_sub_sqrt_le_div (x := (q : ℝ) * 2 ^ P * 2 ^ P) (by positivity)
        hcpos).trans ((div_le_div_of_nonneg_right hdist (Real.sqrt_nonneg _)).trans
          (div_le_div_of_nonneg_left (by positivity) hmR hm1))
      have hfl := (Rat.cast_lt (K := ℝ)).mpr
        (GridBall.natDiv_bounds (Nat.shiftLeft B.e P) m hmpos).2
      push_cast [heP] at hfl
      rw [hsq]
      simp only [Nat.add_eq, GridBall.natDiv_eq_div]
      push_cast
      linarith
    · exact hroot1
  have hroot : |Real.sqrt q * 2 ^ P - m| <
      ((r - (r - sqrtLipschitzRadius P B.e m r) : ℕ) : ℝ) := by
    rw [show r - (r - sqrtLipschitzRadius P B.e m r) = min r (sqrtLipschitzRadius P B.e m r) by
      omega, Nat.cast_min]
    exact lt_min hroot1 hroot2
  have hoff : |(w : ℝ) * 2 ^ P - Real.sqrt q * 2 ^ P| ≤ 2 ^ (P - steps) := by
    rw [← sub_mul, abs_mul, abs_of_pos hP, pow_sub₀ _ two_ne_zero hsP, ← one_div,
      mul_comm (2 ^ P : ℝ)]
    exact mul_le_mul_of_nonneg_right hw hP.le
  have hcen : ((sqrtEndBall P steps B).center : ℚ) = m := by
    rw [GridBall.cast_center]; simp [sqrtEndBall, m, c]
  have he : ((sqrtEndBall P steps B).e : ℚ) =
      ((r - (r - sqrtLipschitzRadius P B.e m r) : ℕ) : ℚ) + 2 ^ (P - steps) := by
    simp only [sqrtEndBall, Nat.add_eq, Nat.sub_eq]
    rw [Nat.shiftLeft_eq' (m := 1) (n := P - steps), Nat.shiftLeft_eq]
    push_cast; ring
  rw [hcen, he]
  have hkey : |(w : ℝ) * 2 ^ P - m| ≤
      ((r - (r - sqrtLipschitzRadius P B.e m r) : ℕ) : ℝ) + 2 ^ (P - steps) := by
    linarith [abs_sub_le ((w : ℝ) * 2 ^ P) (Real.sqrt q * 2 ^ P) m]
  exact_mod_cast hkey

/-- Balls of `sqrtPointInterval q steps` from a ball `B` of `q`, valid when the ball decides the
sign of `q` and `steps ≤ P`. -/
def sqrtPointBall (P steps : ℕ) (B : GridBall) : IntervalBalls :=
  Bool.rec
    (Bool.rec IntervalBalls.invalid (IntervalBalls.const P 0) (GridBall.negCertain B))
    ⟨sqrtEndBall P steps B, sqrtEndBall P steps B⟩ (GridBall.nonnegCertain B)

/-- If `B` encloses `q` at precision `P`, then `sqrtPointBall P steps B` encloses
`sqrtPointInterval q steps`, for every `steps`. -/
theorem sqrtPointBall_encloses {P steps : ℕ} {B : GridBall} {q : ℚ} (hB : B.Encloses P q) :
    (sqrtPointBall P steps B).Encloses P
      (Continuum.RationalInterval.sqrtPointInterval q steps) := by
  unfold sqrtPointBall Continuum.RationalInterval.sqrtPointInterval
  cases h1 : GridBall.nonnegCertain B
  · cases h2 : GridBall.negCertain B
    · exact IntervalBalls.invalid_encloses _
    · rw [dite_eq_right (GridBall.neg_of_negCertain hB h2).not_ge]
      exact IntervalBalls.const_encloses 0
  · have hq := GridBall.nonneg_of_nonnegCertain hB h1
    rw [dite_eq_left hq]
    set J := Continuum.RationalInterval.sqrtNonnegativePointInterval q hq steps
    obtain ⟨hl, hh⟩ := Continuum.RationalInterval.sqrtNonnegativePointInterval_sound q hq steps
    have hw : J.hi - J.lo ≤ 1 / 2 ^ steps :=
      (Continuum.RationalInterval.sqrtNonnegativePointInterval_width_le q hq steps).trans
        (one_div_le_one_div_of_le (by positivity)
          (le_mul_of_one_le_left (by positivity) (by exact_mod_cast q.den_pos)))
    have hwR : (J.hi : ℝ) - J.lo ≤ 1 / 2 ^ steps := by
      have := (Rat.cast_le (K := ℝ)).mpr hw
      push_cast at this; exact this
    refine ⟨sqrtEndBall_encloses hB hq ?_, sqrtEndBall_encloses hB hq ?_⟩ <;> rw [abs_le] <;>
      constructor <;> linarith

/-- Balls of `sqrtRangeInterval I steps` from balls `S` of `I`. -/
def sqrtRangeBall (P steps : ℕ) (S : IntervalBalls) : IntervalBalls :=
  ⟨(sqrtPointBall P steps S.lo).lo, (sqrtPointBall P steps S.hi).hi⟩

/-- If `S` encloses `I` at precision `P`, then `sqrtRangeBall P steps S` encloses
`sqrtRangeInterval I steps`, for every `steps`. -/
theorem sqrtRangeBall_encloses {P steps : ℕ} {S : IntervalBalls}
    {I : Continuum.RationalInterval} (hS : S.Encloses P I) :
    (sqrtRangeBall P steps S).Encloses P
      (Continuum.RationalInterval.sqrtRangeInterval I steps) :=
  ⟨(sqrtPointBall_encloses hS.1).1, (sqrtPointBall_encloses hS.2).2⟩

end CAS.Numerics

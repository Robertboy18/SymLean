/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.GridBallLog
public import CAS.Numerics.GridBallExp
public import CAS.Numerics.GridBallSqrt
public import CAS.Continuum.Interval.Elementary.Rpow

/-!
# Balls for rational powers

`rpowPointBall P p q B` encloses the endpoints of `rpowPoint a q p` for every `a` enclosed by the
ball `B` (`rpowPointBall_encloses`), following the same route: Mathlib's value `0 ^ q` when the
ball is exactly zero, and otherwise, when the ball decides `a > 0`, the dyadic route for
exponents whose denominator is a power of two (`dyadicPowBall`: iterated square-root balls, a
natural power and the exact power `a ^ ⌊q⌋`) or `exp (q log a)` (`expLogPowBall`).
`IntervalBalls.rpowRatBall P p q S` encloses `rpowRat I q p` when `S` encloses `I`
(`rpowRatBall_encloses`): its balls are those of the two endpoint enclosures, in the order
given by the sign of `q`. They are invalid unless the balls decide the domain condition
`PowDomain I q` and every comparison of the route: the sign of the endpoint, and on the
exponential route the reductions of `logBall` and `expBall` (a ball inside `(1/2, 2)` needs no
logarithm reduction, and one straddling a power of two is joined).

The exponents of the weights in Appendix C.1 of Chen and Hou, Part I, applied to `|x|` (or,
halved, to `|x| ^ 2`), take the dyadic route for `-3`, `-5/2`, `-2`, `-3/2`, `-1`, `-1/2`,
`-1/4`, `1/16` and `1/4`, and `exp (q log a)` for `-2.4`, `-7/6`, `-1/6`, `1/6`, `1/7` and
`1/3 + 1e-8`.

## Main definitions

* `IntervalBalls.sqrtIterBall`: balls of `m` iterated square roots of an interval.
* `zpowBall`: the ball of the integer power `a ^ n` of a positive ball.
* `dyadicPowBall`: balls of the dyadic route `dyadicPowPoint`.
* `expLogPowBall`: balls of the exponential route `expLogPowPoint`.
* `rpowPointBall`: balls of `rpowPoint a q p`, choosing the zero, dyadic or exponential route.
* `IntervalBalls.rpowRatBall`: balls of `rpowRat I q p` from balls of `I`.

## Main results

* `rpowPointBall_encloses`: `rpowPointBall P p q B` encloses `rpowPoint a q p` when `B` encloses
  `a`.
* `IntervalBalls.rpowRatBall_encloses`: `rpowRatBall P p q S` encloses `rpowRat I q p` when `S`
  encloses `I`.
* `dyadicPowBall_encloses`, `expLogPowBall_encloses`: the two routes enclose their exact values.
* `zpowBall_encloses`: `zpowBall P n B` encloses `a ^ n` when `B` encloses `a ≥ 0`.

## Implementation notes

Both routes follow `RationalInterval.rpowPoint` step by step, with a ball operation for each
interval operation, so the enclosure theorems are compositions of those of the ball operations
and the kernel computes only balls.

At `P = 200` with 40 logarithm terms, exponential order 40 and 200 root steps, a power of a ball
costs about 160 us (`q = -5/2`), 200 us (`q = 1/16`) and 1.1 ms (`q = -12/5`) in the fast
profile, and 13 ms, 40 ms and 3.3 ms in the kernel, where `Nat.sqrt` dominates the dyadic
route. At the rational point `3/7` the measured relative widths were about `1e-59` on the dyadic
route and `1e-38` on the exponential one; the exponential route carries the truncation of the
logarithm series, `3 ^ -(2 terms)` relatively, whatever the precision `P`.

## References

* Jiajie Chen and Thomas Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D
  Euler equations with smooth data I: Analysis", arXiv:2210.07191 (2022),
  <https://arxiv.org/abs/2210.07191>. Appendix C.1 of version 4 gives the weights (C.1a)-(C.4)
  whose exponents are listed above.
-/

@[expose] public section

namespace CAS.Numerics

open CAS.Continuum

namespace IntervalBalls

/-- Balls of `sqrtIter I steps m`: `m` square roots by `sqrtRangeBall`. -/
def sqrtIterBall (P steps m : ℕ) (S : IntervalBalls) : IntervalBalls :=
  Nat.rec (motive := fun _ ↦ IntervalBalls) S (fun _ T ↦ sqrtRangeBall P steps T) m

/-- `sqrtIterBall P steps m S` encloses `sqrtIter I steps m` when `S` encloses `I`. -/
theorem sqrtIterBall_encloses {P steps : ℕ} {S : IntervalBalls} {I : RationalInterval}
    (hS : S.Encloses P I) (m : ℕ) :
    (sqrtIterBall P steps m S).Encloses P (RationalInterval.sqrtIter I steps m) := by
  induction m with
  | zero => exact hS
  | succ m ih => exact sqrtRangeBall_encloses ih

end IntervalBalls

/-- The ball of the exact rational `a ^ n` from a ball `B` of `a > 0`: a natural power, inverted
for negative `n`. -/
def zpowBall (P : ℕ) (n : ℤ) (B : GridBall) : GridBall :=
  Int.casesOn (motive := fun _ ↦ GridBall) n (fun k ↦ GridBall.powNonneg P B k)
    (fun k ↦ GridBall.inv P (GridBall.powNonneg P B (Nat.add k 1)))

/-- `zpowBall P n B` encloses `a ^ n` when `B` encloses `a ≥ 0`. -/
theorem zpowBall_encloses {P : ℕ} {B : GridBall} {a : ℚ} (hB : B.Encloses P a) (ha : 0 ≤ a)
    (n : ℤ) : (zpowBall P n B).Encloses P (a ^ n) := by
  cases n with
  | ofNat k =>
    simpa [zpowBall] using GridBall.powNonneg_encloses hB ha k
  | negSucc k =>
    simp only [zpowBall, zpow_negSucc]
    exact GridBall.inv_encloses (GridBall.powNonneg_encloses hB ha (Nat.add k 1))

/-- Balls of `dyadicPowPoint a n r m steps` from a ball `B` of `a`. -/
def dyadicPowBall (P steps : ℕ) (n : ℤ) (r m : ℕ) (B : GridBall) : IntervalBalls :=
  IntervalBalls.mul P (IntervalBalls.powNat P (IntervalBalls.sqrtIterBall P steps m ⟨B, B⟩) r)
    ⟨zpowBall P n B, zpowBall P n B⟩

/-- `dyadicPowBall P steps n r m B` encloses `dyadicPowPoint a n r m steps` when `B` encloses
`a ≥ 0`. -/
theorem dyadicPowBall_encloses {P steps : ℕ} {n : ℤ} {r m : ℕ} {B : GridBall} {a : ℚ}
    (hB : B.Encloses P a) (ha : 0 ≤ a) :
    (dyadicPowBall P steps n r m B).Encloses P (RationalInterval.dyadicPowPoint a n r m steps) := by
  exact IntervalBalls.mul_encloses (J := RationalInterval.const (a ^ n))
    (IntervalBalls.powNat_encloses (IntervalBalls.sqrtIterBall_encloses
      (I := RationalInterval.const a) ⟨hB, hB⟩ m) r)
    ⟨zpowBall_encloses hB ha n, zpowBall_encloses hB ha n⟩

/-- Balls of `expLogPowPoint a q terms order ha` from a ball `B` of `a`. -/
def expLogPowBall (P terms order : ℕ) (q : ℚ) (B : GridBall) : IntervalBalls :=
  IntervalBalls.expRangeBall P order
    (IntervalBalls.constMul q (IntervalBalls.logPointBall P terms B))

/-- `expLogPowBall P terms order q B` encloses `expLogPowPoint a q terms order` when `B` encloses
`a > 0`. -/
theorem expLogPowBall_encloses {P terms order : ℕ} {q : ℚ} {B : GridBall} {a : ℚ}
    (hB : B.Encloses P a) (ha : 0 < a) :
    (expLogPowBall P terms order q B).Encloses P
      (RationalInterval.expLogPowPoint a q terms order ha) :=
  IntervalBalls.expRangeBall_encloses
    (IntervalBalls.mulConst_encloses (IntervalBalls.logPointBall_encloses hB ha) q)

/-- Balls of `rpowPoint a q p` from a ball `B` of `a`: Mathlib's `0 ^ q` when the ball is exactly
zero, the dyadic or exponential route when it decides `a > 0`, nothing otherwise. -/
def rpowPointBall (P : ℕ) (p : RationalInterval.PowerPrecision) (q : ℚ) (B : GridBall) :
    IntervalBalls :=
  Bool.rec
    (Bool.rec IntervalBalls.invalid
      (Bool.rec (IntervalBalls.const P 0) (IntervalBalls.const P 1) (decide (q = 0)))
      (GridBall.eqRatCertain P B 0))
    (Bool.rec (expLogPowBall P p.terms p.order q B)
      (dyadicPowBall P p.steps (q.num / q.den) (q.num % q.den).toNat
        (RationalInterval.dyadicLevel q) B)
      (decide (RationalInterval.IsDyadicExponent q)))
    (GridBall.posCertain B)

/-- `rpowPointBall P p q B` encloses `rpowPoint a q p` when `B` encloses `a`. -/
theorem rpowPointBall_encloses {P : ℕ} {p : RationalInterval.PowerPrecision} {q : ℚ}
    {B : GridBall} {a : ℚ} (hB : B.Encloses P a) :
    (rpowPointBall P p q B).Encloses P (RationalInterval.rpowPoint a q p) := by
  unfold rpowPointBall RationalInterval.rpowPoint
  cases h1 : GridBall.posCertain B
  · cases h2 : GridBall.eqRatCertain P B 0
    · exact IntervalBalls.invalid_encloses _
    · have ha := GridBall.eq_of_eqRatCertain hB h2
      simp only [ha, ↓reduceIte]
      by_cases hq : q = 0
      · simpa [hq] using IntervalBalls.const_encloses (P := P) 1
      · simpa [hq] using IntervalBalls.const_encloses (P := P) 0
  · have ha := GridBall.pos_of_posCertain hB h1
    simp only [ha.ne', ↓reduceIte, ha, ↓reduceDIte]
    by_cases hd : RationalInterval.IsDyadicExponent q
    · simpa [hd] using dyadicPowBall_encloses (steps := p.steps) (n := q.num / q.den)
        (r := (q.num % q.den).toNat) (m := RationalInterval.dyadicLevel q) hB ha.le
    · simpa [hd] using expLogPowBall_encloses (terms := p.terms) (order := p.order) (q := q) hB ha

namespace IntervalBalls

/-- Balls of `rpowRat I q p` from balls `S` of `I`; invalid unless the balls decide the domain
(`0 ≤ I.lo` for `q ≥ 0`, `0 < I.lo` for `q < 0`) and the comparisons of the endpoint routes. -/
def rpowRatBall (P : ℕ) (p : RationalInterval.PowerPrecision) (q : ℚ) (S : IntervalBalls) :
    IntervalBalls :=
  Bool.rec
    (guard (GridBall.posCertain S.lo)
      ⟨(rpowPointBall P p q S.hi).lo, (rpowPointBall P p q S.lo).hi⟩)
    (guard (GridBall.nonnegCertain S.lo)
      ⟨(rpowPointBall P p q S.lo).lo, (rpowPointBall P p q S.hi).hi⟩)
    (decide (0 ≤ q))

/-- `rpowRatBall P p q S` encloses `rpowRat I q p` when `S` encloses `I`. -/
theorem rpowRatBall_encloses {P : ℕ} {p : RationalInterval.PowerPrecision} {q : ℚ}
    {S : IntervalBalls} {I : RationalInterval} (hS : S.Encloses P I) :
    (rpowRatBall P p q S).Encloses P (RationalInterval.rpowRat I q p) := by
  unfold rpowRatBall
  by_cases hq : 0 ≤ q
  · rw [decide_eq_true hq]
    refine guard_encloses fun hc ↦ ?_
    have hd : RationalInterval.PowDomain I q :=
      Or.inl ⟨hq, GridBall.nonneg_of_nonnegCertain hS.1 hc⟩
    rw [Encloses, RationalInterval.rpowRat_lo hd, RationalInterval.rpowRat_hi hd]
    simp only [RationalInterval.rpowEnds, hq, ↓reduceIte]
    exact ⟨(rpowPointBall_encloses hS.1).1, (rpowPointBall_encloses hS.2).2⟩
  · rw [decide_eq_false hq]
    refine guard_encloses fun hc ↦ ?_
    have hd : RationalInterval.PowDomain I q := Or.inr (GridBall.pos_of_posCertain hS.1 hc)
    rw [Encloses, RationalInterval.rpowRat_lo hd, RationalInterval.rpowRat_hi hd]
    simp only [RationalInterval.rpowEnds, hq, ↓reduceIte]
    exact ⟨(rpowPointBall_encloses hS.2).1, (rpowPointBall_encloses hS.1).2⟩

end IntervalBalls

end CAS.Numerics

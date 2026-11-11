/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.GridBall
public import CAS.Continuum.Interval.Rational.Arithmetic
public import CAS.Continuum.Interval.Rational.DyadicHullEndpoints
public import CAS.Continuum.Interval.Rational.FiniteSum
public import CAS.Continuum.IntervalRefinement

/-!
# Balls enclosing the endpoints of exact rational intervals

An `IntervalBalls` holds one `GridBall` for each endpoint of a `RationalInterval`. The operations
mirror those of `RationalInterval` (`const`, `add`, `sub`, `neg`, `mul`, `constMul`, `powNat`,
`invPositive`, `divPositive`, `divPositiveOrZero`, `absMax`, `hull`, `inflate`, `dyadicHull`,
`sum` through `sumNat`), and each encloses the exact result when its arguments enclose the exact
arguments (`mul_encloses` and the neighbouring theorems). A branch of an exact operation on the
sign of an endpoint is followed only when the ball decides that sign; otherwise the result is
invalid, or, for products and quotients, the operation falls back to all corner products.

## Mirroring an evaluator

An evaluator written with `RationalInterval` operations is mirrored by the same text over
`IntervalBalls` at a precision `P`, a natural number such as `160`:

* `I.add J`, `I.sub J`, `I.neg`, `I.mul J`, `I.powNat k`, `I.hull J` and `I.dyadicHull bits`
  become `S.add T`, `S.sub T`, `S.neg`, `S.mul P T`, `S.powNat P k`, `S.hull T` and
  `S.dyadicHull P bits`;
* `const q` becomes `const P q`, and a product `(const q).mul I` or `I.mul (const q)` becomes
  `constMul q S`, two scalings with the sign of `q` decided once;
* `divPositiveOrZero I J`, `I.divPositive J h` and `I.invPositive h` become
  `divPositiveOrZero P S T`, `divPositive P S T` and `invPositive P S`;
* `sum Finset.univ f` over `Fin n` and `sum (Finset.range n) f` become `sumNat P n F` for a
  function `F : ℕ → IntervalBalls`;
* the logarithm, exponential and square-root enclosures have mirrors in `GridBallLog`,
  `GridBallExp` and `GridBallSqrt`, at exact rational points given by natural numerators and
  denominators for the logarithm and the exponential (`logPointFrac`, `expPointFrac`) and at balls
  (`logRangeBall`, `expRangeBall`, `sqrtRangeBall`).

The inputs are built from natural numbers (`ofFracs`, `GridBall.ofFrac`, with `signedFrac` for
the exact value) rather than from rational literals computed per cell: a rational operation costs
the kernel about 200 us, more than a ball product. Rational literals that are the same in every
cell, such as the constants of `constMul`, are evaluated once per declaration.

## The enclosure lemma

The enclosure lemma of the mirror is proved by the same composition: one `*_encloses` lemma per
operation, in the order of the definition, from the enclosures of the inputs. For a structure of
inputs with an enclosure predicate `h : S.Encloses s` listing one `IntervalBalls.Encloses` per
field, a definition `gap s = (const 100).sub (s.x.powNat 2)` and its mirror
`gapBalls S = (const P 100).sub (S.x.powNat P 2)` give
`sub_encloses (const_encloses 100) (powNat_encloses h.x 2)`.

## Checks decided by the kernel

A check on the exact evaluator, such as `0 < (gap s).lo`, `checkBounds ends I = true` or
`(I.lo, I.hi) = ends`, becomes a Boolean test on the balls: `GridBall.posCertain`,
`checkBoundsCertain` or `GridBall.eqRatCertain` at both endpoints. For a family of cells the tests
form one closed statement `natAll count (fun k ↦ test (start + k)) = true`, proved by `cega [fast]`
(one kernel decision in the default `kernel` certificate profile, compiled evaluation in the
`fast` profile; the module needs a `public meta import` of the module defining `test`). Each
exact statement then follows from `natAll_range_spec`, the enclosure lemma and `lo_pos_of`,
`checkBounds_of_certain` or `GridBall.eq_of_eqRatCertain`. Equality certificates need balls of
radius zero: `dyadicHull` returns them when the ball decides the rounding, and `GridBall.ofFrac`
when the constant lies on the grid.

## Implementation notes

We decide certificates on the balls rather than on the exact intervals: the ball operations use
natural-number arithmetic only, which the kernel evaluates on literals, and the enclosure lemma
transfers each decided test to the exact evaluator.

Measured in `natAll` loops at `P = 160`: `add` and `sub` about 15 us, `constMul` 50 to 70 us,
`mul` about 100 us when the balls decide the signs of both factors and 330 us otherwise (four
corner products), `divPositiveOrZero` 115 us, `powNat` 110 us for the exponent two and 190 us
for three or four, `dyadicHull` 150 us. A mirror of the reserve evaluator of the canonical
De Gregorio profile, about seventy interval operations, costs 5 to 6 ms per cell.
-/

@[expose] public section

namespace CAS.Numerics

open CAS.Continuum

/-- Balls for the two endpoints of a rational interval. -/
structure IntervalBalls where
  /-- Ball of the lower endpoint. -/
  lo : GridBall
  /-- Ball of the upper endpoint. -/
  hi : GridBall

namespace IntervalBalls

/-- `S` encloses both endpoints of `I` at precision `P`. -/
def Encloses (P : ℕ) (S : IntervalBalls) (I : RationalInterval) : Prop :=
  S.lo.Encloses P I.lo ∧ S.hi.Encloses P I.hi

/-- `S` encloses the rationals `lo` and `hi` at precision `P`, for endpoints of intervals that
are not `RationalInterval`s, such as FloatLib's enclosures. -/
def EnclosesEnds (P : ℕ) (S : IntervalBalls) (lo hi : ℚ) : Prop :=
  S.lo.Encloses P lo ∧ S.hi.Encloses P hi

/-- The invalid balls, which enclose every interval vacuously (`invalid_encloses`). -/
def invalid : IntervalBalls := ⟨GridBall.invalid, GridBall.invalid⟩

/-- The balls of `S`, valid only when `b` also holds. -/
def guard (b : Bool) (S : IntervalBalls) : IntervalBalls := ⟨S.lo.guard b, S.hi.guard b⟩

/-- Balls of the singleton `{q}`. -/
def const (P : ℕ) (q : ℚ) : IntervalBalls := ⟨GridBall.ofRat P q, GridBall.ofRat P q⟩

/-- Balls of the interval with endpoints `±a / b` and `±c / d`, from natural numbers. -/
def ofFracs (P : ℕ) (negLo : Bool) (a b : ℕ) (negHi : Bool) (c d : ℕ) : IntervalBalls :=
  ⟨GridBall.ofFrac P negLo a b, GridBall.ofFrac P negHi c d⟩

/-- Endpointwise sum. -/
def add (S T : IntervalBalls) : IntervalBalls := ⟨S.lo.add T.lo, S.hi.add T.hi⟩

/-- Negation exchanges the endpoints. -/
def neg (S : IntervalBalls) : IntervalBalls := ⟨S.hi.neg, S.lo.neg⟩

/-- Difference of intervals. -/
def sub (S T : IntervalBalls) : IntervalBalls := ⟨S.lo.sub T.hi, S.hi.sub T.lo⟩

/-- Four-corner product at precision `P`. -/
def mulCorners (P : ℕ) (S T : IntervalBalls) : IntervalBalls :=
  let a := GridBall.mul P S.lo T.lo
  let b := GridBall.mul P S.lo T.hi
  let c := GridBall.mul P S.hi T.lo
  let d := GridBall.mul P S.hi T.hi
  ⟨GridBall.min (GridBall.min a b) (GridBall.min c d),
    GridBall.max (GridBall.max a b) (GridBall.max c d)⟩

/-- The product by an interval with nonnegative lower endpoint, by two corner products when the
balls decide the sign of the first interval; negated corners are formed directly. -/
def mulOfNonneg (P : ℕ) (S T : IntervalBalls) : IntervalBalls :=
  Bool.rec
    (Bool.rec (mulCorners P S T)
      ⟨GridBall.mulNonnegNegCore P (Nat.sub S.lo.n S.lo.p) S.lo.e (Nat.sub T.hi.p T.hi.n) T.hi.e
          (S.lo.ok && T.hi.ok),
        GridBall.mulNonnegNegCore P (Nat.sub S.hi.n S.hi.p) S.hi.e (Nat.sub T.lo.p T.lo.n) T.lo.e
          (S.hi.ok && T.lo.ok)⟩
      (GridBall.nonposCertain S.hi))
    ⟨GridBall.mulNonneg P S.lo T.lo, GridBall.mulNonneg P S.hi T.hi⟩
    (GridBall.nonnegCertain S.lo)

/-- The product by an interval with nonpositive upper endpoint, by two corner products when the
balls decide the sign of the first interval; negated corners are formed directly. -/
def mulOfNonpos (P : ℕ) (S T : IntervalBalls) : IntervalBalls :=
  Bool.rec
    (Bool.rec (mulCorners P S T)
      ⟨GridBall.mulNonnegCore P (Nat.sub S.hi.n S.hi.p) S.hi.e (Nat.sub T.hi.n T.hi.p) T.hi.e
          (S.hi.ok && T.hi.ok),
        GridBall.mulNonnegCore P (Nat.sub S.lo.n S.lo.p) S.lo.e (Nat.sub T.lo.n T.lo.p) T.lo.e
          (S.lo.ok && T.lo.ok)⟩
      (GridBall.nonposCertain S.hi))
    ⟨GridBall.mulNonnegNegCore P (Nat.sub S.hi.p S.hi.n) S.hi.e (Nat.sub T.lo.n T.lo.p) T.lo.e
        (S.hi.ok && T.lo.ok),
      GridBall.mulNonnegNegCore P (Nat.sub S.lo.p S.lo.n) S.lo.e (Nat.sub T.hi.n T.hi.p) T.hi.e
        (S.lo.ok && T.hi.ok)⟩
    (GridBall.nonnegCertain S.lo)

/-- The product of intervals at precision `P`: two corner products when the balls decide the
signs of both factors, four corner products otherwise. -/
def mul (P : ℕ) (S T : IntervalBalls) : IntervalBalls :=
  Bool.rec (Bool.rec (mulCorners P S T) (mulOfNonpos P S T) (GridBall.nonposCertain T.hi))
    (mulOfNonneg P S T) (GridBall.nonnegCertain T.lo)

/-- The product `(const (±a / b)).mul I` by two scalings with the fraction `a / b`. -/
def constMulFrac (neg : Bool) (a b : ℕ) (S : IntervalBalls) : IntervalBalls :=
  Bool.rec ⟨S.lo.mulFrac a b, S.hi.mulFrac a b⟩
    ⟨(S.hi.mulFrac a b).neg, (S.lo.mulFrac a b).neg⟩ neg

/-- The product `(const q).mul I` by two scalings, the sign of `q` decided once. -/
def constMul (q : ℚ) (S : IntervalBalls) : IntervalBalls :=
  constMulFrac (decide (q.num < 0)) q.num.natAbs q.den S

/-- The absolute-value range used by even powers, decided from the balls. -/
def absBounds (P : ℕ) (S : IntervalBalls) : IntervalBalls :=
  Bool.rec
    (Bool.rec
      (Bool.rec invalid
        (Bool.rec invalid ⟨GridBall.ofNat P 0, GridBall.max S.lo.neg S.hi⟩
          (GridBall.posCertain S.hi))
        (GridBall.negCertain S.lo))
      (neg S) (GridBall.nonposCertain S.hi))
    S (GridBall.nonnegCertain S.lo)

/-- Natural powers with the sharp even and odd endpoint bounds, by binary powering at
precision `P`; the square and the cube are tested first. -/
def powNat (P : ℕ) (S : IntervalBalls) (k : ℕ) : IntervalBalls :=
  Bool.rec
    (Bool.rec
      (Bool.rec ⟨GridBall.powOdd P S.lo k, GridBall.powOdd P S.hi k⟩
        (Bool.rec
          ⟨GridBall.powNonneg P (absBounds P S).lo k, GridBall.powNonneg P (absBounds P S).hi k⟩
          ⟨GridBall.ofNat P 1, GridBall.ofNat P 1⟩ (Nat.beq k 0))
        (Nat.beq (Nat.mod k 2) 0))
      ⟨GridBall.cube P S.lo, GridBall.cube P S.hi⟩ (Nat.beq k 3))
    ⟨GridBall.sqNonneg P (absBounds P S).lo, GridBall.sqNonneg P (absBounds P S).hi⟩
    (Nat.beq k 2)

/-- Reciprocal of an interval with positive lower endpoint, at precision `P`. -/
def invPositive (P : ℕ) (S : IntervalBalls) : IntervalBalls :=
  ⟨GridBall.inv P S.hi, GridBall.inv P S.lo⟩

/-- Quotient by an interval with positive lower endpoint, at precision `P`: each endpoint is one
quotient when the ball decides its sign, the extreme of two quotients otherwise. -/
def divPositive (P : ℕ) (S T : IntervalBalls) : IntervalBalls :=
  ⟨Bool.rec
      (Bool.rec (GridBall.min (GridBall.divPos P S.lo T.hi) (GridBall.divPos P S.lo T.lo))
        (GridBall.divPos P S.lo T.lo) (GridBall.nonposCertain S.lo))
      (GridBall.divPos P S.lo T.hi) (GridBall.nonnegCertain S.lo),
    Bool.rec
      (Bool.rec (GridBall.max (GridBall.divPos P S.hi T.hi) (GridBall.divPos P S.hi T.lo))
        (GridBall.divPos P S.hi T.hi) (GridBall.nonposCertain S.hi))
      (GridBall.divPos P S.hi T.lo) (GridBall.nonnegCertain S.hi)⟩

/-- Quotient by an interval with positive lower endpoint, or zero when the lower endpoint is
nonpositive, at precision `P`. -/
def divPositiveOrZero (P : ℕ) (S T : IntervalBalls) : IntervalBalls :=
  Bool.rec (Bool.rec invalid (const P 0) (GridBall.nonposCertain T.lo))
    (divPositive P S T) (GridBall.posCertain T.lo)

/-- The ball of the largest absolute endpoint. -/
def absMax (S : IntervalBalls) : GridBall := GridBall.max S.lo.abs S.hi.abs

/-- Endpointwise hull. -/
def hull (S T : IntervalBalls) : IntervalBalls :=
  ⟨GridBall.min S.lo T.lo, GridBall.max S.hi T.hi⟩

/-- Inflation by a rational radius `r`, at precision `P`. -/
def inflate (P : ℕ) (S : IntervalBalls) (r : ℚ) : IntervalBalls :=
  ⟨S.lo.sub (GridBall.ofRat P r), S.hi.add (GridBall.ofRat P r)⟩

/-- The outward rounding to the binary grid of spacing `2 ^ (-bits)`, for `bits ≤ P`. Each
endpoint ball has radius zero when it decides the rounding, and is widened by one grid step
otherwise. -/
def dyadicHull (P bits : ℕ) (S : IntervalBalls) : IntervalBalls :=
  ⟨GridBall.floorGrid P bits S.lo, GridBall.ceilGrid P bits S.hi⟩

/-- The endpointwise sum of `f 0, …, f (n - 1)`. -/
def sumNat (P n : ℕ) (f : ℕ → IntervalBalls) : IntervalBalls :=
  Nat.rec (motive := fun _ ↦ IntervalBalls) ⟨GridBall.ofNat P 0, GridBall.ofNat P 0⟩
    (fun i acc ↦ add acc (f i)) n

/-- Both endpoint bounds of `checkBounds bounds I` hold certainly. -/
def checkBoundsCertain (P : ℕ) (bounds : ℚ × ℚ) (S : IntervalBalls) : Bool :=
  GridBall.leCertain (GridBall.ofRat P bounds.1) S.lo &&
    GridBall.leCertain S.hi (GridBall.ofRat P bounds.2)

/-! ### Soundness -/

variable {P : ℕ}

/-- The invalid balls enclose every rational interval at every precision. -/
theorem invalid_encloses (I : RationalInterval) : invalid.Encloses P I :=
  ⟨GridBall.invalid_encloses P _, GridBall.invalid_encloses P _⟩

/-- If `b = true` implies that `S` encloses `I` at precision `P`, then `guard b S` encloses `I`. -/
theorem guard_encloses {b : Bool} {S : IntervalBalls} {I : RationalInterval}
    (h : b = true → S.Encloses P I) : (guard b S).Encloses P I :=
  ⟨GridBall.guard_encloses fun hb ↦ (h hb).1, GridBall.guard_encloses fun hb ↦ (h hb).2⟩

/-- If `b = true` implies that `S` encloses the rationals `lo` and `hi` at precision `P`, then
`guard b S` encloses them. -/
theorem guard_enclosesEnds {b : Bool} {S : IntervalBalls} {lo hi : ℚ}
    (h : b = true → S.EnclosesEnds P lo hi) : (guard b S).EnclosesEnds P lo hi :=
  ⟨GridBall.guard_encloses fun hb ↦ (h hb).1, GridBall.guard_encloses fun hb ↦ (h hb).2⟩

/-- `const P q` encloses the singleton `RationalInterval.const q` at precision `P`. -/
theorem const_encloses (q : ℚ) : (const P q).Encloses P (RationalInterval.const q) :=
  ⟨GridBall.ofRat_encloses P q, GridBall.ofRat_encloses P q⟩

/-- For `I.lo = signedFrac negLo a b` and `I.hi = signedFrac negHi c d`, the balls
`ofFracs P negLo a b negHi c d` enclose `I` at precision `P`. -/
theorem ofFracs_encloses {negLo negHi : Bool} {a b c d : ℕ} {I : RationalInterval}
    (hlo : I.lo = signedFrac negLo a b) (hhi : I.hi = signedFrac negHi c d) :
    (ofFracs P negLo a b negHi c d).Encloses P I :=
  ⟨hlo ▸ GridBall.ofFrac_encloses_signedFrac P negLo a b,
    hhi ▸ GridBall.ofFrac_encloses_signedFrac P negHi c d⟩

/-- If `S` encloses `I` and `T` encloses `J` at precision `P`, then `add S T` encloses `I.add J`. -/
theorem add_encloses {S T : IntervalBalls} {I J : RationalInterval} (hS : S.Encloses P I)
    (hT : T.Encloses P J) : (add S T).Encloses P (I.add J) :=
  ⟨by rw [RationalInterval.add_lo]; exact GridBall.add_encloses hS.1 hT.1,
    by rw [RationalInterval.add_hi]; exact GridBall.add_encloses hS.2 hT.2⟩

/-- If `S` encloses `I` at precision `P`, then `neg S` encloses `I.neg`. -/
theorem neg_encloses {S : IntervalBalls} {I : RationalInterval} (hS : S.Encloses P I) :
    (neg S).Encloses P I.neg :=
  ⟨by rw [RationalInterval.neg_lo]; exact GridBall.neg_encloses hS.2,
    by rw [RationalInterval.neg_hi]; exact GridBall.neg_encloses hS.1⟩

/-- If `S` encloses `I` and `T` encloses `J` at precision `P`, then `sub S T` encloses `I.sub J`. -/
theorem sub_encloses {S T : IntervalBalls} {I J : RationalInterval} (hS : S.Encloses P I)
    (hT : T.Encloses P J) : (sub S T).Encloses P (I.sub J) :=
  ⟨by rw [RationalInterval.sub_lo]; exact GridBall.sub_encloses hS.1 hT.2,
    by rw [RationalInterval.sub_hi]; exact GridBall.sub_encloses hS.2 hT.1⟩

/-- If `S` encloses `I` and `T` encloses `J` at precision `P`, then `mulCorners P S T` encloses
`I.mul J`. -/
theorem mulCorners_encloses {S T : IntervalBalls} {I J : RationalInterval}
    (hS : S.Encloses P I) (hT : T.Encloses P J) : (mulCorners P S T).Encloses P (I.mul J) := by
  have a := GridBall.mul_encloses hS.1 hT.1
  have b := GridBall.mul_encloses hS.1 hT.2
  have c := GridBall.mul_encloses hS.2 hT.1
  have d := GridBall.mul_encloses hS.2 hT.2
  rw [Encloses, RationalInterval.mul_lo, RationalInterval.mul_hi]
  exact ⟨GridBall.min_encloses (GridBall.min_encloses a b) (GridBall.min_encloses c d),
    GridBall.max_encloses (GridBall.max_encloses a b) (GridBall.max_encloses c d)⟩

/-- The corners of a product of two nonnegative intervals. -/
theorem corners_of_nonneg_nonneg {a b c d : ℚ} (hab : a ≤ b) (hcd : c ≤ d) (ha : 0 ≤ a)
    (hc : 0 ≤ c) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) = a * c ∧
      max (max (a * c) (a * d)) (max (b * c) (b * d)) = b * d := by
  have h1 : a * c ≤ a * d := mul_le_mul_of_nonneg_left hcd ha
  have h2 : a * c ≤ b * c := mul_le_mul_of_nonneg_right hab hc
  have h3 : b * c ≤ b * d := mul_le_mul_of_nonneg_left hcd (ha.trans hab)
  have h4 : a * d ≤ b * d := mul_le_mul_of_nonneg_right hab (hc.trans hcd)
  simp only [min_eq_left h1, min_eq_left h3, min_eq_left h2, max_eq_right h1, max_eq_right h3,
    max_eq_right h4, and_self]

/-- The corners of a product of a nonpositive and a nonnegative interval. -/
theorem corners_of_nonpos_nonneg {a b c d : ℚ} (hab : a ≤ b) (hcd : c ≤ d) (hb : b ≤ 0)
    (hc : 0 ≤ c) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) = a * d ∧
      max (max (a * c) (a * d)) (max (b * c) (b * d)) = b * c := by
  have h1 : a * d ≤ a * c := mul_le_mul_of_nonpos_left hcd (hab.trans hb)
  have h2 : a * c ≤ b * c := mul_le_mul_of_nonneg_right hab hc
  have h3 : b * d ≤ b * c := mul_le_mul_of_nonpos_left hcd hb
  have h4 : a * d ≤ b * d := mul_le_mul_of_nonneg_right hab (hc.trans hcd)
  simp only [min_eq_right h1, min_eq_right h3, min_eq_left h4, max_eq_left h1, max_eq_left h3,
    max_eq_right h2, and_self]

/-- The corners of a product of a nonnegative and a nonpositive interval. -/
theorem corners_of_nonneg_nonpos {a b c d : ℚ} (hab : a ≤ b) (hcd : c ≤ d) (ha : 0 ≤ a)
    (hd : d ≤ 0) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) = b * c ∧
      max (max (a * c) (a * d)) (max (b * c) (b * d)) = a * d := by
  have h1 : a * c ≤ a * d := mul_le_mul_of_nonneg_left hcd ha
  have h2 : b * c ≤ a * c := mul_le_mul_of_nonpos_right hab (hcd.trans hd)
  have h3 : b * c ≤ b * d := mul_le_mul_of_nonneg_left hcd (ha.trans hab)
  have h4 : b * d ≤ a * d := mul_le_mul_of_nonpos_right hab hd
  simp only [min_eq_left h1, min_eq_left h3, min_eq_right h2, max_eq_right h1, max_eq_right h3,
    max_eq_left h4, and_self]

/-- The corners of a product of two nonpositive intervals. -/
theorem corners_of_nonpos_nonpos {a b c d : ℚ} (hab : a ≤ b) (hcd : c ≤ d) (hb : b ≤ 0)
    (hd : d ≤ 0) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) = b * d ∧
      max (max (a * c) (a * d)) (max (b * c) (b * d)) = a * c := by
  have h1 : a * d ≤ a * c := mul_le_mul_of_nonpos_left hcd (hab.trans hb)
  have h2 : b * c ≤ a * c := mul_le_mul_of_nonpos_right hab (hcd.trans hd)
  have h3 : b * d ≤ b * c := mul_le_mul_of_nonpos_left hcd hb
  have h4 : b * d ≤ a * d := mul_le_mul_of_nonpos_right hab hd
  simp only [min_eq_right h1, min_eq_right h3, min_eq_right h4, max_eq_left h1, max_eq_left h3,
    max_eq_left h2, and_self]

/-- If `S` encloses `I` and `T` encloses `J` at precision `P` and `0 ≤ J.lo`, then
`mulOfNonneg P S T` encloses `I.mul J`. -/
theorem mulOfNonneg_encloses {S T : IntervalBalls} {I J : RationalInterval}
    (hS : S.Encloses P I) (hT : T.Encloses P J) (hJ : 0 ≤ J.lo) :
    (mulOfNonneg P S T).Encloses P (I.mul J) := by
  unfold mulOfNonneg
  cases h1 : GridBall.nonnegCertain S.lo
  · cases h2 : GridBall.nonposCertain S.hi
    · exact mulCorners_encloses hS hT
    have hI : I.hi ≤ 0 := GridBall.nonpos_of_nonposCertain hS.2 h2
    obtain ⟨hlo, hhi⟩ := corners_of_nonpos_nonneg I.hle J.hle hI hJ
    rw [Encloses, RationalInterval.mul_lo, RationalInterval.mul_hi, hlo, hhi,
      show I.lo * J.hi = -(-I.lo * J.hi) by ring, show I.hi * J.lo = -(-I.hi * J.lo) by ring]
    exact ⟨GridBall.neg_encloses (GridBall.mulNonneg_encloses (GridBall.neg_encloses hS.1)
        (by linarith [I.hle]) hT.2 (hJ.trans J.hle)),
      GridBall.neg_encloses (GridBall.mulNonneg_encloses (GridBall.neg_encloses hS.2)
        (by linarith) hT.1 hJ)⟩
  · have hI : 0 ≤ I.lo := GridBall.nonneg_of_nonnegCertain hS.1 h1
    obtain ⟨hlo, hhi⟩ := corners_of_nonneg_nonneg I.hle J.hle hI hJ
    rw [Encloses, RationalInterval.mul_lo, RationalInterval.mul_hi, hlo, hhi]
    exact ⟨GridBall.mulNonneg_encloses hS.1 hI hT.1 hJ,
      GridBall.mulNonneg_encloses hS.2 (hI.trans I.hle) hT.2 (hJ.trans J.hle)⟩

/-- If `S` encloses `I` and `T` encloses `J` at precision `P` and `J.hi ≤ 0`, then
`mulOfNonpos P S T` encloses `I.mul J`. -/
theorem mulOfNonpos_encloses {S T : IntervalBalls} {I J : RationalInterval}
    (hS : S.Encloses P I) (hT : T.Encloses P J) (hJ : J.hi ≤ 0) :
    (mulOfNonpos P S T).Encloses P (I.mul J) := by
  unfold mulOfNonpos
  cases h1 : GridBall.nonnegCertain S.lo
  · cases h2 : GridBall.nonposCertain S.hi
    · exact mulCorners_encloses hS hT
    have hI : I.hi ≤ 0 := GridBall.nonpos_of_nonposCertain hS.2 h2
    obtain ⟨hlo, hhi⟩ := corners_of_nonpos_nonpos I.hle J.hle hI hJ
    rw [Encloses, RationalInterval.mul_lo, RationalInterval.mul_hi, hlo, hhi,
      ← neg_mul_neg I.hi J.hi, ← neg_mul_neg I.lo J.lo]
    exact ⟨GridBall.mulNonneg_neg_neg P S.hi T.hi ▸ GridBall.mulNonneg_encloses
        (GridBall.neg_encloses hS.2) (by linarith) (GridBall.neg_encloses hT.2) (by linarith),
      GridBall.mulNonneg_neg_neg P S.lo T.lo ▸ GridBall.mulNonneg_encloses
        (GridBall.neg_encloses hS.1) (by linarith [I.hle]) (GridBall.neg_encloses hT.1)
        (by linarith [J.hle])⟩
  · have hI : 0 ≤ I.lo := GridBall.nonneg_of_nonnegCertain hS.1 h1
    obtain ⟨hlo, hhi⟩ := corners_of_nonneg_nonpos I.hle J.hle hI hJ
    rw [Encloses, RationalInterval.mul_lo, RationalInterval.mul_hi, hlo, hhi,
      show I.hi * J.lo = -(I.hi * -J.lo) by ring, show I.lo * J.hi = -(I.lo * -J.hi) by ring]
    exact ⟨GridBall.neg_encloses (GridBall.mulNonneg_encloses hS.2 (hI.trans I.hle)
        (GridBall.neg_encloses hT.1) (by linarith [J.hle])),
      GridBall.neg_encloses (GridBall.mulNonneg_encloses hS.1 hI
        (GridBall.neg_encloses hT.2) (by linarith))⟩

/-- If `S` encloses `I` and `T` encloses `J` at precision `P`, then `mul P S T` encloses
`I.mul J`. -/
theorem mul_encloses {S T : IntervalBalls} {I J : RationalInterval} (hS : S.Encloses P I)
    (hT : T.Encloses P J) : (mul P S T).Encloses P (I.mul J) := by
  unfold mul
  cases h1 : GridBall.nonnegCertain T.lo
  · cases h2 : GridBall.nonposCertain T.hi
    · exact mulCorners_encloses hS hT
    · exact mulOfNonpos_encloses hS hT (GridBall.nonpos_of_nonposCertain hT.2 h2)
  · exact mulOfNonneg_encloses hS hT (GridBall.nonneg_of_nonnegCertain hT.1 h1)

/-- The endpoints of `(const q).mul I`. -/
theorem const_mul_endpoints (q : ℚ) (I : RationalInterval) :
    ((RationalInterval.const q).mul I).lo = min (q * I.lo) (q * I.hi) ∧
      ((RationalInterval.const q).mul I).hi = max (q * I.lo) (q * I.hi) := by
  constructor <;> simp only [RationalInterval.mul_lo, RationalInterval.mul_hi,
    RationalInterval.const_lo, RationalInterval.const_hi, min_self, max_self]

/-- If `S` encloses `I` at precision `P` and `q = signedFrac neg a b`, then `constMulFrac neg a b S`
encloses `(const q).mul I`. -/
theorem constMulFrac_encloses {S : IntervalBalls} {I : RationalInterval} (hS : S.Encloses P I)
    {neg : Bool} {a b : ℕ} {q : ℚ} (hq : q = signedFrac neg a b) :
    (constMulFrac neg a b S).Encloses P ((RationalInterval.const q).mul I) := by
  obtain ⟨hlo, hhi⟩ := const_mul_endpoints q I
  have hab : (0 : ℚ) ≤ (a : ℚ) / b := by positivity
  subst hq
  cases neg
  · have h1 := mul_le_mul_of_nonneg_left I.hle hab
    rw [Encloses, hlo, hhi, signedFrac_false, min_eq_left h1, max_eq_right h1, mul_comm _ I.lo,
      mul_comm _ I.hi]
    exact ⟨GridBall.mulFrac_encloses hS.1, GridBall.mulFrac_encloses hS.2⟩
  · have h1 := mul_le_mul_of_nonpos_left I.hle (neg_nonpos.mpr hab)
    rw [Encloses, hlo, hhi, signedFrac_true, min_eq_right h1, max_eq_left h1, neg_mul, neg_mul,
      mul_comm _ I.hi, mul_comm _ I.lo]
    exact ⟨GridBall.neg_encloses (GridBall.mulFrac_encloses hS.2),
      GridBall.neg_encloses (GridBall.mulFrac_encloses hS.1)⟩

/-- A rational is `±|num| / den` with the sign of its numerator. -/
theorem rat_eq_signedFrac (q : ℚ) :
    q = signedFrac (decide (q.num < 0)) q.num.natAbs q.den := by
  rcases lt_or_ge q.num 0 with h | h
  · simp [h, abs_of_neg, neg_div, Rat.num_div_den]
  · simp [not_lt.mpr h, abs_of_nonneg h, Rat.num_div_den]

/-- If `S` encloses `I` at precision `P`, then `constMul q S` encloses `(const q).mul I`, for every
rational `q`. -/
theorem constMul_encloses {S : IntervalBalls} {I : RationalInterval} (hS : S.Encloses P I)
    (q : ℚ) : (constMul q S).Encloses P ((RationalInterval.const q).mul I) :=
  constMulFrac_encloses hS (rat_eq_signedFrac q)

/-- `I.mul (const q)` and `(const q).mul I` have the same endpoints. -/
theorem mul_const_eq (q : ℚ) (I : RationalInterval) :
    I.mul (RationalInterval.const q) = (RationalInterval.const q).mul I := by
  apply RationalInterval.ext <;> simp [mul_comm]

/-- If `S` encloses `I` at precision `P`, then `constMul q S` encloses `I.mul (const q)`, for every
rational `q`. -/
theorem mulConst_encloses {S : IntervalBalls} {I : RationalInterval} (hS : S.Encloses P I)
    (q : ℚ) : (constMul q S).Encloses P (I.mul (RationalInterval.const q)) := by
  rw [mul_const_eq]; exact constMul_encloses hS q

/-- Binary powering `npowBinRec k x` of a rational `x` is `x ^ k`. -/
theorem npowBinRec_eq_pow (k : ℕ) (x : ℚ) : npowBinRec k x = x ^ k := by
  induction k with
  | zero => rw [npowBinRec_zero, pow_zero]
  | succ k ih => rw [npowBinRec_succ, ih, pow_succ]

/-- If `S` encloses `I` at precision `P`, then `absBounds P S` encloses both endpoints of FloatLib's
absolute-value range `Interval.absBounds I.toFloatLib`. -/
theorem absBounds_encloses {S : IntervalBalls} {I : RationalInterval} (hS : S.Encloses P I) :
    GridBall.Encloses P (absBounds P S).lo (FloatLib.Numerics.Interval.absBounds I.toFloatLib).lo ∧
      GridBall.Encloses P (absBounds P S).hi
        (FloatLib.Numerics.Interval.absBounds I.toFloatLib).hi := by
  unfold absBounds FloatLib.Numerics.Interval.absBounds
  cases h1 : GridBall.nonnegCertain S.lo
  · cases h3 : GridBall.nonposCertain S.hi
    · cases h2 : GridBall.negCertain S.lo
      · exact ⟨GridBall.invalid_encloses P _, GridBall.invalid_encloses P _⟩
      cases h4 : GridBall.posCertain S.hi
      · exact ⟨GridBall.invalid_encloses P _, GridBall.invalid_encloses P _⟩
      have hlo : ¬ 0 ≤ I.toFloatLib.lo := not_le.mpr (GridBall.neg_of_negCertain hS.1 h2)
      have hhi : ¬ I.toFloatLib.hi ≤ 0 := not_le.mpr (GridBall.pos_of_posCertain hS.2 h4)
      simp only [hlo, hhi, ↓reduceIte]
      exact ⟨by simpa using GridBall.ofNat_encloses P 0,
        GridBall.max_encloses (GridBall.neg_encloses hS.1) hS.2⟩
    · have hhi : I.toFloatLib.hi ≤ 0 := GridBall.nonpos_of_nonposCertain hS.2 h3
      simp only [hhi, ↓reduceIte]
      split_ifs with hlo
      · have h0 : I.lo = -I.hi := by linarith [I.hle]
        have h0' : I.hi = -I.lo := by linarith [I.hle]
        exact ⟨h0 ▸ GridBall.neg_encloses hS.2, h0' ▸ GridBall.neg_encloses hS.1⟩
      · exact ⟨GridBall.neg_encloses hS.2, GridBall.neg_encloses hS.1⟩
  · simp only [show 0 ≤ I.toFloatLib.lo from GridBall.nonneg_of_nonnegCertain hS.1 h1,
      ↓reduceIte]
    exact hS

/-- Both endpoints of the absolute-value range are nonnegative. -/
theorem absBounds_nonneg (I : RationalInterval) :
    0 ≤ (FloatLib.Numerics.Interval.absBounds I.toFloatLib).lo ∧
      0 ≤ (FloatLib.Numerics.Interval.absBounds I.toFloatLib).hi := by
  unfold FloatLib.Numerics.Interval.absBounds
  split_ifs with h1 h2
  · exact ⟨h1, h1.trans I.hle⟩
  · exact ⟨neg_nonneg.mpr h2, neg_nonneg.mpr (I.hle.trans h2)⟩
  · exact ⟨le_rfl, (not_le.mp h2).le.trans (le_max_right _ _)⟩

/-- If `S` encloses `I` at precision `P`, then `powNat P S k` encloses `I.powNat k`, for every
`k`. -/
theorem powNat_encloses {S : IntervalBalls} {I : RationalInterval} (hS : S.Encloses P I)
    (k : ℕ) : (powNat P S k).Encloses P (I.powNat k) := by
  have hA := absBounds_encloses (P := P) hS
  have hN := absBounds_nonneg I
  change (powNat P S k).lo.Encloses P (FloatLib.Numerics.Interval.powBounds I.toFloatLib k).lo ∧
    (powNat P S k).hi.Encloses P (FloatLib.Numerics.Interval.powBounds I.toFloatLib k).hi
  unfold powNat FloatLib.Numerics.Interval.powBounds
  cases h2 : Nat.beq k 2
  · cases h3 : Nat.beq k 3
    · cases he : Nat.beq (Nat.mod k 2) 0
      · have hodd : k % 2 = 1 := Nat.mod_two_ne_zero.mp (Nat.ne_of_beq_eq_false he)
        simp only [show k ≠ 0 by omega, hodd, one_ne_zero, ↓reduceIte, npowBinRec_eq_pow]
        exact ⟨GridBall.powOdd_encloses hS.1 hodd, GridBall.powOdd_encloses hS.2 hodd⟩
      have he : k % 2 = 0 := Nat.eq_of_beq_eq_true he
      cases h0 : Nat.beq k 0
      · simp only [Nat.ne_of_beq_eq_false h0, he, ↓reduceIte, npowBinRec_eq_pow]
        exact ⟨GridBall.powNonneg_encloses hA.1 hN.1 k, GridBall.powNonneg_encloses hA.2 hN.2 k⟩
      obtain rfl := Nat.eq_of_beq_eq_true h0
      simp only [↓reduceIte, FloatLib.Numerics.Interval.point]
      exact ⟨by simpa using GridBall.ofNat_encloses P 1, by simpa using GridBall.ofNat_encloses P 1⟩
    obtain rfl := Nat.eq_of_beq_eq_true h3
    simp only [npowBinRec_eq_pow]
    exact ⟨GridBall.cube_encloses hS.1, GridBall.cube_encloses hS.2⟩
  obtain rfl := Nat.eq_of_beq_eq_true h2
  simp only [↓reduceIte, npowBinRec_eq_pow]
  exact ⟨GridBall.sqNonneg_encloses hA.1 hN.1, GridBall.sqNonneg_encloses hA.2 hN.2⟩

/-- If `S` encloses `I` at precision `P` and `0 < I.lo`, then `invPositive P S` encloses
`I.invPositive hI`. -/
theorem invPositive_encloses {S : IntervalBalls} {I : RationalInterval} (hS : S.Encloses P I)
    (hI : 0 < I.lo) : (invPositive P S).Encloses P (I.invPositive hI) := by
  refine ⟨?_, ?_⟩
  · rw [RationalInterval.invPositive_lo, one_div]; exact GridBall.inv_encloses hS.2
  · rw [RationalInterval.invPositive_hi, one_div]; exact GridBall.inv_encloses hS.1

/-- The endpoints of a quotient by an interval with positive lower endpoint. -/
theorem divPositive_endpoints (I J : RationalInterval) (hJ : 0 < J.lo) :
    (I.divPositive J hJ).lo = min (I.lo / J.hi) (I.lo / J.lo) ∧
      (I.divPositive J hJ).hi = max (I.hi / J.hi) (I.hi / J.lo) := by
  have h1 := div_le_div_of_nonneg_right I.hle (hJ.trans_le J.hle).le
  have h2 := div_le_div_of_nonneg_right I.hle hJ.le
  simp only [RationalInterval.divPositive, RationalInterval.mul_lo, RationalInterval.mul_hi,
    RationalInterval.invPositive_lo, RationalInterval.invPositive_hi, ← div_eq_mul_one_div]
  exact ⟨min_eq_left (le_min (h1.trans' (min_le_left _ _)) (h2.trans' (min_le_right _ _))),
    max_eq_right (max_le (h1.trans (le_max_left _ _)) (h2.trans (le_max_right _ _)))⟩

/-- If `S` encloses `I` and `T` encloses `J` at precision `P` and `0 < J.lo`, then
`divPositive P S T` encloses `I.divPositive J hJ`. -/
theorem divPositive_encloses {S T : IntervalBalls} {I J : RationalInterval}
    (hS : S.Encloses P I) (hT : T.Encloses P J) (hJ : 0 < J.lo) :
    (divPositive P S T).Encloses P (I.divPositive J hJ) := by
  obtain ⟨hlo, hhi⟩ := divPositive_endpoints I J hJ
  unfold divPositive Encloses
  rw [hlo, hhi]
  refine ⟨?_, ?_⟩
  · cases h1 : GridBall.nonnegCertain S.lo
    · cases h2 : GridBall.nonposCertain S.lo
      · exact GridBall.min_encloses (GridBall.divPos_encloses hS.1 hT.2)
          (GridBall.divPos_encloses hS.1 hT.1)
      have hI := neg_nonneg.mpr (GridBall.nonpos_of_nonposCertain hS.1 h2)
      rw [min_eq_right (by simpa [neg_div] using div_le_div_of_nonneg_left hI hJ J.hle)]
      exact GridBall.divPos_encloses hS.1 hT.1
    · have hI := GridBall.nonneg_of_nonnegCertain hS.1 h1
      rw [min_eq_left (div_le_div_of_nonneg_left hI hJ J.hle)]
      exact GridBall.divPos_encloses hS.1 hT.2
  · cases h1 : GridBall.nonnegCertain S.hi
    · cases h2 : GridBall.nonposCertain S.hi
      · exact GridBall.max_encloses (GridBall.divPos_encloses hS.2 hT.2)
          (GridBall.divPos_encloses hS.2 hT.1)
      have hI := neg_nonneg.mpr (GridBall.nonpos_of_nonposCertain hS.2 h2)
      rw [max_eq_left (by simpa [neg_div] using div_le_div_of_nonneg_left hI hJ J.hle)]
      exact GridBall.divPos_encloses hS.2 hT.2
    · have hI := GridBall.nonneg_of_nonnegCertain hS.2 h1
      rw [max_eq_right (div_le_div_of_nonneg_left hI hJ J.hle)]
      exact GridBall.divPos_encloses hS.2 hT.1

/-- If `S` encloses `I` and `T` encloses `J` at precision `P`, then `divPositiveOrZero P S T`
encloses `RationalInterval.divPositiveOrZero I J`. -/
theorem divPositiveOrZero_encloses {S T : IntervalBalls} {I J : RationalInterval}
    (hS : S.Encloses P I) (hT : T.Encloses P J) :
    (divPositiveOrZero P S T).Encloses P (RationalInterval.divPositiveOrZero I J) := by
  unfold divPositiveOrZero RationalInterval.divPositiveOrZero
  cases h1 : GridBall.posCertain T.lo
  · cases h2 : GridBall.nonposCertain T.lo
    · exact invalid_encloses _
    · rw [dite_eq_right (GridBall.nonpos_of_nonposCertain hT.1 h2).not_gt]
      exact const_encloses 0
  · rw [dite_eq_left (GridBall.pos_of_posCertain hT.1 h1)]
    exact divPositive_encloses hS hT _

/-- If `S` encloses `I` at precision `P`, then the ball `absMax S` encloses `I.absMax`. -/
theorem absMax_encloses {S : IntervalBalls} {I : RationalInterval} (hS : S.Encloses P I) :
    (absMax S).Encloses P I.absMax := by
  rw [RationalInterval.absMax_eq_max]
  exact GridBall.max_encloses (GridBall.abs_encloses hS.1) (GridBall.abs_encloses hS.2)

/-- If `S` encloses `I` and `T` encloses `J` at precision `P`, then `hull S T` encloses
`I.hull J`. -/
theorem hull_encloses {S T : IntervalBalls} {I J : RationalInterval} (hS : S.Encloses P I)
    (hT : T.Encloses P J) : (hull S T).Encloses P (I.hull J) :=
  ⟨by rw [RationalInterval.hull_lo]; exact GridBall.min_encloses hS.1 hT.1,
    by rw [RationalInterval.hull_hi]; exact GridBall.max_encloses hS.2 hT.2⟩

/-- If `S` encloses `I` at precision `P` and `0 ≤ r`, then `inflate P S r` encloses
`I.inflate r hr`. -/
theorem inflate_encloses {S : IntervalBalls} {I : RationalInterval} (hS : S.Encloses P I)
    (r : ℚ) (hr : 0 ≤ r) : (inflate P S r).Encloses P (I.inflate r hr) :=
  ⟨GridBall.sub_encloses hS.1 (GridBall.ofRat_encloses P r),
    GridBall.add_encloses hS.2 (GridBall.ofRat_encloses P r)⟩

/-- If `S` encloses `I` at precision `P`, then `dyadicHull P bits S` encloses `I.dyadicHull bits`,
for every `bits`; for `P < bits` the balls are invalid. -/
theorem dyadicHull_encloses {bits : ℕ} {S : IntervalBalls} {I : RationalInterval}
    (hS : S.Encloses P I) : (dyadicHull P bits S).Encloses P (I.dyadicHull bits) :=
  ⟨by rw [RationalInterval.dyadicHull_lo]; exact GridBall.floorGrid_encloses hS.1,
    by rw [RationalInterval.dyadicHull_hi]; exact GridBall.ceilGrid_encloses hS.2⟩

/-- The lower ball of `sumNat P n f` is `GridBall.sumNat` of the lower balls of `f`. -/
theorem sumNat_lo (n : ℕ) (f : ℕ → IntervalBalls) :
    (sumNat P n f).lo = GridBall.sumNat P n (fun i ↦ (f i).lo) := by
  induction n with
  | zero => rfl
  | succ n ih => change (add (sumNat P n f) (f n)).lo = _; rw [add, ih]; rfl

/-- The upper ball of `sumNat P n f` is `GridBall.sumNat` of the upper balls of `f`. -/
theorem sumNat_hi (n : ℕ) (f : ℕ → IntervalBalls) :
    (sumNat P n f).hi = GridBall.sumNat P n (fun i ↦ (f i).hi) := by
  induction n with
  | zero => rfl
  | succ n ih => change (add (sumNat P n f) (f n)).hi = _; rw [add, ih]; rfl

/-- If `f i` encloses `g i` at precision `P` for every `i < n`, then `sumNat P n f` encloses
`RationalInterval.sum (Finset.range n) g`. -/
theorem sumNat_encloses_range {n : ℕ} {f : ℕ → IntervalBalls} {g : ℕ → RationalInterval}
    (h : ∀ i < n, (f i).Encloses P (g i)) :
    (sumNat P n f).Encloses P (RationalInterval.sum (Finset.range n) g) := by
  refine ⟨?_, ?_⟩
  · rw [sumNat_lo]
    exact GridBall.sumNat_encloses (g := fun i ↦ (g i).lo) fun i hi ↦ (h i hi).1
  · rw [sumNat_hi]
    exact GridBall.sumNat_encloses (g := fun i ↦ (g i).hi) fun i hi ↦ (h i hi).2

/-- If `S` encloses `I` at precision `P` and `GridBall.posCertain S.lo`, then `0 < I.lo`. -/
theorem lo_pos_of {S : IntervalBalls} {I : RationalInterval} (hS : S.Encloses P I)
    (h : GridBall.posCertain S.lo = true) : 0 < I.lo :=
  GridBall.pos_of_posCertain hS.1 h

/-- If `S` encloses `I` at precision `P` and `leCertain (ofRat P q) S.lo`, then `q ≤ I.lo`. -/
theorem le_lo_of {S : IntervalBalls} {I : RationalInterval} (hS : S.Encloses P I) {q : ℚ}
    (h : GridBall.leCertain (GridBall.ofRat P q) S.lo = true) : q ≤ I.lo :=
  GridBall.le_of_leCertain (GridBall.ofRat_encloses P q) hS.1 h

/-- If `S` encloses `I` at precision `P` and `leCertain S.hi (ofRat P q)`, then `I.hi ≤ q`. -/
theorem hi_le_of {S : IntervalBalls} {I : RationalInterval} (hS : S.Encloses P I) {q : ℚ}
    (h : GridBall.leCertain S.hi (GridBall.ofRat P q) = true) : I.hi ≤ q :=
  GridBall.le_of_leCertain hS.2 (GridBall.ofRat_encloses P q) h

/-- If `S` encloses `I` at precision `P` and `checkBoundsCertain P bounds S`, then
`RationalInterval.checkBounds bounds I = true`. -/
theorem checkBounds_of_certain {S : IntervalBalls} {I : RationalInterval}
    (hS : S.Encloses P I) {bounds : ℚ × ℚ} (h : checkBoundsCertain P bounds S = true) :
    RationalInterval.checkBounds bounds I = true := by
  simp only [checkBoundsCertain, Bool.and_eq_true] at h
  simp only [RationalInterval.checkBounds, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨le_lo_of hS h.1, hi_le_of hS h.2⟩

end IntervalBalls

end CAS.Numerics

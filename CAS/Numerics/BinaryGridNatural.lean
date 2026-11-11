/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridRuntime
import Mathlib.Tactic.Positivity.Finset

/-!
# FloatLib's binary grid on natural intervals

FloatLib's binary-grid arithmetic works with integer intervals. On intervals with natural
endpoints it agrees exactly with natural-number operations: products take the smallest and
largest of the four corner products, the downward rounding of `z / 2 ^ p` is `z >>> p` and the
upward rounding is `ceilShift p z`, and the outward quotient by a positive natural number is the
floor and the ceiling (`ceilDiv`). The theorems `mul_natInterval`, `square_natInterval`,
`divideNat_natInterval` and `divBounds_eq_natInterval` state these identities, and
`enclose_natCast_div`, `scaleRat_natInterval` and `pow_natInterval_nine` give in the same way the
enclosure of a quotient of natural numbers, the scaling by a nonnegative rational `FN / FD` and
the ninth power. On ordered intervals the corner products reduce to the products of equal
endpoints (`natMul_eq_ord`, `natSquare_eq_ord`), the ninth power of every natural interval is
`natPowNineOrd` (`natPowNine_eq_ord`), and every operation keeps the endpoints ordered.

## Implementation notes

We state each identity as an equation between a FloatLib operation and a natural-number
definition, so a checker replays a FloatLib evaluation with natural-number arithmetic, which the
kernel evaluates on literals, and FloatLib's enclosure theorems apply to the result.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>. The binary-grid
  interval operations that the natural-number definitions restate.
-/

@[expose] public section

namespace CAS.Numerics

open FloatLib.Numerics FloatLib.Numerics.Interval

/-- An interval with natural endpoints, as an integer interval. -/
def natInterval (I : ℕ × ℕ) : Interval ℤ := ⟨I.1, I.2⟩

/-- The lower endpoint of `natInterval I` is `I.1`, cast to `ℤ`. -/
@[simp] theorem natInterval_lo (I : ℕ × ℕ) : (natInterval I).lo = I.1 := rfl

/-- The upper endpoint of `natInterval I` is `I.2`, cast to `ℤ`. -/
@[simp] theorem natInterval_hi (I : ℕ × ℕ) : (natInterval I).hi = I.2 := rfl

/-- The ceiling of `a / b`, for a positive `b`. -/
def ceilDiv (a b : ℕ) : ℕ := Nat.div (Nat.add a (Nat.sub b 1)) b

/-- The ceiling of `a / 2 ^ p`. -/
def ceilShift (p a : ℕ) : ℕ := Nat.shiftRight (Nat.add a (Nat.sub (Nat.shiftLeft 1 p) 1)) p

/-- The sum of two natural intervals. -/
def natAdd (I J : ℕ × ℕ) : ℕ × ℕ := (Nat.add I.1 J.1, Nat.add I.2 J.2)

/-- FloatLib's product of two natural intervals at `p` fractional bits. -/
def natMul (p : ℕ) (I J : ℕ × ℕ) : ℕ × ℕ :=
  let a := Nat.mul I.1 J.1
  let b := Nat.mul I.1 J.2
  let c := Nat.mul I.2 J.1
  let d := Nat.mul I.2 J.2
  (Nat.shiftRight (Nat.min (Nat.min a b) (Nat.min c d)) p,
    ceilShift p (Nat.max (Nat.max a b) (Nat.max c d)))

/-- FloatLib's square of a natural interval at `p` fractional bits. -/
def natSquare (p : ℕ) (I : ℕ × ℕ) : ℕ × ℕ :=
  let a := Nat.mul I.1 I.1
  let b := Nat.mul I.2 I.2
  (Nat.shiftRight a p, ceilShift p (Nat.max a b))

/-- FloatLib's outward quotient of a natural interval by a positive natural number. -/
def natDivide (I : ℕ × ℕ) (n : ℕ) : ℕ × ℕ := (Nat.div I.1 n, ceilDiv I.2 n)

/-- `ceilDiv a b` is `(a + (b - 1)) / b`. -/
theorem ceilDiv_eq (a b : ℕ) : ceilDiv a b = (a + (b - 1)) / b := rfl

/-- `ceilShift p a` is `ceilDiv a (2 ^ p)`. -/
theorem ceilShift_eq (p a : ℕ) : ceilShift p a = ceilDiv a (2 ^ p) := by
  rw [ceilShift, ceilDiv, Nat.shiftLeft_eq', Nat.one_shiftLeft]
  exact Nat.shiftRight_eq_div_pow _ _

/-- The ceiling is the floor, plus one unless the division is exact. -/
theorem ceilDiv_eq_ite {a b : ℕ} (hb : 0 < b) :
    ceilDiv a b = if a / b * b = a then a / b else a / b + 1 := by
  rw [ceilDiv_eq, Nat.add_div hb, Nat.div_eq_of_lt (by omega : b - 1 < b),
    Nat.mod_eq_of_lt (by omega : b - 1 < b)]
  have := Nat.div_add_mod' a b
  have := Nat.mod_lt a hb
  split_ifs <;> omega

/-- For `0 < b`, `a ≤ b * ceilDiv a b`. -/
theorem le_mul_ceilDiv {a b : ℕ} (hb : 0 < b) : a ≤ b * ceilDiv a b := by
  rw [ceilDiv_eq]
  have := Nat.lt_div_mul_add (a := a + (b - 1)) hb
  rw [Nat.mul_comm]
  omega

/-- For `0 < b`, `b * ceilDiv a b < a + b`. -/
theorem mul_ceilDiv_lt {a b : ℕ} (hb : 0 < b) : b * ceilDiv a b < a + b := by
  rw [ceilDiv_eq]
  have := Nat.div_mul_le_self (a + (b - 1)) b
  rw [Nat.mul_comm]
  omega

/-- The Euclidean quotient of a negated natural number is the negated ceiling. -/
theorem neg_natCast_ediv (a b : ℕ) :
    (-(a : ℤ)) / (b : ℤ) = -((ceilDiv a b : ℕ) : ℤ) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [ceilDiv_eq]
  have h1 := le_mul_ceilDiv (a := a) hb
  have h2 := mul_ceilDiv_lt (a := a) hb
  refine ((Int.ediv_emod_unique (r := (b : ℤ) * ceilDiv a b - a) (by exact_mod_cast hb)).mpr
    ⟨by ring, ?_, ?_⟩).1 <;> omega

/-- FloatLib's `BinaryGrid.roundDown p` of a natural number `a` is `a >>> p`. -/
theorem roundDown_natCast (p a : ℕ) :
    BinaryGrid.roundDown p (a : ℤ) = ((Nat.shiftRight a p : ℕ) : ℤ) := rfl

/-- FloatLib's `BinaryGrid.roundUp p` of a natural number `a` is `ceilShift p a`. -/
theorem roundUp_natCast (p a : ℕ) :
    BinaryGrid.roundUp p (a : ℤ) = ((ceilShift p a : ℕ) : ℤ) := by
  unfold BinaryGrid.roundUp
  rw [Int.shiftRight_eq_div_pow, ceilShift_eq, neg_natCast_ediv, neg_neg]

/-- FloatLib's `BinaryGrid.add` of two natural intervals is `natAdd`. -/
theorem add_natInterval (I J : ℕ × ℕ) :
    BinaryGrid.add (natInterval I) (natInterval J) = natInterval (natAdd I J) := by
  simp [BinaryGrid.add, natInterval, natAdd]

/-- FloatLib's `BinaryGrid.mul p` of two natural intervals is `natMul p`. -/
theorem mul_natInterval (p : ℕ) (I J : ℕ × ℕ) :
    BinaryGrid.mul p (natInterval I) (natInterval J) = natInterval (natMul p I J) := by
  unfold BinaryGrid.mul natMul
  simp only [natInterval, minOfFour, maxOfFour, ← Nat.cast_mul, ← Nat.cast_min, ← Nat.cast_max,
    roundDown_natCast, roundUp_natCast]
  rfl

/-- FloatLib's `BinaryGrid.square p` of a natural interval is `natSquare p`. -/
theorem square_natInterval (p : ℕ) (I : ℕ × ℕ) :
    BinaryGrid.square p (natInterval I) = natInterval (natSquare p I) := by
  unfold BinaryGrid.square natSquare
  simp only [natInterval, Int.natCast_nonneg, ↓reduceIte, ← Nat.cast_mul, ← Nat.cast_max,
    roundDown_natCast, roundUp_natCast]
  rfl

/-- FloatLib's `BinaryGrid.abs` leaves every natural interval unchanged. -/
theorem abs_natInterval (I : ℕ × ℕ) : BinaryGrid.abs (natInterval I) = natInterval I := by
  unfold BinaryGrid.abs
  simp [natInterval]

/-- FloatLib's `Enclosure.BinaryGrid.divideNat` of a natural interval by `n` is `natDivide I n`, for
every natural `n`. -/
theorem divideNat_natInterval (I : ℕ × ℕ) (n : ℕ) :
    Enclosure.BinaryGrid.divideNat (natInterval I) n = natInterval (natDivide I n) := by
  rw [Enclosure.BinaryGrid.divideNat_eq_direct]
  unfold Enclosure.BinaryGrid.Internal.divideNat natDivide
  simp only [natInterval, neg_natCast_ediv, neg_neg]
  rfl

/-- FloatLib's outward integer quotient depends only on the rational value of `a / b`. -/
theorem divBounds_eq_natInterval {a b : ℤ} (hb : 0 < b) {A B : ℕ} (hB : 0 < B)
    (h : (a : ℚ) / b = A / B) :
    BinaryGrid.divBounds a b = natInterval (A / B, ceilDiv A B) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = n := ⟨b.toNat, (Int.toNat_of_nonneg hb.le).symm⟩
  have hn : (0 : ℚ) < n := by exact_mod_cast hb
  have hB' : (0 : ℚ) < B := by exact_mod_cast hB
  have h' : (a : ℚ) / (n : ℚ) = A / B := by simpa using h
  have hfloor : a.fdiv n = ((A / B : ℕ) : ℤ) := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg n), ← Rat.floor_intCast_div_natCast, h',
      Rat.floor_natCast_div_natCast]
    rfl
  have hcond : ((A / B : ℕ) : ℤ) * (n : ℤ) = a ↔ A / B * B = A := by
    rw [← @Int.cast_inj ℚ, ← @Nat.cast_inj ℚ, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
      Nat.cast_mul, ← eq_div_iff hn.ne', ← eq_div_iff hB'.ne', h']
  unfold BinaryGrid.divBounds
  simp only [hfloor, natInterval, ceilDiv_eq_ite hB, hcond]
  split_ifs <;> rfl

/-- Enclosing a quotient of natural numbers takes the floor and the ceiling on the grid. -/
theorem enclose_natCast_div (p A B : ℕ) :
    BinaryGrid.enclose p ((A : ℚ) / B) =
      natInterval (Nat.shiftLeft A p / B, ceilDiv (Nat.shiftLeft A p) B) := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp only [BinaryGrid.enclose, BinaryGrid.divBounds, ceilDiv, natInterval]
    simp [show ∀ n : ℕ, n.div 0 = 0 from Nat.div_zero]
  unfold BinaryGrid.enclose
  apply divBounds_eq_natInterval (by exact_mod_cast ((A : ℚ) / B).den_pos) hB
  rw [Int.shiftLeft_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Int.cast_mul, Int.cast_pow,
    mul_div_right_comm, Int.cast_natCast, Rat.num_div_den, Nat.cast_mul, Nat.cast_pow]
  push_cast
  ring

/-- Scaling by a nonnegative rational `FN / FD` takes the floor and the ceiling of the scaled
endpoints. -/
theorem scaleRat_natInterval (I : ℕ × ℕ) {f : ℚ} {FN FD : ℕ}
    (hf : f = (FN : ℚ) / FD) :
    Enclosure.BinaryGrid.scaleRat (natInterval I) f =
      natInterval (I.1 * FN / FD, ceilDiv (I.2 * FN) FD) := by
  rcases Nat.eq_zero_or_pos FD with rfl | hFD
  · simp only [Nat.cast_zero, div_zero] at hf
    subst hf
    simp [Enclosure.BinaryGrid.scaleRat, natInterval, BinaryGrid.divBounds, ceilDiv,
      show ∀ n : ℕ, n.div 0 = 0 from Nat.div_zero]
  have hf0 : 0 ≤ f := by rw [hf]; positivity
  have hden : (0 : ℤ) < f.den := by exact_mod_cast f.den_pos
  have hval (x : ℕ) : ((x * f.num : ℤ) : ℚ) / (f.den : ℤ) = ((x * FN : ℕ) : ℚ) / FD := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, mul_div_assoc, Rat.num_div_den, hf,
      Nat.cast_mul, mul_div_assoc]
  unfold Enclosure.BinaryGrid.scaleRat
  simp only [natInterval, hf0, ↓reduceIte, divBounds_eq_natInterval hden hFD (hval _)]

/-- The ninth power of FloatLib's repeated squaring: three squares and one product. -/
def natPowNineAt (p : ℕ) (I : ℕ × ℕ) : ℕ × ℕ :=
  natMul p (natSquare p (natSquare p (natSquare p I))) I

/-- FloatLib's ninth power of a natural interval; the endpoints of a nondegenerate interval are
powered separately. -/
def natPowNine (p : ℕ) (I : ℕ × ℕ) : ℕ × ℕ :=
  cond (Nat.beq I.1 I.2) (natPowNineAt p I)
    ((natPowNineAt p (I.1, I.1)).1, (natPowNineAt p (I.2, I.2)).2)

/-- FloatLib's repeated squaring `BinaryGrid.Internal.pow p I 9` is three squares of `I` followed by
one product with `I`, for every integer interval `I`. -/
theorem internalPow_nine (p : ℕ) (I : Interval ℤ) :
    BinaryGrid.Internal.pow p I 9 =
      BinaryGrid.mul p (BinaryGrid.square p (BinaryGrid.square p (BinaryGrid.square p I))) I := by
  rw [BinaryGrid.Internal.pow, BinaryGrid.Internal.pow, BinaryGrid.Internal.pow,
    BinaryGrid.Internal.pow]
  simp

/-- FloatLib's ninth power `BinaryGrid.pow p` of a natural interval is `natPowNine p`. -/
theorem pow_natInterval_nine (p : ℕ) (I : ℕ × ℕ) :
    BinaryGrid.pow p (natInterval I) 9 = natInterval (natPowNine p I) := by
  have hat (J : ℕ × ℕ) : BinaryGrid.Internal.pow p (natInterval J) 9 =
      natInterval (natPowNineAt p J) := by
    rw [internalPow_nine, square_natInterval, square_natInterval, square_natInterval,
      mul_natInterval]
    rfl
  unfold BinaryGrid.pow natPowNine
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
  cases hb : Nat.beq I.1 I.2
  · rw [ite_eq_right (by simpa [natInterval] using Nat.ne_of_beq_eq_false hb), Bool.cond_false]
    change (⟨(BinaryGrid.Internal.pow p (natInterval (I.1, I.1)) 9).lo,
      (BinaryGrid.Internal.pow p (natInterval (I.2, I.2)) 9).hi⟩ : Interval ℤ) = _
    rw [hat, hat]
    rfl
  · rw [ite_eq_left (by simp [natInterval, Nat.eq_of_beq_eq_true hb]), hat, Bool.cond_true]

/-! ### Ordered natural intervals -/

/-- The product of two ordered natural intervals: the products of equal endpoints, rounded
outward. -/
def natMulOrd (p : ℕ) (I J : ℕ × ℕ) : ℕ × ℕ :=
  (Nat.shiftRight (Nat.mul I.1 J.1) p, ceilShift p (Nat.mul I.2 J.2))

/-- The square of an ordered natural interval. -/
def natSquareOrd (p : ℕ) (I : ℕ × ℕ) : ℕ × ℕ :=
  (Nat.shiftRight (Nat.mul I.1 I.1) p, ceilShift p (Nat.mul I.2 I.2))

/-- The ninth power of an ordered natural interval by three squares and one product. -/
def natPowNineOrd (p : ℕ) (I : ℕ × ℕ) : ℕ × ℕ :=
  natMulOrd p (natSquareOrd p (natSquareOrd p (natSquareOrd p I))) I

/-- The floor `a / b` is at most `ceilDiv a b`. -/
theorem div_le_ceilDiv (a b : ℕ) : a / b ≤ ceilDiv a b := by
  rw [ceilDiv_eq]
  exact Nat.div_le_div_right (by omega)

/-- For `a ≤ b`, `a >>> p ≤ ceilShift p b`. -/
theorem shiftRight_le_ceilShift {a b : ℕ} (h : a ≤ b) (p : ℕ) :
    Nat.shiftRight a p ≤ ceilShift p b := by
  rw [ceilShift_eq]
  change a >>> p ≤ _
  rw [Nat.shiftRight_eq_div_pow]
  exact (Nat.div_le_div_right h).trans (div_le_ceilDiv b _)

/-- For `I.1 ≤ I.2` and `J.1 ≤ J.2`, `natMul p I J` is `natMulOrd p I J`. -/
theorem natMul_eq_ord (p : ℕ) {I J : ℕ × ℕ} (hI : I.1 ≤ I.2) (hJ : J.1 ≤ J.2) :
    natMul p I J = natMulOrd p I J := by
  have h1 : I.1 * J.1 ≤ I.1 * J.2 := Nat.mul_le_mul_left _ hJ
  have h2 : I.1 * J.1 ≤ I.2 * J.1 := Nat.mul_le_mul_right _ hI
  have h3 : I.2 * J.1 ≤ I.2 * J.2 := Nat.mul_le_mul_left _ hJ
  have h4 : I.1 * J.2 ≤ I.2 * J.2 := Nat.mul_le_mul_right _ hI
  simp only [natMul, natMulOrd, Nat.mul_eq]
  congr 2
  · change min (min (I.1 * J.1) (I.1 * J.2)) (min (I.2 * J.1) (I.2 * J.2)) = I.1 * J.1
    omega
  · change max (max (I.1 * J.1) (I.1 * J.2)) (max (I.2 * J.1) (I.2 * J.2)) = I.2 * J.2
    omega

/-- For `I.1 ≤ I.2`, `natSquare p I` is `natSquareOrd p I`. -/
theorem natSquare_eq_ord (p : ℕ) {I : ℕ × ℕ} (hI : I.1 ≤ I.2) :
    natSquare p I = natSquareOrd p I := by
  have h : I.1 * I.1 ≤ I.2 * I.2 := Nat.mul_le_mul hI hI
  simp only [natSquare, natSquareOrd, Nat.mul_eq]
  congr 2
  change max (I.1 * I.1) (I.2 * I.2) = I.2 * I.2
  omega

/-- For `I.1 ≤ I.2` and `J.1 ≤ J.2`, the endpoints of `natMulOrd p I J` are ordered. -/
theorem natMulOrd_ordered (p : ℕ) {I J : ℕ × ℕ} (hI : I.1 ≤ I.2) (hJ : J.1 ≤ J.2) :
    (natMulOrd p I J).1 ≤ (natMulOrd p I J).2 :=
  shiftRight_le_ceilShift (Nat.mul_le_mul hI hJ) p

/-- For `I.1 ≤ I.2`, the endpoints of `natSquareOrd p I` are ordered. -/
theorem natSquareOrd_ordered (p : ℕ) {I : ℕ × ℕ} (hI : I.1 ≤ I.2) :
    (natSquareOrd p I).1 ≤ (natSquareOrd p I).2 :=
  shiftRight_le_ceilShift (Nat.mul_le_mul hI hI) p

/-- For `I.1 ≤ I.2` and `J.1 ≤ J.2`, the endpoints of `natAdd I J` are ordered. -/
theorem natAdd_ordered {I J : ℕ × ℕ} (hI : I.1 ≤ I.2) (hJ : J.1 ≤ J.2) :
    (natAdd I J).1 ≤ (natAdd I J).2 :=
  Nat.add_le_add hI hJ

/-- For `I.1 ≤ I.2`, the endpoints of `natDivide I n` are ordered, for every `n`. -/
theorem natDivide_ordered {I : ℕ × ℕ} (hI : I.1 ≤ I.2) (n : ℕ) :
    (natDivide I n).1 ≤ (natDivide I n).2 :=
  (Nat.div_le_div_right hI).trans (div_le_ceilDiv _ _)

/-- For `I.1 ≤ I.2`, the endpoints of `natPowNineOrd p I` are ordered. -/
theorem natPowNineOrd_ordered (p : ℕ) {I : ℕ × ℕ} (hI : I.1 ≤ I.2) :
    (natPowNineOrd p I).1 ≤ (natPowNineOrd p I).2 :=
  natMulOrd_ordered p (natSquareOrd_ordered p (natSquareOrd_ordered p (natSquareOrd_ordered p hI)))
    hI

/-- FloatLib's ninth power of a natural interval is the ordered power `natPowNineOrd`. -/
theorem natPowNine_eq_ord (p : ℕ) (I : ℕ × ℕ) :
    natPowNine p I = natPowNineOrd p I := by
  have hord (J : ℕ × ℕ) (hJ : J.1 ≤ J.2) : natPowNineAt p J = natPowNineOrd p J := by
    have h1 := natSquareOrd_ordered p hJ
    have h2 := natSquareOrd_ordered p h1
    unfold natPowNineAt natPowNineOrd
    rw [natSquare_eq_ord p hJ, natSquare_eq_ord p h1, natSquare_eq_ord p h2,
      natMul_eq_ord p (natSquareOrd_ordered p h2) hJ]
  unfold natPowNine
  cases h : Nat.beq I.1 I.2
  · rw [Bool.cond_false, hord _ le_rfl, hord _ le_rfl]
    rfl
  · rw [Bool.cond_true, hord I (le_of_eq (Nat.eq_of_beq_eq_true h))]

/-- For `I.1 ≤ I.2`, multiplying `I` by the grid unit, the point
`(Nat.shiftLeft 1 p, Nat.shiftLeft 1 p)` that is `1` at `p` fractional bits, returns `I`:
`natMul p (Nat.shiftLeft 1 p, Nat.shiftLeft 1 p) I = I`. -/
theorem natMul_unit (p : ℕ) {I : ℕ × ℕ} (hI : I.1 ≤ I.2) :
    natMul p (Nat.shiftLeft 1 p, Nat.shiftLeft 1 p) I = I := by
  rw [natMul_eq_ord p le_rfl hI]
  unfold natMulOrd
  have h1 : Nat.shiftLeft 1 p = 2 ^ p := by rw [Nat.shiftLeft_eq', Nat.one_shiftLeft]
  have hp : 0 < 2 ^ p := by positivity
  simp only [h1, Nat.mul_eq]
  ext
  · change (2 ^ p * I.1) >>> p = I.1
    rw [Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ hp]
  · change ceilShift p (2 ^ p * I.2) = I.2
    rw [ceilShift_eq, ceilDiv_eq_ite hp, Nat.mul_div_cancel_left _ hp, Nat.mul_comm,
      ite_eq_left rfl]

/-- Multiplying by the zero interval gives the zero interval. -/
theorem natMul_zero (p : ℕ) (I : ℕ × ℕ) : natMul p I (0, 0) = (0, 0) := by
  have h : ceilShift p 0 = 0 := by
    rw [ceilShift_eq, ceilDiv_eq_ite (by positivity)]
    simp
  simp only [natMul, Nat.mul_eq, Nat.mul_zero]
  ext
  · exact Nat.zero_shiftRight p
  · change ceilShift p (max (max 0 0) (max 0 0)) = 0
    simpa using h

end CAS.Numerics

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PairChecks
import Mathlib.Tactic.Positivity.Finset

/-!
# Balls on a binary grid enclosing exact rationals

A `GridBall` is a center `p - n` and a radius `e`, natural numbers in units of `2 ^ -P`, with a
validity flag. It encloses a rational `q` at precision `P` when `|q 2 ^ P - (p - n)| ≤ e`
(`GridBall.Encloses`). Sums, products, quotients, reciprocals, minima and maxima of enclosed
rationals are enclosed by balls computed with natural-number operations only (`add_encloses`,
`mul_encloses`, `divPos_encloses`, `inv_encloses`, `min_encloses`, `max_encloses`); the radius
absorbs the truncations. A certificate can thus bound an exact rational computation, whose own
rationals grow without bound, at the cost of a few natural operations per step: a strict sign
of the enclosed rational, or an order between two of them, follows from the balls
(`pos_of_posCertain`, `le_of_leCertain`), and an equality with a rational literal from a ball of
radius zero (`eq_of_eqCertain`).

A step that needs a decision the ball cannot make, such as the sign of a denominator, clears the
validity flag. An invalid ball encloses every rational vacuously (`invalid_encloses`), so it
carries no information: the operations pass the cleared flag on, and every certificate test on
an invalid ball fails.

## Implementation notes

We use midpoint-radius arithmetic on a fixed grid, so the numbers stay near `P` bits plus the
integer part however long the computation runs. Every center is computed by right shifts or
divisions that lose less than one unit each, and the radius adds an a priori bound for that loss
to the classical radius of the exact operation. For balls of centers `x`, `y` and radii `r`, `s`
the product radius is `(|x| + r) s + r |y|`; `mul` truncates it and adds two units, one for the
center and one for the radius. `inv` adds `r / (z (z - r))`, the largest change of `1 / z` over
the ball of center `z` and radius `r`, and `divPos` the corresponding bound for a quotient; both
need `z > r` (`posCertain`). The soundness theorems compare the exact rational result with the
truncated one directly, so nothing depends on a floating-point rounding mode. The center is
split into a positive and a negative part so that every operation is an operation on natural
numbers.

The kernel evaluates natural-number operations on literals with arbitrary-precision arithmetic,
in about one to two microseconds each, while each unfolding of a definition, projection or
`match` costs about as much again. The operations are therefore written without branches where
truncated subtraction suffices (`mag`, `min`, `max`), and the products of balls known to enclose
nonnegative rationals (`mulNonneg`, `sqNonneg`) skip the sign bookkeeping of `mul`. Measured in
a `natAll` loop over 1000 balls of 160 bits: `add` about 5 us, `min` and `max` 12 us, `mulFrac`
14 us, `sqNonneg` 21 us, `mulNonneg` 24 us, `inv` 30 us, `mul` 36 us, `divPos` 46 us,
`floorGrid` 50 us.

## References

* Joris van der Hoeven, "Ball arithmetic", *Logical approaches to Barriers in Computing and
  Complexity*, Preprint-Reihe Mathematik 6, Ernst-Moritz-Arndt-Universität Greifswald, 2010,
  pp. 179-208, <https://www.texmacs.org/joris/ball/ball-abs.html>. Section 3.1, (7), for the
  product of balls; Section 3.2 for a rounded center whose error bound is added to the radius,
  and for a flag that marks a possibly invalid ball.
* Lean 4, release v4.35.0, <https://github.com/leanprover/lean4>. `type_checker::reduce_nat` in
  `src/kernel/type_checker.cpp` lists the natural-number operations the kernel evaluates on
  literals.
-/

@[expose] public section

namespace CAS.Numerics

/-- The signed fraction `±a / b` of natural numbers, negative when `neg`. -/
def signedFrac (neg : Bool) (a b : ℕ) : ℚ := cond neg (-((a : ℚ) / b)) ((a : ℚ) / b)

/-- `signedFrac false a b` is `a / b`. -/
@[simp] theorem signedFrac_false (a b : ℕ) : signedFrac false a b = (a : ℚ) / b := rfl

/-- `signedFrac true a b` is `-(a / b)`. -/
@[simp] theorem signedFrac_true (a b : ℕ) : signedFrac true a b = -((a : ℚ) / b) := rfl

/-- The fraction `a / b` is defined and at most one. -/
def unitFracOk (a b : ℕ) : Bool := Nat.blt 0 b && Nat.ble a b

/-- A ball with center `p - n` and radius `e` in units of `2 ^ -P`, valid when `ok`. -/
structure GridBall where
  /-- Positive part of the center. -/
  p : ℕ
  /-- Negative part of the center. -/
  n : ℕ
  /-- Radius. -/
  e : ℕ
  /-- Validity flag. -/
  ok : Bool

namespace GridBall

/-- The center in units of `2 ^ -P`. -/
def center (s : GridBall) : ℤ := (s.p : ℤ) - s.n

/-- `s` encloses `q` at precision `P`. -/
def Encloses (P : ℕ) (s : GridBall) (q : ℚ) : Prop :=
  s.ok = true → |q * 2 ^ P - s.center| ≤ s.e

/-- The magnitude `|p - n|` of the center, by two truncated subtractions. -/
def mag (a : GridBall) : ℕ := Nat.add (Nat.sub a.p a.n) (Nat.sub a.n a.p)

/-- The exact ball of a natural number. -/
def ofNat (P c : ℕ) : GridBall := ⟨Nat.shiftLeft c P, 0, 0, true⟩

/-- A ball around `±a / b`: the quotient rounded down, radius one unit, or zero when the
quotient is exact on the grid. -/
def ofFrac (P : ℕ) (neg : Bool) (a b : ℕ) : GridBall :=
  ⟨Bool.rec (Nat.div (Nat.shiftLeft a P) b) 0 neg, Bool.rec 0 (Nat.div (Nat.shiftLeft a P) b) neg,
    Nat.sub 1 (Nat.sub 1 (Nat.mod (Nat.shiftLeft a P) b)), Nat.blt 0 b⟩

/-- A ball around the rational `q`, radius one unit, or zero when `q` lies on the grid. -/
def ofRat (P : ℕ) (q : ℚ) : GridBall := ofFrac P (decide (q.num < 0)) q.num.natAbs q.den

/-- The sum of two balls. -/
def add (a b : GridBall) : GridBall :=
  ⟨Nat.add a.p b.p, Nat.add a.n b.n, Nat.add a.e b.e, a.ok && b.ok⟩

/-- The negation of a ball. -/
def neg (a : GridBall) : GridBall := ⟨a.n, a.p, a.e, a.ok⟩

/-- The difference of two balls. -/
def sub (a b : GridBall) : GridBall :=
  ⟨Nat.add a.p b.n, Nat.add a.n b.p, Nat.add a.e b.e, a.ok && b.ok⟩

/-- The product of two balls at precision `P`. -/
def mul (P : ℕ) (a b : GridBall) : GridBall :=
  ⟨Nat.shiftRight (Nat.add (Nat.mul a.p b.p) (Nat.mul a.n b.n)) P,
    Nat.shiftRight (Nat.add (Nat.mul a.p b.n) (Nat.mul a.n b.p)) P,
    Nat.add (Nat.shiftRight (Nat.add (Nat.mul (mag a) b.e)
      (Nat.mul a.e (Nat.add (mag b) b.e))) P) 2, a.ok && b.ok⟩

/-- The ball with center `max (p - n) 0`, enclosing `max x 0` when `a` encloses `x`. -/
def clamp (a : GridBall) : GridBall := ⟨Nat.sub a.p a.n, 0, a.e, a.ok⟩

/-- The product of balls with centers `ma` and `mb` and radii `ea` and `eb`, at precision
`P`. -/
def mulNonnegCore (P ma ea mb eb : ℕ) (ok : Bool) : GridBall :=
  ⟨Nat.shiftRight (Nat.mul ma mb) P, 0,
    Nat.add (Nat.shiftRight (Nat.add (Nat.mul ma eb) (Nat.mul ea (Nat.add mb eb))) P) 2, ok⟩

/-- The negated product of balls with centers `ma` and `mb` and radii `ea` and `eb`, at
precision `P`: `(mulNonnegCore P ma ea mb eb ok).neg` without the rebuilt structure. -/
def mulNonnegNegCore (P ma ea mb eb : ℕ) (ok : Bool) : GridBall :=
  ⟨0, Nat.shiftRight (Nat.mul ma mb) P,
    Nat.add (Nat.shiftRight (Nat.add (Nat.mul ma eb) (Nat.mul ea (Nat.add mb eb))) P) 2, ok⟩

/-- The product of two balls enclosing nonnegative rationals, at precision `P`. -/
def mulNonneg (P : ℕ) (a b : GridBall) : GridBall :=
  mulNonnegCore P (Nat.sub a.p a.n) a.e (Nat.sub b.p b.n) b.e (a.ok && b.ok)

/-- The square of a ball with center `m` and radius `e`, at precision `P`. -/
def sqNonnegCore (P m e : ℕ) (ok : Bool) : GridBall :=
  ⟨Nat.shiftRight (Nat.mul m m) P, 0,
    Nat.add (Nat.shiftRight (Nat.mul e (Nat.add (Nat.add m m) e)) P) 2, ok⟩

/-- The square of a ball enclosing a nonnegative rational, at precision `P`. -/
def sqNonneg (P : ℕ) (a : GridBall) : GridBall := sqNonnegCore P (Nat.sub a.p a.n) a.e a.ok

/-- The product of a ball with the fraction `a / b` of natural numbers. -/
def mulFrac (a b : ℕ) (s : GridBall) : GridBall :=
  ⟨Nat.div (Nat.mul s.p a) b, Nat.div (Nat.mul s.n a) b,
    Nat.add (Nat.div (Nat.mul s.e a) b) 2, s.ok⟩

/-- The product of a ball with a natural number, exactly. -/
def scaleNat (c : ℕ) (s : GridBall) : GridBall :=
  ⟨Nat.mul s.p c, Nat.mul s.n c, Nat.mul s.e c, s.ok⟩

/-- The center minus the radius exceeds zero: the enclosed rational is positive. -/
def posCertain (a : GridBall) : Bool := a.ok && Nat.blt (Nat.add a.n a.e) a.p

/-- The reciprocal of a ball whose enclosed rational is positive, at precision `P`. -/
def inv (P : ℕ) (a : GridBall) : GridBall :=
  let z := Nat.sub a.p a.n
  ⟨Nat.div (Nat.shiftLeft 1 (Nat.add P P)) z, 0,
    Nat.add (Nat.div (Nat.shiftLeft a.e (Nat.add P P)) (Nat.mul z (Nat.sub z a.e))) 2,
    posCertain a⟩

/-- The quotient of the ball with center `ap - an` and radius `ea` by the ball with center `z`
and radius `eb`, at precision `P`. -/
def divPosCore (P ap an ea z eb : ℕ) (ok : Bool) : GridBall :=
  ⟨Nat.div (Nat.shiftLeft ap P) z, Nat.div (Nat.shiftLeft an P) z,
    Nat.add (Nat.div (Nat.shiftLeft (Nat.add (Nat.mul ea z)
      (Nat.mul (Nat.add (Nat.sub ap an) (Nat.sub an ap)) eb)) P)
      (Nat.mul z (Nat.sub z eb))) 2, ok⟩

/-- The quotient of a ball by a ball whose enclosed rational is positive, at precision `P`. -/
def divPos (P : ℕ) (a b : GridBall) : GridBall :=
  divPosCore P a.p a.n a.e (Nat.sub b.p b.n) b.e (a.ok && posCertain b)

/-- The ball of the smaller center, with the larger radius. -/
def min (a b : GridBall) : GridBall :=
  ⟨a.p, Nat.add a.n (Nat.sub (Nat.add a.p b.n) (Nat.add b.p a.n)),
    Nat.add a.e (Nat.sub b.e a.e), a.ok && b.ok⟩

/-- The ball of the larger center, with the larger radius. -/
def max (a b : GridBall) : GridBall :=
  ⟨Nat.add a.p (Nat.sub (Nat.add b.p a.n) (Nat.add a.p b.n)), a.n,
    Nat.add a.e (Nat.sub b.e a.e), a.ok && b.ok⟩

/-- `a` lies below `b` by at least both radii. -/
def leCertain (a b : GridBall) : Bool :=
  a.ok && b.ok && Nat.ble (Nat.add (Nat.add a.p a.e) (Nat.add b.n b.e)) (Nat.add b.p a.n)

/-- `a` lies strictly below `b` by more than both radii. -/
def ltCertain (a b : GridBall) : Bool :=
  a.ok && b.ok && Nat.blt (Nat.add (Nat.add a.p a.e) (Nat.add b.n b.e)) (Nat.add b.p a.n)

/-- The enclosed rational is nonnegative. -/
def nonnegCertain (a : GridBall) : Bool := a.ok && Nat.ble (Nat.add a.n a.e) a.p

/-- The enclosed rational is negative. -/
def negCertain (a : GridBall) : Bool := a.ok && Nat.blt (Nat.add a.p a.e) a.n

/-- The enclosed rational is nonpositive. -/
def nonposCertain (a : GridBall) : Bool := a.ok && Nat.ble (Nat.add a.p a.e) a.n

/-- The ball has radius zero and center `±m 2 ^ P / d`: the enclosed rational is `±m / d`. -/
def eqCertain (P : ℕ) (a : GridBall) (neg : Bool) (m d : ℕ) : Bool :=
  a.ok && Nat.blt 0 d && Nat.beq a.e 0 &&
    cond neg (Nat.beq (Nat.add (Nat.mul a.p d) (Nat.shiftLeft m P)) (Nat.mul a.n d))
      (Nat.beq (Nat.mul a.p d) (Nat.add (Nat.mul a.n d) (Nat.shiftLeft m P)))

/-- The ball has radius zero and encloses exactly the rational `q`. -/
def eqRatCertain (P : ℕ) (a : GridBall) (q : ℚ) : Bool :=
  eqCertain P a (decide (q.num < 0)) q.num.natAbs q.den

/-- The ball of the absolute value. -/
def abs (a : GridBall) : GridBall := ⟨mag a, 0, a.e, a.ok⟩

/-- The invalid ball: it encloses every rational vacuously, and every certificate test on it
fails. -/
def invalid : GridBall := ⟨0, 0, 0, false⟩

/-- The ball `a`, valid only when `b` also holds. -/
def guard (b : Bool) (a : GridBall) : GridBall := ⟨a.p, a.n, a.e, a.ok && b⟩

/-- The `k`-th power of a ball by repeated multiplication at precision `P`. -/
def pow (P : ℕ) (a : GridBall) (k : ℕ) : GridBall :=
  Nat.rec (motive := fun _ ↦ GridBall) (ofNat P 1) (fun _ b ↦ mul P b a) k

/-- The cube of a ball enclosing a nonnegative rational. -/
def cubeNonneg (P : ℕ) (a : GridBall) : GridBall := mulNonneg P (sqNonneg P a) a

/-- Binary powering of a ball enclosing a nonnegative rational, with `fuel` levels of
recursion: the `j`-th power is the square of the `j / 2`-th power, times the ball when `j` is
odd. -/
def powNonnegAux (P : ℕ) (a : GridBall) (fuel : ℕ) : ℕ → GridBall :=
  Nat.rec (motive := fun _ ↦ ℕ → GridBall) (fun _ ↦ ofNat P 1)
    (fun _ ih j ↦ Bool.rec
      (Bool.rec
        (Bool.rec (mulNonneg P (sqNonneg P (ih (Nat.shiftRight j 1))) a)
          (sqNonneg P (ih (Nat.shiftRight j 1))) (Nat.beq (Nat.mod j 2) 0))
        a (Nat.beq j 1))
      (ofNat P 1) (Nat.beq j 0)) fuel

/-- The `k`-th power of a ball enclosing a nonnegative rational, by binary powering, with the
exponents two, three and four written out. -/
def powNonneg (P : ℕ) (a : GridBall) (k : ℕ) : GridBall :=
  Bool.rec
    (Bool.rec
      (Bool.rec (powNonnegAux P a k k) (sqNonneg P (sqNonneg P a)) (Nat.beq k 4))
      (cubeNonneg P a) (Nat.beq k 3))
    (sqNonneg P a) (Nat.beq k 2)

/-- The cube of a ball: through the sign when the ball decides it, by repeated multiplication
otherwise. -/
def cube (P : ℕ) (a : GridBall) : GridBall :=
  Bool.rec (Bool.rec (pow P a 3) (cubeNonneg P a.neg).neg (nonposCertain a))
    (cubeNonneg P a) (nonnegCertain a)

/-- The `k`-th power of a ball for odd `k`: through the sign when the ball decides it, by
repeated multiplication otherwise. -/
def powOdd (P : ℕ) (a : GridBall) (k : ℕ) : GridBall :=
  Bool.rec (Bool.rec (pow P a k) (powNonneg P a.neg k).neg (nonposCertain a))
    (powNonneg P a k) (nonnegCertain a)

/-- The sum of the balls `f 0, …, f (n - 1)`. -/
def sumNat (P n : ℕ) (f : ℕ → GridBall) : GridBall :=
  Nat.rec (motive := fun _ ↦ GridBall) (ofNat P 0) (fun i acc ↦ add acc (f i)) n

/-- The floor of `(p - n) / 2 ^ k`, as a pair of natural numbers. -/
def floorShift (k p n : ℕ) : ℕ × ℕ :=
  (Nat.shiftRight (Nat.sub p n) k,
    Nat.shiftRight (Nat.add (Nat.sub n p) (Nat.sub (Nat.shiftLeft 1 k) 1)) k)

/-- The ceiling of `(p - n) / 2 ^ k`, as a pair of natural numbers. -/
def ceilShift (k p n : ℕ) : ℕ × ℕ :=
  (Nat.shiftRight (Nat.add (Nat.sub p n) (Nat.sub (Nat.shiftLeft 1 k) 1)) k,
    Nat.shiftRight (Nat.sub n p) k)

/-- The ball, on the grid of spacing `2 ^ (P - k)` units, between two grid points `L 2 ^ k` and
`U 2 ^ k` given as pairs. -/
def gridSpan (k : ℕ) (L U : ℕ × ℕ) (ok : Bool) : GridBall :=
  ⟨Nat.shiftLeft L.1 k, Nat.shiftLeft L.2 k,
    Nat.shiftLeft (Nat.sub (Nat.add U.1 L.2) (Nat.add L.1 U.2)) k, ok⟩

/-- A ball enclosing `⌊q 2 ^ bits⌋ / 2 ^ bits` when `a` encloses `q`, for `bits ≤ P`; its radius
is zero when the ball decides the floor. -/
def floorGrid (P bits : ℕ) (a : GridBall) : GridBall :=
  gridSpan (Nat.sub P bits) (floorShift (Nat.sub P bits) a.p (Nat.add a.n a.e))
    (floorShift (Nat.sub P bits) (Nat.add a.p a.e) a.n) (a.ok && Nat.ble bits P)

/-- A ball enclosing `⌈q 2 ^ bits⌉ / 2 ^ bits` when `a` encloses `q`, for `bits ≤ P`; its radius
is zero when the ball decides the ceiling. -/
def ceilGrid (P bits : ℕ) (a : GridBall) : GridBall :=
  gridSpan (Nat.sub P bits) (ceilShift (Nat.sub P bits) a.p (Nat.add a.n a.e))
    (ceilShift (Nat.sub P bits) (Nat.add a.p a.e) a.n) (a.ok && Nat.ble bits P)

/-! ### Natural-number operations -/

/-- `Nat.div a b` is `a / b`. Kept because core has this rewrite for `Nat.add`, `Nat.sub` and
`Nat.mul` (`Nat.add_eq`, `Nat.sub_eq`, `Nat.mul_eq`) but not for `Nat.div`, whose `Nat.div_eq` is
the recursion equation; the definitions here call `Nat.div` directly. -/
theorem natDiv_eq_div (a b : ℕ) : Nat.div a b = a / b := rfl

/-- `Nat.mod a b` is `a % b`. Kept because core has no such rewrite for `Nat.mod`, whose
`Nat.mod_eq` is the recursion equation; the definitions here call `Nat.mod` directly. -/
theorem natMod_eq_mod (a b : ℕ) : Nat.mod a b = a % b := rfl

/-! ### Rounding -/

/-- A natural quotient lies at most one unit below the rational quotient. -/
theorem natDiv_bounds (S d : ℕ) (hd : 0 < d) :
    ((S / d : ℕ) : ℚ) ≤ (S : ℚ) / d ∧ (S : ℚ) / d < (S / d : ℕ) + 1 := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have := Nat.lt_div_mul_add (a := S) hd
  rw [le_div_iff₀ hd', div_lt_iff₀ hd']
  exact ⟨by exact_mod_cast Nat.div_mul_le_self S d,
    by exact_mod_cast (by linarith : S < (S / d + 1) * d)⟩

/-- Two natural quotients differ from the rational quotient of their difference by less than one. -/
theorem abs_sub_natDiv_sub_lt (S T d : ℕ) (hd : 0 < d) :
    |((S : ℚ) - T) / d - (((S / d : ℕ) : ℚ) - (T / d : ℕ))| < 1 := by
  obtain ⟨h1, h2⟩ := natDiv_bounds S d hd
  obtain ⟨h3, h4⟩ := natDiv_bounds T d hd
  rw [sub_div, abs_lt]
  constructor <;> linarith

/-- Rounding the two parts of a center down by `d` moves it by less than one unit. -/
theorem abs_sub_natDiv_lt {V R : ℚ} {A B d : ℕ} (hd : 0 < d)
    (h : |V - ((A : ℚ) - B) / d| ≤ R) :
    |V - (((A / d : ℕ) : ℚ) - (B / d : ℕ))| < R + 1 := by
  have h1 := abs_sub_natDiv_sub_lt A B d hd
  calc |V - (((A / d : ℕ) : ℚ) - (B / d : ℕ))|
      ≤ |V - ((A : ℚ) - B) / d| + |((A : ℚ) - B) / d - (((A / d : ℕ) : ℚ) - (B / d : ℕ))| :=
        abs_sub_le _ _ _
    _ < R + 1 := by linarith

/-- If `V d` lies within `T` of `A - B`, then `V` lies within `T / d + 2` of the rounded
quotients. -/
theorem abs_sub_natDiv_le {V : ℚ} {A B T d : ℕ} (hd : 0 < d)
    (h : |V * d - ((A : ℚ) - B)| ≤ T) :
    |V - (((A / d : ℕ) : ℚ) - (B / d : ℕ))| ≤ ((T / d : ℕ) : ℚ) + 2 := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have h1 : |V - ((A : ℚ) - B) / d| ≤ (T : ℚ) / d := by
    rw [show V - ((A : ℚ) - B) / d = (V * d - ((A : ℚ) - B)) / d by field_simp, abs_div,
      abs_of_pos hd']
    exact div_le_div_of_nonneg_right h hd'.le
  have h2 := abs_sub_natDiv_lt hd h1
  have h3 := (natDiv_bounds T d hd).2
  linarith

/-! ### Soundness -/

/-- The center cast to `ℚ` is `p - n`. -/
theorem cast_center (a : GridBall) : (a.center : ℚ) = (a.p : ℚ) - a.n := by
  simp [center]

/-- The center of `add a b` is the sum of the centers. -/
theorem center_add (a b : GridBall) : (add a b).center = a.center + b.center := by
  simp only [center, add, Nat.add_eq]; push_cast; ring

/-- The center of `neg a` is the negated center. -/
theorem center_neg (a : GridBall) : (neg a).center = -a.center := by
  simp only [center, neg]; ring

/-- The center of `sub a b` is the difference of the centers. -/
theorem center_sub (a b : GridBall) : (sub a b).center = a.center - b.center := by
  simp only [center, sub, Nat.add_eq]; push_cast; ring

/-- The magnitude of the center, as a rational. -/
theorem cast_mag (a : GridBall) : (mag a : ℚ) = |(a.center : ℚ)| := by
  have : mag a = a.center.natAbs := by
    simp only [mag, center, Nat.add_eq, Nat.sub_eq]
    omega
  rw [this, Nat.cast_natAbs, Int.cast_abs]

/-- `ofNat P c` encloses the natural number `c` at precision `P`. -/
theorem ofNat_encloses (P c : ℕ) : (ofNat P c).Encloses P c := by
  intro _
  simp [ofNat, center, Nat.shiftLeft_eq]

/-- If `a` encloses `x` and `b` encloses `y` at precision `P`, then `add a b` encloses `x + y`. -/
theorem add_encloses {P : ℕ} {a b : GridBall} {x y : ℚ} (ha : a.Encloses P x)
    (hb : b.Encloses P y) : (add a b).Encloses P (x + y) := by
  intro h
  simp only [add, Bool.and_eq_true] at h
  have h1 := abs_le.mp (ha h.1)
  have h2 := abs_le.mp (hb h.2)
  rw [center_add, abs_le]
  push_cast [add, Nat.add_eq]
  constructor <;> linarith

/-- If `a` encloses `x` at precision `P`, then `neg a` encloses `-x`. -/
theorem neg_encloses {P : ℕ} {a : GridBall} {x : ℚ} (ha : a.Encloses P x) :
    (neg a).Encloses P (-x) := fun h ↦ by
  rw [center_neg, Int.cast_neg, neg_mul, neg_sub_neg, abs_sub_comm]
  exact ha h

/-- If `a` encloses `x` and `b` encloses `y` at precision `P`, then `sub a b` encloses `x - y`. -/
theorem sub_encloses {P : ℕ} {a b : GridBall} {x y : ℚ} (ha : a.Encloses P x)
    (hb : b.Encloses P y) : (sub a b).Encloses P (x - y) := by
  intro h
  simp only [sub, Bool.and_eq_true] at h
  have h1 := abs_le.mp (ha h.1)
  have h2 := abs_le.mp (hb h.2)
  rw [center_sub, abs_le]
  push_cast [sub, Nat.add_eq]
  constructor <;> linarith

/-- The error of a product of two perturbed values. -/
theorem abs_mul_sub_mul_le {X Y A B ea eb : ℚ} (hX : |X - A| ≤ ea) (hY : |Y - B| ≤ eb) :
    |X * Y - A * B| ≤ |A| * eb + ea * (|B| + eb) := by
  have hea : 0 ≤ ea := (abs_nonneg _).trans hX
  calc |X * Y - A * B| = |A * (Y - B) + B * (X - A) + (X - A) * (Y - B)| := by ring_nf
    _ ≤ |A| * |Y - B| + |B| * |X - A| + |X - A| * |Y - B| := by
        simpa only [abs_mul] using abs_add_three (A * (Y - B)) (B * (X - A)) ((X - A) * (Y - B))
    _ ≤ |A| * eb + |B| * ea + ea * eb := by gcongr
    _ = |A| * eb + ea * (|B| + eb) := by ring

/-- If `a` encloses `x` and `b` encloses `y` at precision `P`, then `mul P a b` encloses `x * y`. -/
theorem mul_encloses {P : ℕ} {a b : GridBall} {x y : ℚ} (ha : a.Encloses P x)
    (hb : b.Encloses P y) : (mul P a b).Encloses P (x * y) := by
  intro h
  simp only [mul, Bool.and_eq_true] at h
  have hT := abs_mul_sub_mul_le (ha h.1) (hb h.2)
  rw [← cast_mag, ← cast_mag, cast_center, cast_center] at hT
  have key := abs_sub_natDiv_le (V := x * y * 2 ^ P)
    (A := a.p * b.p + a.n * b.n) (B := a.p * b.n + a.n * b.p)
    (T := mag a * b.e + a.e * (mag b + b.e)) (d := 2 ^ P) (by positivity) (by
      push_cast
      convert hT using 2
      ring)
  rw [cast_center]
  simp only [mul, Nat.add_eq, Nat.mul_eq, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
  push_cast at key ⊢
  exact key

/-- If `a` encloses `x` at precision `P` and `posCertain a`, then `0 < x`. -/
theorem pos_of_posCertain {P : ℕ} {a : GridBall} {x : ℚ} (ha : a.Encloses P x)
    (h : posCertain a = true) : 0 < x := by
  simp only [posCertain, Bool.and_eq_true, Nat.blt_eq, Nat.add_eq] at h
  have h1 := abs_le.mp (ha h.1)
  have hlt : (a.n : ℚ) + a.e < a.p := by exact_mod_cast h.2
  exact pos_of_mul_pos_left (by linarith [cast_center a]) (by positivity : (0 : ℚ) < 2 ^ P).le

/-- If `a` encloses `x` and `b` encloses `y` at precision `P` and `leCertain a b`, then `x ≤ y`. -/
theorem le_of_leCertain {P : ℕ} {a b : GridBall} {x y : ℚ} (ha : a.Encloses P x)
    (hb : b.Encloses P y) (h : leCertain a b = true) : x ≤ y := by
  simp only [leCertain, Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at h
  have h1 := abs_le.mp (ha h.1.1)
  have h2 := abs_le.mp (hb h.1.2)
  have hle : (a.p : ℚ) + a.e + (b.n + b.e) ≤ b.p + a.n := by exact_mod_cast h.2
  exact le_of_mul_le_mul_right (by linarith [cast_center a, cast_center b])
    (by positivity : (0 : ℚ) < 2 ^ P)

/-- If `a` encloses `x` and `b` encloses `y` at precision `P` and `ltCertain a b`, then `x < y`. -/
theorem lt_of_ltCertain {P : ℕ} {a b : GridBall} {x y : ℚ} (ha : a.Encloses P x)
    (hb : b.Encloses P y) (h : ltCertain a b = true) : x < y := by
  simp only [ltCertain, Bool.and_eq_true, Nat.blt_eq, Nat.add_eq] at h
  have h1 := abs_le.mp (ha h.1.1)
  have h2 := abs_le.mp (hb h.1.2)
  have hlt : (a.p : ℚ) + a.e + (b.n + b.e) < b.p + a.n := by exact_mod_cast h.2
  exact lt_of_mul_lt_mul_right (by linarith [cast_center a, cast_center b])
    (by positivity : (0 : ℚ) < 2 ^ P).le

/-- If `a` encloses `x` and `b` encloses `y` at precision `P`, then `GridBall.min a b` encloses
`min x y`. -/
theorem min_encloses {P : ℕ} {a b : GridBall} {x y : ℚ} (ha : a.Encloses P x)
    (hb : b.Encloses P y) : (GridBall.min a b).Encloses P (Min.min x y) := by
  intro h
  simp only [GridBall.min, Bool.and_eq_true] at h
  have hc : (GridBall.min a b).center = Min.min a.center b.center := by
    simp only [GridBall.min, center, Nat.add_eq, Nat.sub_eq]
    omega
  have he : (GridBall.min a b).e = Max.max a.e b.e := by
    simp only [GridBall.min, Nat.add_eq, Nat.sub_eq]
    omega
  rw [hc, he, Int.cast_min, Nat.cast_max, min_mul_of_nonneg _ _ (by positivity)]
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le_max (ha h.1) (hb h.2))

/-- If `a` encloses `x` and `b` encloses `y` at precision `P`, then `GridBall.max a b` encloses
`max x y`. -/
theorem max_encloses {P : ℕ} {a b : GridBall} {x y : ℚ} (ha : a.Encloses P x)
    (hb : b.Encloses P y) : (GridBall.max a b).Encloses P (Max.max x y) := by
  intro h
  simp only [GridBall.max, Bool.and_eq_true] at h
  have hc : (GridBall.max a b).center = Max.max a.center b.center := by
    simp only [GridBall.max, center, Nat.add_eq, Nat.sub_eq]
    omega
  have he : (GridBall.max a b).e = Max.max a.e b.e := by
    simp only [GridBall.max, Nat.add_eq, Nat.sub_eq]
    omega
  rw [hc, he, Int.cast_max, Nat.cast_max, max_mul_of_nonneg _ _ (by positivity)]
  exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le_max (ha h.1) (hb h.2))

/-- If `a` encloses `x` at precision `P`, then `inv P a` encloses `x⁻¹`. No sign hypothesis is
needed: the result is valid only when `posCertain a`. -/
theorem inv_encloses {P : ℕ} {a : GridBall} {x : ℚ} (ha : a.Encloses P x) :
    (inv P a).Encloses P x⁻¹ := by
  intro h
  have hpos : posCertain a = true := h
  simp only [posCertain, Bool.and_eq_true, Nat.blt_eq, Nat.add_eq] at hpos
  have h1 := abs_le.mp (ha hpos.1)
  have hP : (0 : ℚ) < 2 ^ P := by positivity
  set z := Nat.sub a.p a.n with hz
  have hzc : (z : ℚ) = a.center := by
    simp only [z, center, Nat.sub_eq]; push_cast [Nat.cast_sub (by omega : a.n ≤ a.p)]; ring
  have hze : a.e < z := by simp only [z, Nat.sub_eq]; omega
  have hzpos : 0 < z := by omega
  have hzeq : (0 : ℚ) < (z : ℚ) - a.e := sub_pos.mpr (by exact_mod_cast hze)
  set X := x * 2 ^ P
  have hX1 : (z : ℚ) - a.e ≤ X := by rw [hzc]; linarith
  have hXpos : 0 < X := lt_of_lt_of_le hzeq hX1
  have hzq : (0 : ℚ) < z := by exact_mod_cast hzpos
  have hpp : ((Nat.shiftLeft 1 (Nat.add P P) : ℕ) : ℚ) = 2 ^ P * 2 ^ P := by
    simp [Nat.shiftLeft_eq, pow_add]
  have hpe : ((Nat.shiftLeft a.e (Nat.add P P) : ℕ) : ℚ) = a.e * (2 ^ P * 2 ^ P) := by
    simp [Nat.shiftLeft_eq, pow_add]
  obtain ⟨hq1, hq2⟩ := natDiv_bounds (Nat.shiftLeft 1 (Nat.add P P)) z hzpos
  have hden : 0 < z * (z - a.e) := Nat.mul_pos hzpos (by omega)
  obtain ⟨_, hr2⟩ := natDiv_bounds (Nat.shiftLeft a.e (Nat.add P P)) (z * (z - a.e)) hden
  rw [hpp] at hq1 hq2
  rw [hpe] at hr2
  push_cast [Nat.cast_sub hze.le] at hr2
  have hcen : ((inv P a).center : ℚ) = ((Nat.shiftLeft 1 (Nat.add P P) / z : ℕ) : ℚ) := by
    simp [inv, center, z]; rfl
  have herr : ((inv P a).e : ℚ) =
      ((Nat.shiftLeft a.e (Nat.add P P) / (z * (z - a.e)) : ℕ) : ℚ) + 2 := by
    simp [inv, z]; rfl
  rw [hcen, herr, show x⁻¹ * 2 ^ P = 2 ^ P * 2 ^ P / X by simp only [X]; field_simp]
  have hdiff : |2 ^ P * 2 ^ P / X - 2 ^ P * 2 ^ P / z| ≤
      a.e * (2 ^ P * 2 ^ P) / (z * (z - a.e)) := by
    rw [div_sub_div _ _ hXpos.ne' hzq.ne', abs_div, abs_of_pos (mul_pos hXpos hzq),
      div_le_div_iff₀ (mul_pos hXpos hzq) (mul_pos hzq hzeq),
      show 2 ^ P * 2 ^ P * (z : ℚ) - X * (2 ^ P * 2 ^ P) = 2 ^ P * 2 ^ P * ((z : ℚ) - X) by ring,
      abs_mul, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ P * 2 ^ P)]
    have hzX : |(z : ℚ) - X| ≤ a.e := by rw [abs_le]; constructor <;> linarith
    have : (z : ℚ) * (z - a.e) ≤ X * z := by
      rw [mul_comm X]
      exact mul_le_mul_of_nonneg_left hX1 hzq.le
    calc 2 ^ P * 2 ^ P * |(z : ℚ) - X| * (z * (z - a.e))
        ≤ 2 ^ P * 2 ^ P * a.e * (X * z) :=
          mul_le_mul (by gcongr) this (mul_pos hzq hzeq).le (by positivity)
      _ = a.e * (2 ^ P * 2 ^ P) * (X * z) := by ring
  have hround : |2 ^ P * 2 ^ P / (z : ℚ) - ((Nat.shiftLeft 1 (Nat.add P P) / z : ℕ) : ℚ)| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  linarith [abs_sub_le (2 ^ P * 2 ^ P / X) (2 ^ P * 2 ^ P / z)
    ((Nat.shiftLeft 1 (Nat.add P P) / z : ℕ) : ℚ)]

/-- If `a` encloses `x` and `b` encloses `y` at precision `P`, then `divPos P a b` encloses `x / y`.
No sign hypothesis is needed: the result is valid only when `posCertain b`. -/
theorem divPos_encloses {P : ℕ} {a b : GridBall} {x y : ℚ} (ha : a.Encloses P x)
    (hb : b.Encloses P y) : (divPos P a b).Encloses P (x / y) := by
  intro h
  have hok : a.ok = true ∧ posCertain b = true := by simpa [divPos, divPosCore] using h
  have hpos := hok.2
  simp only [posCertain, Bool.and_eq_true, Nat.blt_eq, Nat.add_eq] at hpos
  have h1 := ha hok.1
  have h2 := abs_le.mp (hb hpos.1)
  have hP : (0 : ℚ) < 2 ^ P := by positivity
  set z := Nat.sub b.p b.n with hz
  have hzc : (z : ℚ) = b.center := by
    simp only [z, center, Nat.sub_eq]; push_cast [Nat.cast_sub (by omega : b.n ≤ b.p)]; ring
  have hze : b.e < z := by simp only [z, Nat.sub_eq]; omega
  have hzpos : 0 < z := by omega
  have hzq : (0 : ℚ) < z := by exact_mod_cast hzpos
  have hzeq : (0 : ℚ) < (z : ℚ) - b.e := sub_pos.mpr (by exact_mod_cast hze)
  set X := x * 2 ^ P
  set Y := y * 2 ^ P
  have hY1 : (z : ℚ) - b.e ≤ Y := by rw [hzc]; linarith
  have hY2 : |Y - z| ≤ b.e := by rw [abs_le, hzc]; constructor <;> linarith
  have hYpos : 0 < Y := lt_of_lt_of_le hzeq hY1
  set A : ℚ := (a.center : ℚ)
  have hden : 0 < z * (z - b.e) := Nat.mul_pos hzpos (by omega)
  set T := (a.e * z + mag a * b.e) * 2 ^ P with hT
  have hgoal : x / y * 2 ^ P = X / Y * 2 ^ P := by
    simp only [X, Y]; field_simp
  -- the quotient error before rounding
  have hdiff : |X / Y * 2 ^ P - A * 2 ^ P / z| ≤ (T : ℚ) / (z * (z - b.e)) := by
    have hT' : (T : ℚ) = (a.e * z + |A| * b.e) * 2 ^ P := by
      simp only [T, A]; push_cast; rw [cast_mag]
    rw [hT', show X / Y * 2 ^ P - A * 2 ^ P / z = (X * z - A * Y) * 2 ^ P / (Y * z) by
      field_simp, abs_div, abs_mul, abs_of_pos hP, abs_of_pos (mul_pos hYpos hzq),
      div_le_div_iff₀ (mul_pos hYpos hzq) (by positivity)]
    have hnum : |X * z - A * Y| ≤ a.e * z + |A| * b.e := by
      rw [show X * z - A * Y = (X - A) * z - A * (Y - z) by ring]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos hzq]
      gcongr
    have hzz : (z : ℚ) * ((z : ℚ) - b.e) ≤ Y * z := by
      rw [mul_comm Y]
      exact mul_le_mul_of_nonneg_left hY1 hzq.le
    exact mul_le_mul (mul_le_mul_of_nonneg_right hnum hP.le) hzz (mul_pos hzq hzeq).le
      (by positivity)
  have hAeq : A * 2 ^ P / z = (((a.p * 2 ^ P : ℕ) : ℚ) - ((a.n * 2 ^ P : ℕ) : ℚ)) / z := by
    simp only [A, center]; push_cast; ring
  rw [hAeq] at hdiff
  have key := abs_sub_natDiv_lt hzpos hdiff
  obtain ⟨_, hr2⟩ := natDiv_bounds T (z * (z - b.e)) hden
  have hcen : ((divPos P a b).center : ℚ) =
      ((a.p * 2 ^ P / z : ℕ) : ℚ) - ((a.n * 2 ^ P / z : ℕ) : ℚ) := by
    rw [cast_center]; simp only [divPos, divPosCore, natDiv_eq_div, Nat.shiftLeft_eq',
        Nat.shiftLeft_eq, z]
  have herr : ((divPos P a b).e : ℚ) = ((T / (z * (z - b.e)) : ℕ) : ℚ) + 2 := by
    simp only [divPos, divPosCore, natDiv_eq_div, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.add_eq,
      Nat.mul_eq, Nat.sub_eq, T, z, mag]
    push_cast; ring
  push_cast [Nat.cast_sub hze.le] at hr2
  rw [hgoal, hcen, herr]
  linarith

/-- For all naturals `a` and `b`, `ofFrac P false a b` encloses `a / b` and `ofFrac P true a b`
encloses `-(a / b)` at precision `P`; for `b = 0` both balls are invalid. -/
theorem ofFrac_encloses (P : ℕ) (a b : ℕ) :
    (ofFrac P false a b).Encloses P ((a : ℚ) / b) ∧
      (ofFrac P true a b).Encloses P (-((a : ℚ) / b)) := by
  have key : ∀ hb : 0 < b, |(a : ℚ) / b * 2 ^ P - ((a * 2 ^ P / b : ℕ) : ℚ)| ≤
      ((1 - (1 - a * 2 ^ P % b) : ℕ) : ℚ) := by
    intro hb
    have hb' : (0 : ℚ) < b := by exact_mod_cast hb
    have hS : (a : ℚ) * 2 ^ P = b * (a * 2 ^ P / b : ℕ) + (a * 2 ^ P % b : ℕ) := by
      exact_mod_cast (Nat.div_add_mod (a * 2 ^ P) b).symm
    rw [div_mul_eq_mul_div, hS, show ((b : ℚ) * (a * 2 ^ P / b : ℕ) + (a * 2 ^ P % b : ℕ)) / b -
      (a * 2 ^ P / b : ℕ) = (a * 2 ^ P % b : ℕ) / b by field_simp; ring,
      abs_of_nonneg (by positivity)]
    rcases Nat.eq_zero_or_pos (a * 2 ^ P % b) with h0 | h0
    · simp [h0]
    · rw [show 1 - (1 - a * 2 ^ P % b) = 1 by omega, Nat.cast_one, div_le_one hb']
      exact_mod_cast (Nat.mod_lt _ hb).le
  constructor <;> intro h <;> simp only [ofFrac, Nat.blt_eq] at h
  · rw [cast_center]
    simpa [ofFrac, natDiv_eq_div, natMod_eq_mod, Nat.shiftLeft_eq', Nat.shiftLeft_eq] using key h
  · rw [cast_center, ← abs_neg]
    simpa [ofFrac, natDiv_eq_div, natMod_eq_mod, Nat.shiftLeft_eq', Nat.shiftLeft_eq,
      neg_add_eq_sub] using key h

/-- `ofFrac P neg a b` encloses `signedFrac neg a b` at precision `P`, for all `neg`, `a` and
`b`. -/
theorem ofFrac_encloses_signedFrac (P : ℕ) (neg : Bool) (a b : ℕ) :
    (ofFrac P neg a b).Encloses P (signedFrac neg a b) := by
  cases neg
  · exact (ofFrac_encloses P a b).1
  · exact (ofFrac_encloses P a b).2

/-- `ofRat P q` encloses `q` at precision `P`, for every rational `q`. -/
theorem ofRat_encloses (P : ℕ) (q : ℚ) : (ofRat P q).Encloses P q := by
  have hq : signedFrac (decide (q.num < 0)) q.num.natAbs q.den = q := by
    rcases lt_or_ge q.num 0 with h | h
    · simp [h, abs_of_neg, neg_div, Rat.num_div_den]
    · simp [not_lt.mpr h, abs_of_nonneg h, Rat.num_div_den]
  have h := ofFrac_encloses_signedFrac P (decide (q.num < 0)) q.num.natAbs q.den
  rwa [hq] at h

/-- The invalid ball encloses every rational at every precision. -/
theorem invalid_encloses (P : ℕ) (q : ℚ) : invalid.Encloses P q := by
  intro h; simp [invalid] at h

/-- If `b = true` implies that `a` encloses `x` at precision `P`, then `guard b a` encloses `x`. -/
theorem guard_encloses {P : ℕ} {b : Bool} {a : GridBall} {x : ℚ}
    (h : b = true → a.Encloses P x) : (guard b a).Encloses P x := by
  intro hok
  simp only [guard, Bool.and_eq_true] at hok
  exact h hok.2 hok.1

/-- Clamping the center at zero encloses `max 0 x`. -/
theorem clamp_encloses_max {P : ℕ} {a : GridBall} {x : ℚ} (ha : a.Encloses P x) :
    (clamp a).Encloses P (Max.max 0 x) := by
  intro h
  have h1 := ha h
  have hP : (0 : ℚ) < 2 ^ P := by positivity
  rw [cast_center] at h1 ⊢
  simp only [clamp, Nat.sub_eq, Nat.cast_zero, sub_zero]
  have hm : ((a.p - a.n : ℕ) : ℚ) = Max.max 0 ((a.p : ℚ) - a.n) := by
    exact_mod_cast (by omega : ((a.p - a.n : ℕ) : ℤ) = Max.max 0 ((a.p : ℤ) - a.n))
  rw [hm, max_mul_of_nonneg _ _ hP.le, zero_mul, max_comm 0 (x * 2 ^ P),
    max_comm 0 ((a.p : ℚ) - a.n)]
  exact (abs_max_sub_max_le_abs _ _ _).trans h1

/-- If `a` encloses `x` at precision `P` and `nonnegCertain a`, then `0 ≤ x`. -/
theorem nonneg_of_nonnegCertain {P : ℕ} {a : GridBall} {x : ℚ} (ha : a.Encloses P x)
    (h : nonnegCertain a = true) : 0 ≤ x := by
  simp only [nonnegCertain, Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at h
  have h1 := abs_le.mp (ha h.1)
  have hle : (a.n : ℚ) + a.e ≤ a.p := by exact_mod_cast h.2
  exact nonneg_of_mul_nonneg_left (by linarith [cast_center a]) (by positivity : (0 : ℚ) < 2 ^ P)

/-- If `a` encloses `x` at precision `P` and `negCertain a`, then `x < 0`. -/
theorem neg_of_negCertain {P : ℕ} {a : GridBall} {x : ℚ} (ha : a.Encloses P x)
    (h : negCertain a = true) : x < 0 := by
  simp only [negCertain, Bool.and_eq_true, Nat.blt_eq, Nat.add_eq] at h
  have h1 := abs_le.mp (ha h.1)
  have hlt : (a.p : ℚ) + a.e < a.n := by exact_mod_cast h.2
  exact neg_of_mul_neg_left (by linarith [cast_center a]) (by positivity : (0 : ℚ) < 2 ^ P).le

/-- If `a` encloses `x` at precision `P` and `nonposCertain a`, then `x ≤ 0`. -/
theorem nonpos_of_nonposCertain {P : ℕ} {a : GridBall} {x : ℚ} (ha : a.Encloses P x)
    (h : nonposCertain a = true) : x ≤ 0 := by
  simp only [nonposCertain, Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at h
  have h1 := abs_le.mp (ha h.1)
  have hle : (a.p : ℚ) + a.e ≤ a.n := by exact_mod_cast h.2
  exact nonpos_of_mul_nonpos_left (by linarith [cast_center a]) (by positivity : (0 : ℚ) < 2 ^ P)

/-- If `a` encloses `x` at precision `P`, then `abs a` encloses `|x|`. -/
theorem abs_encloses {P : ℕ} {a : GridBall} {x : ℚ} (ha : a.Encloses P x) :
    (abs a).Encloses P |x| := by
  intro h
  have h1 := ha h
  have hP : (0 : ℚ) < 2 ^ P := by positivity
  have hc : ((abs a).center : ℚ) = |(a.center : ℚ)| := by
    rw [← cast_mag]; simp [abs, center]
  rw [hc, show |x| * 2 ^ P = |x * 2 ^ P| by rw [abs_mul, abs_of_pos hP]]
  exact (abs_abs_sub_abs_le_abs_sub _ _).trans h1

/-- If `a` encloses `x` at precision `P`, then `pow P a k` encloses `x ^ k`, for every `k`. -/
theorem pow_encloses {P : ℕ} {a : GridBall} {x : ℚ} (ha : a.Encloses P x) (k : ℕ) :
    (pow P a k).Encloses P (x ^ k) := by
  induction k with
  | zero => simpa [pow] using ofNat_encloses P 1
  | succ k ih =>
    rw [pow_succ]
    exact mul_encloses ih ha

/-- Clamping the center at zero keeps a nonnegative rational enclosed. -/
theorem clamp_encloses {P : ℕ} {a : GridBall} {x : ℚ} (ha : a.Encloses P x) (hx : 0 ≤ x) :
    (clamp a).Encloses P x :=
  max_eq_right hx ▸ clamp_encloses_max ha

/-- The center of a clamped ball, cast to the rationals. -/
theorem clamp_center (a : GridBall) : ((clamp a).center : ℚ) = ((a.p - a.n : ℕ) : ℚ) := by
  simp [clamp, center]

/-- If `a` encloses `x` and `b` encloses `y` at precision `P`, with `0 ≤ x` and `0 ≤ y`, then
`mulNonneg P a b` encloses `x * y`. -/
theorem mulNonneg_encloses {P : ℕ} {a b : GridBall} {x y : ℚ} (ha : a.Encloses P x)
    (hx : 0 ≤ x) (hb : b.Encloses P y) (hy : 0 ≤ y) :
    (mulNonneg P a b).Encloses P (x * y) := by
  intro h
  simp only [mulNonneg, mulNonnegCore, Bool.and_eq_true] at h
  have h1 : |x * 2 ^ P - ((a.p - a.n : ℕ) : ℚ)| ≤ a.e := clamp_center a ▸ clamp_encloses ha hx h.1
  have h2 : |y * 2 ^ P - ((b.p - b.n : ℕ) : ℚ)| ≤ b.e := clamp_center b ▸ clamp_encloses hb hy h.2
  have hT := abs_mul_sub_mul_le h1 h2
  simp only [Nat.abs_cast] at hT
  have key := abs_sub_natDiv_le (V := x * y * 2 ^ P)
    (A := (a.p - a.n) * (b.p - b.n)) (B := 0)
    (T := (a.p - a.n) * b.e + a.e * ((b.p - b.n) + b.e)) (d := 2 ^ P) (by positivity) (by
      push_cast
      convert hT using 2
      ring)
  rw [cast_center]
  simp only [mulNonneg, mulNonnegCore, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, Nat.shiftRight_eq',
      Nat.shiftRight_eq_div_pow]
  push_cast at key ⊢
  simpa using key

/-- The product of two negated factors, formed directly. -/
theorem mulNonneg_neg_neg (P : ℕ) (a b : GridBall) :
    mulNonneg P a.neg b.neg =
      mulNonnegCore P (Nat.sub a.n a.p) a.e (Nat.sub b.n b.p) b.e (a.ok && b.ok) := rfl

/-- If `a` encloses `x` at precision `P` and `0 ≤ x`, then `sqNonneg P a` encloses `x ^ 2`. -/
theorem sqNonneg_encloses {P : ℕ} {a : GridBall} {x : ℚ} (ha : a.Encloses P x) (hx : 0 ≤ x) :
    (sqNonneg P a).Encloses P (x ^ 2) := by
  intro h
  simp only [sqNonneg, sqNonnegCore] at h
  have h1 : |x * 2 ^ P - ((a.p - a.n : ℕ) : ℚ)| ≤ a.e := clamp_center a ▸ clamp_encloses ha hx h
  have hT := abs_mul_sub_mul_le h1 h1
  simp only [Nat.abs_cast] at hT
  have key := abs_sub_natDiv_le (V := x ^ 2 * 2 ^ P)
    (A := (a.p - a.n) * (a.p - a.n)) (B := 0)
    (T := a.e * ((a.p - a.n) + (a.p - a.n) + a.e)) (d := 2 ^ P) (by positivity) (by
      push_cast
      convert hT using 2 <;> ring)
  rw [cast_center]
  simp only [sqNonneg, sqNonnegCore, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, Nat.shiftRight_eq',
      Nat.shiftRight_eq_div_pow]
  push_cast at key ⊢
  simpa using key

/-- If `s` encloses `x` at precision `P`, then `mulFrac a b s` encloses `x * (a / b)`, for all
naturals `a` and `b`. -/
theorem mulFrac_encloses {a b : ℕ} {P : ℕ} {s : GridBall} {x : ℚ} (hs : s.Encloses P x) :
    (mulFrac a b s).Encloses P (x * (a / b)) := by
  intro h
  have h1 := hs h
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    simp [mulFrac, center, natDiv_eq_div]
  · have key := abs_sub_natDiv_le (V := x * (a / b) * 2 ^ P)
      (A := s.p * a) (B := s.n * a) (T := s.e * a) (d := b) hb (by
        have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
        rw [show x * (a / b) * 2 ^ P * (b : ℚ) - (((s.p * a : ℕ) : ℚ) - ((s.n * a : ℕ) : ℚ)) =
            (x * 2 ^ P - s.center) * a by
          rw [cast_center]; push_cast; field_simp, abs_mul,
          abs_of_nonneg (Nat.cast_nonneg (α := ℚ) a)]
        push_cast
        exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _))
    rw [cast_center]
    simpa [mulFrac, natDiv_eq_div] using key

/-- If `s` encloses `x` at precision `P`, then `scaleNat c s` encloses `x * c`, for every natural
`c`. -/
theorem scaleNat_encloses {c P : ℕ} {s : GridBall} {x : ℚ} (hs : s.Encloses P x) :
    (scaleNat c s).Encloses P (x * c) := by
  intro h
  have h1 := hs h
  rw [cast_center] at h1 ⊢
  simp only [scaleNat, Nat.mul_eq, Nat.cast_mul]
  rw [show x * c * 2 ^ P - (s.p * c - s.n * c) = (x * 2 ^ P - (s.p - s.n)) * c by ring,
    abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℚ) c)]
  exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)

/-- If `a` encloses `x` at precision `P`, `0 ≤ x` and `j ≤ fuel`, then `powNonnegAux P a fuel j`
encloses `x ^ j`. -/
theorem powNonnegAux_encloses {P : ℕ} {a : GridBall} {x : ℚ} (ha : a.Encloses P x)
    (hx : 0 ≤ x) (fuel : ℕ) {j : ℕ} (hj : j ≤ fuel) :
    (powNonnegAux P a fuel j).Encloses P (x ^ j) := by
  induction fuel generalizing j with
  | zero =>
    obtain rfl : j = 0 := by omega
    change (ofNat P 1).Encloses P (x ^ 0)
    simpa using ofNat_encloses P 1
  | succ fuel ih =>
    have hj2 : Nat.shiftRight j 1 = j / 2 := by rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow,
        pow_one]
    have hdef : powNonnegAux P a (fuel + 1) j = Bool.rec (motive := fun _ ↦ GridBall)
        (Bool.rec (motive := fun _ ↦ GridBall)
          (Bool.rec (motive := fun _ ↦ GridBall)
            (mulNonneg P (sqNonneg P (powNonnegAux P a fuel (j / 2))) a)
            (sqNonneg P (powNonnegAux P a fuel (j / 2))) (Nat.beq (Nat.mod j 2) 0))
          a (Nat.beq j 1))
        (ofNat P 1) (Nat.beq j 0) := by
      rw [← hj2]; rfl
    rw [hdef]
    cases h0 : Nat.beq j 0
    · cases h1 : Nat.beq j 1
      · have := Nat.ne_of_beq_eq_false h0
        have := Nat.ne_of_beq_eq_false h1
        have hsq := sqNonneg_encloses (ih (j := j / 2) (by omega)) (by positivity)
        rw [← pow_mul] at hsq
        cases h2 : Nat.beq (Nat.mod j 2) 0
        · have : j % 2 ≠ 0 := Nat.ne_of_beq_eq_false h2
          have hm := mulNonneg_encloses hsq (by positivity) ha hx
          rw [← pow_succ] at hm
          convert hm using 2
          omega
        · have : j % 2 = 0 := Nat.eq_of_beq_eq_true h2
          convert hsq using 2
          omega
      · obtain rfl := Nat.eq_of_beq_eq_true h1
        simpa using ha
    · obtain rfl := Nat.eq_of_beq_eq_true h0
      simpa using ofNat_encloses P 1

/-- If `a` encloses `x` at precision `P` and `0 ≤ x`, then `cubeNonneg P a` encloses `x ^ 3`. -/
theorem cubeNonneg_encloses {P : ℕ} {a : GridBall} {x : ℚ} (ha : a.Encloses P x)
    (hx : 0 ≤ x) : (cubeNonneg P a).Encloses P (x ^ 3) := by
  have h := mulNonneg_encloses (sqNonneg_encloses ha hx) (by positivity) ha hx
  rwa [← pow_succ] at h

/-- If `a` encloses `x` at precision `P` and `0 ≤ x`, then `powNonneg P a k` encloses `x ^ k`, for
every `k`. -/
theorem powNonneg_encloses {P : ℕ} {a : GridBall} {x : ℚ} (ha : a.Encloses P x) (hx : 0 ≤ x)
    (k : ℕ) : (powNonneg P a k).Encloses P (x ^ k) := by
  unfold powNonneg
  have hsq := sqNonneg_encloses ha hx
  cases h2 : Nat.beq k 2
  · cases h3 : Nat.beq k 3
    · cases h4 : Nat.beq k 4
      · exact powNonnegAux_encloses ha hx k le_rfl
      · obtain rfl := Nat.eq_of_beq_eq_true h4
        have h := sqNonneg_encloses hsq (by positivity)
        rwa [← pow_mul] at h
    · obtain rfl := Nat.eq_of_beq_eq_true h3
      exact cubeNonneg_encloses ha hx
  · obtain rfl := Nat.eq_of_beq_eq_true h2
    exact hsq

/-- If `a` encloses `x` at precision `P`, then `cube P a` encloses `x ^ 3`. -/
theorem cube_encloses {P : ℕ} {a : GridBall} {x : ℚ} (ha : a.Encloses P x) :
    (cube P a).Encloses P (x ^ 3) := by
  unfold cube
  cases h1 : nonnegCertain a
  · cases h2 : nonposCertain a
    · exact pow_encloses ha 3
    · have hx := nonpos_of_nonposCertain ha h2
      have h := neg_encloses (cubeNonneg_encloses (neg_encloses ha) (neg_nonneg.mpr hx))
      rwa [Odd.neg_pow (by decide), neg_neg] at h
  · exact cubeNonneg_encloses ha (nonneg_of_nonnegCertain ha h1)

/-- If `a` encloses `x` at precision `P` and `k % 2 = 1`, then `powOdd P a k` encloses `x ^ k`. -/
theorem powOdd_encloses {P : ℕ} {a : GridBall} {x : ℚ} (ha : a.Encloses P x) {k : ℕ}
    (hk : k % 2 = 1) : (powOdd P a k).Encloses P (x ^ k) := by
  unfold powOdd
  cases h1 : nonnegCertain a
  · cases h2 : nonposCertain a
    · exact pow_encloses ha k
    · have hx := nonpos_of_nonposCertain ha h2
      have h := neg_encloses (powNonneg_encloses (neg_encloses ha) (neg_nonneg.mpr hx) k)
      rwa [(Nat.odd_iff.mpr hk).neg_pow, neg_neg] at h
  · exact powNonneg_encloses ha (nonneg_of_nonnegCertain ha h1) k

/-- If `f i` encloses `g i` at precision `P` for every `i < n`, then `sumNat P n f` encloses
`∑ i ∈ Finset.range n, g i`. -/
theorem sumNat_encloses {P n : ℕ} {f : ℕ → GridBall} {g : ℕ → ℚ}
    (h : ∀ i < n, (f i).Encloses P (g i)) :
    (sumNat P n f).Encloses P (∑ i ∈ Finset.range n, g i) := by
  induction n with
  | zero => simpa [sumNat] using ofNat_encloses P 0
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact add_encloses (ih fun i hi ↦ h i (by omega)) (h n (by omega))

/-- If `a` encloses `x` at precision `P` and `eqCertain P a neg m d`, then
`x = signedFrac neg m d`. -/
theorem eq_of_eqCertain {P : ℕ} {a : GridBall} {x : ℚ} {neg : Bool} {m d : ℕ}
    (ha : a.Encloses P x) (h : eqCertain P a neg m d = true) :
    x = signedFrac neg m d := by
  simp only [eqCertain, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨hok, hd⟩, he⟩, hc⟩ := h
  have h1 := ha hok
  rw [he, Nat.cast_zero, abs_nonpos_iff, sub_eq_zero, cast_center] at h1
  have hP : (0 : ℚ) < 2 ^ P := by positivity
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  cases neg
  · simp only [Bool.cond_false, signedFrac_false, Nat.beq_eq, Nat.add_eq, Nat.mul_eq,
      Nat.shiftLeft_eq', Nat.shiftLeft_eq] at hc ⊢
    have hc' : (a.p : ℚ) * d = a.n * d + m * 2 ^ P := by exact_mod_cast hc
    field_simp
    nlinarith
  · simp only [Bool.cond_true, signedFrac_true, Nat.beq_eq, Nat.add_eq, Nat.mul_eq,
      Nat.shiftLeft_eq', Nat.shiftLeft_eq] at hc ⊢
    have hc' : (a.p : ℚ) * d + m * 2 ^ P = a.n * d := by exact_mod_cast hc
    field_simp
    nlinarith

/-- If `a` encloses `x` at precision `P` and `eqRatCertain P a q`, then `x = q`. -/
theorem eq_of_eqRatCertain {P : ℕ} {a : GridBall} {x q : ℚ} (ha : a.Encloses P x)
    (h : eqRatCertain P a q = true) : x = q := by
  refine (eq_of_eqCertain ha h).trans ?_
  rcases lt_or_ge q.num 0 with hq | hq
  · simp [hq, abs_of_neg, neg_div, Rat.num_div_den]
  · simp [not_lt.mpr hq, abs_of_nonneg hq, Rat.num_div_den]

/-- `floorShift k p n` is the floor of `(p - n) / 2 ^ k`. -/
theorem floorShift_eq (k p n : ℕ) :
    pairValue (floorShift k p n) = ⌊((p : ℚ) - n) / 2 ^ k⌋ := by
  have hD : 0 < 2 ^ k := by positivity
  have hDq : (0 : ℚ) < 2 ^ k := by positivity
  have hfs : floorShift k p n = ((p - n) / 2 ^ k, (n - p + (2 ^ k - 1)) / 2 ^ k) := by
    simp only [floorShift, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.add_eq, Nat.sub_eq,
        Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]
  rw [hfs, eq_comm, Int.floor_eq_iff]
  simp only [pairValue, Int.cast_sub, Int.cast_natCast]
  rcases le_total n p with h | h
  · have h0 : (n - p + (2 ^ k - 1)) / 2 ^ k = 0 := by
      rw [Nat.sub_eq_zero_of_le h, zero_add]; exact Nat.div_eq_of_lt (by omega)
    rw [h0]
    obtain ⟨h1, h2⟩ := natDiv_bounds (p - n) (2 ^ k) hD
    rw [Nat.cast_sub h] at h1 h2
    push_cast at h1 h2 ⊢
    exact ⟨by linarith, by linarith⟩
  · have h0 : (p - n) / 2 ^ k = 0 := by rw [Nat.sub_eq_zero_of_le h, Nat.zero_div]
    rw [h0]
    set D := 2 ^ k with hDdef
    set c := (n - p + (D - 1)) / D
    have hc1 : c * D ≤ n - p + (D - 1) := Nat.div_mul_le_self _ _
    have hc2 : n - p + (D - 1) < c * D + D := Nat.lt_div_mul_add hD
    have hA : n - p ≤ c * D := by omega
    have hB : c * D < n - p + D := by omega
    have hA' : ((n : ℚ) - p) ≤ c * D := by rw [← Nat.cast_sub h]; exact_mod_cast hA
    have hB' : (c : ℚ) * D < (n : ℚ) - p + D := by rw [← Nat.cast_sub h]; exact_mod_cast hB
    have hDq' : (0 : ℚ) < D := by simp only [D]; positivity
    rw [show (2 : ℚ) ^ k = D by simp [D], Nat.cast_zero, zero_sub, le_div_iff₀ hDq',
      div_lt_iff₀ hDq']
    constructor <;> linarith

/-- `ceilShift k p n` is the ceiling of `(p - n) / 2 ^ k`. -/
theorem ceilShift_eq (k p n : ℕ) :
    pairValue (ceilShift k p n) = ⌈((p : ℚ) - n) / 2 ^ k⌉ := by
  have hsw : pairValue (ceilShift k p n) = -pairValue (floorShift k n p) := by
    simp only [ceilShift, floorShift, pairValue]; ring
  rw [hsw, floorShift_eq, show ((p : ℚ) - n) / 2 ^ k = -(((n : ℚ) - p) / 2 ^ k) by ring,
    Int.ceil_neg]

/-- A grid span encloses every grid point between its two ends. -/
theorem gridSpan_encloses {P k : ℕ} {L U : ℕ × ℕ} {ok : Bool} {z : ℤ}
    (hL : pairValue L ≤ z) (hU : z ≤ pairValue U) :
    (gridSpan k L U ok).Encloses P ((z : ℚ) * 2 ^ k / 2 ^ P) := by
  intro _
  have hP : (0 : ℚ) < 2 ^ P := by positivity
  rw [cast_center]
  simp only [gridSpan, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.sub_eq, Nat.add_eq]
  have hle : L.1 + U.2 ≤ U.1 + L.2 := by simp only [pairValue] at hL hU; omega
  rw [div_mul_cancel₀ _ hP.ne']
  push_cast [Nat.cast_sub hle]
  have hk : (0 : ℚ) ≤ 2 ^ k := by positivity
  have hL' : ((L.1 : ℚ) - L.2) ≤ z := by exact_mod_cast (show (L.1 : ℤ) - L.2 ≤ z from hL)
  have hU' : (z : ℚ) ≤ (U.1 : ℚ) - U.2 := by exact_mod_cast (show z ≤ (U.1 : ℤ) - U.2 from hU)
  rw [show (z : ℚ) * 2 ^ k - (L.1 * 2 ^ k - L.2 * 2 ^ k) = (z - (L.1 - L.2)) * 2 ^ k by ring,
    abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hk]
  exact mul_le_mul_of_nonneg_right (by linarith) hk

/-- If `a` encloses `q` at precision `P`, then `floorGrid P bits a` encloses
`⌊q * 2 ^ bits⌋ / 2 ^ bits`, for every `bits`; for `P < bits` the result is invalid. -/
theorem floorGrid_encloses {P bits : ℕ} {a : GridBall} {q : ℚ} (ha : a.Encloses P q) :
    (floorGrid P bits a).Encloses P ((⌊q * 2 ^ bits⌋ : ℚ) / 2 ^ bits) := by
  intro h
  have hok : a.ok = true ∧ bits ≤ P := by simpa [floorGrid, gridSpan] using h
  have h1 := abs_le.mp (ha hok.1)
  rw [cast_center] at h1
  set k := Nat.sub P bits
  have hPk : P = bits + k := by simp only [k, Nat.sub_eq]; omega
  have hq : q * 2 ^ bits = q * 2 ^ P / 2 ^ k := by
    rw [hPk, pow_add]; field_simp
  rw [show (⌊q * 2 ^ bits⌋ : ℚ) / 2 ^ bits = (⌊q * 2 ^ bits⌋ : ℚ) * 2 ^ k / 2 ^ P by
    rw [hPk, pow_add]; field_simp]
  refine gridSpan_encloses (P := P) ?_ ?_ h <;> rw [floorShift_eq, hq] <;>
    refine Int.floor_mono (div_le_div_of_nonneg_right ?_ (by positivity)) <;>
    push_cast [Nat.add_eq] <;> linarith

/-- If `a` encloses `q` at precision `P`, then `ceilGrid P bits a` encloses
`⌈q * 2 ^ bits⌉ / 2 ^ bits`, for every `bits`; for `P < bits` the result is invalid. -/
theorem ceilGrid_encloses {P bits : ℕ} {a : GridBall} {q : ℚ} (ha : a.Encloses P q) :
    (ceilGrid P bits a).Encloses P ((⌈q * 2 ^ bits⌉ : ℚ) / 2 ^ bits) := by
  intro h
  have hok : a.ok = true ∧ bits ≤ P := by simpa [ceilGrid, gridSpan] using h
  have h1 := abs_le.mp (ha hok.1)
  rw [cast_center] at h1
  set k := Nat.sub P bits
  have hPk : P = bits + k := by simp only [k, Nat.sub_eq]; omega
  have hq : q * 2 ^ bits = q * 2 ^ P / 2 ^ k := by
    rw [hPk, pow_add]; field_simp
  rw [show (⌈q * 2 ^ bits⌉ : ℚ) / 2 ^ bits = (⌈q * 2 ^ bits⌉ : ℚ) * 2 ^ k / 2 ^ P by
    rw [hPk, pow_add]; field_simp]
  refine gridSpan_encloses (P := P) ?_ ?_ h <;> rw [ceilShift_eq, hq] <;>
    refine Int.ceil_mono (div_le_div_of_nonneg_right ?_ (by positivity)) <;>
    push_cast [Nat.add_eq] <;> linarith

end GridBall

end CAS.Numerics

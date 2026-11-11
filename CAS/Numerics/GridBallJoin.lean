/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.IntervalBalls

/-!
# Joining two balls

`GridBall.join a b` is the ball around the center of `a` with radius
`max a.e (|a.center - b.center| + b.e)`: it encloses every rational enclosed by `a` or by `b`
(`join_encloses_left`, `join_encloses_right`). A mirror of a function defined by cases uses it
where the balls do not decide the case: both branches are evaluated and joined, and the join
encloses the exact value whichever branch the exact argument takes (`join_encloses_ite`).
`IntervalBalls.join` joins both endpoints.

## Main definitions

* `GridBall.join`: the ball around the center of `a` with radius
  `max a.e (|a.center - b.center| + b.e)`.
* `IntervalBalls.join`: the endpointwise join of two interval balls.

## Main results

* `GridBall.join_encloses_left`, `GridBall.join_encloses_right`: `join a b` encloses every
  rational enclosed by `a` and every rational enclosed by `b`.
* `GridBall.join_encloses_ite`: if `a` encloses `x` and `b` encloses `y`, then `join a b`
  encloses `if c then x else y`.
* `IntervalBalls.join_encloses_ite`: if `S` encloses `J` and `T` encloses `K`, then `join S T`
  encloses `if c then J else K`.
* `IntervalBalls.join_enclosesEnds_ite`: the same for enclosures of the ends.

## Implementation notes

We keep the center of `a` and widen only the radius, rather than taking the smallest ball that
contains both, whose center need not lie on the grid. With `d = centerDist a b`, computed by two
truncated subtractions, the radius `max a.e (d + b.e)` is `a.e + ((d + b.e) - a.e)`, so a join
costs a few natural-number operations. The join is not symmetric in `a` and `b`: it encloses
what `a` encloses because its radius is at least `a.e`, and what `b` encloses by the triangle
inequality through the center of `b`.
-/

@[expose] public section

namespace CAS.Numerics

open FloatLib.Numerics

namespace GridBall

/-- The distance `|a.center - b.center|` of two centers. -/
def centerDist (a b : GridBall) : ℕ :=
  Nat.add (Nat.sub (Nat.add a.p b.n) (Nat.add b.p a.n))
    (Nat.sub (Nat.add b.p a.n) (Nat.add a.p b.n))

/-- `centerDist a b` is the distance `|a.center - b.center|` of the two centers. -/
theorem cast_centerDist (a b : GridBall) :
    (centerDist a b : ℚ) = |(a.center : ℚ) - b.center| := by
  have : (centerDist a b : ℤ) = |((a.p : ℤ) - a.n) - (b.p - b.n)| := by
    simp only [centerDist, Nat.add_eq, Nat.sub_eq, abs_eq_max_neg]
    omega
  rw [cast_center, cast_center]
  exact_mod_cast this

/-- The ball around the center of `a` with the radius `max a.e (|a.center - b.center| + b.e)`:
it encloses every rational enclosed by `a` or by `b`. -/
def join (a b : GridBall) : GridBall :=
  ⟨a.p, a.n, Nat.add a.e (Nat.sub (Nat.add (centerDist a b) b.e) a.e), a.ok && b.ok⟩

/-- `join a b` encloses every rational enclosed by `a`. -/
theorem join_encloses_left {P : ℕ} {a b : GridBall} {x : ℚ} (ha : a.Encloses P x) :
    (join a b).Encloses P x := by
  intro h
  simp only [join, Bool.and_eq_true] at h
  refine (ha h.1).trans ?_
  exact_mod_cast Nat.le_add_right a.e _

/-- `join a b` encloses every rational enclosed by `b`. -/
theorem join_encloses_right {P : ℕ} {a b : GridBall} {y : ℚ} (hb : b.Encloses P y) :
    (join a b).Encloses P y := by
  intro h
  simp only [join, Bool.and_eq_true] at h
  have he : ((centerDist a b + b.e : ℕ) : ℚ) ≤ (join a b).e := by
    exact_mod_cast (by simp only [join, Nat.add_eq, Nat.sub_eq]; omega)
  have htri := abs_sub_le (y * 2 ^ P) (b.center : ℚ) a.center
  rw [abs_sub_comm (b.center : ℚ), ← cast_centerDist] at htri
  push_cast at he
  change |y * 2 ^ P - (a.center : ℚ)| ≤ _
  linarith [hb h.2]

/-- If `a` encloses `x` and `b` encloses `y`, then `join a b` encloses `if c then x else y`,
whichever way the condition `c` is decided. -/
theorem join_encloses_ite {P : ℕ} {a b : GridBall} {x y : ℚ} (ha : a.Encloses P x)
    (hb : b.Encloses P y) (c : Prop) [Decidable c] :
    (join a b).Encloses P (if c then x else y) := by
  split_ifs
  · exact join_encloses_left ha
  · exact join_encloses_right hb

end GridBall

namespace IntervalBalls

/-- Endpointwise `GridBall.join`. -/
def join (S T : IntervalBalls) : IntervalBalls := ⟨S.lo.join T.lo, S.hi.join T.hi⟩

/-- If `S` encloses the ends of `J` and `T` those of `K`, then `join S T` encloses the ends of
`if c then J else K`. -/
theorem join_enclosesEnds_ite {P : ℕ} {S T : IntervalBalls} {J K : RationalInterval}
    (hS : S.EnclosesEnds P J.lo J.hi) (hT : T.EnclosesEnds P K.lo K.hi) (c : Prop)
    [Decidable c] :
    (join S T).EnclosesEnds P (if c then J else K).lo (if c then J else K).hi := by
  split_ifs
  · exact ⟨GridBall.join_encloses_left hS.1, GridBall.join_encloses_left hS.2⟩
  · exact ⟨GridBall.join_encloses_right hT.1, GridBall.join_encloses_right hT.2⟩

/-- If `S` encloses `J` and `T` encloses `K`, then `join S T` encloses `if c then J else K`. -/
theorem join_encloses_ite {P : ℕ} {S T : IntervalBalls} {J K : Continuum.RationalInterval}
    (hS : S.Encloses P J) (hT : T.Encloses P K) (c : Prop) [Decidable c] :
    (join S T).Encloses P (if c then J else K) := by
  split_ifs
  · exact ⟨GridBall.join_encloses_left hS.1, GridBall.join_encloses_left hS.2⟩
  · exact ⟨GridBall.join_encloses_right hT.1, GridBall.join_encloses_right hT.2⟩

end IntervalBalls

end CAS.Numerics

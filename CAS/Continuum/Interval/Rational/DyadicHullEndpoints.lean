/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.DyadicHull
import CAS.Numerics.Binary64Grid

/-!
# The endpoints of a dyadic hull

The endpoints of `dyadicHull bits I` are the floor and the ceiling of `2 ^ bits` times the
endpoints of `I`, divided by `2 ^ bits` (`dyadicHull_lo`, `dyadicHull_hi`), because FloatLib's
grid enclosure of a rational is its floor and ceiling on the grid (`grid_enclose_lo`,
`grid_enclose_hi`).

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>.
-/

@[expose] public section

namespace CAS.Continuum.RationalInterval

open FloatLib.Numerics.Interval

/-- The lower grid coefficient of `q` is the floor of `q 2 ^ bits`. -/
theorem grid_enclose_lo (bits : ℕ) (q : ℚ) :
    (BinaryGrid.enclose bits q).lo = ⌊q * 2 ^ bits⌋ := by
  have hden : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hq : q * 2 ^ bits = ((q.num * 2 ^ bits : ℤ) : ℚ) / q.den := by
    conv_lhs => rw [← Rat.num_div_den q]
    push_cast; ring
  rw [eq_comm, Int.floor_eq_iff]
  simp only [BinaryGrid.enclose, BinaryGrid.divBounds, Int.shiftLeft_eq]
  rw [Int.fdiv_eq_ediv]
  simp only [hden.le, true_or, ↓reduceIte, sub_zero]
  rw [hq, le_div_iff₀ hd, div_lt_iff₀ hd]
  exact ⟨by exact_mod_cast Int.ediv_mul_le _ hden.ne',
    by exact_mod_cast Int.lt_ediv_add_one_mul_self _ hden⟩

/-- The upper grid coefficient of `q` is the ceiling of `q 2 ^ bits`. -/
theorem grid_enclose_hi (bits : ℕ) (q : ℚ) :
    (BinaryGrid.enclose bits q).hi = ⌈q * 2 ^ bits⌉ := by
  have hfl := Int.floor_le (q * 2 ^ bits)
  have hlt := Int.lt_floor_add_one (q * 2 ^ bits)
  rw [← grid_enclose_lo] at hfl hlt
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  simp only [BinaryGrid.enclose, BinaryGrid.divBounds] at hfl hlt ⊢
  set a := q.num <<< bits
  have hq : q * 2 ^ bits = (a : ℚ) / q.den := by
    rw [show a = q.num * 2 ^ bits from Int.shiftLeft_eq _ _]
    conv_lhs => rw [← Rat.num_div_den q]
    push_cast; ring
  rw [eq_comm, Int.ceil_eq_iff]
  split_ifs with hex
  · have hc : ((a.fdiv q.den : ℤ) : ℚ) = q * 2 ^ bits := by
      rw [hq, eq_div_iff hd.ne']
      exact_mod_cast hex
    constructor <;> linarith
  · have hne : ((a.fdiv q.den : ℤ) : ℚ) ≠ q * 2 ^ bits := fun h ↦
      hex (by exact_mod_cast (eq_div_iff hd.ne').mp (h.trans hq))
    push_cast
    constructor <;> linarith [lt_of_le_of_ne hfl hne]

/-- The lower endpoint of `dyadicHull bits I` is `⌊I.lo 2 ^ bits⌋ / 2 ^ bits`. -/
theorem dyadicHull_lo (bits : ℕ) (I : RationalInterval) :
    (dyadicHull bits I).lo = (⌊I.lo * 2 ^ bits⌋ : ℚ) / 2 ^ bits := by
  change BinaryGrid.toRat bits (BinaryGrid.enclose bits I.lo).lo = _
  rw [Numerics.binaryGrid_toRat_eq_div, grid_enclose_lo]

/-- The upper endpoint of `dyadicHull bits I` is `⌈I.hi 2 ^ bits⌉ / 2 ^ bits`. -/
theorem dyadicHull_hi (bits : ℕ) (I : RationalInterval) :
    (dyadicHull bits I).hi = (⌈I.hi * 2 ^ bits⌉ : ℚ) / 2 ^ bits := by
  change BinaryGrid.toRat bits (BinaryGrid.enclose bits I.hi).hi = _
  rw [Numerics.binaryGrid_toRat_eq_div, grid_enclose_hi]

end CAS.Continuum.RationalInterval

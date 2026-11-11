/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Data.Int.Basic

/-!
# Integer rounding at a power-of-two scale

`roundShift g c` is the integer quotient `(c + 2^(g-1)) / 2^g`. For `g ≥ 1` it rounds
`c / 2^g` to the nearest integer, with ties upward. Its definition also covers `g = 0`, where
natural subtraction in the exponent gives `c + 1`.

This module contains integer arithmetic only. The real error estimate is
`CAS.Numerics.abs_roundShift_sub_le` in `CAS.Numerics.TrigTable`.
-/

namespace CAS.Numerics

/-- The integer quotient `(c + 2^(g-1)) / 2^g`; for `g ≥ 1`, nearest-integer rounding with
upward ties. At `g = 0` the value is `c + 1`. -/
@[expose] public def roundShift (g : ℕ) (c : ℤ) : ℤ :=
  (c + ((2 ^ (g - 1) : ℕ) : ℤ)) / ((2 ^ g : ℕ) : ℤ)

end CAS.Numerics

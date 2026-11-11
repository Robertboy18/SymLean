/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.Binary64
import Mathlib.Tactic.NormNum

/-!
# Exact decoding of special binary64 words

Signed zeros, signed one and the least positive subnormal decode to their exact
rational values. The words are the standard IEEE-754 encodings, written as natural
numbers.
-/

@[expose] public section

namespace CAS.Examples.Numerics.Binary64

open CAS.Numerics

/-- Positive and negative IEEE zero have the same rational value. -/
theorem binary64DyadicValue_signed_zero :
    binary64DyadicValue 0 = 0 ∧ binary64DyadicValue (2 ^ 63) = 0 := by
  norm_num [binary64DyadicValue, binary64DyadicMagnitude]

/-- The normal encodings of positive and negative one decode exactly. -/
theorem binary64DyadicValue_signed_one :
    binary64DyadicValue 4607182418800017408 = 1 ∧
      binary64DyadicValue 13830554455654793216 = -1 := by
  norm_num [binary64DyadicValue, binary64DyadicMagnitude]

/-- The least positive subnormal retains its exact value. -/
theorem binary64DyadicValue_min_subnormal : binary64DyadicValue 1 = 1 / 2 ^ 1074 := by
  norm_num [binary64DyadicValue, binary64DyadicMagnitude]

end CAS.Examples.Numerics.Binary64

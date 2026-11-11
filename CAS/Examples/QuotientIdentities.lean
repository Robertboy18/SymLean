/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ExactTactic

/-!
# Quotient identities inside elementary functions

CAS cancels common polynomial factors before comparing the square root or the sine. The
hypotheses exclude the cancelled factors' zeros.
-/

@[expose] public section

namespace CAS.Examples.QuotientIdentities

example (x y : ℝ) (h : x ^ 2 - y ^ 2 ≠ 0) :
    Real.sqrt ((x ^ 4 - y ^ 4) / (x ^ 2 - y ^ 2)) = Real.sqrt (x ^ 2 + y ^ 2) := by
  cas

example (x y : ℝ) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    Real.sin ((x * y + y ^ 2) / (y * (x + y))) = Real.sin 1 := by
  cas

end CAS.Examples.QuotientIdentities

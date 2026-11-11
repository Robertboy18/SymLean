/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# Multiple angles, exponentials of logarithms, and sums of real exponents

The last stage of bare `cas` on an identity rewrites multiple angles and sums inside `sin` and
`cos`, exponentials of multiples of logarithms, and products of real powers with one base, each
with the hypothesis its theorem needs, and then proves the rewritten identity, modulo
`sin a ^ 2 + cos a ^ 2 = 1` when sines and cosines remain. The refusals check that the
hypotheses are required.
-/

namespace CAS.Examples.ElementaryRewrites

/-! ## Multiple angles -/

example (x : ℝ) : Real.cos (3 * x) = 4 * Real.cos x ^ 3 - 3 * Real.cos x := by
  cas

/-- The double-angle formula in the form `1 - 2 sin² x` needs the Pythagorean identity. -/
example (x : ℝ) : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
  cas

example (x y : ℝ) :
    Real.sin (x + y) * Real.sin (x - y) = Real.sin x ^ 2 - Real.sin y ^ 2 := by
  cas

/-- A false multiple-angle identity is refused. -/
example (x : ℝ) : x = x := by
  fail_if_success have : Real.sin (2 * x) = 2 * Real.sin x := by cas
  rfl

/-! ## Exponentials of multiples of logarithms -/

example (x : ℝ) (hx : 0 < x) : Real.exp (2 * Real.log x) = x ^ 2 := by
  cas

/-- For `x ≠ 0` the logarithm sees `|x|`. -/
example (x : ℝ) (hx : x ≠ 0) : Real.exp (3 * Real.log x) = |x| ^ 3 := by
  cas

/-- A non-integer multiple is a real power. -/
example (x : ℝ) (hx : 0 < x) : Real.exp (Real.log x * (1 / 2)) = x ^ (1 / 2 : ℝ) := by
  cas

/-- Without a sign of `x` the identity fails at `x = 0`, where `exp (2 * log 0) = 1`. -/
example (x : ℝ) : x = x := by
  fail_if_success have : Real.exp (2 * Real.log x) = x ^ 2 := by cas
  rfl

/-! ## Products of real powers -/

/-- `0 ≤ x` suffices because the exponents do not add up to `0`. -/
example (x : ℝ) (hx : 0 ≤ x) : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
  cas

/-- At `x = 0` with exponents adding up to `0` the product is `0 ^ a * 0 ^ (-a) = 0` while
`0 ^ 0 = 1`, so `0 ≤ x` is not enough. -/
example (x : ℝ) : x = x := by
  fail_if_success
    have : ∀ y : ℝ, 0 ≤ y → y ^ (1 / 2 : ℝ) * y ^ (-1 / 2 : ℝ) = 1 := by intro y hy; cas
  rfl

end CAS.Examples.ElementaryRewrites

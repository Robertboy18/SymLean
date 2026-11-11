/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import CAS.IntegrationTactic

/-!
# Elementary integrals with symbolic exponents

`cas` evaluates
`∫ t in a..b, t ^ n` for a symbolic natural exponent and `∫ t in a..b, t ^ r` for a real
exponent under Mathlib's hypotheses: `-1 < r`, or `r ≠ -1` together with `0 ∉ [a, b]`. The
hypotheses may be supplied in an equivalent form or as one conjunction.
-/

@[expose] public noncomputable section

namespace CAS.Examples.Integration.Elementary

/-- The power rule integrates a symbolic natural exponent. -/
example (n : ℕ) (a b : ℝ) :
    (∫ t : ℝ in a..b, t ^ n) =
      (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  cas

/-- An exponent above `-1` permits intervals containing zero, with either orientation. -/
theorem real_power_above_neg_one (r a b : ℝ) (hr : -1 < r) :
    (∫ t : ℝ in a..b, t ^ r) = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) := by
  cas using hr

/-- Equivalent bounds can supply the exact exponent condition as a checked proof. -/
theorem real_power_derived_condition (r a b : ℝ) (hr : 0 < r + 1) :
    (∫ t : ℝ in a..b, t ^ r) = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) := by
  cas using (show -1 < r from by linarith)

/-- Away from zero, the power formula needs only exclusion of the logarithmic exponent. -/
theorem real_power_avoiding_zero (r a b : ℝ) (hr : r ≠ -1)
    (hab : (0 : ℝ) ∉ Set.uIcc a b) :
    (∫ t : ℝ in a..b, t ^ r) = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) := by
  cas using And.intro hr hab

end CAS.Examples.Integration.Elementary

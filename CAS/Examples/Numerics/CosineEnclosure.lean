/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.CEGA

/-!
# A reusable cosine enclosure

On `[-1/10, 1/10]`, CEGA proves `199/200 ≤ cos x ≤ 1`. We store the
bound in a certificate so a later proof can reuse it without evaluating cosine again.
-/

@[expose] public noncomputable section

namespace CAS.Examples.Numerics.CosineEnclosure

open CAS.Certificate

/-- The interval on which the cosine bound holds. -/
def domain : Set ℝ := Set.Icc (-1 / 10 : ℝ) (1 / 10 : ℝ)

/-- A cosine enclosure proved once and available to later bounds. -/
def cosineEnclosure : EnclosureCert ℝ domain where
  fn := Real.cos
  lo := 199 / 200
  hi := 1
  sound := by
    intro x hx
    change x ∈ Set.Icc (-1 / 10 : ℝ) (1 / 10 : ℝ) at hx
    constructor <;> cega

/-- Project the stored certificate to an ordinary two-sided bound. -/
theorem cosine_enclosed : EnclosedOn Real.cos domain (199 / 200 : ℝ) 1 := by
  cega using cosineEnclosure

end CAS.Examples.Numerics.CosineEnclosure

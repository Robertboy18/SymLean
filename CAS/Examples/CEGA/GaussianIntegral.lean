/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
public meta import CAS.CEGA

/-!
# The `cega` tactic on the Gaussian integral

Sample enclosures on checked panels and Simpson's remainder together bound
`∫ x in 0..1, exp (-x ^ 2)` to within one millionth. Bare `cega` doubles the number of panels
until their enclosure proves the bound, and the kernel then checks that certificate in one
evaluation.
-/

@[expose] public section

namespace CAS.Examples.CEGA.GaussianIntegral

open CAS.Certificate
open CAS.CEGA

/-- Checked Simpson panels locate the Gaussian integral to within one millionth. -/
theorem gaussian_integral_approx :
    |(∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) - 746824 / 1000000| ≤ 1 / 1000000 := by
  cega

end CAS.Examples.CEGA.GaussianIntegral

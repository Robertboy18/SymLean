/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.IntegrationTactic

/-!
# Supplying an antiderivative

For `c log t / t + d`, supply `d t + c (log t)² / 2` as the primitive.
CAS checks its derivative before evaluating it at the two endpoints. The interval
must avoid zero, but its endpoints may occur in either order.
-/

public section

namespace CAS.Examples.Integration.SuppliedPrimitive

/-- Integrating a logarithmic term and a constant with an explicitly supplied primitive. -/
theorem explicit_parametric_primitive (a b c d : ℝ)
    (h : ∀ t ∈ Set.uIcc a b, t ≠ 0) :
    (∫ t in a..b, c * Real.log t / t + d) =
      (d * b + c * Real.log b ^ 2 / 2) - (d * a + c * Real.log a ^ 2 / 2) := by
  cas [integrate primitive := (fun t : ℝ ↦ d * t + c * Real.log t ^ 2 / 2) using h]

end CAS.Examples.Integration.SuppliedPrimitive

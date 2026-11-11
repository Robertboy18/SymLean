/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import CAS.ExactTactic

/-!
# Algebra with integral-valued opaque arguments

The exact frontend can clear denominators without evaluating an integral hidden in an atom.
In particular, a selected footpoint may depend on a primitive without requiring integration.
-/

public section

open MeasureTheory

namespace CAS.Examples.Integration.OpaqueIntegrals

/-- The rational rearrangement used by Lax–Oleinik localization treats the footpoint as an atom. -/
theorem opaque_primitive_argument
    (select : (ℝ → ℝ) → ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (s d σ u x : ℝ) (hs : 0 < s) (hd : 0 < d) :
    let y : ℝ → ℝ := select (fun w ↦ ∫ r in (0 : ℝ)..w, g r) (s ^ 2)
    u - (x - σ * s ^ 2) / (d * s ^ 2) =
      (u - (((x - y x) / s ^ 2) - σ) / d) - y x / (d * s ^ 2) := by
  intro y
  cas

/-- A positive denominator preserves the sign of an integral-valued opaque atom. -/
theorem opaque_integral_order (F : ℝ → ℝ) (g : ℝ → ℝ) (a b d : ℝ)
    (hd : 0 < d) (hF : 0 < F (∫ t in a..b, g t)) :
    0 < F (∫ t in a..b, g t) / d := by
  cas

end CAS.Examples.Integration.OpaqueIntegrals

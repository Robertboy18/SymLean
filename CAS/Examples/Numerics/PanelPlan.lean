/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.CompositeSimpson

/-!
# Planning composite Simpson panels with the executable planner

Composite Simpson on `[0, 1]` with `‖f⁗‖ ≤ 1` has the error model `B / N ^ 4` with
`B = 1 / 2880` (`QuadratureCert.compositeSimpson_error`). For the tolerance `10⁻⁸` the
executable planner `PanelPlan.ratRequiredPanels` takes `⌈B / 10⁻⁸⌉₊ = 34723`, whose floor
fourth root is `13`, and returns `14` panels; `PanelPlan.div_ratRequiredPanels_pow_le` shows
that they meet the tolerance. One example of the order-`m` planner, at `m = 4`.
-/

@[expose] public section

namespace CAS.Examples.Numerics.PanelPlan

open CAS.Continuum

/-- The planned Simpson panel count for `B = 1 / 2880` and the tolerance `10⁻⁸`, evaluated by
the kernel. -/
theorem simpson_ratRequiredPanels :
    PanelPlan.ratRequiredPanels 4 (1 / 2880) (1 / 10 ^ 8) = 14 := by
  decide +kernel

/-- The planned count meets the tolerance: `(1 / 2880) / N ^ 4 ≤ 10⁻⁸`. -/
theorem simpson_div_ratRequiredPanels_pow_le :
    (1 / 2880 : ℚ) / (PanelPlan.ratRequiredPanels 4 (1 / 2880) (1 / 10 ^ 8) : ℚ) ^ 4 ≤
      1 / 10 ^ 8 :=
  PanelPlan.div_ratRequiredPanels_pow_le four_ne_zero (by norm_num)

end CAS.Examples.Numerics.PanelPlan

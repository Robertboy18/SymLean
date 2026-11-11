/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
public import CAS.Continuum.IntervalBackend

/-!
# Exact weighted sums for quadrature rules

`weightedSum` evaluates an ordered list of weight-value pairs exactly. The real rules
(`QuadratureRule.valueOn`) and the executable rational rules (`RationalQuadratureRule.valueOn`)
share it, and `RationalQuadratureRule.cast_weightedSum` relates the two.

## Implementation notes

The terms stay in a list, in the order the rules produce them, and `List.sum` adds them as a
right fold, so `weightedSum_cons` holds by `rfl`. A finite set would merge equal terms, and
composite Simpson repeats one at every interior mesh point. The scalars of the rules are `ℚ`,
where `RationalQuadratureRule.valueOn` computes the sum, and `ℝ`, where it only appears in
proofs; both are exact, so the order of the additions does not change the value.
`weightedSum_append` splits a composite sum into its panels
(`weightedSum_uniformCompositeTerms`).
-/

@[expose] public section

namespace CAS.Continuum

/-- Exact value of an ordered list of weight-value pairs. -/
def weightedSum {R : Type*} [AddCommMonoid R] [Mul R]
    (terms : List (R × R)) : R :=
  (terms.map fun term ↦ term.1 * term.2).sum

/-- The weighted sum of the empty term list is zero. -/
@[simp]
theorem weightedSum_nil {R : Type*} [AddCommMonoid R] [Mul R] :
    weightedSum ([] : List (R × R)) = 0 :=
  rfl

/-- Peeling off the head term: the weighted sum is the head product plus the sum of the tail. -/
@[simp]
theorem weightedSum_cons {R : Type*} [AddCommMonoid R] [Mul R]
    (term : R × R) (terms : List (R × R)) :
    weightedSum (term :: terms) =
      term.1 * term.2 + weightedSum terms :=
  rfl

/-- Weighted sums distribute over concatenation of ordered term lists. -/
theorem weightedSum_append {R : Type*} [AddCommMonoid R] [Mul R]
    (left right : List (R × R)) :
    weightedSum (left ++ right) =
      weightedSum left + weightedSum right := by
  simp [weightedSum]

end CAS.Continuum

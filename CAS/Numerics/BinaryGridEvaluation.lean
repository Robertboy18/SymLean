/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.BinaryGridProof
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Cancellation-preserving finite evaluation on FloatLib's integer grid

Integer intervals on FloatLib's grid `2 ^ -precision` enclose finite sums, dot products and
separable double sums `∑ m, (∑ l, c m l * a l) * r m` of the reals that their inputs enclose.
Coefficient enclosures and elementary-function enclosures are independent inputs to these
finite evaluators. Addition is exact on the common grid; only multiplication rounds outward.

## Main definitions

* `binaryGridSum`: the sums of the endpoints of a finite family of grid intervals.
* `binaryGridDot`: a dot product of grid intervals with FloatLib's `BinaryGrid.mul`.
* `binaryGridSeparable`: the dot product of each coefficient row with the angular factors, then
  the dot product of these with the radial factors.

## Main results

* `binaryGridSum_sound`, `binaryGridDot_sound`, `binaryGridSeparable_sound`: each evaluator
  encloses the corresponding sum of real values enclosed by its inputs.

## Implementation notes

We add each signed angular row exactly before multiplying it by its radial factor. Interval
multiplication is subdistributive, `(X + Y) R ⊆ X R + Y R`, so the product of the row sum is
never wider than the sum of the products, apart from rounding, and it rounds outward once per
row instead of once per term.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>. The grid
  intervals, `BinaryGrid.mul` with four integer products and two outward-rounded shifts, and
  its enclosure `BinaryGrid.containsReal_mul`.
-/

@[expose] public section

namespace CAS.Numerics

open scoped BigOperators
open FloatLib.Numerics FloatLib.Numerics.Interval

/-- Sum interval endpoints exactly on a common integer grid. -/
def binaryGridSum {ι : Type*} (s : Finset ι) (boxes : ι → Interval Int) : Interval Int :=
  ⟨∑ i ∈ s, (boxes i).lo, ∑ i ∈ s, (boxes i).hi⟩

/-- Exact endpoint addition encloses the complete signed sum. -/
theorem binaryGridSum_sound {ι : Type*} (precision : ℕ) (s : Finset ι)
    (boxes : ι → Interval Int) (values : ι → ℝ)
    (h : ∀ i ∈ s, (boxes i).ContainsReal (BinaryGrid.decode precision) (values i)) :
    (binaryGridSum s boxes).ContainsReal (BinaryGrid.decode precision) (∑ i ∈ s, values i) := by
  simp only [binaryGridSum, BinaryGrid.containsReal_iff, BinaryGrid.value, Int.cast_sum,
    Finset.sum_div] at h ⊢
  exact ⟨Finset.sum_le_sum fun i hi ↦ (h i hi).1, Finset.sum_le_sum fun i hi ↦ (h i hi).2⟩

/-- A signed dot product uses FloatLib's proved outward-rounded multiplication. -/
def binaryGridDot {n : ℕ} (precision : ℕ) (a b : Fin n → Interval Int) : Interval Int :=
  binaryGridSum Finset.univ (fun i ↦ BinaryGrid.mul precision (a i) (b i))

/-- The dot product encloses every represented real scalar product. -/
theorem binaryGridDot_sound {n : ℕ} (precision : ℕ)
    (a b : Fin n → Interval Int) (x y : Fin n → ℝ)
    (ha : ∀ i, (a i).ContainsReal (BinaryGrid.decode precision) (x i))
    (hb : ∀ i, (b i).ContainsReal (BinaryGrid.decode precision) (y i)) :
    (binaryGridDot precision a b).ContainsReal (BinaryGrid.decode precision)
      (∑ i : Fin n, x i * y i) := by
  exact binaryGridSum_sound precision Finset.univ _ _
    (fun i _ ↦ BinaryGrid.containsReal_mul precision (ha i) (hb i))

/-- Evaluate angular rows first, retaining signed cancellation before radial multiplication. -/
def binaryGridSeparable {M L : ℕ} (precision : ℕ)
    (coefficients : Fin M → Fin L → Interval Int)
    (radial : Fin M → Interval Int) (angular : Fin L → Interval Int) : Interval Int :=
  binaryGridDot precision (fun m ↦ binaryGridDot precision (coefficients m) angular) radial

/-- The separable integer evaluator encloses the full represented two-variable finite sum. -/
theorem binaryGridSeparable_sound {M L : ℕ} (precision : ℕ)
    (coefficients : Fin M → Fin L → Interval Int)
    (radial : Fin M → Interval Int) (angular : Fin L → Interval Int)
    (c : Fin M → Fin L → ℝ) (r : Fin M → ℝ) (a : Fin L → ℝ)
    (hc : ∀ m l, (coefficients m l).ContainsReal (BinaryGrid.decode precision) (c m l))
    (hr : ∀ m, (radial m).ContainsReal (BinaryGrid.decode precision) (r m))
    (ha : ∀ l, (angular l).ContainsReal (BinaryGrid.decode precision) (a l)) :
    (binaryGridSeparable precision coefficients radial angular).ContainsReal
      (BinaryGrid.decode precision) (∑ m : Fin M, (∑ l : Fin L, c m l * a l) * r m) := by
  exact binaryGridDot_sound precision _ _ _ _
    (fun m ↦ binaryGridDot_sound precision _ _ _ _ (hc m) ha) hr

end CAS.Numerics

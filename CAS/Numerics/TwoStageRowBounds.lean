/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.TwoStageRows
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

/-!
# Two packed stages with bounds per term

`signedSlot_twoStageRow` asks for one bound `ρ` of all the biased coefficients of the first
stage. When the coefficients grow with the index, as `(m + 1)`-weighted combinations of
trigonometric words do, the sum `∑_m ρ_m` of bounds per term is about half of `n ρ_max`, which
can decide whether a slot width suffices. `fitsSlot_sum_mul_le` and
`signedSlot_twoStageRow_le` are the forms with bounds per term.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- A sum of products bounded by `a j` and `b` is bounded by `(∑ a) b`. -/
theorem natAbs_sum_mul_le_sum_bound {n b : ℕ} {x y : ℕ → ℤ} (a : ℕ → ℕ)
    (hx : ∀ j < n, (x j).natAbs ≤ a j) (hy : ∀ j < n, (y j).natAbs ≤ b) :
    (∑ j ∈ range n, x j * y j).natAbs ≤ (∑ j ∈ range n, a j) * b := by
  refine (Int.natAbs_sum_le _ _).trans
    ((sum_le_sum (g := fun j ↦ a j * b) fun j hj ↦ ?_).trans_eq (sum_mul _ _ _).symm)
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul (hx j (mem_range.mp hj)) (hy j (mem_range.mp hj))

/-- A sum of products bounded by `a j` and `b` fits when `2 (∑ a) b < 2 ^ w`. -/
theorem fitsSlot_sum_mul_le {w n b : ℕ} {x y : ℕ → ℤ} (a : ℕ → ℕ)
    (hx : ∀ j < n, (x j).natAbs ≤ a j) (hy : ∀ j < n, (y j).natAbs ≤ b)
    (hw : 2 * (∑ j ∈ range n, a j) * b < 2 ^ w) : FitsSlot w (∑ j ∈ range n, x j * y j) :=
  fitsSlot_of_natAbs_le (natAbs_sum_mul_le_sum_bound a hx hy) (by linarith)

/-- Every slot of the two-stage row is the exact double sum, with bounds `ρ m` per coefficient
of the first stage. -/
theorem signedSlot_twoStageRow_le {w₁ q₁ n₁ α d w₂ q₂ t : ℕ} {R D Θ : ℕ → ℕ} (ρ : ℕ → ℕ)
    (hD : ∀ m < n₁, D m < 2 ^ (w₁ * q₁)) (hΘ : ∀ l < q₁, Θ l < 2 ^ (w₂ * q₂))
    (hR : ∀ m < n₁, ((R m : ℤ) - α).natAbs ≤ ρ m)
    (hDb : ∀ m < n₁, ∀ l < q₁, (signedSlot w₁ l (D m)).natAbs ≤ d)
    (hΘb : ∀ l < q₁, ∀ n < q₂, (signedSlot w₂ n (Θ l)).natAbs ≤ t)
    (h₁ : 2 * (∑ m ∈ range n₁, ρ m) * d < 2 ^ w₁)
    (h₂ : 2 * q₁ * ((∑ m ∈ range n₁, ρ m) * d) * t < 2 ^ w₂) {n : ℕ} (hn : n < q₂) :
    signedSlot w₂ n (twoStageRow w₁ q₁ n₁ α R D w₂ q₂ Θ) =
      ∑ l ∈ range q₁, (∑ m ∈ range n₁, ((R m : ℤ) - α) * signedSlot w₁ l (D m)) *
        signedSlot w₂ n (Θ l) := by
  have hone : ∀ l < q₁, signedSlot w₁ l (packedRowCombination w₁ q₁ n₁ α R D) =
      ∑ m ∈ range n₁, ((R m : ℤ) - α) * signedSlot w₁ l (D m) := fun l hl ↦
    signedSlot_packedRowCombination hD
      (fun k hk ↦ fitsSlot_sum_mul_le ρ (fun m hm ↦ hR m hm) (fun m hm ↦ hDb m hm k hk) h₁) hl
  have hbound : ∀ l < q₁, (signedSlot w₁ l (packedRowCombination w₁ q₁ n₁ α R D)).natAbs ≤
      (∑ m ∈ range n₁, ρ m) * d := fun l hl ↦ by
    rw [hone l hl]
    exact natAbs_sum_mul_le_sum_bound ρ (fun m hm ↦ hR m hm) (fun m hm ↦ hDb m hm l hl)
  unfold twoStageRow
  rw [signedSlot_packedRowCombination_slots hΘ (fun k hk ↦ fitsSlot_sum_mul
    (fun l hl ↦ hbound l hl) (fun l hl ↦ hΘb l hl k hk) h₂) hn]
  exact sum_congr rfl fun l hl ↦ by rw [hone l (mem_range.mp hl)]

end CAS.Numerics

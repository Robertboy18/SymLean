/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedLinearAlgebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

/-!
# Separable evaluation in two packed stages

A separable sum `∑_l (∑_m c_{ml} r_m) t_l(n)` is evaluated at all nodes `n` at once in two
packed stages with natural-number operations: `H = ∑_{m < n₁} (R m - α) D m`, one packed row
over `l` (the data rows `D m` with the biased coefficients `R m`), and
`F = ∑_{l < q₁} H_l Θ l`, one packed row over the nodes (the rows `Θ l` of the angular values
with the slots of `H` as coefficients). `signedSlot_twoStageRow` gives every slot of `F` as the
exact double sum when the coefficients, data slots and angular slots are bounded by `ρ`, `d`,
`t` and the widths satisfy `2 n₁ ρ d < 2^w₁` and `2 q₁ (n₁ ρ d) t < 2^w₂`.
`signedSlot_firstStage` and `natAbs_signedSlot_firstStage_le` give the slots of the first stage
and their bound `n₁ ρ d`.

## Implementation notes

Each stage is one `packedRowCombination`: a few multiplications and additions of natural literals
per input row, however many nodes the rows hold, and the kernel evaluates them with its
arbitrary-precision arithmetic. The slots of `H` enter the second stage still biased, with
`slotBias w₁` as the coefficient bias, so no signed value is formed. The width conditions are the
hypotheses of `fitsSlot_sum_mul` for the two stages. Compiled code runs `twoStageRowFast`
(`twoStageRow_eq_fast`, a `csimp` lemma), which passes the first-stage row to the `noinline`
function `twoStageRowOf` so that it is computed once; the kernel unfolds `twoStageRow` itself.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- The two-stage row: `∑_{l < q₁} H_l Θ l` with `H = ∑_{m < n₁} (R m - α) D m`. -/
def twoStageRow (w₁ q₁ n₁ α : ℕ) (R D : ℕ → ℕ) (w₂ q₂ : ℕ) (Θ : ℕ → ℕ) : ℕ :=
  packedRowCombination w₂ q₂ q₁ (slotBias w₁)
    (fun l ↦ slot w₁ l (packedRowCombination w₁ q₁ n₁ α R D)) Θ

/-- The second stage for a given first-stage row `H`. The row enters as an argument, so that
compiled code computes it once rather than once per slot. -/
@[noinline] def twoStageRowOf (H w₁ q₁ w₂ q₂ : ℕ) (Θ : ℕ → ℕ) : ℕ :=
  packedRowCombination w₂ q₂ q₁ (slotBias w₁) (fun l ↦ slot w₁ l H) Θ

/-- The two-stage row with its first stage computed once. -/
def twoStageRowFast (w₁ q₁ n₁ α : ℕ) (R D : ℕ → ℕ) (w₂ q₂ : ℕ) (Θ : ℕ → ℕ) : ℕ :=
  twoStageRowOf (packedRowCombination w₁ q₁ n₁ α R D) w₁ q₁ w₂ q₂ Θ

/-- `twoStageRow` and `twoStageRowFast` are the same function, by `rfl`; as a `csimp` lemma it
makes compiled code evaluate `twoStageRowFast`, while the kernel unfolds `twoStageRow`. -/
@[csimp] theorem twoStageRow_eq_fast : @twoStageRow = @twoStageRowFast := rfl

/-- The slots of the first stage. -/
theorem signedSlot_firstStage {w₁ q₁ n₁ α ρ d : ℕ} {R D : ℕ → ℕ}
    (hD : ∀ m < n₁, D m < 2 ^ (w₁ * q₁)) (hR : ∀ m < n₁, ((R m : ℤ) - α).natAbs ≤ ρ)
    (hDb : ∀ m < n₁, ∀ l < q₁, (signedSlot w₁ l (D m)).natAbs ≤ d)
    (h₁ : 2 * n₁ * ρ * d < 2 ^ w₁) {l : ℕ} (hl : l < q₁) :
    signedSlot w₁ l (packedRowCombination w₁ q₁ n₁ α R D) =
      ∑ m ∈ range n₁, ((R m : ℤ) - α) * signedSlot w₁ l (D m) :=
  signedSlot_packedRowCombination hD
    (fun k hk ↦ fitsSlot_sum_mul (fun m hm ↦ hR m hm) (fun m hm ↦ hDb m hm k hk) h₁) hl

/-- The first-stage slots are bounded by `n₁ ρ d`. -/
theorem natAbs_signedSlot_firstStage_le {w₁ q₁ n₁ α ρ d : ℕ} {R D : ℕ → ℕ}
    (hD : ∀ m < n₁, D m < 2 ^ (w₁ * q₁)) (hR : ∀ m < n₁, ((R m : ℤ) - α).natAbs ≤ ρ)
    (hDb : ∀ m < n₁, ∀ l < q₁, (signedSlot w₁ l (D m)).natAbs ≤ d)
    (h₁ : 2 * n₁ * ρ * d < 2 ^ w₁) {l : ℕ} (hl : l < q₁) :
    (signedSlot w₁ l (packedRowCombination w₁ q₁ n₁ α R D)).natAbs ≤ n₁ * ρ * d := by
  rw [signedSlot_firstStage hD hR hDb h₁ hl]
  refine (Int.natAbs_sum_le _ _).trans
    ((sum_le_sum (g := fun _ ↦ ρ * d) fun m hm ↦ ?_).trans_eq ?_)
  · rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (hR m (mem_range.mp hm)) (hDb m (mem_range.mp hm) l hl)
  · rw [sum_const, card_range, smul_eq_mul, mul_assoc]

/-- Every slot of the two-stage row is the exact double sum. -/
theorem signedSlot_twoStageRow {w₁ q₁ n₁ α ρ d w₂ q₂ t : ℕ} {R D Θ : ℕ → ℕ}
    (hD : ∀ m < n₁, D m < 2 ^ (w₁ * q₁)) (hΘ : ∀ l < q₁, Θ l < 2 ^ (w₂ * q₂))
    (hR : ∀ m < n₁, ((R m : ℤ) - α).natAbs ≤ ρ)
    (hDb : ∀ m < n₁, ∀ l < q₁, (signedSlot w₁ l (D m)).natAbs ≤ d)
    (hΘb : ∀ l < q₁, ∀ n < q₂, (signedSlot w₂ n (Θ l)).natAbs ≤ t)
    (h₁ : 2 * n₁ * ρ * d < 2 ^ w₁) (h₂ : 2 * q₁ * (n₁ * ρ * d) * t < 2 ^ w₂)
    {n : ℕ} (hn : n < q₂) :
    signedSlot w₂ n (twoStageRow w₁ q₁ n₁ α R D w₂ q₂ Θ) =
      ∑ l ∈ range q₁, (∑ m ∈ range n₁, ((R m : ℤ) - α) * signedSlot w₁ l (D m)) *
        signedSlot w₂ n (Θ l) := by
  unfold twoStageRow
  rw [signedSlot_packedRowCombination_slots hΘ (fun k hk ↦ fitsSlot_sum_mul
    (fun l hl ↦ natAbs_signedSlot_firstStage_le hD hR hDb h₁ hl) (fun l hl ↦ hΘb l hl k hk) h₂) hn]
  exact sum_congr rfl fun l hl ↦ by rw [signedSlot_firstStage hD hR hDb h₁ (mem_range.mp hl)]

end CAS.Numerics

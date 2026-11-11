/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedLinearAlgebra
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# Separable evaluation of a coefficient table in packed rows

A table `∑_{m, l} D m l · ρ_m(β) τ_l(θ)` with `τ_l = ∑_k κ l k · g_k` is evaluated at one node
`β` and at all nodes `θ_n` at once in three packed stages, with natural-number operations only:

1. `H l = ∑_m R m · D m l`, one packed row over `l` (`packedRowCombination` of the data rows with
   the biased mode values `R m` as coefficients);
2. `y k = ∑_l H l · κ l k`, one packed row over `k`, then `z k = ⌊y k / 2^e⌋` slot by slot
   (`slotShift`), which removes the common denominator `2^e` of the conversion `κ`;
3. `F n = ∑_k c k · z k · G k n`, one packed row over the nodes `n`, from the rows `G k` of the
   mode values at the nodes, with integer factors `c k = cp k - cn k` (`factorCoefficient`).

`signedSlot_factorRow` states the exact value of every slot of the final row once every stage
fits its slots, and `slotShift_floor` bounds the rounding of the middle stage.

## Implementation notes

Each stage is one `packedRowCombination`, a few multiplications and additions of natural literals
per input row, which the kernel evaluates with its arbitrary-precision arithmetic. We keep every
intermediate value natural. The slots of the first stage enter the second stage still biased,
with `slotBias w₁` as the coefficient bias. The shift acts on the biased slot of the second
stage, so its bias becomes `2^(w₂ - 1 - e)` (this needs `e < w₂`), and `factorCoefficient` forms
the biased coefficient `α + (cp - cn) (u - b)` as `α + cp u + cn b` minus `cp b + cn u`, a
truncated subtraction that is exact when the coefficient is nonnegative (the hypothesis of
`factorCoefficient_eq`). The floor of the shift is the only rounding, and `FactorRowError` carries
`slotShift_floor` through the third stage. Compiled code runs `factorRowFast`, which computes the
first two stages once (`factorRow_eq_factorRowFast`, a `csimp` lemma); the kernel unfolds
`factorRow` itself.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- Slot `k` of width `w` of `x`, shifted right by `e` bits. -/
def slotShift (w e k x : ℕ) : ℕ := Nat.shiftRight (slot w k x) e

/-- The shifted slot is the floor of the signed slot over `2^e`, rebiased to `2^(w - 1 - e)`. -/
theorem slotShift_floor {w e : ℕ} (he : e < w) (k x : ℕ) :
    ((slotShift w e k x : ℤ) - 2 ^ (w - 1 - e) : ℝ) ≤ (signedSlot w k x : ℝ) / 2 ^ e ∧
      (signedSlot w k x : ℝ) / 2 ^ e < ((slotShift w e k x : ℤ) - 2 ^ (w - 1 - e) : ℝ) + 1 := by
  have hb : slotBias w = 2 ^ e * 2 ^ (w - 1 - e) := by
    rw [slotBias_eq, ← pow_add, show e + (w - 1 - e) = w - 1 by omega]
    obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
    rw [pow_succ, Nat.mul_div_cancel _ (by norm_num), Nat.add_sub_cancel]
  set s := slot w k x
  have hshift : slotShift w e k x = s / 2 ^ e := Nat.shiftRight_eq_div_pow s e
  have hdiv := Nat.div_add_mod s (2 ^ e)
  have hmod := Nat.mod_lt s (show 0 < 2 ^ e by positivity)
  set u := s / 2 ^ e
  set r := s % 2 ^ e
  have h2e : (0 : ℝ) < 2 ^ e := by positivity
  have hval : (signedSlot w k x : ℝ) = 2 ^ e * (u : ℝ) + r - 2 ^ e * 2 ^ (w - 1 - e) := by
    have hs : (s : ℝ) = 2 ^ e * (u : ℝ) + r := by exact_mod_cast hdiv.symm
    rw [signedSlot, hb]
    push_cast
    rw [hs]
  have hm0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  have hm1 : (r : ℝ) < 2 ^ e := by exact_mod_cast hmod
  rw [hshift, hval, Int.cast_natCast]
  constructor
  · rw [le_div_iff₀ h2e]
    linarith
  · rw [div_lt_iff₀ h2e]
    linarith

/-- The biased coefficient `α + (cp - cn) (u - b)` of a scaled slot `u` with bias `b`. -/
def factorCoefficient (α cp cn b u : ℕ) : ℕ := α + cp * u + cn * b - (cp * b + cn * u)

/-- If `(cp - cn) * (u - b) + α ≥ 0`, the truncated subtraction in `factorCoefficient` is exact:
`factorCoefficient α cp cn b u - α = (cp - cn) * (u - b)` in the integers. -/
theorem factorCoefficient_eq {α cp cn b u : ℕ}
    (h : ((cp : ℤ) - cn) * ((u : ℤ) - b) + α ≥ 0) :
    (factorCoefficient α cp cn b u : ℤ) - α = ((cp : ℤ) - cn) * ((u : ℤ) - b) := by
  unfold factorCoefficient
  have hle : cp * b + cn * u ≤ α + cp * u + cn * b := by linarith
  rw [Nat.cast_sub hle]
  push_cast
  ring

/-- The three-stage row: data rows `D` (`q₁` slots of width `w₁`, `n₁` rows) with biased mode
values `R` (bias `α₁`); conversion rows `K` (`q₂` slots of width `w₂`, `q₁` rows) read with the
slots of the first stage; a shift by `e`; node rows `G` (`q₃` slots of width `w₃`, `q₂` rows)
with factors `cp - cn` and coefficient bias `α₃`. -/
def factorRow (w₁ q₁ n₁ α₁ : ℕ) (R D : ℕ → ℕ) (w₂ q₂ : ℕ) (K : ℕ → ℕ) (e : ℕ)
    (w₃ q₃ α₃ : ℕ) (cp cn G : ℕ → ℕ) : ℕ :=
  packedRowCombination w₃ q₃ q₂ α₃
    (fun k ↦ factorCoefficient α₃ (cp k) (cn k) (2 ^ (w₂ - 1 - e))
      (slotShift w₂ e k (packedRowCombination w₂ q₂ q₁ (slotBias w₁)
        (fun l ↦ slot w₁ l (packedRowCombination w₁ q₁ n₁ α₁ R D)) K)))
    G

/-- The values of the first two stages: `H l = ∑_m (R m - α₁) D_m l` and
`y k = ∑_l H l K_l k`. -/
theorem signedSlot_factorRow_stages {w₁ q₁ n₁ α₁ : ℕ} {R D : ℕ → ℕ} {w₂ q₂ : ℕ} {K : ℕ → ℕ}
    (hD : ∀ m < n₁, D m < 2 ^ (w₁ * q₁)) (hK : ∀ l < q₁, K l < 2 ^ (w₂ * q₂))
    (hfit₁ : ∀ l < q₁, FitsSlot w₁ (∑ m ∈ range n₁, ((R m : ℤ) - α₁) * signedSlot w₁ l (D m)))
    (hfit₂ : ∀ k < q₂, FitsSlot w₂ (∑ l ∈ range q₁,
      (∑ m ∈ range n₁, ((R m : ℤ) - α₁) * signedSlot w₁ l (D m)) * signedSlot w₂ k (K l)))
    {k : ℕ} (hk : k < q₂) :
    signedSlot w₂ k (packedRowCombination w₂ q₂ q₁ (slotBias w₁)
        (fun l ↦ slot w₁ l (packedRowCombination w₁ q₁ n₁ α₁ R D)) K) =
      ∑ l ∈ range q₁,
        (∑ m ∈ range n₁, ((R m : ℤ) - α₁) * signedSlot w₁ l (D m)) * signedSlot w₂ k (K l) := by
  have hH : ∀ l < q₁, signedSlot w₁ l (packedRowCombination w₁ q₁ n₁ α₁ R D) =
      ∑ m ∈ range n₁, ((R m : ℤ) - α₁) * signedSlot w₁ l (D m) :=
    fun l hl ↦ signedSlot_packedRowCombination hD hfit₁ hl
  have hfit₂' : ∀ k < q₂, FitsSlot w₂ (∑ l ∈ range q₁,
      signedSlot w₁ l (packedRowCombination w₁ q₁ n₁ α₁ R D) * signedSlot w₂ k (K l)) := by
    intro k hk
    rw [sum_congr rfl fun l hl ↦ by rw [hH l (mem_range.mp hl)]]
    exact hfit₂ k hk
  rw [signedSlot_packedRowCombination_slots hK hfit₂' hk]
  exact sum_congr rfl fun l hl ↦ by rw [hH l (mem_range.mp hl)]

/-- Every slot of the three-stage row: `F n = ∑_k (cp k - cn k) z_k G_k n`, where `z_k` is the
rebiased shifted slot of the second stage. -/
theorem signedSlot_factorRow {w₁ q₁ n₁ α₁ : ℕ} {R D : ℕ → ℕ} {w₂ q₂ : ℕ} {K : ℕ → ℕ} {e : ℕ}
    {w₃ q₃ α₃ : ℕ} {cp cn G : ℕ → ℕ} (hG : ∀ k < q₂, G k < 2 ^ (w₃ * q₃))
    (hα : ∀ k < q₂, ((cp k : ℤ) - cn k) * ((slotShift w₂ e k (packedRowCombination w₂ q₂ q₁
      (slotBias w₁) (fun l ↦ slot w₁ l (packedRowCombination w₁ q₁ n₁ α₁ R D)) K) : ℤ) -
        2 ^ (w₂ - 1 - e)) + α₃ ≥ 0)
    (hfit₃ : ∀ n < q₃, FitsSlot w₃ (∑ k ∈ range q₂, ((cp k : ℤ) - cn k) *
      ((slotShift w₂ e k (packedRowCombination w₂ q₂ q₁ (slotBias w₁)
        (fun l ↦ slot w₁ l (packedRowCombination w₁ q₁ n₁ α₁ R D)) K) : ℤ) -
          2 ^ (w₂ - 1 - e)) * signedSlot w₃ n (G k)))
    {n : ℕ} (hn : n < q₃) :
    signedSlot w₃ n (factorRow w₁ q₁ n₁ α₁ R D w₂ q₂ K e w₃ q₃ α₃ cp cn G) =
      ∑ k ∈ range q₂, ((cp k : ℤ) - cn k) *
        ((slotShift w₂ e k (packedRowCombination w₂ q₂ q₁ (slotBias w₁)
          (fun l ↦ slot w₁ l (packedRowCombination w₁ q₁ n₁ α₁ R D)) K) : ℤ) -
            2 ^ (w₂ - 1 - e)) * signedSlot w₃ n (G k) := by
  have hcoef : ∀ k ∈ range q₂,
      ((factorCoefficient α₃ (cp k) (cn k) (2 ^ (w₂ - 1 - e))
        (slotShift w₂ e k (packedRowCombination w₂ q₂ q₁ (slotBias w₁)
          (fun l ↦ slot w₁ l (packedRowCombination w₁ q₁ n₁ α₁ R D)) K)) : ℤ) - α₃) =
      ((cp k : ℤ) - cn k) * ((slotShift w₂ e k (packedRowCombination w₂ q₂ q₁ (slotBias w₁)
        (fun l ↦ slot w₁ l (packedRowCombination w₁ q₁ n₁ α₁ R D)) K) : ℤ) -
          2 ^ (w₂ - 1 - e)) := fun k hk ↦ by
    exact_mod_cast factorCoefficient_eq (α := α₃) (cp := cp k) (cn := cn k)
      (b := 2 ^ (w₂ - 1 - e)) (u := slotShift w₂ e k (packedRowCombination w₂ q₂ q₁ (slotBias w₁)
        (fun l ↦ slot w₁ l (packedRowCombination w₁ q₁ n₁ α₁ R D)) K))
      (by push_cast; exact hα k (mem_range.mp hk))
  unfold factorRow
  rw [signedSlot_packedRowCombination hG (fun n hn ↦ by
    rw [sum_congr rfl fun k hk ↦ by rw [hcoef k hk]]; exact hfit₃ n hn) hn]
  exact sum_congr rfl fun k hk ↦ by rw [hcoef k hk]

/-- `factorRow` with the first two stages computed once, for compiled code: a compiled call
does not share the stages between the slots of the next stage. -/
def factorRowFast (w₁ q₁ n₁ α₁ : ℕ) (R D : ℕ → ℕ) (w₂ q₂ : ℕ) (K : ℕ → ℕ) (e : ℕ)
    (w₃ q₃ α₃ : ℕ) (cp cn G : ℕ → ℕ) : ℕ :=
  let H := packedRowCombination w₁ q₁ n₁ α₁ R D
  let Y := packedRowCombination w₂ q₂ q₁ (slotBias w₁) (fun l ↦ slot w₁ l H) K
  packedRowCombination w₃ q₃ q₂ α₃
    (fun k ↦ factorCoefficient α₃ (cp k) (cn k) (2 ^ (w₂ - 1 - e)) (slotShift w₂ e k Y)) G

/-- Compiled code evaluates `factorRow` as `factorRowFast`; proofs and kernel checks are
unchanged. -/
@[csimp] theorem factorRow_eq_factorRowFast : @factorRow = @factorRowFast := rfl

end CAS.Numerics

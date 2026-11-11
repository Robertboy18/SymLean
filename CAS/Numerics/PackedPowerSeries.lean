/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedLinearAlgebra
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

/-!
# Packed evaluation of polynomials at a rational point

The rows `rows p`, `p < N`, hold in `q` biased slots of width `w` the coefficients `c k p` of
`q` polynomials `∑ₚ c k p xᵖ`. At a point `x = u / v ∈ [0, 1]` the powers are kept on the grid
`2 ^ -P` by floor division, `powerScaled P u v (p + 1) = powerScaled P u v p * u / v`, which
stays within `p` units of `2 ^ P xᵖ` (`abs_powerScaled_sub_le`). One packed row combination
`packedPowerRow` evaluates all `q` polynomials at once: its slots are `∑ₚ Sₚ c k p` exactly
(`signedSlot_packedPowerRow`), within `∑ₚ |c k p| p` of `2 ^ P ∑ₚ c k p xᵖ`
(`abs_signedSlot_packedPowerRow_sub_le`).

## Implementation notes

The powers are the scalars of one `packedRowCombination` with offset `α = 0`, so all `q`
polynomials together cost `N` products of a power with a row and the additions of
[PackedLinearAlgebra](PackedLinearAlgebra.lean), whatever `q`. Only the powers are rounded.
`powerScaled` is a structural recursion on `p` from `1 <<< P`; each step loses less than one
unit to the floor and, since `u ≤ v`, does not enlarge the earlier error, which gives the bound
`p` of `abs_powerScaled_sub_le`. The packed sum is exact, so the error of slot `k` is at most the
errors of the powers weighted by `|c k p|`. The hypotheses are those of
`signedSlot_packedRowCombination`: every row below `2 ^ (w q)` and every exact sum fitting its
slot. No module of the library imports this one; certificates outside the library use it.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- The powers of `u / v` on the grid `2 ^ -P`, rounded down at every step. -/
def powerScaled (P u v : ℕ) : ℕ → ℕ
  | 0 => Nat.shiftLeft 1 P
  | p + 1 => Nat.div (Nat.mul (powerScaled P u v p) u) v

/-- The scaled power of exponent `0` is `2 ^ P`. -/
theorem powerScaled_zero (P u v : ℕ) : powerScaled P u v 0 = 2 ^ P := by
  simp only [powerScaled]
  rw [show Nat.shiftLeft 1 P = 1 <<< P from rfl, Nat.one_shiftLeft]

/-- The next scaled power is `powerScaled P u v p * u / v`, rounded down. -/
theorem powerScaled_succ (P u v p : ℕ) :
    powerScaled P u v (p + 1) = powerScaled P u v p * u / v := rfl

/-- The rounded powers stay within `p` units of `2 ^ P (u / v) ^ p` when `u ≤ v`. -/
theorem abs_powerScaled_sub_le {P u v : ℕ} (hv : 0 < v) (huv : u ≤ v) (p : ℕ) :
    |(powerScaled P u v p : ℝ) - 2 ^ P * ((u : ℝ) / v) ^ p| ≤ p := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hx0 : (0 : ℝ) ≤ (u : ℝ) / v := by positivity
  have hx1 : (u : ℝ) / v ≤ 1 := (div_le_one hvR).mpr (by exact_mod_cast huv)
  induction p with
  | zero => simp [powerScaled_zero]
  | succ p ih =>
    rw [powerScaled_succ]
    set S := powerScaled P u v p
    have hfloor : |(((S * u / v : ℕ) : ℝ)) - (S : ℝ) * u / v| ≤ 1 := by
      have h₁ : (((S * u / v : ℕ) : ℝ)) ≤ (S : ℝ) * u / v := by
        exact_mod_cast Nat.cast_div_le (α := ℝ) (m := S * u) (n := v)
      have h₂ : (S : ℝ) * u / v < (((S * u / v : ℕ) : ℝ)) + 1 := by
        rw [div_lt_iff₀ hvR]
        have h' : (S * u : ℝ) < ((S * u / v : ℕ) : ℝ) * v + v := by
          exact_mod_cast Nat.lt_div_mul_add (a := S * u) hv
        linarith
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have hmul : |(S : ℝ) * u / v - 2 ^ P * ((u : ℝ) / v) ^ (p + 1)| ≤ p := by
      rw [show (S : ℝ) * u / v - 2 ^ P * ((u : ℝ) / v) ^ (p + 1) =
          ((S : ℝ) - 2 ^ P * ((u : ℝ) / v) ^ p) * ((u : ℝ) / v) by rw [pow_succ]; ring,
        abs_mul, abs_of_nonneg hx0]
      exact (mul_le_of_le_one_right (abs_nonneg _) hx1).trans ih
    refine (abs_sub_le _ ((S : ℝ) * u / v) _).trans ?_
    push_cast
    linarith

/-- The packed values `∑ₚ Sₚ • row p` of the `q` polynomials stored in `rows`, at the point
`u / v`, with the powers `Sₚ = powerScaled P u v p`. -/
def packedPowerRow (w q P u v N : ℕ) (rows : ℕ → ℕ) : ℕ :=
  packedRowCombination w q N 0 (powerScaled P u v) rows

/-- The slots of the packed values are the exact sums `∑ₚ Sₚ c k p` once these fit. -/
theorem signedSlot_packedPowerRow {w q P u v N : ℕ} {rows : ℕ → ℕ}
    (hrows : ∀ p < N, rows p < 2 ^ (w * q))
    (hfit : ∀ k < q, FitsSlot w (∑ p ∈ range N,
      (powerScaled P u v p : ℤ) * signedSlot w k (rows p)))
    {k : ℕ} (hk : k < q) :
    signedSlot w k (packedPowerRow w q P u v N rows) =
      ∑ p ∈ range N, (powerScaled P u v p : ℤ) * signedSlot w k (rows p) := by
  simpa [packedPowerRow] using signedSlot_packedRowCombination (w := w) (q := q) (n := N)
    (α := 0) (s := powerScaled P u v) hrows (by simpa using hfit) hk

/-- The packed values approximate `2 ^ P` times the polynomials at `u / v`: the error of slot
`k` is at most `∑ₚ |c k p| p`. -/
theorem abs_signedSlot_packedPowerRow_sub_le {w q P u v N : ℕ} {rows : ℕ → ℕ}
    (hv : 0 < v) (huv : u ≤ v)
    (hrows : ∀ p < N, rows p < 2 ^ (w * q))
    (hfit : ∀ k < q, FitsSlot w (∑ p ∈ range N,
      (powerScaled P u v p : ℤ) * signedSlot w k (rows p)))
    {k : ℕ} (hk : k < q) :
    |(signedSlot w k (packedPowerRow w q P u v N rows) : ℝ) -
        2 ^ P * ∑ p ∈ range N, (signedSlot w k (rows p) : ℝ) * ((u : ℝ) / v) ^ p| ≤
      ∑ p ∈ range N, |(signedSlot w k (rows p) : ℝ)| * p := by
  rw [signedSlot_packedPowerRow hrows hfit hk]
  push_cast
  rw [mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ ↦ ?_)
  have h := abs_powerScaled_sub_le (P := P) hv huv p
  calc _ = |(signedSlot w k (rows p) : ℝ)| *
          |(powerScaled P u v p : ℝ) - 2 ^ P * ((u : ℝ) / v) ^ p| := by
        rw [← abs_mul]
        ring_nf
    _ ≤ |(signedSlot w k (rows p) : ℝ)| * p := by gcongr

end CAS.Numerics

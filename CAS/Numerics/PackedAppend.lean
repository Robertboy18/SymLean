/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedSpread
public import CAS.Numerics.PackedRounding
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.SuccPred.Nat
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# Splitting packed rows

A packed row of `h + m` slots is its low `h` slots plus the remaining `m` slots shifted up
(`packSlots_append`), and every entry is at most the row shifted down to its slot
(`le_shiftRight_packSlots`). `sub_constSlots_mod_eq` subtracts a constant `c` from the low `N`
slots of a longer row with one subtraction and one remainder: when slot `N` of the row is
positive and every slot of the result stays below `2 ^ w - c - 1`, no slot borrows, every one of
the low slots is at least `c`, and the result is the row of differences.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- A packing of `h + m` entries is the packing of the first `h` plus the packing of the next `m`
shifted up by `2 ^ (W * h)`, for entries of any size. -/
theorem packSlots_append (W h m : ℕ) (f : ℕ → ℕ) :
    packSlots W (h + m) f = packSlots W h f + packSlots W m (fun k ↦ f (h + k)) * 2 ^ (W * h) := by
  rw [packSlots_eq_sum, packSlots_eq_sum, packSlots_eq_sum, sum_range_add, sum_mul]
  congr 1
  refine sum_congr rfl fun k _ ↦ ?_
  rw [mul_assoc, ← pow_add, Nat.mul_add, Nat.add_comm (W * k)]

/-- For `q < N`, entry `q` is at most the packing of `N` entries shifted right by `w * q` bits,
for entries of any size. -/
theorem le_shiftRight_packSlots {w N : ℕ} (f : ℕ → ℕ) {q : ℕ} (hq : q < N) :
    f q ≤ Nat.shiftRight (packSlots w N f) (w * q) := by
  change f q ≤ packSlots w N f >>> (w * q)
  rw [Nat.shiftRight_eq_div_pow, Nat.le_div_iff_mul_le (by positivity), packSlots_eq_sum]
  exact single_le_sum (f := fun k ↦ f k * 2 ^ (w * k)) (fun _ _ ↦ Nat.zero_le _)
    (mem_range.mpr hq)

/-- Subtracting a constant row from the low `N` slots of a longer row, modulo `2 ^ (w N)`: when
slot `N` of the row is positive and every slot of the result stays below `2 ^ w - c - 1`, no slot
borrows, and the result is the row of differences. -/
theorem sub_constSlots_mod_eq {w N K c : ℕ} {r : ℕ → ℕ}
    (hr : ∀ k < N + K, r k < 2 ^ w) (hK : 0 < K) (hpos : 1 ≤ r N)
    (hX : ∀ k < N, slot w k ((packSlots w (N + K) r - packSlots w N fun _ ↦ c) % 2 ^ (w * N)) <
      2 ^ w - c - 1) :
    (∀ k < N, c ≤ r k) ∧
      (packSlots w (N + K) r - packSlots w N fun _ ↦ c) % 2 ^ (w * N) =
        packSlots w N fun k ↦ r k - c := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨fun k hk ↦ absurd hk (Nat.not_lt_zero k), ?_⟩
    rw [Nat.mul_zero, pow_zero, Nat.mod_one]
    rfl
  have hc : c + 1 < 2 ^ w := by have := hX 0 hN; omega
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  set M := 2 ^ (w * (n + 1)) with hM
  set Rlo := packSlots w (n + 1) r
  set H := packSlots w K fun k ↦ r (n + 1 + k)
  set C := packSlots w (n + 1) fun _ ↦ c
  have hsplit : packSlots w (n + 1 + K) r = Rlo + H * M := packSlots_append w (n + 1) K r
  have hH : 1 ≤ H := hpos.trans <| by
    simpa [Nat.shiftRight] using le_shiftRight_packSlots (w := w) (fun k ↦ r (n + 1 + k)) hK
  have hRlo : Rlo < M := packSlots_lt fun k hk ↦ hr k (by omega)
  have hw : 0 < w := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hc
  -- the constant row is below `(c + 1) 2 ^ (w n)`
  have hCtop : C < (c + 1) * 2 ^ (w * n) := by
    have : packSlots w n (fun _ ↦ c) < 2 ^ (w * n) := packSlots_lt fun _ _ ↦ by omega
    rw [show C = packSlots w n (fun _ ↦ c) + c * 2 ^ (w * n) from packSlots_succ w n _, add_mul,
      one_mul]
    omega
  have hMsplit : M = 2 ^ w * 2 ^ (w * n) := by
    rw [hM, Nat.mul_succ, pow_add, Nat.mul_comm (2 ^ (w * n))]
  have hCM : C < M := by
    rw [hMsplit]
    exact hCtop.trans_le (Nat.mul_le_mul_right _ (by omega))
  have hge : C ≤ Rlo := by
    by_contra hlt
    push Not at hlt
    have hXval : (Rlo + H * M - C) % M = Rlo + M - C := by
      have : M ≤ H * M := Nat.le_mul_of_pos_left _ hH
      rw [show Rlo + H * M - C = (Rlo + M - C) + (H - 1) * M by
        rw [Nat.sub_mul, one_mul]; omega, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (by omega)]
    have htop := hX n (by omega)
    rw [hsplit, hXval, slot_eq] at htop
    have hlow : (2 ^ w - c - 1) * 2 ^ (w * n) ≤ Rlo + M - C := by
      have : (2 ^ w - c - 1) * 2 ^ (w * n) + (c + 1) * 2 ^ (w * n) = M := by
        rw [hMsplit, ← add_mul]; congr 1; omega
      omega
    have hq := (Nat.le_div_iff_mul_le (by positivity)).mpr hlow
    have hlt' : (Rlo + M - C) / 2 ^ (w * n) < 2 ^ w := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← hMsplit]; omega
    rw [Nat.mod_eq_of_lt hlt'] at htop
    omega
  have hXeq : (packSlots w (n + 1 + K) r - C) % M = Rlo - C := by
    rw [hsplit, show Rlo + H * M - C = (Rlo - C) + H * M by omega, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (by omega)]
  have hle := le_of_sub_constSlots (w := w) (c := c) (n + 1) (r := r)
    (fun k hk ↦ hr k (by omega)) hge (fun k hk ↦ by
      have := hX k hk
      rw [hXeq] at this
      exact lt_of_lt_of_le this (Nat.sub_le _ _))
  exact ⟨hle, hXeq.trans (packSlots_sub hle)⟩

end CAS.Numerics

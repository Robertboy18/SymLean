/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedSlots
public import CAS.Numerics.TrigTable

/-!
# Stored trigonometric tables

A table of `n` integer pairs with entries of absolute value below `2 ^ 63` is stored as `2 n`
words of 64 bits, the cosine of entry `k` at word `2 k` and its sine at word `2 k + 1`, each
word holding the integer plus `2 ^ 63`. `binary64_words%` imports such a word list from
hexadecimal text as one packed literal with a balanced lookup tree, so a lookup reduces only
its own branch. With `p ≤ 62` every entry of `trigTable N p` fits.

## Main results

* `pairedWordEntry_trigTable_sound`: a stored copy of `trigTable N p` has the error bounds of
  `trigTable_sound`.
* `pairedWordEntry_trigTable_sound_mul`, `abs_pairedWordEntry_div_sub_cos_le`: the same bounds
  at the product index `n j`, and for the scaled cosine at every natural index, both reduced
  modulo `4 N`.

## Implementation notes

A lookup in the stored table reduces one branch of the word tree, while an entry of `trigTable`
costs the kernel a fixed-point π and two Taylor sums. We therefore identify a stored table with
the computed one once, by the finite check `∀ k, pairedWordEntry words k = trigTable N p k`, and
the main results transfer the bounds of `trigTable_sound` by rewriting with it. The words are
candidate data from outside the kernel, and this check is the only thing that makes them usable.
In the kernel profile it costs about 20 ms per entry, so a large table is checked in index ranges
with `RangeAll`. The words are read as offset integers (`offsetWordValue`, the signed 64-bit
slots of `PackedSlots`), not decoded as binary64 floating-point values.
-/

@[expose] public section

namespace CAS.Numerics

/-- The integer held by a 64-bit word with offset `2 ^ 63`. -/
def offsetWordValue (word : ℕ) : ℤ := (word : ℤ) - 9223372036854775808

/-- The offset decoding of a 64-bit slot is the signed slot of the packed-literal layer, since
`slotBias 64 = 2 ^ 63`. With `get_ofPacked`, every entry of a `binary64_words%` table is a
signed 64-bit slot of its literal. -/
theorem offsetWordValue_eq_signedSlot (x k : ℕ) :
    offsetWordValue (slot 64 k x) = signedSlot 64 k x := by
  rw [offsetWordValue, signedSlot, slotBias_succ 63]
  norm_num

/-- The pair stored at index `k`: the words `2 k` and `2 k + 1`. -/
def pairedWordEntry {n : ℕ} (words : Binary64WordTree (2 * n)) (k : Fin n) : ℤ × ℤ :=
  (offsetWordValue (words.get ⟨2 * k.val, by omega⟩),
    offsetWordValue (words.get ⟨2 * k.val + 1, by omega⟩))

/-- A stored copy of `trigTable N p` has the error bounds of `trigTable_sound`. -/
theorem pairedWordEntry_trigTable_sound {N p : ℕ} (hN : 0 < N)
    {words : Binary64WordTree (2 * (4 * N + 1))}
    (h : ∀ k, pairedWordEntry words k = trigTable N p k) (k : Fin (4 * N + 1)) :
    TrigApprox p (pairedWordEntry words k) (k * Real.pi / (2 * N)) := by
  rw [h k]
  exact trigTable_sound N p hN k

/-- In a stored copy of `trigTable N p`, the basis function of frequency `n` at the grid node
`j π / (2 N)` is the entry at `n j` modulo `4 N`. -/
theorem pairedWordEntry_trigTable_sound_mul {N p : ℕ} (hN : 0 < N)
    {words : Binary64WordTree (2 * (4 * N + 1))}
    (h : ∀ k, pairedWordEntry words k = trigTable N p k) (n j : ℕ) :
    TrigApprox p (pairedWordEntry words ⟨n * j % (4 * N), by
        have := Nat.mod_lt (n * j) (show 0 < 4 * N by omega); omega⟩)
      (n * (j * Real.pi / (2 * N))) := by
  rw [h, trigTable, trigPi_mod]
  exact trigPi_sound_mul N p hN n j

/-- In a stored copy of `trigTable N p`, the scaled cosine at the index `m` modulo `4 N` is
within `2 ^ (-p)` of `cos (m π / (2 N))`, for every natural `m`. -/
theorem abs_pairedWordEntry_div_sub_cos_le {N p : ℕ} (hN : 0 < N)
    {words : Binary64WordTree (2 * (4 * N + 1))}
    (h : ∀ k, pairedWordEntry words k = trigTable N p k) (m : ℕ) :
    |((pairedWordEntry words ⟨m % (4 * N), by
        have := Nat.mod_lt m (show 0 < 4 * N by omega); omega⟩).1 : ℝ) / 2 ^ p -
      Real.cos (m * Real.pi / (2 * N))| ≤ 1 / 2 ^ p := by
  rw [h, trigTable, trigPi_mod]
  exact abs_trigPi_div_sub_cos_le N p hN m

end CAS.Numerics

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.LaurentGram

/-!
# Two-stage evaluation of rows of exponential coefficients for many fields

The data of `F` fields are stored side by side: row `m` of a data array holds the integers
`D_{m,(a,l)}` of every field `a < F` and column `l < L` in the signed slots `a L + l`. With integer
mode values `κ_m` at one node:

* `stageOne`: `H_{a,l} = ∑_m κ_m D_{m,(a,l)}` for all fields at once, one packed combination of the
  data rows (`signedSlot_stageOne`);
* `stageTwo`: for one field `a`, the row `ξ_t = ∑_{(v, f)} ∑_l H^{(v)}_{a,l} K^{(f)}_{l,t}` of a
  list of terms, each pairing a first-stage vector `v` with a family `f` of rows `K^{(f)}_l`:
  the biased packing of `ξ`.

The fitting conditions are bounds on the slots; with them every step is exact. Only
`signedSlot_stageOne` is proved here: `stageTwo` is one `packedRowCombination` of
`terms.length * L` rows with the biased first-stage slots as coefficients, so
`signedSlot_packedRowCombination` gives its slots once they fit.

## Implementation notes

We store the fields side by side so that one combination of the `n` data rows forms the first
stage of all `F` fields at once; the second stage reads only the slots of its field. The signed
mode values enter as the naturals `(κ m + α).toNat` with bias `α`, which is exact when
`|κ m| ≤ α`, so both stages use natural-number operations only.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- The first stage for all fields: `H_{a,l} = ∑_{m < n} κ_m D_{m,(a,l)}` with the mode values
biased by `α`. -/
def stageOne (w₁ FL n α : ℕ) (κ : ℕ → ℤ) (D : ℕ → ℕ) : ℕ :=
  packedRowCombination w₁ FL n α (fun m ↦ (κ m + α).toNat) D

/-- The second stage for the field `a`: the rows `K f l` of the families of a list of terms,
combined with the first-stage slots of the field. -/
def stageTwo (W q L w₁ a : ℕ) (S : ℕ → ℕ) (K : ℕ → ℕ → ℕ) (terms : List (ℕ × ℕ)) : ℕ :=
  packedRowCombination W q (terms.length * L) (slotBias w₁)
    (fun i ↦ slot w₁ (a * L + i % L) (S (terms.getD (i / L) (0, 0)).1))
    (fun i ↦ K (terms.getD (i / L) (0, 0)).2 (i % L))

/-- The first-stage slots are the mode combinations of the data. -/
theorem signedSlot_stageOne {w₁ FL n α : ℕ} {κ : ℕ → ℤ} {D : ℕ → ℕ}
    (hD : ∀ m < n, D m < 2 ^ (w₁ * FL)) (hκ : ∀ m < n, -(α : ℤ) ≤ κ m ∧ κ m ≤ α)
    (hfit : ∀ k < FL, FitsSlot w₁ (∑ m ∈ range n, κ m * signedSlot w₁ k (D m)))
    {k : ℕ} (hk : k < FL) :
    signedSlot w₁ k (stageOne w₁ FL n α κ D) = ∑ m ∈ range n, κ m * signedSlot w₁ k (D m) := by
  have hcoef : ∀ m < n, (((κ m + α).toNat : ℕ) : ℤ) - α = κ m := fun m hm ↦ by
    have h := hκ m hm
    omega
  have hsum : ∀ k, (∑ m ∈ range n, ((((κ m + α).toNat : ℕ) : ℤ) - α) * signedSlot w₁ k (D m)) =
      ∑ m ∈ range n, κ m * signedSlot w₁ k (D m) := fun k ↦
    sum_congr rfl fun m hm ↦ by rw [hcoef m (mem_range.mp hm)]
  unfold stageOne
  rw [signedSlot_packedRowCombination hD (fun k hk ↦ by rw [hsum]; exact hfit k hk) hk, hsum]

end CAS.Numerics

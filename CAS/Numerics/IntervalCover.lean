/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order

/-!
# Checking a property on the cells of a walk

`coverWalk next ok fuel w e` walks from `w` to `e` through the nodes `min (next w) e` and checks
`ok` on every cell `[l, u]`; it fails if the fuel runs out or the nodes stop increasing.
`coverWalk_sound`: after a successful walk with `w < e`, every real `v ∈ [w, e]` lies in a cell
`[a, b]` with `w ≤ a` on which `ok` holds. This turns a cell check into a bound at every point
of an interval.

## Main definitions

* `coverWalk`: the walk from `w` to `e` through `min (next w) e`, checking `ok` on every cell.

## Main results

* `coverWalk_sound`: after a successful walk with `w < e`, every point of `[w, e]` lies in a cell
  `[a, b]` with `w ≤ a` on which `ok` holds.

## Implementation notes

We take the nodes from an arbitrary function `next`: `coverWalk_sound` holds for every `next`,
so untrusted code may choose the cells, and only the increase of the nodes and `ok` are checked.
The fuel bounds the walk because `next` need not approach `e`. The proof is an induction on the
fuel: a point of `[w, e]` lies in the first cell or in `[min (next w) e, e]`, which the rest of
the walk covers.
-/

@[expose] public section

namespace CAS.Numerics

/-- The walk from `w` to `e` through `min (next w) e`, checking `ok` on every cell. -/
def coverWalk (next : ℚ → ℚ) (ok : ℚ → ℚ → Bool) : ℕ → ℚ → ℚ → Bool
  | 0, _, _ => false
  | fuel + 1, w, e =>
    if e ≤ w then true
    else
      let w' := min (next w) e
      decide (w < w') && ok w w' && coverWalk next ok fuel w' e

/-- **Soundness of the walk**: every point of `[w, e]` lies in a cell where `ok` holds. -/
theorem coverWalk_sound {next : ℚ → ℚ} {ok : ℚ → ℚ → Bool} :
    ∀ (fuel : ℕ) (w e : ℚ), coverWalk next ok fuel w e = true → w < e →
      ∀ v : ℝ, (w : ℝ) ≤ v → v ≤ e →
        ∃ a b : ℚ, ok a b = true ∧ w ≤ a ∧ (a : ℝ) ≤ v ∧ v ≤ b
  | 0, _, _, h, _, _, _, _ => by simp [coverWalk] at h
  | fuel + 1, w, e, h, hwe, v, hv₀, hv₁ => by
    simp only [coverWalk, not_le.2 hwe, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlt, hok⟩, hrest⟩ := h
    set w' := min (next w) e
    by_cases hv : v ≤ w'
    · exact ⟨w, w', hok, le_rfl, hv₀, hv⟩
    · have hw'e : w' < e := by exact_mod_cast (not_le.1 hv).trans_le hv₁
      obtain ⟨a, b, hab, hwa, hav, hvb⟩ :=
        coverWalk_sound fuel w' e hrest hw'e v (not_le.1 hv).le hv₁
      exact ⟨a, b, hab, hlt.le.trans hwa, hav, hvb⟩

end CAS.Numerics

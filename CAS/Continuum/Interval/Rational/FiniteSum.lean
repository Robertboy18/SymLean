/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Bounds

/-!
# Finite sums of rational intervals

`sum s f` is the interval whose endpoints are the sums of the endpoints of `f i` over the
finite set `s`. `sum_sound` shows that it contains `∑ i ∈ s, g i` whenever each `f i` contains
`g i`. The extensionality lemma `ext` and the regrouping lemma `sum_fin_mul` let a sum over
`Fin (m * n)` be evaluated block by block.
`sum_memReal_of_bounds` assembles proposed bounds over any finite index type.

## Implementation notes

We sum the lower and the upper endpoints separately with `Finset.sum` in `ℚ`, so nothing is
rounded and `Finset.sum_le_sum` gives the endpoint order; `RationalInterval` has no additive
instance, so the interval itself is never a `Finset.sum`. `sum_sound` pushes the cast through
both sums with `Rat.cast_sum` and applies `Finset.sum_le_sum` twice. `sum_fin_mul` regroups
each endpoint sum along `finProdFinEquiv` with `Equiv.sum_comp` and `Fintype.sum_prod_type`. The
interval integrals, the products of `CAS.Continuum.Interval.Rational.Matrix`, the logarithmic
panels, `CAS.Continuum.Krawczyk.Interval` and the jets of `CAS.Numerics.IntervalJets` use `sum`,
and `CAS.Numerics.IntervalBalls` mirrors it on balls (`sumNat`).
-/

@[expose] public section

namespace CAS.Continuum.RationalInterval

/-- The interval `[∑ i ∈ s, (f i).lo, ∑ i ∈ s, (f i).hi]`. -/
def sum {ι : Type*} (s : Finset ι) (f : ι → RationalInterval) : RationalInterval where
  lo := ∑ i ∈ s, (f i).lo
  hi := ∑ i ∈ s, (f i).hi
  hle := Finset.sum_le_sum (fun i _ ↦ (f i).hle)

/-- A finite sum of enclosed real values is enclosed by the endpoint sum. -/
theorem sum_sound {ι : Type*} {s : Finset ι} {f : ι → RationalInterval} {g : ι → ℝ}
    (h : ∀ i ∈ s, (f i).MemReal (g i)) :
    (sum s f).MemReal (∑ i ∈ s, g i) := by
  simp only [MemReal, sum, Rat.cast_sum]
  exact ⟨Finset.sum_le_sum fun i hi ↦ (h i hi).1, Finset.sum_le_sum fun i hi ↦ (h i hi).2⟩

/-- Summed stored bounds contain every value enclosed by a finite interval sum.
The endpoints need only bound each summand; they need not equal its endpoints. -/
theorem sum_memReal_of_bounds {ι : Type*} [Fintype ι]
    (f : ι → RationalInterval) (ends : ι → ℚ × ℚ) (I : RationalInterval)
    (h : ∀ i, (ends i).1 ≤ (f i).lo ∧ (f i).hi ≤ (ends i).2)
    (hsum : ((∑ i, (ends i).1), (∑ i, (ends i).2)) = (I.lo, I.hi))
    {x : ℝ} (hx : (sum Finset.univ f).MemReal x) : I.MemReal x := by
  obtain ⟨h1, h2⟩ := Prod.mk.inj hsum
  exact mem_Icc_of_bounds hx (h1 ▸ Finset.sum_le_sum fun i _ ↦ (h i).1)
    (h2 ▸ Finset.sum_le_sum fun i _ ↦ (h i).2)

/-- A rational interval is determined by its endpoints. -/
@[ext]
theorem ext {I J : RationalInterval} (hlo : I.lo = J.lo) (hhi : I.hi = J.hi) : I = J := by
  rcases I with ⟨⟨a, b⟩, hab⟩
  rcases J with ⟨⟨c, d⟩, hcd⟩
  cases hlo
  cases hhi
  rfl

/-- A sum over `Fin (m * n)` is the double sum over `Fin m × Fin n` via `finProdFinEquiv`. -/
theorem sum_fin_mul {m n : ℕ} (f : Fin (m * n) → RationalInterval) :
    sum Finset.univ f = sum Finset.univ (fun i : Fin m ↦
      sum Finset.univ (fun j : Fin n ↦ f (finProdFinEquiv (i, j)))) := by
  ext
  · exact (finProdFinEquiv.sum_comp (fun i ↦ (f i).lo)).symm.trans (Fintype.sum_prod_type _)
  · exact (finProdFinEquiv.sum_comp (fun i ↦ (f i).hi)).symm.trans (Fintype.sum_prod_type _)

end CAS.Continuum.RationalInterval

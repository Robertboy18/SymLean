/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.FiniteSum
public import CAS.Continuum.Interval.Rational.Arithmetic

/-!
# Interval enclosures of matrix products and of `trace (A ^ 4)`

`matrixMul A B` encloses each entry of a product of interval matrices by the interval sum of
the interval products `A i k * B k j`. `matrixTraceFourth A` encloses `trace (a ^ 4)` as
`∑ i j, (a * a) i j * (a * a) j i`. The soundness theorems `matrixMul_sound` and
`matrixTraceFourth_sound` hold for every real matrix `a` with entries in `A`, symmetric or not.

## Implementation notes

Each entry of `matrixMul` is a `sum` of exact products `RationalInterval.mul`, so nothing is
rounded. The products keep their signs, so terms of opposite sign can cancel in the sum, where a
bound through absolute values would add them up. `matrixTraceFourth` needs only the square
`B = matrixMul A A`; `B` is a function, so for an `n × n` matrix each of the `n ^ 2` terms
`B i j * B j i` recomputes its two entries. `matrixMul_sound` is `sum_sound` of `mul_sound`, and
`matrixTraceFourth_sound` rewrites `a ^ 4 = (a * a) * (a * a)` with `pow_mul` and `pow_two` and
nests the same two lemmas. No module of SymLean imports this one; it serves certificates built on
the library.

## References

* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Section 9 for interval matrix operations, which replace each real operation by the interval
  operation.
-/

@[expose] public section

namespace CAS.Continuum.RationalInterval

variable {ι κ ν : Type*} [Fintype κ]

/-- Entrywise enclosure of a matrix product: `∑ k, A i k * B k j` in interval arithmetic. -/
def matrixMul (A : Matrix ι κ RationalInterval) (B : Matrix κ ν RationalInterval) :
    Matrix ι ν RationalInterval :=
  fun i j ↦ sum Finset.univ (fun k ↦ (A i k).mul (B k j))

/-- If `a` and `b` have entries in `A` and `B`, then `a * b` has entries in `matrixMul A B`. -/
theorem matrixMul_sound {A : Matrix ι κ RationalInterval} {B : Matrix κ ν RationalInterval}
    {a : Matrix ι κ ℝ} {b : Matrix κ ν ℝ}
    (ha : ∀ i k, (A i k).MemReal (a i k)) (hb : ∀ k j, (B k j).MemReal (b k j))
    (i : ι) (j : ν) :
    (matrixMul A B i j).MemReal ((a * b) i j) :=
  sum_sound (fun k (_ : k ∈ (Finset.univ : Finset κ)) ↦ mul_sound (ha i k) (hb k j))

variable [Fintype ι]

/-- Enclosure of `trace (a ^ 4)` as `∑ i j, B i j * B j i` with `B = matrixMul A A`. -/
def matrixTraceFourth (A : Matrix ι ι RationalInterval) : RationalInterval :=
  let B := matrixMul A A
  sum Finset.univ (fun i ↦ sum Finset.univ (fun j ↦ (B i j).mul (B j i)))

/-- If `a` has entries in `A`, then `matrixTraceFourth A` contains `trace (a ^ 4)`. -/
theorem matrixTraceFourth_sound [DecidableEq ι]
    {A : Matrix ι ι RationalInterval} {a : Matrix ι ι ℝ}
    (ha : ∀ i j, (A i j).MemReal (a i j)) :
    (matrixTraceFourth A).MemReal (Matrix.trace (a ^ 4)) := by
  have hs := matrixMul_sound ha ha
  have hfour : a ^ 4 = (a * a) * (a * a) := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
  exact hfour ▸ sum_sound fun i _ ↦ sum_sound fun j _ ↦ mul_sound (hs i j) (hs j i)

end CAS.Continuum.RationalInterval

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedSlots
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring.RingNF

/-!
# Products of packed rows

The product of two packed rows of natural numbers is the packed row of their convolution:
`packSlots W n u * packSlots W m v = packSlots W (n + m) (packedConvolution n m u v)`
(`packSlots_mul_packSlots`), so one natural multiplication gives every coefficient
`∑_{i + j = q} u i v j` of a product of polynomials, or of trigonometric sums collected by
frequency, once these fit the slots (`slot_packSlots_mul`). Reversing one factor gives the
correlation `∑_{i - j = q}` in the same way.

## Main results

* `packSlots_mul_packSlots`: the product identity, for all entries, carries included.
* `slot_packSlots_mul`: when every coefficient is below `2 ^ W`, slot `q` of the product is the
  coefficient `q`.
* `packedConvolution_reverse_eq`, `packedConvolution_reverse_right_eq`: correlations as slots of
  the product with one factor reversed.
* `packedConvolution_le`: each coefficient is at most `∑ u` times a bound of `v`.
* `sum_packedConvolution`: the coefficients sum to the product of the sums of the factors.

## Implementation notes

The product identity is the classical Kronecker substitution: packing the coefficients in slots
of `W` bits evaluates the polynomial at `2 ^ W`, and the coefficients of the product can be read
from the bits of one integer product as long as they do not overlap. In the kernel that product
is one multiplication of natural-number literals by the arbitrary-precision library (see
[PackedSlots](PackedSlots.lean)), so a certificate that needs all `n + m - 1` coefficients, or
one correlation slot, pays one big multiplication instead of `n m` small products.

## References

* David Harvey, "Faster polynomial multiplication via multipoint Kronecker substitution",
  *Journal of Symbolic Computation* 44 (2009), pp. 1502-1510,
  <https://doi.org/10.1016/j.jsc.2009.05.004>. Section 1 describes the standard substitution:
  evaluate at a power of two, multiply the integers, read the coefficients from the bits.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

/-- The convolution `∑_{i < n, j < m, i + j = q} u i v j`. -/
def packedConvolution (n m : ℕ) (u v : ℕ → ℕ) (q : ℕ) : ℕ :=
  ∑ i ∈ range n, ∑ j ∈ range m, if i + j = q then u i * v j else 0

/-- Kronecker substitution: the product of the packings of `n` and `m` entries in slots of width
`W` is the packing of the `n + m` coefficients of their convolution, for entries of any size. -/
theorem packSlots_mul_packSlots (W n m : ℕ) (u v : ℕ → ℕ) :
    packSlots W n u * packSlots W m v = packSlots W (n + m) (packedConvolution n m u v) := by
  rw [packSlots_eq_sum, packSlots_eq_sum, packSlots_eq_sum, sum_mul_sum]
  symm
  simp only [packedConvolution, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [mem_range] at hi hj
  rw [sum_ite_eq]
  simp only [mem_range, show i + j < n + m by omega, ↓reduceIte, Nat.mul_add, pow_add]
  ring

/-- If every coefficient `packedConvolution n m u v q` with `q < n + m` is below `2 ^ W`, then
for each `q < n + m`, slot `q` of `packSlots W n u * packSlots W m v` is coefficient `q`. -/
theorem slot_packSlots_mul {W n m : ℕ} {u v : ℕ → ℕ}
    (h : ∀ q < n + m, packedConvolution n m u v q < 2 ^ W) {q : ℕ} (hq : q < n + m) :
    slot W q (packSlots W n u * packSlots W m v) = packedConvolution n m u v q := by
  rw [packSlots_mul_packSlots, slot_packed_eq h]
  simp [hq]

/-- Correlation by one product: with the first factor reversed, slot `K - 1 + n` of the
convolution is `∑_{k < K} u k v (k + n)`. -/
theorem packedConvolution_reverse_eq (K M : ℕ) (u v : ℕ → ℕ) {n : ℕ} (hn : n + K ≤ M) :
    packedConvolution K M (fun i ↦ u (K - 1 - i)) v (K - 1 + n) =
      ∑ k ∈ range K, u k * v (k + n) := by
  unfold packedConvolution
  have h : ∀ i ∈ range K, (∑ j ∈ range M, if i + j = K - 1 + n then u (K - 1 - i) * v j else 0) =
      u (K - 1 - i) * v (K - 1 - i + n) := fun i hi ↦ by
    rw [mem_range] at hi
    rw [sum_eq_single (K - 1 - i + n)]
    · simp only [show i + (K - 1 - i + n) = K - 1 + n by omega, ↓reduceIte]
    · intro j _ hj
      simp only [show ¬ (i + j = K - 1 + n) by omega, ↓reduceIte]
    · exact fun hj ↦ absurd (mem_range.2 (by omega)) hj
  rw [sum_congr rfl h]
  exact sum_range_reflect (fun k ↦ u k * v (k + n)) K

/-- Each coefficient of a convolution is at most `∑ u` times a bound of `v`. -/
theorem packedConvolution_le (n m : ℕ) (u v : ℕ → ℕ) (B : ℕ) (hv : ∀ j, v j ≤ B) (q : ℕ) :
    packedConvolution n m u v q ≤ (∑ i ∈ range n, u i) * B := by
  unfold packedConvolution
  rw [sum_mul]
  refine sum_le_sum fun i _ ↦ ?_
  by_cases hiq : i ≤ q
  · calc (∑ j ∈ range m, if i + j = q then u i * v j else 0)
        = ∑ j ∈ range m, if q - i = j then u i * v j else 0 :=
          sum_congr rfl fun j _ ↦ if_congr (by omega) rfl rfl
      _ ≤ u i * v (q - i) := by
          rw [sum_ite_eq]
          split_ifs <;> simp
      _ ≤ u i * B := Nat.mul_le_mul_left _ (hv _)
  · calc (∑ j ∈ range m, if i + j = q then u i * v j else 0) = 0 :=
          sum_eq_zero fun j _ ↦ by simp only [show ¬ (i + j = q) by omega, ↓reduceIte]
      _ ≤ u i * B := Nat.zero_le _

/-- Correlation by one product with the second factor reversed: slot `M - 1 - n` of the
convolution is `∑_{k < K} u k v (k + n)`. -/
theorem packedConvolution_reverse_right_eq (K M : ℕ) (u v : ℕ → ℕ) {n : ℕ} (hn : n + K ≤ M) :
    packedConvolution K M u (fun j ↦ v (M - 1 - j)) (M - 1 - n) =
      ∑ k ∈ range K, u k * v (k + n) := by
  unfold packedConvolution
  refine sum_congr rfl fun k hk ↦ ?_
  rw [mem_range] at hk
  rw [sum_eq_single (M - 1 - n - k)]
  · simp only [show k + (M - 1 - n - k) = M - 1 - n by omega, ↓reduceIte,
      show M - 1 - (M - 1 - n - k) = k + n by omega]
  · intro j _ hj
    simp only [show ¬ (k + j = M - 1 - n) by omega, ↓reduceIte]
  · exact fun hj ↦ absurd (mem_range.2 (by omega)) hj

/-- The coefficients of a convolution sum to the product of the sums of the factors. -/
theorem sum_packedConvolution (n m : ℕ) (u v : ℕ → ℕ) :
    ∑ q ∈ range (n + m), packedConvolution n m u v q =
      (∑ i ∈ range n, u i) * ∑ j ∈ range m, v j := by
  unfold packedConvolution
  rw [sum_comm, sum_mul_sum]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [mem_range] at hi hj
  rw [sum_ite_eq]
  simp [show i + j < n + m by omega]

end CAS.Numerics

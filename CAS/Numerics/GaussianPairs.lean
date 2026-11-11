/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Gaussian integers as pairs of integers

Exact computations with complex numbers of integer coordinates, such as the powers `(a + b i)ⁿ`
of a lattice point or the Horner evaluation of a Taylor polynomial in `x + i y`, are carried out on
pairs `(re, im) : ℤ × ℤ` with executable operations. `gaussianToComplex` sends a pair to the
complex number `re + im i`; it turns `gaussianMul` into multiplication and componentwise addition
into addition, and the binary powering `gaussianPow` computes the complex power.

## Main definitions

* `gaussianMul`: the product of pairs, `(x₁ + y₁ i)(x₂ + y₂ i)`.
* `gaussianBinaryPow`, `gaussianPow`: binary powering with a recursion bound, and the power.
* `gaussianIPow`: the pair of `iᵗ`.
* `gaussianToComplex`: the complex number of a pair.

## Main results

* `gaussianToComplex_mul`, `gaussianToComplex_add`, `gaussianToComplex_smul`: products, sums and
  integer multiples of pairs are those of their complex numbers.
* `gaussianPow_eq`: `gaussianPow z n` is the complex power `zⁿ`.
* `gaussianToComplex_iPow`: `gaussianIPow t` is `iᵗ`.
* `gaussianToComplex_re`, `gaussianToComplex_im`, `gaussianToComplex_conj`,
  `normSq_gaussianToComplex`: coordinates, conjugate and squared modulus.

## Implementation notes

The complex numbers of Mathlib have no equality that the kernel could decide, so we compute on
the pairs and carry the result to `ℂ` once for all inputs: `gaussianToComplex_add` by `push_cast`
and `ring`, `gaussianToComplex_mul` with `Complex.I_sq` as well, and `gaussianPow_eq` by induction
on the fuel of `gaussianBinaryPow` (`gaussianBinaryPow_eq`). The fuel only makes the recursion
structural, so the kernel unfolds it without well-founded recursion. Each step halves the exponent
and costs one or two products of pairs; any fuel of at least `n` gives the power, and
`gaussianPow z n` takes fuel `n`. `gaussianIPow t` looks `iᵗ` up from `t % 4`, with no product
at all. No module of SymLean imports this one; it serves certificates built on the library.
-/

@[expose] public section

open scoped ComplexConjugate

namespace CAS.Numerics

/-- The product of the Gaussian integers `x₁ + y₁ i` and `x₂ + y₂ i`, as pairs. -/
def gaussianMul (z w : ℤ × ℤ) : ℤ × ℤ := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- Binary powering of a Gaussian integer; `fuel` bounds the recursion depth. -/
def gaussianBinaryPow (z : ℤ × ℤ) : ℕ → ℕ → ℤ × ℤ
  | 0, _ => (1, 0)
  | fuel + 1, n =>
    if n = 0 then (1, 0)
    else
      let h := gaussianBinaryPow z fuel (n / 2)
      if n % 2 = 0 then gaussianMul h h else gaussianMul (gaussianMul h h) z

/-- The power `z ^ n` of a Gaussian integer. -/
def gaussianPow (z : ℤ × ℤ) (n : ℕ) : ℤ × ℤ := gaussianBinaryPow z n n

/-- The pair of `iᵗ`: `(1, 0)`, `(0, 1)`, `(-1, 0)` or `(0, -1)` according to `t mod 4`. -/
def gaussianIPow (t : ℕ) : ℤ × ℤ :=
  if t % 4 = 0 then (1, 0) else if t % 4 = 1 then (0, 1) else if t % 4 = 2 then (-1, 0) else (0, -1)

/-- The complex number `x + y i` of a pair. -/
noncomputable def gaussianToComplex (z : ℤ × ℤ) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

/-- The complex number of a product of pairs is the product of their complex numbers. -/
theorem gaussianToComplex_mul (z w : ℤ × ℤ) :
    gaussianToComplex (gaussianMul z w) = gaussianToComplex z * gaussianToComplex w := by
  simp only [gaussianToComplex, gaussianMul]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The complex number of a sum of pairs is the sum of their complex numbers. -/
theorem gaussianToComplex_add (z w : ℤ × ℤ) :
    gaussianToComplex (z + w) = gaussianToComplex z + gaussianToComplex w := by
  simp only [gaussianToComplex, Prod.fst_add, Prod.snd_add]
  push_cast
  ring

/-- Multiplying both entries of a pair by an integer `k` multiplies its complex number by `k`. -/
theorem gaussianToComplex_smul (k : ℤ) (z : ℤ × ℤ) :
    gaussianToComplex (k * z.1, k * z.2) = (k : ℂ) * gaussianToComplex z := by
  simp only [gaussianToComplex]
  push_cast
  ring

/-- The pair `gaussianIPow t` is the complex number `iᵗ`. -/
theorem gaussianToComplex_iPow (t : ℕ) : gaussianToComplex (gaussianIPow t) = Complex.I ^ t := by
  rw [← Nat.div_add_mod t 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]
  have h := Nat.mod_lt t (by norm_num : 4 > 0)
  interval_cases h' : t % 4 <;> simp [gaussianIPow, gaussianToComplex, pow_succ]

/-- The imaginary part of the complex number of a pair is its second entry. -/
theorem gaussianToComplex_im (a : ℤ × ℤ) : (gaussianToComplex a).im = a.2 := by
  simp [gaussianToComplex]

/-- The real part of the complex number of a pair is its first entry. -/
theorem gaussianToComplex_re (a : ℤ × ℤ) : (gaussianToComplex a).re = a.1 := by
  simp [gaussianToComplex]

/-- Negating the second entry of a pair conjugates its complex number. -/
theorem gaussianToComplex_conj (a : ℤ × ℤ) :
    gaussianToComplex (a.1, -a.2) = conj (gaussianToComplex a) := by
  apply Complex.ext <;> simp [gaussianToComplex]

/-- The squared modulus of the complex number of `(a₁, a₂)` is `a₁² + a₂²`. -/
theorem normSq_gaussianToComplex (a : ℤ × ℤ) :
    Complex.normSq (gaussianToComplex a) = ((a.1 ^ 2 + a.2 ^ 2 : ℤ) : ℝ) := by
  rw [Complex.normSq_apply, gaussianToComplex_re, gaussianToComplex_im]
  push_cast
  ring

/-- Binary powering with enough fuel computes the complex power. -/
theorem gaussianBinaryPow_eq (z : ℤ × ℤ) (fuel n : ℕ) (hn : n ≤ fuel) :
    gaussianToComplex (gaussianBinaryPow z fuel n) = gaussianToComplex z ^ n := by
  induction fuel generalizing n with
  | zero =>
    obtain rfl : n = 0 := by omega
    simp [gaussianBinaryPow, gaussianToComplex]
  | succ fuel ih =>
    rw [gaussianBinaryPow]
    split_ifs with h0 h2
    · subst h0
      simp [gaussianToComplex]
    · rw [gaussianToComplex_mul, ih (n / 2) (by omega), ← pow_add,
        show n / 2 + n / 2 = n by omega]
    · rw [gaussianToComplex_mul, gaussianToComplex_mul, ih (n / 2) (by omega), ← pow_add,
        ← pow_succ, show n / 2 + n / 2 + 1 = n by omega]

/-- `gaussianPow z n` is the complex power `zⁿ`. -/
theorem gaussianPow_eq (z : ℤ × ℤ) (n : ℕ) :
    gaussianToComplex (gaussianPow z n) = gaussianToComplex z ^ n :=
  gaussianBinaryPow_eq z n n le_rfl

end CAS.Numerics

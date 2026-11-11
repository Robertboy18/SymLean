/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.SpecialFunctions.Bernoulli
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# Coefficient lists of the Chebyshev, Hermite and Bernoulli polynomials

`intPoly R l` is the polynomial `c₀ + X (c₁ + X (c₂ + …))` of an integer coefficient list
`l = [c₀, c₁, …]` in `R[X]`. The lists below follow the recurrences of Mathlib's polynomials, and
each comes with the theorem that identifies its polynomial with Mathlib's, for every degree.

## Main results

* `chebyshevT_eq_intPoly`, `chebyshevU_eq_intPoly`: `T R n` and `U R n` in every commutative
  ring, by `P_{k+2} = 2 X P_{k+1} - P_k`.
* `hermite_eq_intPoly`: Mathlib's probabilists' `hermite n`, by `He_{k+1} = X Heₖ - Heₖ'`.
* `sqrt_two_pow_mul_aeval_hermite`: the physicists' `Hₙ (x) = √2 ^ n Heₙ (√2 x)` is the
  polynomial of `physHermiteCoeffs n`, by `H_{k+1} = 2 X Hₖ - Hₖ'`.
* `bernoulli_eq_intPoly`: `Polynomial.bernoulli n` is `1 / (n + 1)!` times the polynomial of
  `bernoulliPolyNumerators n`, the coefficients `C(n, i) B_{n-i} (n + 1)!` read from
  `bernoulliNumerators n`.

## Implementation notes

The recurrences are classical. We run them on integer coefficient lists, which the kernel
evaluates at a given degree in a few list operations. A `#cas` command for one of these families
proves the monomial expansion at degree `n` by one such evaluation (`decide +kernel`), the
theorem above that identifies the list with Mathlib's polynomial, and one `ring` normalization,
instead of one `ring` step per degree. The Chebyshev and Hermite identifications are proved by
induction on the degree along the same recurrences; the Bernoulli one compares coefficients with
Mathlib's `Polynomial.coeff_bernoulli`.

## References

* NIST Digital Library of Mathematical Functions, §18.9 Recurrence Relations and Derivatives,
  Version 1.2.8 (2026-09-15), <https://dlmf.nist.gov/18.9>. The three-term recurrence (18.9.1)
  with Table 18.9.1 for `Tₙ` and `Uₙ`. (18.9.26) and (18.9.28) give the derivatives of
  `e^(-x²) Hₙ` and `e^(-x²/2) Heₙ`; written out, they are `H_{n+1} = 2 x Hₙ - Hₙ'` and
  `He_{n+1} = x Heₙ - Heₙ'`.
* NIST Digital Library of Mathematical Functions, §18.7 Interrelations and Limit Relations,
  Version 1.2.8 (2026-09-15), <https://dlmf.nist.gov/18.7>. `Hₙ (x) = 2^(n/2) Heₙ (√2 x)` is
  (18.7.12).
* NIST Digital Library of Mathematical Functions, §24.2 Definitions and Generating Functions,
  Version 1.2.8 (2026-09-15), <https://dlmf.nist.gov/24.2>. `Bₙ (x) = ∑ k ≤ n, C(n, k) Bₖ x^(n-k)`
  is (24.2.5).
-/

@[expose] public section

namespace CAS.Analysis.SpecialFunctions

open _root_.Polynomial Finset

/-! ### Integer coefficient lists -/

/-- The polynomial `c₀ + X (c₁ + X (c₂ + …))` of the integer list `[c₀, c₁, …]` in `R[X]`. -/
noncomputable def intPoly (R : Type*) [Ring R] : List ℤ → R[X]
  | [] => 0
  | c :: l => (c : R[X]) + X * intPoly R l

section IntPoly

variable {R : Type*} [CommRing R]

/-- The empty coefficient list denotes the zero polynomial. -/
@[simp] theorem intPoly_nil : intPoly R [] = 0 := rfl

/-- The list `c :: l` denotes `c + X * intPoly R l`. -/
@[simp] theorem intPoly_cons (c : ℤ) (l : List ℤ) :
    intPoly R (c :: l) = (c : R[X]) + X * intPoly R l := rfl

/-- The coefficients of `intPoly R l` are the entries of `l`. -/
theorem coeff_intPoly (l : List ℤ) (i : ℕ) : (intPoly R l).coeff i = (l.getD i 0 : R) := by
  induction l generalizing i with
  | nil => simp
  | cons c l ih =>
    cases i with
    | zero => simp only [intPoly_cons, ← C_eq_intCast, coeff_add, coeff_C_zero, coeff_X_mul_zero,
        add_zero, List.getD_cons_zero]
    | succ i => simp only [intPoly_cons, ← C_eq_intCast, coeff_add, coeff_C_succ, coeff_X_mul, ih,
        zero_add, List.getD_cons_succ]

/-- The sum of two coefficient lists. -/
def addCoeffs : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addCoeffs p q

/-- A multiple `c l` of a coefficient list. -/
def scaleCoeffs (c : ℤ) (l : List ℤ) : List ℤ := l.map (c * ·)

/-- The list `[k c₀, (k + 1) c₁, (k + 2) c₂, …]` of `l = [c₀, c₁, …]`. -/
def derivCoeffsFrom (k : ℕ) : List ℤ → List ℤ
  | [] => []
  | c :: l => (k * c) :: derivCoeffsFrom (k + 1) l

/-- The derivative of a coefficient list. -/
def derivCoeffs : List ℤ → List ℤ
  | [] => []
  | _ :: l => derivCoeffsFrom 1 l

/-- Over a commutative ring `R`, the list `addCoeffs p q` denotes the sum of the polynomials of `p`
and `q`, for lists of any lengths. -/
theorem intPoly_addCoeffs (p q : List ℤ) :
    intPoly R (addCoeffs p q) = intPoly R p + intPoly R q := by
  fun_induction addCoeffs p q with
  | case1 => simp
  | case2 => simp
  | case3 a p b q ih =>
    simp only [intPoly_cons, ih, Int.cast_add]
    ring

/-- Over a commutative ring `R`, the list `scaleCoeffs c l` denotes `c` times the polynomial of
`l`. -/
theorem intPoly_scaleCoeffs (c : ℤ) (l : List ℤ) :
    intPoly R (scaleCoeffs c l) = (c : R[X]) * intPoly R l := by
  induction l with
  | nil => simp [scaleCoeffs]
  | cons a l ih =>
    simp only [scaleCoeffs, List.map_cons, intPoly_cons, Int.cast_mul] at ih ⊢
    rw [ih]
    ring

/-- Over a commutative ring `R`, the list `derivCoeffsFrom k l` denotes `k p + X p'`, where `p` is
the polynomial of `l` and `p'` its derivative. -/
theorem intPoly_derivCoeffsFrom (k : ℕ) (l : List ℤ) :
    intPoly R (derivCoeffsFrom k l) = (k : R[X]) * intPoly R l + X * derivative (intPoly R l) := by
  induction l generalizing k with
  | nil => simp [derivCoeffsFrom]
  | cons c l ih =>
    simp only [derivCoeffsFrom, intPoly_cons, ih, Int.cast_mul, Int.cast_natCast,
      derivative_add, derivative_intCast, derivative_mul, derivative_X, Nat.cast_add, Nat.cast_one]
    ring

/-- Over a commutative ring `R`, the list `derivCoeffs l` denotes the derivative of the polynomial
of `l`. -/
theorem intPoly_derivCoeffs (l : List ℤ) :
    intPoly R (derivCoeffs l) = derivative (intPoly R l) := by
  cases l with
  | nil => simp [derivCoeffs]
  | cons c l =>
    simp [derivCoeffs, intPoly_derivCoeffsFrom, derivative_mul]

end IntPoly

/-! ### Chebyshev polynomials -/

/-- `2 X q - p` on coefficient lists. -/
def chebyshevStep (p q : List ℤ) : List ℤ := addCoeffs (scaleCoeffs 2 (0 :: q)) (scaleCoeffs (-1) p)

/-- The coefficient lists of `Pₙ` and `Pₙ₊₁` for `P_{k+2} = 2 X P_{k+1} - P_k`, `P₀ = 1` and
`P₁ = p₁`: `p₁ = [0, 1]` gives `Tₙ`, `p₁ = [0, 2]` gives `Uₙ`. -/
def chebyshevCoeffs (p₁ : List ℤ) : ℕ → List ℤ × List ℤ
  | 0 => ([1], p₁)
  | n + 1 =>
    let pq := chebyshevCoeffs p₁ n
    (pq.2, chebyshevStep pq.1 pq.2)

/-- A sequence with `P₀ = 1`, `P₁ = intPoly R p₁` and `P_{k+2} = 2 X P_{k+1} - P_k` is given by
`chebyshevCoeffs p₁`. -/
theorem chebyshevCoeffs_spec {R : Type*} [CommRing R] (P : ℤ → R[X]) (p₁ : List ℤ)
    (h₀ : P 0 = 1) (h₁ : P 1 = intPoly R p₁)
    (hstep : ∀ n : ℤ, P (n + 2) = 2 * X * P (n + 1) - P n) (n : ℕ) :
    P n = intPoly R (chebyshevCoeffs p₁ n).1 ∧ P (n + 1) = intPoly R (chebyshevCoeffs p₁ n).2 := by
  induction n with
  | zero => simp [chebyshevCoeffs, h₀, h₁]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    push_cast
    refine ⟨by rw [h2]; rfl, ?_⟩
    rw [show (n : ℤ) + 1 + 1 = n + 2 by ring, hstep, h1, h2]
    simp only [chebyshevCoeffs, chebyshevStep, intPoly_addCoeffs, intPoly_scaleCoeffs,
      intPoly_cons]
    push_cast
    ring

/-- `Tₙ` in every commutative ring is the polynomial of `(chebyshevCoeffs [0, 1] n).1`. -/
theorem chebyshevT_eq_intPoly (R : Type*) [CommRing R] (n : ℕ) :
    Chebyshev.T R n = intPoly R (chebyshevCoeffs [0, 1] n).1 :=
  (chebyshevCoeffs_spec (Chebyshev.T R) [0, 1] (Chebyshev.T_zero R) (by simp [Chebyshev.T_one R])
    (Chebyshev.T_add_two R) n).1

/-- `Uₙ` in every commutative ring is the polynomial of `(chebyshevCoeffs [0, 2] n).1`. -/
theorem chebyshevU_eq_intPoly (R : Type*) [CommRing R] (n : ℕ) :
    Chebyshev.U R n = intPoly R (chebyshevCoeffs [0, 2] n).1 :=
  (chebyshevCoeffs_spec (Chebyshev.U R) [0, 2] (Chebyshev.U_zero R)
    (by simp [Chebyshev.U_one R, mul_comm]) (Chebyshev.U_add_two R) n).1

/-! ### Hermite polynomials -/

/-- The coefficient list of Mathlib's probabilists' `hermite n`, by `He_{k+1} = X Heₖ - Heₖ'`. -/
def hermiteCoeffs : ℕ → List ℤ
  | 0 => [1]
  | n + 1 =>
    let p := hermiteCoeffs n
    addCoeffs (0 :: p) (scaleCoeffs (-1) (derivCoeffs p))

/-- Mathlib's `hermite n` is the polynomial of `hermiteCoeffs n`. -/
theorem hermite_eq_intPoly (n : ℕ) : hermite n = intPoly ℤ (hermiteCoeffs n) := by
  induction n with
  | zero => simp [hermiteCoeffs]
  | succ n ih =>
    rw [hermite_succ, ih]
    simp only [hermiteCoeffs, intPoly_addCoeffs, intPoly_scaleCoeffs, intPoly_derivCoeffs,
      intPoly_cons]
    push_cast
    ring

/-- The coefficient list of the physicists' `Hₙ`, by `H_{k+1} = 2 X Hₖ - Hₖ'`. -/
def physHermiteCoeffs : ℕ → List ℤ
  | 0 => [1]
  | n + 1 =>
    let p := physHermiteCoeffs n
    addCoeffs (scaleCoeffs 2 (0 :: p)) (scaleCoeffs (-1) (derivCoeffs p))

/-- The physicists' `Hₙ (x) = √2 ^ n Heₙ (√2 x)` as a polynomial over `ℝ`. -/
theorem physHermite_eq_intPoly (n : ℕ) :
    C (√2 ^ n) * ((hermite n).map (Int.castRingHom ℝ)).comp (C √2 * X) =
      intPoly ℝ (physHermiteCoeffs n) := by
  induction n with
  | zero => simp [physHermiteCoeffs]
  | succ n ih =>
    have h2 : (C √2 * C √2 : ℝ[X]) = 2 := by
      rw [← C_mul, Real.mul_self_sqrt zero_le_two, C_ofNat]
    simp only [physHermiteCoeffs, intPoly_addCoeffs, intPoly_scaleCoeffs, intPoly_derivCoeffs,
      intPoly_cons, ← ih]
    rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_comp, derivative_mul,
      derivative_C, derivative_X, zero_mul, zero_add, mul_one, derivative_map, hermite_succ,
      Polynomial.map_sub, Polynomial.map_mul, map_X, sub_comp, mul_comp, X_comp, pow_succ, C_mul]
    push_cast
    linear_combination (C (√2 ^ n) * X * ((hermite n).map (Int.castRingHom ℝ)).comp (C √2 * X)) *
      h2

/-- The physicists' `√2 ^ n Heₙ (√2 x)` evaluates the polynomial of `physHermiteCoeffs n`. -/
theorem sqrt_two_pow_mul_aeval_hermite (n : ℕ) (x : ℝ) :
    √2 ^ n * aeval (√2 * x) (hermite n) = (intPoly ℝ (physHermiteCoeffs n)).eval x := by
  rw [← physHermite_eq_intPoly, eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_X,
    eval_map, aeval_def, eval₂_eq_eval_map, algebraMap_int_eq, eval_map]

/-! ### Bernoulli polynomials -/

/-- The list `[C(n, j) l₀, C(n, j + 1) l₁, …]`, given `c = C(n, j)`. -/
def binomialScale (n : ℕ) : List ℤ → ℕ → ℕ → List ℤ
  | [], _, _ => []
  | x :: l, j, c => Int.mul (Int.ofNat c) x ::
      binomialScale n l (Nat.add j 1) (Nat.div (Nat.mul c (Nat.sub n j)) (Nat.add j 1))

/-- Entry `i` of `binomialScale n l j (C(n, j))` is `C(n, j + i) l[i]`. -/
theorem binomialScale_getD (n : ℕ) (l : List ℤ) (j i : ℕ) :
    (binomialScale n l j (n.choose j)).getD i 0 = (n.choose (j + i) : ℤ) * l.getD i 0 := by
  induction l generalizing j i with
  | nil => simp [binomialScale]
  | cons x l ih =>
    change (((n.choose j : ℤ) * x) ::
      binomialScale n l (j + 1) (n.choose j * (n - j) / (j + 1))).getD i 0 = _
    rw [← Nat.choose_succ_right_eq, Nat.mul_div_cancel _ (Nat.succ_pos j)]
    cases i with
    | zero => simp
    | succ i => rw [List.getD_cons_succ, ih, List.getD_cons_succ, Nat.add_right_comm, Nat.add_assoc]

/-- The coefficients `C(n, i) B_{n-i} (n + 1)!` of `(n + 1)! Bₙ (X)`, lowest degree first. -/
def bernoulliPolyNumerators (n : ℕ) : List ℤ :=
  binomialScale n (bernoulliNumerators n).reverse 0 1

/-- `Polynomial.bernoulli n` is `1 / (n + 1)!` times the polynomial of
`bernoulliPolyNumerators n`; the kernel evaluates the list. -/
theorem bernoulli_eq_intPoly (n : ℕ) :
    Polynomial.bernoulli n =
      C ((n + 1).factorial : ℚ)⁻¹ * intPoly ℚ (bernoulliPolyNumerators n) := by
  ext i
  have hf : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
  have hs := binomialScale_getD n (bernoulliNumerators n).reverse 0 i
  rw [Nat.choose_zero_right, zero_add] at hs
  rw [coeff_bernoulli, coeff_C_mul, coeff_intPoly, bernoulliPolyNumerators, hs]
  have hlen := length_bernoulliNumerators n
  split_ifs with hi
  · rw [List.getD_eq_getElem _ _ (by simp [hlen]; omega), List.getElem_reverse,
      ← List.getD_eq_getElem _ 0, hlen, show n + 1 - 1 - i = n - i by omega]
    push_cast
    rw [← bernoulliNumerators_getD n (n - i) (by omega)]
    field_simp
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

end CAS.Analysis.SpecialFunctions

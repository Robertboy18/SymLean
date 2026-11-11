/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import CAS.Analysis.Matrix.QuadraticForm
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.LinearCombination

/-!
# Lower bounds for matrix quadratic forms

The quadratic form of a real square matrix `A` is written `∑ i, ∑ j, A i j * x i * x j`. We
prove the bounds behind the exact positivity certificates: a factor `L D Lᵀ` with `D ≥ 0` has a
nonnegative form, a residual with small entries changes the form by a multiple of `|x|²`, and
diagonal dominance or positive leading principal minors of a symmetric `3 × 3` matrix give
nonnegative forms; the form of a block matrix splits into the forms of its blocks.

## Main results

* `quadForm_ldlt_nonneg`: a factor `L D Lᵀ` with nonnegative `D` has a nonnegative form, for any
  `L`.
* `abs_quadForm_le_of_abs_le`, `abs_quadForm_le_of_frobenius`: a residual whose entries are at
  most `ε` in absolute value changes the form by at most `n ε |x|²`, and one of Frobenius norm
  at most `e` by at most `e |x|²`.
* `quadForm_nonneg_of_diagDominant`: a residual whose diagonal dominates the symmetrized
  off-diagonal row sums has a nonnegative form.
* `quadForm_ge_of_ldlt_add`, `quadForm_ge_of_ldlt_abs_le`, `quadForm_ge_of_ldlt_diagDominant`:
  `A = τ I + L D Lᵀ + R` with `D ≥ 0` gives `A ⪰ (τ + c) I` from `R ⪰ c I`, hence
  `A ⪰ (τ - n ε) I` from `|R i j| ≤ ε` and `A ⪰ τ I` from diagonal dominance of `R`.
* `quadForm_nonneg_of_leadingMinors_three`: a symmetric `3 × 3` matrix with positive leading
  principal minors has a nonnegative form (Sylvester's criterion).
* `quadForm_appendBlocks`: the form of a block matrix `[[A, B], [Bᵀ, D]]` on `Fin (p + q)`
  splits into the three blocks.

## Implementation notes

In `A = τ I + L D Lᵀ + R` the factor need not be triangular or exact. It comes from an untrusted
factorization, and only the residual `R`, computed exactly, needs a bound. The entrywise bound
is Cauchy-Schwarz for `∑ |xᵢ|` (`sq_sum_abs_le_card_mul_sum_sq`), the Frobenius bound
Cauchy-Schwarz over all index pairs (`Finset.sum_mul_sq_le_sq_mul_sq`). For diagonal dominance
we prove `2 Rᵢⱼ xᵢ xⱼ + |Rᵢⱼ| (xᵢ² + xⱼ²) ≥ 0` for every pair and sum; for a symmetric
matrix this is what Gershgorin's disc theorem gives when all discs lie in `[0, ∞)`, but no
eigenvalue enters the proof. Sylvester's criterion for `3 × 3` matrices is one completed-square
identity, proved by `ring`, with `Matrix.det_fin_three` for the determinant. The splitting into
blocks lets a block certificate avoid the inverse of `A`.

## References

* S. Gershgorin, "Über die Abgrenzung der Eigenwerte einer Matrix", *Izv. Akad. Nauk SSSR, Otd.
  Mat. Estest. Nauk, VII. Ser.* 1931, no. 6, pp. 749-754, <https://zbmath.org/?q=an:0003.00102>.
  The disc theorem, of which `quadForm_nonneg_of_diagDominant` is the form for quadratic forms.
-/

@[expose] public section

open Finset Matrix
open scoped Matrix

namespace CAS.Analysis.Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The double-sum quadratic form is the dot product with the matrix-vector product. -/
theorem sum_sum_mul_mul_eq_dotProduct_mulVec (A : _root_.Matrix ι ι ℝ) (x : ι → ℝ) :
    ∑ i, ∑ j, A i j * x i * x j = x ⬝ᵥ (A *ᵥ x) := by
  simp only [dotProduct, _root_.Matrix.mulVec, mul_sum]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring

/-- For a real vector `x` over a finite index type, the sum of squares `∑ i, x i ^ 2` equals the dot
product `x ⬝ᵥ x`. -/
theorem sum_sq_eq_dotProduct (x : ι → ℝ) : ∑ i, x i ^ 2 = x ⬝ᵥ x := by
  simp only [dotProduct, sq]

/-- The quadratic form of a sum of rank-one terms `d k • (column k) (column k)ᵀ`. -/
theorem quadForm_ldlt_eq (L : ι → κ → ℝ) (d : κ → ℝ) (x : ι → ℝ) :
    ∑ i, ∑ j, (∑ k, L i k * d k * L j k) * x i * x j = ∑ k, d k * (∑ i, L i k * x i) ^ 2 := by
  simp only [sq, mul_sum, sum_mul]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [sum_comm]
  exact sum_congr rfl fun k _ ↦ sum_congr rfl fun j _ ↦ by ring

/-- A factor `L D Lᵀ` with nonnegative diagonal `D` has a nonnegative quadratic form. -/
theorem quadForm_ldlt_nonneg (L : ι → κ → ℝ) {d : κ → ℝ} (hd : ∀ k, 0 ≤ d k) (x : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, (∑ k, L i k * d k * L j k) * x i * x j := by
  rw [quadForm_ldlt_eq]
  exact sum_nonneg fun k _ ↦ mul_nonneg (hd k) (sq_nonneg _)

/-- The squared `ℓ¹` norm is at most the cardinality times the squared Euclidean norm. -/
theorem sq_sum_abs_le_card_mul_sum_sq (x : ι → ℝ) :
    (∑ i, |x i|) ^ 2 ≤ Fintype.card ι * ∑ i, x i ^ 2 := by
  simpa only [sq_abs, card_univ] using
    sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := fun i ↦ |x i|)

/-- Entries bounded by `ε` give a quadratic form bounded by `n ε |x|²`. -/
theorem abs_quadForm_le_of_abs_le {R : ι → ι → ℝ} {ε : ℝ} (hR : ∀ i j, |R i j| ≤ ε)
    (x : ι → ℝ) :
    |∑ i, ∑ j, R i j * x i * x j| ≤ Fintype.card ι * ε * ∑ i, x i ^ 2 := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · simp
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hR i₀ i₀)
  calc |∑ i, ∑ j, R i j * x i * x j| ≤ ∑ i, ∑ j, |R i j * x i * x j| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, ε * |x i| * |x j| := by
        refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ ?_
        rw [abs_mul, abs_mul]
        gcongr
        exact hR i j
    _ = ε * (∑ i, |x i|) ^ 2 := by
        simp only [sq, mul_sum, sum_mul]
        exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
    _ ≤ ε * (Fintype.card ι * ∑ i, x i ^ 2) := by
        gcongr
        exact sq_sum_abs_le_card_mul_sum_sq x
    _ = Fintype.card ι * ε * ∑ i, x i ^ 2 := by ring

/-- Cauchy–Schwarz over all index pairs: a residual of Frobenius norm at most `e` changes the
quadratic form by at most `e |x|²`. -/
theorem abs_quadForm_le_of_frobenius {R : ι → ι → ℝ} {e : ℝ} (he : 0 ≤ e)
    (hR : ∑ i, ∑ j, R i j ^ 2 ≤ e ^ 2) (x : ι → ℝ) :
    |∑ i, ∑ j, R i j * x i * x j| ≤ e * ∑ i, x i ^ 2 := by
  have hcs := sum_mul_sq_le_sq_mul_sq (s := (univ : Finset (ι × ι)))
    (f := fun p ↦ R p.1 p.2) (g := fun p ↦ x p.1 * x p.2)
  simp only [← univ_product_univ, sum_product] at hcs
  have hxx : ∑ i, ∑ j, (x i * x j) ^ 2 = (∑ i, x i ^ 2) ^ 2 := by
    simp only [sq, sum_mul, mul_sum]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  have hsum : ∑ i, ∑ j, R i j * x i * x j = ∑ i, ∑ j, R i j * (x i * x j) :=
    sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  rw [hxx, ← hsum] at hcs
  have hS : 0 ≤ ∑ i, x i ^ 2 := sum_nonneg fun i _ ↦ sq_nonneg _
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg he hS)).mp
  rw [sq_abs, mul_pow]
  exact hcs.trans (mul_le_mul_of_nonneg_right hR (sq_nonneg _))

/-- **Gershgorin's criterion** for quadratic forms: if every diagonal entry dominates half of the
symmetrized off-diagonal absolute row sum, the quadratic form is nonnegative. Symmetry is not
assumed. -/
theorem quadForm_nonneg_of_diagDominant [DecidableEq ι] {R : ι → ι → ℝ}
    (hR : ∀ i, ∑ j ∈ univ.erase i, (|R i j| + |R j i|) ≤ 2 * R i i) (x : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, R i j * x i * x j := by
  -- `f i j ≥ 0` off the diagonal, and `∑ f = 2 S + P` with `P` the absolute row sums.
  set f : ι → ι → ℝ := fun i j ↦ 2 * (R i j * x i * x j) + |R i j| * (x i ^ 2 + x j ^ 2)
  have hoff (i j : ι) : 0 ≤ f i j := by
    have h₁ : 0 ≤ |R i j| + R i j := by linarith [neg_abs_le (R i j)]
    have h₂ : 0 ≤ |R i j| - R i j := by linarith [le_abs_self (R i j)]
    linarith [mul_nonneg h₁ (sq_nonneg (x i + x j)), mul_nonneg h₂ (sq_nonneg (x i - x j))]
  have hrow (i : ι) : f i i ≤ ∑ j, f i j := single_le_sum (fun j _ ↦ hoff i j) (mem_univ i)
  have hdiag : ∀ i, f i i = 2 * (R i i + |R i i|) * x i ^ 2 := fun i ↦ by simp only [f]; ring
  have htotal : ∑ i, ∑ j, f i j = 2 * ∑ i, ∑ j, R i j * x i * x j +
      ∑ i, x i ^ 2 * ∑ j, (|R i j| + |R j i|) := by
    have hP : ∑ i, ∑ j, |R i j| * (x i ^ 2 + x j ^ 2) =
        ∑ i, x i ^ 2 * ∑ j, (|R i j| + |R j i|) := by
      simp only [mul_add, sum_add_distrib]
      congr 1
      · exact sum_congr rfl fun i _ ↦ by rw [mul_sum]; exact sum_congr rfl fun j _ ↦ by ring
      · rw [sum_comm]
        exact sum_congr rfl fun i _ ↦ by rw [mul_sum]; exact sum_congr rfl fun j _ ↦ by ring
    simp only [f, sum_add_distrib, ← mul_sum, hP]
  have hrowsum : ∀ i, ∑ j, (|R i j| + |R j i|) ≤ 2 * (R i i + |R i i|) := by
    intro i
    rw [← sum_erase_add _ _ (mem_univ i)]
    linarith [hR i]
  have hlow : ∑ i, x i ^ 2 * ∑ j, (|R i j| + |R j i|) ≤ ∑ i, ∑ j, f i j := by
    calc ∑ i, x i ^ 2 * ∑ j, (|R i j| + |R j i|) ≤ ∑ i, x i ^ 2 * (2 * (R i i + |R i i|)) :=
          sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hrowsum i) (sq_nonneg _)
      _ = ∑ i, f i i := sum_congr rfl fun i _ ↦ by rw [hdiag]; ring
      _ ≤ ∑ i, ∑ j, f i j := sum_le_sum fun i _ ↦ hrow i
  linarith [htotal, hlow]

/-- A matrix `A = L D Lᵀ + τ I + R` with `D ≥ 0` and a quadratic lower bound `c` for `R` has
the quadratic lower bound `τ + c`. -/
theorem quadForm_ge_of_ldlt_add [DecidableEq ι] {A R : ι → ι → ℝ} (L : ι → κ → ℝ)
    {d : κ → ℝ} {τ c : ℝ} (hd : ∀ k, 0 ≤ d k)
    (hA : ∀ i j, A i j = ∑ k, L i k * d k * L j k + (if i = j then τ else 0) + R i j)
    (hR : ∀ x : ι → ℝ, c * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, R i j * x i * x j) (x : ι → ℝ) :
    (τ + c) * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, A i j * x i * x j := by
  have hsplit : ∑ i, ∑ j, A i j * x i * x j =
      ∑ i, ∑ j, (∑ k, L i k * d k * L j k) * x i * x j + τ * ∑ i, x i ^ 2 +
        ∑ i, ∑ j, R i j * x i * x j := by
    simp only [hA, add_mul, sum_add_distrib, mul_sum]
    congr 1
    congr 1
    refine sum_congr rfl fun i _ ↦ ?_
    simp [sq, mul_assoc]
  rw [hsplit]
  linarith [quadForm_ldlt_nonneg L hd x, hR x]

/-- The `LDLᵀ` certificate with an entrywise residual bound: `A = L D Lᵀ + τ I + R`, `D ≥ 0`
and `|R i j| ≤ ε` give `A ⪰ (τ - n ε) I`. -/
theorem quadForm_ge_of_ldlt_abs_le [DecidableEq ι] {A R : ι → ι → ℝ} (L : ι → κ → ℝ)
    {d : κ → ℝ} {τ ε : ℝ} (hd : ∀ k, 0 ≤ d k)
    (hA : ∀ i j, A i j = ∑ k, L i k * d k * L j k + (if i = j then τ else 0) + R i j)
    (hR : ∀ i j, |R i j| ≤ ε) (x : ι → ℝ) :
    (τ - Fintype.card ι * ε) * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, A i j * x i * x j := by
  have h := quadForm_ge_of_ldlt_add L (c := -(Fintype.card ι * ε)) hd hA (fun y ↦ by
    have := (abs_le.mp (abs_quadForm_le_of_abs_le hR y)).1
    linarith) x
  simpa only [sub_eq_add_neg] using h

/-- The `LDLᵀ` certificate with a diagonally dominant residual: `A = L D Lᵀ + τ I + R`,
`D ≥ 0` and Gershgorin's condition on `R` give `A ⪰ τ I`. -/
theorem quadForm_ge_of_ldlt_diagDominant [DecidableEq ι] {A R : ι → ι → ℝ}
    (L : ι → κ → ℝ) {d : κ → ℝ} {τ : ℝ} (hd : ∀ k, 0 ≤ d k)
    (hA : ∀ i j, A i j = ∑ k, L i k * d k * L j k + (if i = j then τ else 0) + R i j)
    (hR : ∀ i, ∑ j ∈ univ.erase i, (|R i j| + |R j i|) ≤ 2 * R i i) (x : ι → ℝ) :
    τ * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, A i j * x i * x j := by
  have h := quadForm_ge_of_ldlt_add L (c := 0) hd hA (fun y ↦ by
    simpa using quadForm_nonneg_of_diagDominant hR y) x
  simpa using h

/-! ### Sylvester's criterion in dimension three -/

/-- Completing squares: for a symmetric `3 × 3` matrix with rows `a b c`, `b d e`, `c e f`
the form times `a (a d - b²)` is a sum of squares plus `a det v₂²`. -/
private theorem three_by_three_identity (a b c d e f v₀ v₁ v₂ : ℝ) :
    a * (a * d - b * b) * (a * v₀ ^ 2 + d * v₁ ^ 2 + f * v₂ ^ 2 + 2 * b * v₀ * v₁ +
      2 * c * v₀ * v₂ + 2 * e * v₁ * v₂) =
      (a * d - b * b) * (a * v₀ + b * v₁ + c * v₂) ^ 2 +
        ((a * d - b * b) * v₁ + (a * e - b * c) * v₂) ^ 2 +
        a * (a * (d * f - e * e) - b * (b * f - e * c) + c * (b * e - d * c)) * v₂ ^ 2 := by
  ring

/-- **Sylvester's criterion** for a symmetric `3 × 3` real matrix: positive leading principal
minors give a nonnegative quadratic form. -/
theorem quadForm_nonneg_of_leadingMinors_three {B : _root_.Matrix (Fin 3) (Fin 3) ℝ}
    (hB : B.IsSymm) (h₁ : 0 < B 0 0) (h₂ : 0 < B 0 0 * B 1 1 - B 0 1 * B 1 0)
    (h₃ : 0 < B.det) (v : Fin 3 → ℝ) : 0 ≤ ∑ i, ∑ j, B i j * v i * v j := by
  have hs : ∀ i j, B j i = B i j := fun i j ↦ by
    simpa using congrFun (congrFun hB i) j
  rw [_root_.Matrix.det_fin_three, hs 0 1, hs 0 2, hs 1 2] at h₃
  rw [hs 0 1] at h₂
  simp only [Fin.sum_univ_three]
  rw [hs 0 1, hs 0 2, hs 1 2]
  have hid := three_by_three_identity (B 0 0) (B 0 1) (B 0 2) (B 1 1) (B 1 2) (B 2 2)
    (v 0) (v 1) (v 2)
  have hpos : 0 < B 0 0 * (B 0 0 * B 1 1 - B 0 1 * B 0 1) := mul_pos h₁ h₂
  have hdet : 0 < B 0 0 * (B 1 1 * B 2 2 - B 1 2 * B 1 2) - B 0 1 * (B 0 1 * B 2 2 -
      B 1 2 * B 0 2) + B 0 2 * (B 0 1 * B 1 2 - B 1 1 * B 0 2) := by linear_combination h₃
  have hrhs : 0 ≤ (B 0 0 * B 1 1 - B 0 1 * B 0 1) *
      (B 0 0 * v 0 + B 0 1 * v 1 + B 0 2 * v 2) ^ 2 +
      ((B 0 0 * B 1 1 - B 0 1 * B 0 1) * v 1 + (B 0 0 * B 1 2 - B 0 1 * B 0 2) * v 2) ^ 2 +
      B 0 0 * (B 0 0 * (B 1 1 * B 2 2 - B 1 2 * B 1 2) - B 0 1 * (B 0 1 * B 2 2 -
        B 1 2 * B 0 2) + B 0 2 * (B 0 1 * B 1 2 - B 1 1 * B 0 2)) * v 2 ^ 2 := by
    have := mul_pos h₁ hdet
    positivity
  rw [← hid] at hrhs
  have hq := (mul_nonneg_iff_of_pos_left hpos).mp hrhs
  linear_combination hq

/-! ### Block matrices and upper bounds -/

/-- The symmetric block matrix `[[A, B], [Bᵀ, D]]` on `Fin (p + q)`. -/
def appendBlocks {p q : ℕ} (A : Fin p → Fin p → ℝ) (B : Fin p → Fin q → ℝ)
    (D : Fin q → Fin q → ℝ) : Fin (p + q) → Fin (p + q) → ℝ :=
  Fin.append (fun i ↦ Fin.append (A i) (B i)) (fun i ↦ Fin.append (fun j ↦ B j i) (D i))

/-- The form of a block matrix at `(x, y)` is `xᵀ A x + 2 xᵀ B y + yᵀ D y`. -/
theorem quadForm_appendBlocks {p q : ℕ} (A : Fin p → Fin p → ℝ) (B : Fin p → Fin q → ℝ)
    (D : Fin q → Fin q → ℝ) (x : Fin p → ℝ) (y : Fin q → ℝ) :
    ∑ i, ∑ j, appendBlocks A B D i j * Fin.append x y i * Fin.append x y j =
      ∑ i, ∑ j, A i j * x i * x j + 2 * ∑ i, ∑ j, x i * B i j * y j +
        ∑ i, ∑ j, D i j * y i * y j := by
  simp only [appendBlocks, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have hcross : ∑ i : Fin q, ∑ j : Fin p, B j i * y i * x j = ∑ i, ∑ j, x i * B i j * y j := by
    rw [sum_comm]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  have hleft : ∑ i : Fin p, (∑ j : Fin p, A i j * x i * x j + ∑ j : Fin q, B i j * x i * y j) =
      ∑ i, ∑ j, A i j * x i * x j + ∑ i, ∑ j, x i * B i j * y j := by
    rw [sum_add_distrib]
    congr 1
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  rw [hleft, sum_add_distrib, hcross]
  ring

end CAS.Analysis.Matrix

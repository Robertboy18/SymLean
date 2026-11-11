/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.Matrix.QuadraticFormBounds
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity.Finset

/-!
# Exact positivity checks for small matrices

`ldltCheck M L d s τ` certifies `A ⪰ τ I` for `A = M / 2 ^ s` from an untrusted factor: with
`L / 2 ^ s` and `d / 2 ^ s` it forms the scaled residual
`R = den τ (2 ^ (2 s) M - L d Lᵀ) - num τ 2 ^ (3 s) I` in exact integers, that is
`A - τ I - (L / 2 ^ s) (d / 2 ^ s) (L / 2 ^ s)ᵀ` times `den τ 2 ^ (3 s)`, and checks Gershgorin's
condition on `R`. `sylvester3Check A m` tests the three leading principal minors of `A - m I` for
a symmetric rational `3 × 3` matrix, and `sylvester3SlotCheck` is the same test for biased
natural entries `x - β`, as read from packed slots; `natAll` runs such a test at many points.

## Main definitions

* `ldltResidual`, `ldltCheck`: the scaled residual and Gershgorin's condition on it.
* `sylvester3Check`: positivity of the leading principal minors of `A - m I`.
* `biasedAbs`, `sylvester3SlotCheck`: the same test on biased natural entries, with
  natural-number operations only.
* `natAll`: a test at every index below `n`.

## Main results

* `quadForm_ge_of_ldltCheck`: a passing `ldltCheck` gives `τ |x|² ≤ xᵀ (M / 2 ^ s) x`.
* `quadForm_ge_of_sylvester3`: a passing `sylvester3Check A m` gives `m |v|² ≤ vᵀ A v`.
* `quadForm_nonneg_of_sylvester3SlotCheck`: a passing `sylvester3SlotCheck` makes the matrix of
  entries `x - β` positive semidefinite.
* `natAll_spec`: a passing `natAll n p` gives `p j` for every `j < n`.

## Implementation notes

The factor need not be triangular, symmetric or exact. It is computed by untrusted code for a
slightly larger shift than `τ`, so the residual is about the difference of the shifts times `I`
plus rounding, and Gershgorin's condition holds with room to spare; the kernel checks only that
condition, and `quadForm_ge_of_ldltCheck` concludes through `quadForm_ge_of_ldlt_diagDominant`
(Gershgorin's condition makes the form of the residual nonnegative). This is the classical route
of an approximate factor of a shifted matrix with a rigorous residual estimate (Rump, (10.54));
the scaling by `den τ 2 ^ (3 s)`, which keeps the whole check in integers, is ours. The check
uses `n³` integer operations, so it serves small matrices; large ones use the packed rows of
[PackedLDL](PackedLDL.lean).

Sylvester's criterion is classical; `quadForm_nonneg_of_leadingMinors_three` proves it in
dimension three by completing squares. `sylvester3SlotCheck` stays in natural numbers, which the
kernel evaluates as literals ([PackedSlots](PackedSlots.lean)): it compares products of absolute
values and takes the sign of the off-diagonal triple product from the parity of its negative
factors (`biased_triple_product`), so a vertex test costs a few dozen small natural-number
operations in the kernel.

The analytic side of these checks and of [PackedLDL](PackedLDL.lean) is
`CAS.Analysis.Matrix.QuadraticFormBounds`: a factor `L D Lᵀ` with `D ≥ 0`, Gershgorin's and
Sylvester's criteria, block matrices, and Weyl's inequality (`abs_quadForm_le_of_frobenius`,
`abs_quadForm_le_of_abs_le`), which bounds how much a residual small in Frobenius norm or in every
entry changes the form.

## References

* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Section 10.8, (10.54): a lower bound for the smallest eigenvalue from an approximate Cholesky
  factor of a shifted matrix and a bound on the residual.
* Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th ed., The Johns Hopkins
  University Press, Baltimore, 2013, <https://doi.org/10.56021/9781421407944>. For the `LDLᵀ`
  and Cholesky factorizations.
-/

@[expose] public section

open Finset CAS.Analysis.Matrix

namespace CAS.Numerics

/-! ### Dense `LDLᵀ` with a Gershgorin residual -/

/-- The scaled residual `den τ (2 ^ (2 s) M - L d Lᵀ) - num τ 2 ^ (3 s) I` of a factor
`(L / 2 ^ s) (d / 2 ^ s) (L / 2 ^ s)ᵀ` of `M / 2 ^ s - τ I`. -/
def ldltResidual {n : ℕ} (M L : Fin n → Fin n → ℤ) (d : Fin n → ℕ) (s : ℕ) (τ : ℚ)
    (i j : Fin n) : ℤ :=
  (τ.den : ℤ) * (2 ^ (2 * s) * M i j - ∑ k, L i k * d k * L j k) -
    if i = j then τ.num * 2 ^ (3 * s) else 0

/-- Gershgorin's condition on the scaled residual: every diagonal entry dominates half of the
symmetrized off-diagonal absolute row sum. -/
def ldltCheck {n : ℕ} (M L : Fin n → Fin n → ℤ) (d : Fin n → ℕ) (s : ℕ) (τ : ℚ) : Bool :=
  decide (∀ i, ∑ j ∈ univ.erase i,
    (|ldltResidual M L d s τ i j| + |ldltResidual M L d s τ j i|) ≤
      2 * ldltResidual M L d s τ i i)

/-- **Dense `LDLᵀ` certificate.** A passing `ldltCheck` gives `A ⪰ τ I` for `A = M / 2 ^ s`. -/
theorem quadForm_ge_of_ldltCheck {n : ℕ} (M L : Fin n → Fin n → ℤ) (d : Fin n → ℕ) (s : ℕ)
    (τ : ℚ) (h : ldltCheck M L d s τ = true) (x : Fin n → ℝ) :
    (τ : ℝ) * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, ((M i j : ℝ) / 2 ^ s) * x i * x j := by
  have hc : (0 : ℝ) < τ.den * 2 ^ (3 * s) := by positivity
  set c : ℝ := τ.den * 2 ^ (3 * s)
  set R : Fin n → Fin n → ℝ := fun i j ↦ (ldltResidual M L d s τ i j : ℝ) * c⁻¹
  have hdom := of_decide_eq_true h
  have hci : 0 < c⁻¹ := inv_pos.mpr hc
  have hR : ∀ i, ∑ j ∈ univ.erase i, (|R i j| + |R j i|) ≤ 2 * R i i := by
    intro i
    have hi := (Int.cast_le (R := ℝ)).mpr (hdom i)
    push_cast at hi
    have hscale := mul_le_mul_of_nonneg_right hi hci.le
    simp only [R, abs_mul, abs_of_pos hci, ← add_mul, ← sum_mul]
    linarith
  have hτ : (τ : ℝ) = τ.num / τ.den := by exact_mod_cast (Rat.num_div_den τ).symm
  have hA : ∀ i j, (M i j : ℝ) / 2 ^ s = ∑ k, ((L i k : ℝ) / 2 ^ s) * ((d k : ℝ) / 2 ^ s) *
      ((L j k : ℝ) / 2 ^ s) + (if i = j then (τ : ℝ) else 0) + R i j := by
    intro i j
    have hden : (0 : ℝ) < τ.den := by positivity
    have h2 : (2 : ℝ) ^ (2 * s) = (2 ^ s) ^ 2 := by rw [mul_comm, pow_mul]
    have h3 : (2 : ℝ) ^ (3 * s) = (2 ^ s) ^ 3 := by rw [mul_comm, pow_mul]
    have hsum : ∑ k, ((L i k : ℝ) / 2 ^ s) * ((d k : ℝ) / 2 ^ s) * ((L j k : ℝ) / 2 ^ s) =
        (∑ k, (L i k : ℝ) * d k * L j k) / (2 ^ s) ^ 3 := by
      rw [sum_div]
      exact sum_congr rfl fun k _ ↦ by field_simp
    rw [hsum]
    simp only [R, c, ldltResidual, h3]
    split_ifs <;> push_cast [h2, hτ] <;> field_simp <;> ring
  have := quadForm_ge_of_ldlt_diagDominant (A := fun i j ↦ (M i j : ℝ) / 2 ^ s)
    (fun i k ↦ (L i k : ℝ) / 2 ^ s) (d := fun k ↦ (d k : ℝ) / 2 ^ s)
    (fun k ↦ by positivity) hA hR x
  simpa only using this

/-! ### Sylvester's criterion in dimension three -/

/-- The three leading principal minors of `A - m I` are positive, for a rational `3 × 3`
matrix read as symmetric. -/
def sylvester3Check (A : Matrix (Fin 3) (Fin 3) ℚ) (m : ℚ) : Bool :=
  let a := A 0 0 - m
  let b := A 0 1
  let c := A 0 2
  let d := A 1 1 - m
  let e := A 1 2
  let f := A 2 2 - m
  decide (0 < a) && decide (0 < a * d - b * b) &&
    decide (0 < a * (d * f - e * e) - b * (b * f - e * c) + c * (b * e - d * c))

/-- **Sylvester's test.** A symmetric rational `3 × 3` matrix whose shift `A - m I` passes
`sylvester3Check` has quadratic lower bound `m`. -/
theorem quadForm_ge_of_sylvester3 (A : Matrix (Fin 3) (Fin 3) ℚ) (hA : A.IsSymm) (m : ℚ)
    (h : sylvester3Check A m = true) (v : Fin 3 → ℝ) :
    (m : ℝ) * ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, (A i j : ℝ) * v i * v j := by
  simp only [sylvester3Check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
  have hs : ∀ i j, A j i = A i j := fun i j ↦ by
    simpa using congrFun (congrFun hA i) j
  set B : Matrix (Fin 3) (Fin 3) ℝ := fun i j ↦ (A i j : ℝ) - if i = j then (m : ℝ) else 0
  have hB : B.IsSymm := by
    refine Matrix.IsSymm.ext fun i j ↦ ?_
    simp only [B]
    rw [hs i j]
    by_cases hij : i = j <;> simp [hij, eq_comm]
  have h₁' := (Rat.cast_lt (K := ℝ)).mpr h₁
  have h₂' := (Rat.cast_lt (K := ℝ)).mpr h₂
  have h₃' := (Rat.cast_lt (K := ℝ)).mpr h₃
  push_cast at h₁' h₂' h₃'
  have hq := quadForm_nonneg_of_leadingMinors_three hB (by simp [B]; linarith)
    (by simp [B, hs 0 1]; linarith)
    (by rw [Matrix.det_fin_three]; simp [B, hs 0 1, hs 0 2, hs 1 2]; linarith) v
  have hsplit : ∑ i, ∑ j, B i j * v i * v j =
      ∑ i, ∑ j, (A i j : ℝ) * v i * v j - (m : ℝ) * ∑ i, v i ^ 2 := by
    simp only [B, Fin.sum_univ_three]
    simp
    ring
  linarith

/-- The absolute value `|x - β|` of a biased natural entry, by truncated subtraction. -/
def biasedAbs (β x : ℕ) : ℕ := Nat.add (Nat.sub x β) (Nat.sub β x)

/-- `biasedAbs β x` is `|x - β|` in the integers. -/
theorem cast_biasedAbs (β x : ℕ) : (biasedAbs β x : ℤ) = |(x : ℤ) - β| := by
  change ((x - β + (β - x) : ℕ) : ℤ) = _
  rcases le_total β x with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.add_zero, Nat.cast_sub h, abs_of_nonneg (by omega)]
  · rw [Nat.sub_eq_zero_of_le h, Nat.zero_add, Nat.cast_sub h, abs_of_nonpos (by omega)]
    ring

/-- Sylvester's test for the symmetric matrix with entries `x - β` (diagonal `x₀₀, x₁₁, x₂₂`,
off-diagonal `x₀₁, x₀₂, x₁₂`), with natural-number operations only. The sign of the
off-diagonal triple product is the parity of its negative factors. -/
def sylvester3SlotCheck (β x₀₀ x₀₁ x₀₂ x₁₁ x₁₂ x₂₂ : ℕ) : Bool :=
  let a := Nat.sub x₀₀ β
  let d := Nat.sub x₁₁ β
  let f := Nat.sub x₂₂ β
  let p := biasedAbs β x₀₁
  let q := biasedAbs β x₀₂
  let r := biasedAbs β x₁₂
  let t := Nat.mul 2 (Nat.mul p (Nat.mul q r))
  let negative := xor (xor (Nat.blt x₀₁ β) (Nat.blt x₀₂ β)) (Nat.blt x₁₂ β)
  Nat.blt β x₀₀ && Nat.blt β x₁₁ && Nat.blt β x₂₂ &&
    Nat.blt (Nat.mul p p) (Nat.mul a d) &&
    Nat.blt (Nat.add (Nat.add (Nat.mul a (Nat.mul r r)) (Nat.mul d (Nat.mul q q)))
        (Nat.add (Nat.mul f (Nat.mul p p)) (cond negative t 0)))
      (Nat.add (Nat.mul a (Nat.mul d f)) (cond negative 0 t))

/-- The triple product of three biased entries is the product of their absolute values, with
the sign given by the parity of the negative factors. -/
private theorem biased_triple_product (β x y z : ℕ) :
    ((x : ℤ) - β) * ((y : ℤ) - β) * ((z : ℤ) - β) =
      if xor (xor (Nat.blt x β) (Nat.blt y β)) (Nat.blt z β) then
        -((biasedAbs β x : ℤ) * biasedAbs β y * biasedAbs β z)
      else (biasedAbs β x : ℤ) * biasedAbs β y * biasedAbs β z := by
  simp only [cast_biasedAbs]
  have key (w : ℕ) : ((w : ℤ) - β) = if Nat.blt w β then -|(w : ℤ) - β| else |(w : ℤ) - β| := by
    split_ifs with hw
    · rw [abs_of_neg (by simp at hw; omega), neg_neg]
    · rw [abs_of_nonneg (by simp at hw; omega)]
  conv_lhs => rw [key x, key y, key z]
  cases Nat.blt x β <;> cases Nat.blt y β <;> cases Nat.blt z β <;> simp

/-- **Sylvester's test on biased entries.** A passing `sylvester3SlotCheck` makes the symmetric
matrix with entries `x - β` positive semidefinite. -/
theorem quadForm_nonneg_of_sylvester3SlotCheck {β x₀₀ x₀₁ x₀₂ x₁₁ x₁₂ x₂₂ : ℕ}
    (h : sylvester3SlotCheck β x₀₀ x₀₁ x₀₂ x₁₁ x₁₂ x₂₂ = true) (v : Fin 3 → ℝ) :
    0 ≤ ∑ i, ∑ j, (!![(x₀₀ : ℝ) - β, (x₀₁ : ℝ) - β, (x₀₂ : ℝ) - β;
      (x₀₁ : ℝ) - β, (x₁₁ : ℝ) - β, (x₁₂ : ℝ) - β;
      (x₀₂ : ℝ) - β, (x₁₂ : ℝ) - β, (x₂₂ : ℝ) - β] : Matrix (Fin 3) (Fin 3) ℝ) i j *
        v i * v j := by
  simp only [sylvester3SlotCheck, Bool.and_eq_true, Nat.blt_eq, Nat.mul_eq, Nat.add_eq,
    Nat.sub_eq] at h
  obtain ⟨⟨⟨⟨h00, h11⟩, h22⟩, h2⟩, h3⟩ := h
  set B : Matrix (Fin 3) (Fin 3) ℝ := !![(x₀₀ : ℝ) - β, (x₀₁ : ℝ) - β, (x₀₂ : ℝ) - β;
      (x₀₁ : ℝ) - β, (x₁₁ : ℝ) - β, (x₁₂ : ℝ) - β;
      (x₀₂ : ℝ) - β, (x₁₂ : ℝ) - β, (x₂₂ : ℝ) - β]
  have hB : B.IsSymm := Matrix.IsSymm.ext fun i j ↦ by fin_cases i <;> fin_cases j <;> rfl
  have hR (x : ℕ) : ((biasedAbs β x : ℕ) : ℝ) = |(x : ℝ) - β| := by
    exact_mod_cast cast_biasedAbs β x
  have hsq (z : ℝ) : |z| * |z| = z * z := by rw [← abs_mul, abs_mul_self]
  have h2' := (Nat.cast_lt (α := ℝ)).mpr h2
  push_cast [Nat.cast_sub h00.le, Nat.cast_sub h11.le, hR, hsq] at h2'
  have htri := congrArg (Int.cast : ℤ → ℝ) (biased_triple_product β x₀₁ x₀₂ x₁₂)
  push_cast [hR] at htri
  refine quadForm_nonneg_of_leadingMinors_three hB ?_ ?_ ?_ v
  · simp only [B]
    norm_num
    exact_mod_cast h00
  · simp only [B]
    norm_num
    linarith
  · rw [Matrix.det_fin_three]
    simp only [B]
    norm_num
    cases hneg : xor (xor (Nat.blt x₀₁ β) (Nat.blt x₀₂ β)) (Nat.blt x₁₂ β)
    · simp only [hneg, Bool.cond_false, Bool.false_eq_true, ↓reduceIte] at h3 htri
      have h3' := (Nat.cast_lt (α := ℝ)).mpr h3
      push_cast [Nat.cast_sub h00.le, Nat.cast_sub h11.le, Nat.cast_sub h22.le, hR, hsq] at h3'
      linarith
    · simp only [hneg, Bool.cond_true, ↓reduceIte] at h3 htri
      have h3' := (Nat.cast_lt (α := ℝ)).mpr h3
      push_cast [Nat.cast_sub h00.le, Nat.cast_sub h11.le, Nat.cast_sub h22.le, hR, hsq] at h3'
      linarith

/-! ### Tests at many points -/

/-- `p j` holds for every `j < n`. Each step tests `p j` before the remaining indices, so the
kernel reduces the loop without nesting the remaining tests. -/
def natAll (n : ℕ) (p : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ ↦ Bool) true (fun j acc ↦ p j && acc) n

/-- If `natAll n p` holds, then `p j` holds for every `j < n`. -/
theorem natAll_spec {n : ℕ} {p : ℕ → Bool} (h : natAll n p = true) {j : ℕ} (hj : j < n) :
    p j = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact ih h2 hj
    · exact h1

end CAS.Numerics

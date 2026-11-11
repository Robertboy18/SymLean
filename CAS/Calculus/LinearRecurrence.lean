/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
module

public import CAS.Calculus.LinearODERoots

/-!
# Linear recurrences with constant coefficients

The recurrence `∑ₖ₌₀ᵈ aₖ y (n + k) = F n` is written `sLop d a y n = F n`. A nonzero root `μ`
of multiplicity `m` of the characteristic polynomial `∑ₖ aₖ Xᵏ` gives the solutions `nʲ μⁿ` with
`j < m` of the homogeneous recurrence, and `rec_general_iff` states that the solutions are a
particular solution plus a real combination of `seqBasis rs`: `nʲ rⁿ` for a real root `r`, and
`nʲ Re zⁿ`, `nʲ Im zⁿ` for a pair of conjugate roots `z`, `z̄`. When `a d = 1` and `a 0 ≠ 0`, the
values at `d` consecutive indices determine a solution (`rec_ivp_iff`).

## Main definitions

* `sLop`: the recurrence operator `∑ₖ₌₀ᵈ aₖ y (n + k)`.
* `seqBasis`: the real solutions `nʲ rⁿ`, `nʲ Re zⁿ`, `nʲ Im zⁿ`, factor by factor.
* `encSeq`: the sums `∑ G(μ) μⁿ` over the roots of a squarefree factor `R` enclosed by `D`.
* `quadUV`: the rational coordinates of the powers of a quadratic surd.

## Main results

* `pOpS_eq_zero_iff`: the kernel of `(E - μₙ) ⋯ (E - μ₁)`, for nonzero `μᵢ`, is the complex
  span of the `nʲ μᵢⁿ`.
* `rec_general_iff`, `rec_ivp_iff`: the general solution, and the solution determined by `d`
  consecutive values.
* `rec_general`, `rec_ivp`: the same for a characteristic polynomial split into exact roots
  (`CharRoot`) and the roots of a squarefree factor `R` enclosed by `D : Enclosures`.
* `encSeq_eq`: the value of `encSeq R D G` at `j` is a coefficient of the remainder of `G R' Xʲ`
  by `R`.

## Implementation notes

We follow the differential case (`pOp_eq_zero_iff`) with the shift `E` in place of `D`. For
`μ ≠ 0`, `E - μ` maps the span for `μ :: rest` onto the span for `rest` (`span_le_map_sOp`, by
strong induction on the power, and `sOp_mem_span`), and its own kernel is `ℂ μⁿ`
(`eq_of_sOp_eq_zero`). Stanley proves the same description through rational generating
functions and a count of dimensions; peeling off the factors needs no power series and repeats
the proof for differential equations. Uniqueness (`eq_of_sLop`) is an induction forward from
`k₀` and, since `a 0 ≠ 0`, backward to the indices below it.

The roots are not rational, but the values the kernel compares are. The powers of a quadratic
surd `α ± c √m` have rational coordinates `quadUV`, from
`(u + v β) (α + β) = (α u + q v) + (u + α v) β` when `β ^ 2 = q` (`pow_eq_quadUV`), which give
the values of the exact solutions (`pair_add_eq`, `pair_sub_eq`, `pairC_re_eq`, `pairC_im_eq`).
Over the enclosed roots the combinations are `encSeq R D G`, whose values come from one division
by `R` (`encSeq_eq`, from `Enclosures.sum_mul_pow`).

## References

* Richard P. Stanley, *Enumerative Combinatorics*, Volume 1, 2nd ed., Cambridge Studies in
  Advanced Mathematics 49, Cambridge University Press, Cambridge, 2012,
  <https://doi.org/10.1017/CBO9781139058520>. Chapter 4, Rational Generating Functions,
  pp. 464-570; we read Theorem 4.1.1, the solutions `∑ Pᵢ(n) γᵢⁿ` of a recurrence with
  `α_d ≠ 0`, in the author's manuscript of 15 July 2011.
* Manuel Kauers and Peter Paule, *The Concrete Tetrahedron*, Texts and Monographs in Symbolic
  Computation, Springer, Vienna, 2011, <https://doi.org/10.1007/978-3-7091-0445-3>. The chapter
  C-Finite Sequences, pp. 63-86, <https://doi.org/10.1007/978-3-7091-0445-3_4>.
-/

@[expose] public section

namespace CAS.LinearRecurrence

open Finset Submodule Complex _root_.Polynomial
open CAS.LinearODE CAS.AlgRoot
open CAS.Polynomial (coeffEval coeffAdd coeffMul coeffDeriv coeffEq)

/-! ## The complex span -/

/-- `nʲ μⁿ`. -/
noncomputable def sMono (μ : ℂ) (j n : ℕ) : ℂ := (n : ℂ) ^ j * μ ^ n

/-- `E - μ`: `f ↦ (n ↦ f (n + 1) - μ f n)`. -/
noncomputable def sOp (μ : ℂ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f n := f (n + 1) - μ * f n
  map_add' f g := by
    funext n
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- `sOp` unfolded: `sOp μ f n = f (n + 1) - μ * f n`. -/
theorem sOp_apply (μ : ℂ) (f : ℕ → ℂ) (n : ℕ) : sOp μ f n = f (n + 1) - μ * f n := rfl

/-- `(E - μₙ) ⋯ (E - μ₁)`, the first root applied first. -/
noncomputable def pOpS : List ℂ → (ℕ → ℂ) → ℕ → ℂ
  | [], f => f
  | μ :: rest, f => pOpS rest (sOp μ f)

/-- The sequences `nʲ μⁿ` with `j` below the multiplicity of `μ` in the list. -/
def seqBasisC (ls : List ℂ) : Set (ℕ → ℂ) := {f | ∃ μ j, j < ls.count μ ∧ f = sMono μ j}

/-- For `j` below the multiplicity of `μ` in `ls`, the sequence `sMono μ j` lies in the complex span
of `seqBasisC ls`. -/
theorem sMono_mem_span {ls : List ℂ} {μ : ℂ} {j : ℕ} (h : j < ls.count μ) :
    sMono μ j ∈ span ℂ (seqBasisC ls) :=
  subset_span ⟨μ, j, h, rfl⟩

/-- `E - μ` on `nʲ νⁿ`, for all complex `μ` and `ν`: `sOp μ (sMono ν j)` is
`(ν - μ) • sMono ν j + ν • ∑ i ∈ range j, (j.choose i) • sMono ν i`. -/
theorem sOp_sMono (μ ν : ℂ) (j : ℕ) :
    sOp μ (sMono ν j) =
      (ν - μ) • sMono ν j + ν • ∑ i ∈ range j, (j.choose i : ℂ) • sMono ν i := by
  funext n
  simp only [sOp_apply, sMono, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  have h : ((n + 1 : ℕ) : ℂ) ^ j =
      ∑ i ∈ range j, (j.choose i : ℂ) * (n : ℂ) ^ i + (n : ℂ) ^ j := by
    rw [Nat.cast_add_one, add_pow, sum_range_succ, Nat.choose_self]
    simp only [one_pow, mul_one, Nat.cast_one]
    congr 1
    exact sum_congr rfl fun i _ ↦ by ring
  have e : ∑ i ∈ range j, (j.choose i : ℂ) * ((n : ℂ) ^ i * ν ^ n) =
      (∑ i ∈ range j, (j.choose i : ℂ) * (n : ℂ) ^ i) * ν ^ n := by
    rw [sum_mul]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [h, e, pow_succ]
  ring

/-- The kernel of `E - μ`. -/
theorem eq_of_sOp_eq_zero {μ : ℂ} {f : ℕ → ℂ} (h : sOp μ f = 0) : f = f 0 • sMono μ 0 := by
  funext n
  induction n with
  | zero => simp [sMono]
  | succ n ih =>
    have hn := congrFun h n
    rw [sOp_apply, Pi.zero_apply, sub_eq_zero] at hn
    rw [hn, ih]
    simp only [Pi.smul_apply, sMono, pow_zero, one_mul, smul_eq_mul, pow_succ]
    ring

/-- `E - μ` maps the span for `μ :: rest` into the span for `rest`. -/
theorem sOp_mem_span (μ : ℂ) (rest : List ℂ) {f : ℕ → ℂ}
    (hf : f ∈ span ℂ (seqBasisC (μ :: rest))) : sOp μ f ∈ span ℂ (seqBasisC rest) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨ν, j, hj, rfl⟩ := hg
    have hle : j ≤ rest.count ν := by
      rw [List.count_cons] at hj
      split_ifs at hj <;> omega
    rw [sOp_sMono]
    refine add_mem ?_ (smul_mem _ _ (sum_mem fun i hi ↦
      smul_mem _ _ (sMono_mem_span (by have := mem_range.mp hi; omega))))
    by_cases hν : ν = μ
    · simp [hν]
    · rw [List.count_cons_of_ne (Ne.symm hν)] at hj
      exact smul_mem _ _ (sMono_mem_span hj)
  | zero => simp
  | add g h _ _ hg hh => rw [map_add]; exact add_mem hg hh
  | smul c g _ hg => rw [map_smul]; exact smul_mem _ c hg

/-- `E - μ` maps the span for `μ :: rest` onto the span for `rest` when `μ ≠ 0`. -/
theorem span_le_map_sOp {μ : ℂ} (hμ : μ ≠ 0) (rest : List ℂ) :
    span ℂ (seqBasisC rest) ≤ (span ℂ (seqBasisC (μ :: rest))).map (sOp μ) := by
  rw [span_le]
  rintro _ ⟨ν, J, hJ, rfl⟩
  have hin : ∀ i, i < (μ :: rest).count ν →
      sOp μ (sMono ν i) ∈ (span ℂ (seqBasisC (μ :: rest))).map (sOp μ) :=
    fun i hi ↦ mem_map_of_mem (sMono_mem_span hi)
  induction J using Nat.strong_induction_on with
  | _ J ih =>
    have hlow (c : ℕ → ℂ) : ∑ i ∈ range J, c i • sMono ν i ∈
        (span ℂ (seqBasisC (μ :: rest))).map (sOp μ) :=
      sum_mem fun i hi ↦ smul_mem _ _ (ih i (mem_range.mp hi) (by have := mem_range.mp hi; omega))
    by_cases hν : ν = μ
    · subst hν
      have h1 := hin (J + 1) (by rw [List.count_cons_self]; omega)
      rw [sOp_sMono, sub_self, zero_smul, zero_add, sum_range_succ, Nat.choose_succ_self_right,
        smul_add] at h1
      have hne : ν * ((J + 1 : ℕ) : ℂ) ≠ 0 :=
        mul_ne_zero hμ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero J))
      have key : sMono ν J = (ν * ((J + 1 : ℕ) : ℂ))⁻¹ •
          ((ν • ∑ i ∈ range J, ((J + 1).choose i : ℂ) • sMono ν i +
            ν • (((J + 1 : ℕ) : ℂ) • sMono ν J)) -
          ν • ∑ i ∈ range J, ((J + 1).choose i : ℂ) • sMono ν i) := by
        rw [add_sub_cancel_left, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hne, one_smul]
      rw [key]
      exact smul_mem _ _ (sub_mem h1 (smul_mem _ _ (hlow _)))
    · have h1 := hin J (by rw [List.count_cons_of_ne (Ne.symm hν)]; exact hJ)
      rw [sOp_sMono] at h1
      have key : sMono ν J = (ν - μ)⁻¹ •
          (((ν - μ) • sMono ν J + ν • ∑ i ∈ range J, (J.choose i : ℂ) • sMono ν i) -
          ν • ∑ i ∈ range J, (J.choose i : ℂ) • sMono ν i) := by
        rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hν), one_smul]
      rw [key]
      exact smul_mem _ _ (sub_mem h1 (smul_mem _ _ (hlow _)))

/-- The kernel of `(E - μₙ) ⋯ (E - μ₁)` for nonzero `μᵢ`. -/
theorem pOpS_eq_zero_iff : ∀ (ls : List ℂ), (∀ μ ∈ ls, μ ≠ 0) → ∀ {f : ℕ → ℂ},
    (pOpS ls f = 0 ↔ f ∈ span ℂ (seqBasisC ls))
  | [], _, f => by simp [pOpS, seqBasisC]
  | μ :: rest, h0, f => by
    rw [pOpS, pOpS_eq_zero_iff rest fun ν hν ↦ h0 ν (List.mem_cons_of_mem _ hν)]
    refine ⟨fun h ↦ ?_, sOp_mem_span μ rest⟩
    obtain ⟨χ, hχ, hχeq⟩ := mem_map.mp (span_le_map_sOp (h0 μ (by simp)) rest h)
    have hk := eq_of_sOp_eq_zero (f := f - χ) (by rw [map_sub, hχeq, sub_self])
    rw [← sub_add_cancel f χ, hk]
    exact add_mem (smul_mem _ _ (sMono_mem_span (by simp))) hχ

/-- `(E - μₙ) ⋯ (E - μ₁) f = ∑ cₖ f (n + k)` with the coefficients of `∏ (X - μᵢ)`. -/
theorem pOpS_eq_sum : ∀ (ls : List ℂ) (f : ℕ → ℂ) (n : ℕ),
    pOpS ls f n = ∑ k ∈ range (ls.length + 1), charC ls k * f (n + k)
  | [], f, n => by simp [pOpS, charC]
  | μ :: rest, f, n => by
    rw [pOpS, pOpS_eq_sum rest (sOp μ f) n]
    simp only [List.length_cons, charC]
    have hterm : ∀ k ∈ range (rest.length + 1), charC rest k * sOp μ f (n + k) =
        charC rest k * f (n + k + 1) - μ * (charC rest k * f (n + k)) :=
      fun k _ ↦ by rw [sOp_apply]; ring
    have hs := sum_range_succ' (fun k ↦ charC rest k * f (n + k)) (rest.length + 1)
    rw [sum_range_succ, charC_eq_zero rest (lt_add_one _), zero_mul, add_zero] at hs
    rw [sum_congr rfl hterm, sum_range_succ' _ (rest.length + 1)]
    simp only [mulRoot, sub_mul, mul_assoc, sum_sub_distrib, ← mul_sum, ← add_assoc,
      add_zero] at hs ⊢
    linear_combination (-μ) * hs

/-! ## Real recurrences -/

/-- `∑ₖ₌₀ᵈ aₖ y (n + k)`. -/
def sLop (d : ℕ) (a : ℕ → ℝ) (y : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ range (d + 1), a k * y (n + k)

/-- The recurrence operator takes differences to differences:
`sLop d a (y - z) n = sLop d a y n - sLop d a z n`. -/
theorem sLop_sub (d : ℕ) (a : ℕ → ℝ) (y z : ℕ → ℝ) (n : ℕ) :
    sLop d a (fun m ↦ y m - z m) n = sLop d a y n - sLop d a z n := by
  simp only [sLop, mul_sub, sum_sub_distrib]

/-- At a real `r`, `sMono r j n` is the cast of the real number `nʲ rⁿ`. -/
theorem sMono_ofReal (r : ℝ) (j n : ℕ) : sMono (r : ℂ) j n = (((n : ℝ) ^ j * r ^ n : ℝ) : ℂ) := by
  simp [sMono]

/-- For real `a` and `b`, `sMono (a + b i) j n` is `nʲ Re ((a + b i)ⁿ) + i nʲ Im ((a + b i)ⁿ)`, both
parts cast from `ℝ`. -/
theorem sMono_pair_add (a b : ℝ) (j n : ℕ) :
    sMono ((a : ℂ) + (b : ℂ) * I) j n =
      (((n : ℝ) ^ j * (((a : ℂ) + (b : ℂ) * I) ^ n).re : ℝ) : ℂ) +
        I * (((n : ℝ) ^ j * (((a : ℂ) + (b : ℂ) * I) ^ n).im : ℝ) : ℂ) := by
  have := Complex.re_add_im (((a : ℂ) + (b : ℂ) * I) ^ n)
  simp only [sMono, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
  linear_combination ((n : ℂ) ^ j) * this.symm

/-- For real `a` and `b`, `a - b i` is the complex conjugate of `a + b i`. -/
theorem conj_pair (a b : ℝ) : (a : ℂ) - (b : ℂ) * I = (starRingEnd ℂ) ((a : ℂ) + (b : ℂ) * I) := by
  apply Complex.ext <;> simp

/-- For real `a` and `b`, `sMono (a - b i) j n` is `nʲ Re ((a + b i)ⁿ) - i nʲ Im ((a + b i)ⁿ)`, both
parts cast from `ℝ`. -/
theorem sMono_pair_sub (a b : ℝ) (j n : ℕ) :
    sMono ((a : ℂ) - (b : ℂ) * I) j n =
      (((n : ℝ) ^ j * (((a : ℂ) + (b : ℂ) * I) ^ n).re : ℝ) : ℂ) -
        I * (((n : ℝ) ^ j * (((a : ℂ) + (b : ℂ) * I) ^ n).im : ℝ) : ℂ) := by
  have h1 : ((a : ℂ) - (b : ℂ) * I) ^ n = ((((a : ℂ) + (b : ℂ) * I) ^ n).re : ℂ) -
      ((((a : ℂ) + (b : ℂ) * I) ^ n).im : ℂ) * I := by
    rw [conj_pair, ← map_pow]
    generalize ((a : ℂ) + (b : ℂ) * I) ^ n = w
    apply Complex.ext <;> simp
  simp only [sMono, h1, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
  ring

/-- The real solutions for a factor of `CharRoot`. -/
noncomputable def charSeqs : CharRoot → ℕ → List (ℕ → ℝ)
  | .real r, j => [fun n ↦ (n : ℝ) ^ j * (r : ℝ) ^ n]
  | .realPair α c m, j => [fun n ↦ (n : ℝ) ^ j * ((α : ℝ) + CharRoot.width c m) ^ n,
      fun n ↦ (n : ℝ) ^ j * ((α : ℝ) - CharRoot.width c m) ^ n]
  | .pair α c m, j =>
      [fun n ↦ (n : ℝ) ^ j * ((((α : ℝ) : ℂ) + (CharRoot.width c m : ℂ) * I) ^ n).re,
        fun n ↦ (n : ℝ) ^ j * ((((α : ℝ) : ℂ) + (CharRoot.width c m : ℂ) * I) ^ n).im]

/-- The real solutions `nʲ rⁿ`, `nʲ Re zⁿ`, `nʲ Im zⁿ` for a factor. -/
noncomputable def rootSeqs : RRoot → ℕ → List (ℕ → ℝ)
  | .char ρ, j => charSeqs ρ j
  | .real r, j => [fun n ↦ (n : ℝ) ^ j * r ^ n]
  | .pair α β, j => [fun n ↦ (n : ℝ) ^ j * (((α : ℂ) + (β : ℂ) * I) ^ n).re,
      fun n ↦ (n : ℝ) ^ j * (((α : ℂ) + (β : ℂ) * I) ^ n).im]

/-- The real solutions, factor by factor and power by power. -/
noncomputable def seqBasis : List (RRoot × ℕ) → List (ℕ → ℝ)
  | [] => []
  | (ρ, k) :: rest => (List.range k).flatMap (rootSeqs ρ) ++ seqBasis rest

/-- `f` lies in `seqBasis rs` exactly when `f ∈ rootSeqs ρ j` for some factor `(ρ, k)` of `rs` and
some `j < k`. -/
theorem mem_seqBasis {f : ℕ → ℝ} :
    ∀ {rs : List (RRoot × ℕ)}, f ∈ seqBasis rs ↔ ∃ e ∈ rs, ∃ j < e.2, f ∈ rootSeqs e.1 j
  | [] => by simp [seqBasis]
  | (ρ, k) :: rest => by
    simp only [seqBasis, List.mem_append, List.mem_flatMap, List.mem_range, mem_seqBasis,
      List.mem_cons, exists_eq_or_imp]

/-- A real root contributes `nʲ rⁿ`. -/
theorem real_sMono_mem {S : Set (ℕ → ℝ)} {r : ℝ} {j : ℕ}
    (hS : (fun n : ℕ ↦ (n : ℝ) ^ j * r ^ n) ∈ S) :
    ∃ h₁ ∈ span ℝ S, ∃ h₂ ∈ span ℝ S, ∀ n, sMono (r : ℂ) j n = (h₁ n : ℂ) + I * (h₂ n : ℂ) :=
  ⟨_, subset_span hS, 0, zero_mem _, fun n ↦ by rw [sMono_ofReal]; simp⟩

/-- A pair `a ± b i` contributes `nʲ Re zⁿ` and `nʲ Im zⁿ`. -/
theorem pair_sMono_mem {S : Set (ℕ → ℝ)} {a b : ℝ} {j : ℕ}
    (hre : (fun n : ℕ ↦ (n : ℝ) ^ j * (((a : ℂ) + (b : ℂ) * I) ^ n).re) ∈ S)
    (him : (fun n : ℕ ↦ (n : ℝ) ^ j * (((a : ℂ) + (b : ℂ) * I) ^ n).im) ∈ S) {μ : ℂ}
    (hμ : μ = (a : ℂ) + (b : ℂ) * I ∨ μ = (a : ℂ) - (b : ℂ) * I) :
    ∃ h₁ ∈ span ℝ S, ∃ h₂ ∈ span ℝ S, ∀ n, sMono μ j n = (h₁ n : ℂ) + I * (h₂ n : ℂ) := by
  rcases hμ with rfl | rfl
  · exact ⟨_, subset_span hre, _, subset_span him, fun n ↦ sMono_pair_add a b j n⟩
  · refine ⟨_, subset_span hre, _, neg_mem (subset_span him), fun n ↦ ?_⟩
    rw [sMono_pair_sub]
    simp only [Pi.neg_apply, Complex.ofReal_neg]
    ring

/-- For a root `μ` of `ρ`, the sequence `sMono μ j` is `h₁ + i h₂` with `h₁` and `h₂` in the real
span of `rootSeqs ρ j`. -/
theorem sMono_eq_of_mem_rootSeqs {ρ : RRoot} {μ : ℂ} (hμ : μ ∈ ρ.roots) (j : ℕ) :
    ∃ h₁ ∈ span ℝ {f | f ∈ rootSeqs ρ j}, ∃ h₂ ∈ span ℝ {f | f ∈ rootSeqs ρ j},
      ∀ n, sMono μ j n = (h₁ n : ℂ) + I * (h₂ n : ℂ) := by
  rcases ρ with (r | ⟨α, c, m⟩ | ⟨α, c, m⟩) | r | ⟨α, β⟩
  · obtain rfl := List.mem_singleton.mp hμ
    exact real_sMono_mem (by simp [rootSeqs, charSeqs])
  · simp only [RRoot.roots, CharRoot.roots, List.mem_cons, List.not_mem_nil, or_false] at hμ
    rcases hμ with rfl | rfl
    · exact real_sMono_mem (by simp [rootSeqs, charSeqs])
    · exact real_sMono_mem (by simp [rootSeqs, charSeqs])
  · simp only [RRoot.roots, CharRoot.roots, List.mem_cons, List.not_mem_nil, or_false] at hμ
    exact pair_sMono_mem (by simp [rootSeqs, charSeqs]) (by simp [rootSeqs, charSeqs]) hμ
  · obtain rfl := List.mem_singleton.mp hμ
    exact real_sMono_mem (by simp [rootSeqs])
  · simp only [RRoot.roots, List.mem_cons, List.not_mem_nil, or_false] at hμ
    exact pair_sMono_mem (by simp [rootSeqs]) (by simp [rootSeqs]) hμ

/-- The real and imaginary parts of `nʲ zⁿ` from `nʲ zⁿ` and `nʲ z̄ⁿ`. -/
theorem pair_ofReal_mem {T : Set (ℕ → ℂ)} {a b : ℝ} {j : ℕ}
    (h₁ : sMono ((a : ℂ) + (b : ℂ) * I) j ∈ span ℂ T)
    (h₂ : sMono ((a : ℂ) - (b : ℂ) * I) j ∈ span ℂ T) :
    (fun n : ℕ ↦ (((n : ℝ) ^ j * (((a : ℂ) + (b : ℂ) * I) ^ n).re : ℝ) : ℂ)) ∈ span ℂ T ∧
      (fun n : ℕ ↦ (((n : ℝ) ^ j * (((a : ℂ) + (b : ℂ) * I) ^ n).im : ℝ) : ℂ)) ∈ span ℂ T := by
  constructor
  · convert add_mem (smul_mem _ (1 / 2 : ℂ) h₁) (smul_mem _ (1 / 2 : ℂ) h₂) using 1
    funext n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sMono_pair_add, sMono_pair_sub]
    ring
  · convert add_mem (smul_mem _ (-I / 2) h₁) (smul_mem _ (I / 2) h₂) using 1
    funext n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sMono_pair_add, sMono_pair_sub]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- Each real solution `f ∈ rootSeqs ρ j`, cast to `ℂ`, lies in the complex span of the sequences
`sMono μ j` at the roots `μ` of `ρ`. -/
theorem ofReal_mem_span_of_mem_rootSeqs {ρ : RRoot} {j : ℕ} {f : ℕ → ℝ}
    (hf : f ∈ rootSeqs ρ j) :
    (fun n ↦ (f n : ℂ)) ∈ span ℂ ((fun μ ↦ sMono μ j) '' {μ | μ ∈ ρ.roots}) := by
  have mem : ∀ μ ∈ ρ.roots, sMono μ j ∈ span ℂ ((fun μ ↦ sMono μ j) '' {μ | μ ∈ ρ.roots}) :=
    fun μ hμ ↦ subset_span ⟨μ, hμ, rfl⟩
  rcases ρ with (r | ⟨α, c, m⟩ | ⟨α, c, m⟩) | r | ⟨α, β⟩
  · obtain rfl := List.mem_singleton.mp hf
    convert mem (((r : ℝ) : ℂ)) (by simp [RRoot.roots, CharRoot.roots]) using 1
    exact funext fun n ↦ (sMono_ofReal _ j n).symm
  · simp only [rootSeqs, charSeqs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · convert mem (((α : ℝ) + CharRoot.width c m : ℝ) : ℂ)
        (by simp [RRoot.roots, CharRoot.roots]) using 1
      exact funext fun n ↦ (sMono_ofReal _ j n).symm
    · convert mem (((α : ℝ) - CharRoot.width c m : ℝ) : ℂ)
        (by simp [RRoot.roots, CharRoot.roots]) using 1
      exact funext fun n ↦ (sMono_ofReal _ j n).symm
  · simp only [rootSeqs, charSeqs, List.mem_cons, List.not_mem_nil, or_false] at hf
    have h := pair_ofReal_mem (a := (α : ℝ)) (b := CharRoot.width c m)
      (mem _ (by simp [RRoot.roots, CharRoot.roots]))
      (mem _ (by simp [RRoot.roots, CharRoot.roots]))
    rcases hf with rfl | rfl
    · exact h.1
    · exact h.2
  · obtain rfl := List.mem_singleton.mp hf
    convert mem (r : ℂ) (by simp [RRoot.roots]) using 1
    exact funext fun n ↦ (sMono_ofReal _ j n).symm
  · simp only [rootSeqs, List.mem_cons, List.not_mem_nil, or_false] at hf
    have h := pair_ofReal_mem (a := α) (b := β) (mem _ (by simp [RRoot.roots]))
      (mem _ (by simp [RRoot.roots]))
    rcases hf with rfl | rfl
    · exact h.1
    · exact h.2

/-- The real solutions of `∑ aₖ y (n + k) = 0` when the `aₖ` are the coefficients of
`∏ (X - μ)` over the nonzero roots `rrList rs`. -/
theorem sLop_eq_zero_iff (rs : List (RRoot × ℕ)) (hnd : (rrAll rs).Nodup)
    (h0 : ∀ μ ∈ rrAll rs, μ ≠ 0) (a : List ℚ)
    (hc : ∀ k, charC (rrList rs) k = (a.getD k 0 : ℂ)) {y : ℕ → ℝ} :
    (∀ n, sLop (rrList rs).length (fun k ↦ (a.getD k 0 : ℝ)) y n = 0) ↔
      y ∈ span ℝ {f | f ∈ seqBasis rs} := by
  set z : ℕ → ℂ := fun n ↦ (y n : ℂ) with hz
  have h0' : ∀ μ ∈ rrList rs, μ ≠ 0 := fun μ hμ ↦ by
    obtain ⟨e, he, hμe⟩ := mem_of_mem_rrList hμ
    exact h0 μ (List.mem_flatMap.mpr ⟨e, he, hμe⟩)
  have hop : ∀ n, pOpS (rrList rs) z n =
      ((sLop (rrList rs).length (fun k ↦ (a.getD k 0 : ℝ)) y n : ℝ) : ℂ) := by
    intro n
    rw [pOpS_eq_sum, sLop, hz]
    push_cast
    exact sum_congr rfl fun k _ ↦ by rw [hc k]
  have step₁ : (∀ n, sLop (rrList rs).length (fun k ↦ (a.getD k 0 : ℝ)) y n = 0) ↔
      z ∈ span ℂ (seqBasisC (rrList rs)) := by
    rw [← pOpS_eq_zero_iff _ h0', funext_iff]
    simp only [hop, Pi.zero_apply, Complex.ofReal_eq_zero]
  rw [step₁]
  set S := span ℝ {f | f ∈ seqBasis rs}
  have hsub : ∀ e ∈ rs, ∀ j < e.2, span ℝ {f | f ∈ rootSeqs e.1 j} ≤ S := fun e he j hj ↦
    span_mono fun f hf ↦ mem_seqBasis.mpr ⟨e, he, j, hj, hf⟩
  constructor
  · intro hmem
    have key : ∀ g ∈ span ℂ (seqBasisC (rrList rs)),
        ∃ h₁ ∈ S, ∃ h₂ ∈ S, ∀ n, g n = (h₁ n : ℂ) + I * (h₂ n : ℂ) := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨μ, j, hj, rfl⟩ := hg
        have hpos : 0 < (rrList rs).count μ := by omega
        obtain ⟨e, he, hμ⟩ := mem_of_mem_rrList (List.count_pos_iff.mp hpos)
        have hk := count_rrList_of_mem hnd he hμ
        obtain ⟨h₁, hh₁, h₂, hh₂, hx⟩ := sMono_eq_of_mem_rootSeqs hμ j
        exact ⟨h₁, hsub e he j (by omega) hh₁, h₂, hsub e he j (by omega) hh₂, hx⟩
      | zero => exact ⟨0, zero_mem _, 0, zero_mem _, fun n ↦ by simp⟩
      | add g g' _ _ hg hg' =>
        obtain ⟨a₁, ha₁, a₂, ha₂, ha⟩ := hg
        obtain ⟨b₁, hb₁, b₂, hb₂, hb⟩ := hg'
        refine ⟨a₁ + b₁, add_mem ha₁ hb₁, a₂ + b₂, add_mem ha₂ hb₂, fun n ↦ ?_⟩
        simp only [Pi.add_apply, ha, hb, Complex.ofReal_add]
        ring
      | smul c g _ hg =>
        obtain ⟨a₁, ha₁, a₂, ha₂, ha⟩ := hg
        refine ⟨c.re • a₁ - c.im • a₂, sub_mem (smul_mem _ _ ha₁) (smul_mem _ _ ha₂),
          c.im • a₁ + c.re • a₂, add_mem (smul_mem _ _ ha₁) (smul_mem _ _ ha₂), fun n ↦ ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, ha, Pi.sub_apply, Pi.add_apply,
          Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
        linear_combination ((a₁ n : ℂ) + I * a₂ n) * (Complex.re_add_im c).symm +
          (c.im : ℂ) * a₂ n * Complex.I_sq
    obtain ⟨h₁, hh₁, h₂, -, hx⟩ := key z hmem
    rwa [show y = h₁ from funext fun n ↦ by simpa [hz] using congrArg Complex.re (hx n)]
  · intro hmem
    have key : ∀ f ∈ S, (fun n ↦ (f n : ℂ)) ∈ span ℂ (seqBasisC (rrList rs)) := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨e, he, j, hj, hfe⟩ := mem_seqBasis.mp hf
        refine span_mono ?_ (ofReal_mem_span_of_mem_rootSeqs hfe)
        rintro g ⟨μ, hμ, rfl⟩
        exact ⟨μ, j, lt_of_lt_of_le hj (le_count_rrList he hμ), rfl⟩
      | zero =>
        convert zero_mem (span ℂ (seqBasisC (rrList rs))) using 1
      | add f g _ _ hf hg =>
        convert add_mem hf hg using 1
        exact funext fun n ↦ by simp
      | smul c f _ hf =>
        convert smul_mem _ (c : ℂ) hf using 1
        exact funext fun n ↦ by simp
    exact key y hmem

/-- The general solution of `∑ aₖ y (n + k) = F n` with a particular solution `Yp`. -/
theorem rec_general_iff (rs : List (RRoot × ℕ)) (hnd : (rrAll rs).Nodup)
    (h0 : ∀ μ ∈ rrAll rs, μ ≠ 0) (a : List ℚ)
    (hc : ∀ k, charC (rrList rs) k = (a.getD k 0 : ℂ)) {d : ℕ} (hd : (rrList rs).length = d)
    {Yp F : ℕ → ℝ} (hpart : ∀ n, sLop d (fun k ↦ (a.getD k 0 : ℝ)) Yp n = F n) {y : ℕ → ℝ} :
    (∀ n, sLop d (fun k ↦ (a.getD k 0 : ℝ)) y n = F n) ↔
      (fun n ↦ y n - Yp n) ∈ span ℝ {f | f ∈ seqBasis rs} := by
  subst hd
  rw [← sLop_eq_zero_iff rs hnd h0 a hc]
  exact forall_congr' fun n ↦ by rw [sLop_sub, hpart, sub_eq_zero]

/-- A solution is determined by `d` consecutive values when `a₀ ≠ 0` and `a_d = 1`. -/
theorem eq_of_sLop {d : ℕ} {a : ℕ → ℝ} (ha : a d = 1) (h0 : a 0 ≠ 0) {F y z : ℕ → ℝ}
    (hy : ∀ n, sLop d a y n = F n) (hz : ∀ n, sLop d a z n = F n) (k₀ : ℕ)
    (hinit : ∀ k < d, y (k₀ + k) = z (k₀ + k)) : y = z := by
  set w : ℕ → ℝ := fun n ↦ y n - z n with hw
  have hL : ∀ n, sLop d a w n = 0 := fun n ↦ by rw [hw, sLop_sub, hy, hz, sub_self]
  have hfwd : ∀ n, k₀ ≤ n → w n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      by_cases hlt : n < k₀ + d
      · have := hinit (n - k₀) (by omega)
        rw [show k₀ + (n - k₀) = n by omega] at this
        simp [hw, this]
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + d := ⟨n - d, by omega⟩
        have h := hL m
        rw [sLop, sum_range_succ, ha, one_mul] at h
        have hs : ∑ k ∈ range d, a k * w (m + k) = 0 :=
          sum_eq_zero fun k hk ↦ by
            rw [ih (m + k) (by have := mem_range.mp hk; omega)
              (by have := mem_range.mp hk; omega), mul_zero]
        rw [hs, zero_add] at h
        exact h
  have hback : ∀ t n, k₀ ≤ n + t → w n = 0 := by
    intro t
    induction t with
    | zero => exact fun n hn ↦ hfwd n hn
    | succ t ih =>
      intro n hn
      by_cases hle : k₀ ≤ n + t
      · exact ih n hle
      · have h := hL n
        rw [sLop, sum_range_succ'] at h
        have hs : ∑ k ∈ range d, a (k + 1) * w (n + (k + 1)) = 0 :=
          sum_eq_zero fun k _ ↦ by rw [ih (n + (k + 1)) (by omega), mul_zero]
        rw [hs, zero_add, add_zero] at h
        exact (mul_eq_zero.mp h).resolve_left h0
  funext n
  have := hback k₀ n (by omega)
  simpa [hw, sub_eq_zero] using this

/-- The initial-value problem: `d` consecutive values from `k₀` on determine the solution. -/
theorem rec_ivp_iff {d : ℕ} {a : ℕ → ℝ} (ha : a d = 1) (h0 : a 0 ≠ 0) {F Y : ℕ → ℝ}
    (hY : ∀ n, sLop d a Y n = F n) (k₀ : ℕ) (v : ℕ → ℝ) (hv : ∀ k < d, Y (k₀ + k) = v k)
    {y : ℕ → ℝ} :
    ((∀ n, sLop d a y n = F n) ∧ ∀ k < d, y (k₀ + k) = v k) ↔ ∀ n, y n = Y n := by
  constructor
  · rintro ⟨h, hinit⟩
    exact congrFun (eq_of_sLop ha h0 h hY k₀ fun k hk ↦ by rw [hinit k hk, hv k hk])
  · intro h
    rw [show y = Y from funext h]
    exact ⟨hY, hv⟩

/-! ## Enclosed roots in recurrences -/

/-- `seqBasis (l₁ ++ l₂) = seqBasis l₁ ++ seqBasis l₂`. -/
theorem seqBasis_append : ∀ (l₁ l₂ : List (RRoot × ℕ)),
    seqBasis (l₁ ++ l₂) = seqBasis l₁ ++ seqBasis l₂
  | [], _ => rfl
  | (ρ, k) :: l₁, l₂ => by
    rw [List.cons_append, seqBasis, seqBasis, seqBasis_append l₁ l₂, List.append_assoc]

/-- `∑ G(μ) μⁿ` over the roots enclosed by `D`, in real numbers: `G(r) rⁿ` for a real root and
`2 Re (G(z) zⁿ)` for a conjugate pair. -/
noncomputable def encSeq (R : List ℚ) (D : Enclosures) (G : List ℚ) (n : ℕ) : ℝ :=
  (D.reals.map fun I ↦ coeffEval G (CAS.AlgRoot.real R I.1 I.2) *
      CAS.AlgRoot.real R I.1 I.2 ^ n).sum +
    (D.discs.map fun d ↦ 2 * ((polyC G).eval (CAS.AlgRoot.complex R d.1 d.2.1 d.2.2.1) *
      CAS.AlgRoot.complex R d.1 d.2.1 d.2.2.1 ^ n).re).sum

/-- If `g x` lies in a submodule `S` of real sequences for every `x ∈ l`, so does the pointwise sum
`n ↦ ∑ x ∈ l, g x n`. -/
theorem fun_sum_mem {α : Type*} {S : Submodule ℝ (ℕ → ℝ)} (l : List α) (g : α → ℕ → ℝ)
    (h : ∀ x ∈ l, g x ∈ S) : (fun n ↦ (l.map fun x ↦ g x n).sum) ∈ S := by
  induction l with
  | nil => exact zero_mem S
  | cons x l ih =>
    have := add_mem (h x (by simp)) (ih fun y hy ↦ h y (by simp [hy]))
    convert this using 1
    funext n
    simp

/-- `encSeq R D G` lies in the real span of `seqBasis (D.rroots R)`, for every `R`, `D` and `G`. No
check of `D` is assumed. -/
theorem encSeq_mem (R : List ℚ) (D : Enclosures) (G : List ℚ) :
    encSeq R D G ∈ span ℝ {f | f ∈ seqBasis (D.rroots R)} := by
  set S := span ℝ {f | f ∈ seqBasis (D.rroots R)}
  have hS : ∀ e ∈ D.rroots R, ∀ f ∈ rootSeqs e.1 0, f ∈ S := fun e he f hf ↦ by
    refine subset_span (mem_seqBasis.mpr ⟨e, he, 0, ?_, hf⟩)
    simp only [Enclosures.rroots, List.mem_append, List.mem_map] at he
    rcases he with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact Nat.one_pos
  refine add_mem (fun_sum_mem D.reals _ fun I hI ↦ ?_) (fun_sum_mem D.discs _ fun d hd ↦ ?_)
  · have h := hS _ (List.mem_append_left _ (List.mem_map.mpr ⟨I, hI, rfl⟩)) _
      (List.mem_singleton_self _)
    convert smul_mem S (coeffEval G (CAS.AlgRoot.real R I.1 I.2)) h using 1
    funext n
    simp
  · set z := CAS.AlgRoot.complex R d.1 d.2.1 d.2.2.1
    set w := (polyC G).eval z
    have he : (RRoot.pair z.re z.im, 1) ∈ D.rroots R :=
      List.mem_append_right _ (List.mem_map.mpr ⟨d, hd, rfl⟩)
    have h1 := hS _ he (fun n ↦ (n : ℝ) ^ 0 * (((z.re : ℂ) + (z.im : ℂ) * I) ^ n).re)
      (by simp [rootSeqs])
    have h2 := hS _ he (fun n ↦ (n : ℝ) ^ 0 * (((z.re : ℂ) + (z.im : ℂ) * I) ^ n).im)
      (by simp [rootSeqs])
    convert add_mem (smul_mem S (2 * w.re) h1) (smul_mem S (-(2 * w.im)) h2) using 1
    funext n
    simp only [Complex.re_add_im, Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_zero, one_mul,
      Complex.mul_re]
    ring

/-- The value of `encSeq` at `j`, from the remainder `Q` of `G R' Xʲ` by `R`. -/
theorem encSeq_eq (R : List ℚ) (D : Enclosures) (hD : D.check R = true)
    (G T Q : List ℚ) (j : ℕ)
    (hdiv : coeffEq (coeffMul (coeffMul G (coeffDeriv R)) (powX j)) (coeffAdd (coeffMul T R) Q) =
      true)
    (hQ : Q.length < R.length) : encSeq R D G j = (Q.getD (R.length - 2) 0 : ℝ) := by
  have h : ((encSeq R D G j : ℝ) : ℂ) = ((Q.getD (R.length - 2) 0 : ℚ) : ℂ) :=
    (Enclosures.sum_real R D G j).symm.trans (Enclosures.sum_mul_pow R D hD G T Q j hdiv hQ)
  exact_mod_cast h

/-! ## Powers of quadratic surds -/

/-- One step of `quadUV`: `(u + v β) (α + β) = (α u + q v) + (u + α v) β` when `β ^ 2 = q`. -/
def quadStep (α q : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (α * p.1 + q * p.2, p.1 + α * p.2)

/-- The rational coordinates `(u, v)` of `(α + β) ^ n = u + v β` when `β ^ 2 = q`. -/
def quadUV (α q : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => quadStep α q (quadUV α q n)

/-- In a field `K` of characteristic zero, for `β` with `β ^ 2 = q`, `(α + β) ^ N = u + v β` with
`(u, v) = quadUV α q N`. -/
theorem pow_eq_quadUV {K : Type*} [Field K] [CharZero K] (α q : ℚ) {β : K} (hβ : β ^ 2 = q)
    (N : ℕ) : ((α : K) + β) ^ N = (quadUV α q N).1 + (quadUV α q N).2 * β := by
  induction N with
  | zero => simp [quadUV]
  | succ N ih =>
    rw [pow_succ, ih]
    simp only [quadUV, quadStep]
    push_cast
    linear_combination ((quadUV α q N).2 : K) * hβ

/-- `r₊ᴺ + r₋ᴺ` for `r± = α ± c √m`. -/
theorem pair_add_eq (α c m : ℚ) (hm : 0 ≤ m) (N : ℕ) :
    ((α : ℝ) + CharRoot.width c m) ^ N + ((α : ℝ) - CharRoot.width c m) ^ N =
      2 * ((quadUV α (c ^ 2 * m) N).1 : ℝ) := by
  have h₁ := pow_eq_quadUV α (c ^ 2 * m) (width_sq hm) N
  have h₂ := pow_eq_quadUV α (c ^ 2 * m) (β := -CharRoot.width c m)
    (by rw [neg_sq]; exact width_sq hm) N
  rw [sub_eq_add_neg, h₁, h₂]
  ring

/-- `(r₊ᴺ - r₋ᴺ) / √m` for `r± = α ± c √m`. -/
theorem pair_sub_eq (α c m : ℚ) (hm : 0 < m) (N : ℕ) :
    (((α : ℝ) + CharRoot.width c m) ^ N - ((α : ℝ) - CharRoot.width c m) ^ N) /
        Real.sqrt (m : ℝ) = 2 * ((c * (quadUV α (c ^ 2 * m) N).2 : ℚ) : ℝ) := by
  have h₁ := pow_eq_quadUV α (c ^ 2 * m) (width_sq hm.le) N
  have h₂ := pow_eq_quadUV α (c ^ 2 * m) (β := -CharRoot.width c m)
    (by rw [neg_sq]; exact width_sq hm.le) N
  have hs : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Rat.cast_pos.mpr hm)).ne'
  rw [sub_eq_add_neg ((α : ℝ)), h₁, h₂, CharRoot.width, div_eq_iff hs]
  push_cast
  ring

/-- `zᴺ` for `z = α + c √m i`, in rational coordinates. -/
theorem pairC_eq (α c m : ℚ) (hm : 0 ≤ m) (N : ℕ) :
    (((α : ℝ) : ℂ) + (CharRoot.width c m : ℂ) * I) ^ N =
      (((quadUV α (-(c ^ 2 * m)) N).1 : ℝ) : ℂ) +
        (((quadUV α (-(c ^ 2 * m)) N).2 * CharRoot.width c m : ℝ) : ℂ) * I := by
  have hβ : ((CharRoot.width c m : ℂ) * I) ^ 2 = ((-(c ^ 2 * m) : ℚ) : ℂ) := by
    rw [mul_pow, I_sq, ← Complex.ofReal_pow, width_sq hm]
    push_cast
    ring
  rw [Complex.ofReal_ratCast α, pow_eq_quadUV α _ hβ N]
  push_cast
  ring

/-- `Re zᴺ` for `z = α + c √m i`. -/
theorem pairC_re_eq (α c m : ℚ) (hm : 0 ≤ m) (N : ℕ) :
    ((((α : ℝ) : ℂ) + (CharRoot.width c m : ℂ) * I) ^ N).re =
      ((quadUV α (-(c ^ 2 * m)) N).1 : ℝ) := by
  rw [pairC_eq α c m hm N]
  simp

/-- `Im zᴺ / √m` for `z = α + c √m i`. -/
theorem pairC_im_eq (α c m : ℚ) (hm : 0 < m) (N : ℕ) :
    ((((α : ℝ) : ℂ) + (CharRoot.width c m : ℂ) * I) ^ N).im / Real.sqrt (m : ℝ) =
      ((c * (quadUV α (-(c ^ 2 * m)) N).2 : ℚ) : ℝ) := by
  have hs : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Rat.cast_pos.mpr hm)).ne'
  rw [pairC_eq α c m hm.le N, div_eq_iff hs]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, CharRoot.width]
  push_cast
  ring

/-! ## Recurrences split by `RootSplit` -/

/-- The roots of the product `a` of the exact factors and `R` are nonzero when `a₀ ≠ 0`. -/
theorem combined_ne_zero (rs : List (CharRoot × ℕ)) (hv : ∀ e ∈ rs, e.1.Valid)
    (hpos : ∀ e ∈ rs, 0 < e.2) (R : List ℚ) (D : Enclosures) (hD : D.check R = true)
    (a : List ℚ) (ha : coeffMul (charList rs) R = a) (h : a.getD 0 0 ≠ 0) :
    ∀ μ ∈ rrAll (combined rs R D), μ ≠ 0 := by
  intro μ hμ hzero
  have hev := (eval_eq_zero_iff_combined rs hv hpos R D hD a ha μ).mpr hμ
  rw [hzero] at hev
  cases a with
  | nil => exact h rfl
  | cons c cs =>
    simp only [polyC_cons, eval_add, eval_C, eval_mul, eval_X, zero_mul, add_zero,
      Rat.cast_eq_zero] at hev
    exact h hev

/-- The general solution of `∑ₖ aₖ y (n + k) = F n` when `RootSplit` splits `a` into the exact
roots `rs` and the roots of `R` enclosed by `D`: `y - Yp` is a real combination of
`seqBasis (combined rs R D)`. -/
theorem rec_general (rs : List (CharRoot × ℕ)) (hv : ∀ e ∈ rs, e.1.Valid) {p : ℕ}
    (hsep : separated rs p = true) (hpos : ∀ e ∈ rs, 0 < e.2) (R : List ℚ) (D : Enclosures)
    (hD : D.check R = true) (U V : List ℚ)
    (hb : coeffEq (coeffAdd (coeffMul U (charList rs)) (coeffMul V R)) [1] = true) (a : List ℚ)
    (hA : coeffMul (charList rs) R = a) {d : ℕ} (hlen : degQ rs + (R.length - 1) = d)
    (ha0 : a.getD 0 0 ≠ 0) {Yp F : ℕ → ℝ}
    (hpart : ∀ n, sLop d (fun k ↦ (a.getD k 0 : ℝ)) Yp n = F n) {y : ℕ → ℝ} :
    (∀ n, sLop d (fun k ↦ (a.getD k 0 : ℝ)) y n = F n) ↔
      (fun n ↦ y n - Yp n) ∈ span ℝ {f | f ∈ seqBasis (combined rs R D)} :=
  rec_general_iff (combined rs R D) (nodup_combined rs hv hsep hpos R D hD U V hb)
    (combined_ne_zero rs hv hpos R D hD a hA ha0) a (charC_combined rs hv R D hD a hA)
    ((length_rrList_combined rs R D hD).trans hlen) hpart

/-- The initial-value problem when `RootSplit` splits the monic `a`: a sequence satisfies the
recurrence and takes the values `v k` at `k₀ + k` for `k < d` exactly when it is
`Y = Yp + E + encSeq R D G`, for a particular solution `Yp`, a combination `E` of the exact
solutions and the polynomial `G` over the enclosed roots, with these values. -/
theorem rec_ivp (rs : List (CharRoot × ℕ)) (hv : ∀ e ∈ rs, e.1.Valid) {p : ℕ}
    (hsep : separated rs p = true) (hpos : ∀ e ∈ rs, 0 < e.2) (R : List ℚ) (D : Enclosures)
    (hD : D.check R = true) (U V : List ℚ)
    (hb : coeffEq (coeffAdd (coeffMul U (charList rs)) (coeffMul V R)) [1] = true) (a : List ℚ)
    (hA : coeffMul (charList rs) R = a) {d : ℕ} (hlen : degQ rs + (R.length - 1) = d)
    (ha : a.getD d 0 = 1) (ha0 : a.getD 0 0 ≠ 0) {Yp F : ℕ → ℝ}
    (hpart : ∀ n, sLop d (fun k ↦ (a.getD k 0 : ℝ)) Yp n = F n) (G : List ℚ) {E : ℕ → ℝ}
    (hE : E ∈ span ℝ {f | f ∈ seqBasis (rs.map fun e ↦ (RRoot.char e.1, e.2))})
    (k₀ : ℕ) (v : ℕ → ℝ)
    (hval : ∀ k < d, Yp (k₀ + k) + E (k₀ + k) + encSeq R D G (k₀ + k) = v k)
    {Y : ℕ → ℝ} (hY : ∀ n, Yp n + E n + encSeq R D G n = Y n) {y : ℕ → ℝ} :
    ((∀ n, sLop d (fun k ↦ (a.getD k 0 : ℝ)) y n = F n) ∧ ∀ k < d, y (k₀ + k) = v k) ↔
      ∀ n, y n = Y n := by
  have h₁ : span ℝ {f | f ∈ seqBasis (rs.map fun e ↦ (RRoot.char e.1, e.2))} ≤
      span ℝ {f | f ∈ seqBasis (combined rs R D)} := by
    apply span_mono
    intro f hf
    rw [Set.mem_ofPred_eq, combined, seqBasis_append, List.mem_append]
    exact Or.inl hf
  have h₂ : span ℝ {f | f ∈ seqBasis (D.rroots R)} ≤
      span ℝ {f | f ∈ seqBasis (combined rs R D)} := by
    apply span_mono
    intro f hf
    rw [Set.mem_ofPred_eq, combined, seqBasis_append, List.mem_append]
    exact Or.inr hf
  have hfun : (fun n ↦ (Yp n + E n + encSeq R D G n) - Yp n) = E + encSeq R D G := by
    funext n
    simp only [Pi.add_apply]
    ring
  have hmem : (fun n ↦ (Yp n + E n + encSeq R D G n) - Yp n) ∈
      span ℝ {f | f ∈ seqBasis (combined rs R D)} := by
    rw [hfun]
    exact add_mem (h₁ hE) (h₂ (encSeq_mem R D G))
  have hYrec : ∀ n, sLop d (fun k ↦ (a.getD k 0 : ℝ)) Y n = F n := by
    rw [show Y = fun n ↦ Yp n + E n + encSeq R D G n from funext fun n ↦ (hY n).symm]
    exact (rec_general rs hv hsep hpos R D hD U V hb a hA hlen ha0 hpart).mpr hmem
  have ha' : ((a.getD d 0 : ℚ) : ℝ) = 1 := by rw [ha, Rat.cast_one]
  exact rec_ivp_iff (a := fun k ↦ ((a.getD k 0 : ℚ) : ℝ)) ha' (Rat.cast_ne_zero.mpr ha0) hYrec
    k₀ v fun k hk ↦ (hY (k₀ + k)).symm.trans (hval k hk)

end CAS.LinearRecurrence

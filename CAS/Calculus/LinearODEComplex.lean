/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Linear equations with constant complex coefficients

For a list of complex numbers `μ₁, …, μₙ` (repetitions allowed), the operator
`(D - μₙ) ⋯ (D - μ₁)` acting on complex functions of a real variable has as kernel, among the
`Cⁿ` functions, exactly the complex span of `x ^ j e ^ (μ x)` with `j` below the multiplicity of
`μ` (`pOp_eq_zero_iff`). The operator is `∑ aₖ f⁽ᵏ⁾` with the coefficients of `∏ (X - μᵢ)`
(`pOp_eq_cLop`).

## Main definitions

* `cMono`: the exponential monomial `x ^ j e ^ (μ x)`.
* `pOp`: the factored operator `(D - μₙ) ⋯ (D - μ₁)`, the first root applied first.
* `rootBasis`: the exponential monomials of a list of roots, with multiplicities.
* `charC`: the coefficients of `∏ (X - μᵢ)`.

## Main results

* `pOp_eq_zero_iff`: a `Cⁿ` function is killed by `pOp` if and only if it lies in the complex
  span of `rootBasis`.
* `pOp_eq_cLop`: `pOp` agrees with `∑ aₖ f⁽ᵏ⁾` for the coefficients `charC` of `∏ (X - μᵢ)`.

## Implementation notes

We peel off one factor at a time. `D - μ` maps the span for `μ :: rest` onto the span for
`rest`: `exists_cOp_preimage` builds a preimage of each monomial (by induction on its power
when its root differs from `μ`), and `cOp_mem_span` gives the other inclusion. The kernel of
`D - μ` itself is `ℂ e ^ (μ x)` (`eq_of_cOp_eq_zero`), from the integrating factor
`e ^ (-μ x)`. Induction on the list then proves `pOp_eq_zero_iff`. Teschl proves the same basis
through the Jordan form of the companion matrix of the equation; the induction needs no matrix,
only spans and one derivative at a time. The real theorems `rLop_eq_zero_iff` (exact roots) and
`rLop_eq_zero_iff_rr` (roots given by real data, such as enclosed roots) apply it to `ofReal ∘ y`.

## References

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, Graduate Studies in
  Mathematics 140, American Mathematical Society, Providence, 2012,
  <https://doi.org/10.1090/gsm/140>. Theorem 3.7 (§3.3) states the basis `tᵏ exp(αⱼ t)`; we read
  it in the author's online version, <https://www.mat.univie.ac.at/~gerald/ftp/book-ode/>.
-/

@[expose] public section

namespace CAS.LinearODE

open Finset Submodule
open scoped ContDiff

/-! ## Exponential monomials -/

/-- `x ^ j e ^ (μ x)`. -/
noncomputable def cMono (μ : ℂ) (j : ℕ) (x : ℝ) : ℂ := (x : ℂ) ^ j * Complex.exp (μ * x)

/-- At every real `x`, `cMono μ j` has derivative `j * cMono μ (j - 1) x + μ * cMono μ j x`. -/
theorem hasDerivAt_cMono (μ : ℂ) (j : ℕ) (x : ℝ) :
    HasDerivAt (cMono μ j) (j * cMono μ (j - 1) x + μ * cMono μ j x) x := by
  have hx : HasDerivAt (fun x : ℝ ↦ (x : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  refine ((hx.fun_pow j).mul (hx.const_mul μ).cexp).congr_deriv ?_
  simp only [cMono]
  ring

/-- The derivative of `cMono μ j` is `x ↦ j * cMono μ (j - 1) x + μ * cMono μ j x`. -/
theorem deriv_cMono (μ : ℂ) (j : ℕ) :
    deriv (cMono μ j) = fun x ↦ j * cMono μ (j - 1) x + μ * cMono μ j x :=
  funext fun x ↦ (hasDerivAt_cMono μ j x).deriv

/-- `cMono μ j` is smooth as a function of the real variable. -/
theorem contDiff_cMono (μ : ℂ) (j : ℕ) : ContDiff ℝ ∞ (cMono μ j) :=
  (Complex.ofRealCLM.contDiff.pow j).mul (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

/-! ## The operators `D - μ` -/

/-- `D - μ`. -/
noncomputable def cOp (μ : ℂ) (f : ℝ → ℂ) : ℝ → ℂ := fun x ↦ deriv f x - μ * f x

/-- `(D - μₙ) ⋯ (D - μ₁)`, the first root applied first. -/
noncomputable def pOp : List ℂ → (ℝ → ℂ) → ℝ → ℂ
  | [], f => f
  | μ :: rest, f => pOp rest (cOp μ f)

/-- For differentiable `f` and `g`, `cOp μ (f + g) = cOp μ f + cOp μ g`. -/
theorem cOp_add (μ : ℂ) {f g : ℝ → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    cOp μ (f + g) = cOp μ f + cOp μ g := by
  funext x
  simp only [cOp, Pi.add_apply, deriv_add (hf x) (hg x)]
  ring

/-- For differentiable `f` and `g`, `cOp μ (f - g) = cOp μ f - cOp μ g`. -/
theorem cOp_sub (μ : ℂ) {f g : ℝ → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    cOp μ (f - g) = cOp μ f - cOp μ g := by
  funext x
  simp only [cOp, Pi.sub_apply, deriv_sub (hf x) (hg x)]
  ring

/-- For differentiable `f` and a complex constant `c`, `cOp μ (c • f) = c • cOp μ f`. -/
theorem cOp_smul (μ c : ℂ) {f : ℝ → ℂ} (hf : Differentiable ℝ f) :
    cOp μ (c • f) = c • cOp μ f := by
  funext x
  simp only [cOp, Pi.smul_apply, smul_eq_mul, deriv_const_smul c (hf x)]
  ring

/-- `D - μ` maps the zero function to zero. -/
theorem cOp_zero (μ : ℂ) : cOp μ 0 = 0 :=
  funext fun x ↦ by simp [cOp]

/-- If `f` is `Cⁿ⁺¹`, then `cOp μ f` is `Cⁿ`. -/
theorem contDiff_cOp_of_succ (μ : ℂ) {n : ℕ} {f : ℝ → ℂ} (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (cOp μ f) :=
  (contDiff_succ_iff_deriv.mp hf).2.2.sub
    (contDiff_const.mul (hf.of_le (by exact_mod_cast Nat.le_succ n)))

/-- `D - μ` applied to `cMono ν j` is `x ↦ j * cMono ν (j - 1) x + (ν - μ) * cMono ν j x`. -/
theorem cOp_cMono (μ ν : ℂ) (j : ℕ) :
    cOp μ (cMono ν j) = fun x ↦ j * cMono ν (j - 1) x + (ν - μ) * cMono ν j x := by
  funext x
  simp only [cOp, deriv_cMono]
  ring

/-! ## The span of the exponential monomials -/

/-- The functions `x ^ j e ^ (μ x)` with `j` below the multiplicity of `μ` in the list. -/
def rootBasis (ls : List ℂ) : Set (ℝ → ℂ) := {f | ∃ μ j, j < ls.count μ ∧ f = cMono μ j}

/-- Every function in the complex span of `rootBasis ls` is smooth. -/
theorem contDiff_of_mem_span {ls : List ℂ} {f : ℝ → ℂ} (hf : f ∈ span ℂ (rootBasis ls)) :
    ContDiff ℝ ∞ f :=
  span_induction (fun _ ⟨μ, j, _, h⟩ ↦ h ▸ contDiff_cMono μ j) contDiff_const
    (fun _ _ _ _ ↦ .add) (fun _ _ _ ↦ contDiff_const.smul) hf

/-- For `j` below the multiplicity `ls.count μ`, `cMono μ j` lies in the complex span of
`rootBasis ls`. -/
theorem cMono_mem_span {ls : List ℂ} {μ : ℂ} {j : ℕ} (h : j < ls.count μ) :
    cMono μ j ∈ span ℂ (rootBasis ls) :=
  subset_span ⟨μ, j, h, rfl⟩

/-- The kernel of `D - μ`. -/
theorem eq_of_cOp_eq_zero {μ : ℂ} {f : ℝ → ℂ} (hf : Differentiable ℝ f) (h : cOp μ f = 0) :
    f = f 0 • cMono μ 0 := by
  have hg (x : ℝ) : HasDerivAt (fun x ↦ cMono (-μ) 0 x * f x) 0 x := by
    refine ((hasDerivAt_cMono (-μ) 0 x).mul (hf x).hasDerivAt).congr_deriv ?_
    rw [sub_eq_zero.mp (congrFun h x)]
    ring
  funext x
  have := is_const_of_deriv_eq_zero (fun x ↦ (hg x).differentiableAt) (fun x ↦ (hg x).deriv) x 0
  simp only [cMono, pow_zero, one_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero] at this
  simp [cMono, ← this, mul_right_comm _ (f x), ← Complex.exp_add]

/-- `D - μ` maps the span for `μ :: rest` onto the span for `rest`. -/
theorem exists_cOp_preimage (μ : ℂ) (rest : List ℂ) {g : ℝ → ℂ}
    (hg : g ∈ span ℂ (rootBasis rest)) :
    ∃ χ ∈ span ℂ (rootBasis (μ :: rest)), cOp μ χ = g := by
  have hD {f} (hf : f ∈ span ℂ (rootBasis (μ :: rest))) : Differentiable ℝ f :=
    (contDiff_of_mem_span hf).differentiable (by simp)
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨ν, J, hJ, rfl⟩ := hg
    have hd j : Differentiable ℝ (cMono ν j) := (contDiff_cMono ν j).differentiable (by simp)
    by_cases hν : ν = μ
    · subst hν
      refine ⟨((J + 1 : ℕ) : ℂ)⁻¹ • cMono ν (J + 1), smul_mem _ _ (cMono_mem_span ?_), ?_⟩
      · simpa using hJ
      rw [cOp_smul _ _ (hd _), cOp_cMono]
      funext x
      simp [Nat.cast_add_one_ne_zero]
    have hνμ : ν - μ ≠ 0 := sub_ne_zero.mpr hν
    rw [← List.count_cons_of_ne (l := rest) (Ne.symm hν)] at hJ
    induction J with
    | zero =>
      refine ⟨(ν - μ)⁻¹ • cMono ν 0, smul_mem _ _ (cMono_mem_span hJ), ?_⟩
      rw [cOp_smul _ _ (hd 0), cOp_cMono]
      funext x
      simp [hνμ]
    | succ j ih =>
      obtain ⟨χ, hχ, hχeq⟩ := ih (by omega)
      refine ⟨(ν - μ)⁻¹ • (cMono ν (j + 1) - ((j + 1 : ℕ) : ℂ) • χ),
        smul_mem _ _ (sub_mem (cMono_mem_span hJ) (smul_mem _ _ hχ)), ?_⟩
      rw [cOp_smul _ _ ((hd _).sub ((hD hχ).const_smul _)),
        cOp_sub _ (hd _) ((hD hχ).const_smul _), cOp_smul _ _ (hD hχ), hχeq, cOp_cMono]
      funext x
      simp [hνμ]
  | zero => exact ⟨0, zero_mem _, cOp_zero μ⟩
  | add g h _ _ hg hh =>
    obtain ⟨χ₁, h₁, rfl⟩ := hg
    obtain ⟨χ₂, h₂, rfl⟩ := hh
    exact ⟨χ₁ + χ₂, add_mem h₁ h₂, cOp_add μ (hD h₁) (hD h₂)⟩
  | smul c g _ hg =>
    obtain ⟨χ, hχ, rfl⟩ := hg
    exact ⟨c • χ, smul_mem _ _ hχ, cOp_smul μ c (hD hχ)⟩

/-- `D - μ` maps the span for `μ :: rest` into the span for `rest`. -/
theorem cOp_mem_span (μ : ℂ) (rest : List ℂ) {f : ℝ → ℂ}
    (hf : f ∈ span ℂ (rootBasis (μ :: rest))) : cOp μ f ∈ span ℂ (rootBasis rest) := by
  have hD {f} (hf : f ∈ span ℂ (rootBasis (μ :: rest))) : Differentiable ℝ f :=
    (contDiff_of_mem_span hf).differentiable (by simp)
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨ν, j, hj, rfl⟩ := hg
    rw [cOp_cMono]
    refine add_mem ?_ ?_
    · rcases j with _ | j
      · simp [← Pi.zero_def]
      · exact smul_mem _ _ (cMono_mem_span (by grind))
    · by_cases hν : ν = μ
      · simp [hν, ← Pi.zero_def]
      · exact smul_mem _ _ (cMono_mem_span (by simpa [Ne.symm hν] using hj))
  | zero => simp [cOp_zero]
  | add g h hgs hhs hg hh => exact cOp_add μ (hD hgs) (hD hhs) ▸ add_mem hg hh
  | smul c g hgs hg => exact cOp_smul μ c (hD hgs) ▸ smul_mem _ c hg

/-- The kernel of `(D - μₙ) ⋯ (D - μ₁)` among `Cⁿ` functions. -/
theorem pOp_eq_zero_iff : ∀ (ls : List ℂ) {f : ℝ → ℂ}, ContDiff ℝ ls.length f →
    (pOp ls f = 0 ↔ f ∈ span ℂ (rootBasis ls))
  | [], f, _ => by simp [pOp, rootBasis]
  | μ :: rest, f, hf => by
    have hd : Differentiable ℝ f := hf.differentiable (by simp)
    rw [pOp, pOp_eq_zero_iff rest (contDiff_cOp_of_succ μ hf)]
    refine ⟨fun h ↦ ?_, cOp_mem_span μ rest⟩
    obtain ⟨χ, hχ, hχeq⟩ := exists_cOp_preimage μ rest h
    have hχd := (contDiff_of_mem_span hχ).differentiable (by simp)
    have hk := eq_of_cOp_eq_zero (hd.sub hχd) (by rw [cOp_sub μ hd hχd, hχeq, sub_self])
    rw [← sub_add_cancel f χ, hk]
    exact add_mem (smul_mem _ _ (cMono_mem_span (by simp))) hχ

/-! ## Coefficients -/

/-- `∑ₖ₌₀ⁿ aₖ f⁽ᵏ⁾`. -/
noncomputable def cLop (n : ℕ) (a : ℕ → ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), a k * iteratedDeriv k f x

/-- The coefficients of `(X - μ) q`. -/
def mulRoot (μ : ℂ) (q : ℕ → ℂ) : ℕ → ℂ
  | 0 => -μ * q 0
  | k + 1 => q k - μ * q (k + 1)

/-- The coefficients of `∏ (X - μᵢ)`. -/
noncomputable def charC : List ℂ → ℕ → ℂ
  | [] => fun k ↦ if k = 0 then 1 else 0
  | μ :: rest => mulRoot μ (charC rest)

/-- The coefficients of `∏ (X - μᵢ)` vanish above the degree: `charC ls k = 0` when
`ls.length < k`. -/
theorem charC_eq_zero : ∀ (ls : List ℂ) {k : ℕ}, ls.length < k → charC ls k = 0
  | [], _, hk => ite_eq_right (Nat.pos_iff_ne_zero.mp hk)
  | _ :: _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | _ :: rest, k + 1, hk => by
    have hk : rest.length < k := Nat.lt_of_succ_lt_succ hk
    simp [charC, mulRoot, charC_eq_zero rest hk, charC_eq_zero rest (Nat.lt_succ_of_lt hk)]

/-- For `f` of class `Cⁿ⁺¹` and `k ≤ n`, the `k`-th derivative of `cOp μ f` at `x` is
`iteratedDeriv (k + 1) f x - μ * iteratedDeriv k f x`. -/
theorem iteratedDeriv_cOp (μ : ℂ) {n : ℕ} {f : ℝ → ℂ} (hf : ContDiff ℝ (n + 1) f) {k : ℕ}
    (hk : k ≤ n) (x : ℝ) :
    iteratedDeriv k (cOp μ f) x = iteratedDeriv (k + 1) f x - μ * iteratedDeriv k f x := by
  have h1 : ContDiffAt ℝ k (deriv f) x :=
    ((contDiff_succ_iff_deriv.mp hf).2.2.of_le (by exact_mod_cast hk)).contDiffAt
  have h2 : ContDiffAt ℝ k (fun x ↦ μ * f x) x :=
    ((contDiff_const.mul hf).of_le (by exact_mod_cast (hk.trans (Nat.le_succ n)))).contDiffAt
  unfold cOp
  rw [iteratedDeriv_fun_sub h1 h2, iteratedDeriv_const_mul_field, iteratedDeriv_succ']

/-- `(D - μₙ) ⋯ (D - μ₁) f = ∑ cₖ f⁽ᵏ⁾` with the coefficients of `∏ (X - μᵢ)`. -/
theorem pOp_eq_cLop : ∀ (ls : List ℂ) {f : ℝ → ℂ}, ContDiff ℝ ls.length f →
    ∀ x, pOp ls f x = cLop ls.length (charC ls) f x
  | [], f, _, x => by simp [pOp, cLop, charC]
  | μ :: rest, f, hf, x => by
    rw [pOp, pOp_eq_cLop rest (contDiff_cOp_of_succ μ hf) x]
    simp only [cLop, List.length_cons, charC]
    have hterm : ∀ k ∈ range (rest.length + 1), charC rest k * iteratedDeriv k (cOp μ f) x =
        charC rest k * iteratedDeriv (k + 1) f x - μ * (charC rest k * iteratedDeriv k f x) :=
      fun k hk ↦ by rw [iteratedDeriv_cOp μ hf (Nat.lt_succ_iff.mp (mem_range.mp hk))]; ring
    have hs := sum_range_sub (fun k ↦ charC rest k * iteratedDeriv k f x) (rest.length + 1)
    rw [charC_eq_zero rest (lt_add_one _), zero_mul] at hs
    rw [sum_congr rfl hterm, sum_range_succ' _ (rest.length + 1)]
    simp only [mulRoot, sub_mul, mul_assoc, sum_sub_distrib, ← mul_sum] at hs ⊢
    linear_combination μ * hs

end CAS.LinearODE

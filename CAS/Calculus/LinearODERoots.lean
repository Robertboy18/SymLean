/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.LinearODEOrder
public import CAS.Calculus.AlgebraicRoots
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Data.List.GetD

/-!
# Linear equations whose characteristic roots are algebraic numbers

`LinearODE.general_iff` needs the characteristic polynomial factored over `ℚ` into linear
factors and quadratics. `general_iff_rr` is `general_iff` for roots given by real data
(`RRoot`), so the characteristic polynomial may also have a squarefree factor `R` without such a
factorization: its roots are named by certified enclosures (`AlgRoot.real`, `AlgRoot.complex`)
and joined to the exact ones by `combined`. Sums over the enclosed roots get rational forms
(`Enclosures.sum_mul_pow`, `Enclosures.partial_fraction`).

## Main definitions

* `RRoot`: a factor of `LinearODE.CharRoot`, a real root `r`, or a pair `α ± i β` of complex
  roots, with `α` and `β` real.
* `Enclosures`: intervals around the real roots of `R` and discs around one root of each
  conjugate pair.
* `Enclosures.check`: the decidable test of the enclosures.
* `combined`: the roots of `(∏ ρᵏ) · R`.

## Main results

* `general_iff_rr`: the general solution of `∑ aₖ y⁽ᵏ⁾ = F` for distinct roots with real data,
  with the coefficients of `∏ (X - μ)` given by a hypothesis.
* `Enclosures.prod_eq`: when `Enclosures.check` holds, the enclosed roots are all the roots of
  `R`: `∏ (X - μ) = R`.
* `charC_combined`, `nodup_combined`, `eval_eq_zero_iff_combined`: the coefficients, the
  distinctness and the completeness of the roots of `(∏ ρᵏ) · R`.
* `Enclosures.sum_mul_pow`: `∑ G(μ) μʲ` over the enclosed roots is a coefficient of the
  remainder of `G R' Xʲ` by `R`.
* `Enclosures.partial_fraction`: when `Enclosures.check` holds, `B` has fewer coefficients than
  `R` and `W R' ≡ B` modulo `R`, then `B(s) / R(s) = ∑ W(μ) / (s - μ)` wherever `R(s) ≠ 0`.

## Implementation notes

Untrusted code proposes the enclosures, the Bézout cofactors and the remainders; the kernel
checks them over `ℚ`. `Enclosures.check` asks that the intervals be ordered and change sign,
that the discs pass `AlgRoot.cCheck`, lie in the upper half plane and be disjoint, and that
there be as many roots as the degree of the monic `R`. Distinct roots in that number are all
the roots (`Enclosures.prod_eq`, through `prod_eq_polyC`). A Bézout identity
`U ∏ ρᵏ + V R = 1` separates them from the exact roots (`nodup_combined`).

The enclosed roots are not rational, so we turn sums over them into rational data by
Lagrange interpolation at the roots (`sum_div_derivative`, through Mathlib's `Lagrange.nodal`):
`∑ P(μ) / R'(μ)` is the coefficient of `X ^ (e - 1)` in `P` when `deg P < e`, the number of
roots. With the remainder `Q` of `G R' Xʲ` by `R`, checked by `coeffEq`, this gives
`Enclosures.sum_mul_pow`. The linear recurrences take their initial values from it, and the
inverse Laplace transforms take their terms from `Enclosures.partial_fraction`.

## References

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, Graduate Studies in
  Mathematics 140, American Mathematical Society, Providence, 2012,
  <https://doi.org/10.1090/gsm/140>. §3.3, Theorem 3.7 and (3.55), for the basis of solutions;
  we read them in the author's online version,
  <https://www.mat.univie.ac.at/~gerald/ftp/book-ode/>.
-/

@[expose] public section

namespace CAS.LinearODE

open Finset Submodule Complex _root_.Polynomial
open CAS.AlgRoot
open CAS.Polynomial (coeffEval coeffEvalRat coeffAdd coeffMul coeffDeriv coeffEq)
open scoped ContDiff

/-! ## Roots with real data -/

/-- A factor of `CharRoot`, a real root `r`, or a pair of complex roots `α ± i β`. -/
inductive RRoot
  /-- A factor `ρ` of `CharRoot`, with its roots in closed form. -/
  | char (ρ : CharRoot)
  /-- A real root `r`. -/
  | real (r : ℝ)
  /-- The pair of complex roots `α ± i β`. -/
  | pair (α β : ℝ)

namespace RRoot

/-- The roots, as complex numbers. -/
noncomputable def roots : RRoot → List ℂ
  | char ρ => ρ.roots
  | real r => [(r : ℂ)]
  | pair α β => [(α : ℂ) + (β : ℂ) * I, (α : ℂ) - (β : ℂ) * I]

/-- The real solutions `xʲ e ^ (r x)`, `xʲ e ^ (α x) cos (β x)`, `xʲ e ^ (α x) sin (β x)`. -/
noncomputable def funs : RRoot → ℕ → List (ℝ → ℝ)
  | char ρ, j => ρ.funs j
  | real r, j => [fun x ↦ x ^ j * Real.exp (r * x)]
  | pair α β, j => [fun x ↦ x ^ j * Real.exp (α * x) * Real.cos (β * x),
      fun x ↦ x ^ j * Real.exp (α * x) * Real.sin (β * x)]

end RRoot

/-- The roots with repetitions. -/
noncomputable def rrList : List (RRoot × ℕ) → List ℂ
  | [] => []
  | (ρ, k) :: rest => (List.replicate k ρ.roots).flatten ++ rrList rest

/-- The roots without repetitions. -/
noncomputable def rrAll (rs : List (RRoot × ℕ)) : List ℂ := rs.flatMap (·.1.roots)

/-- The real solutions, factor by factor and power by power. -/
noncomputable def rrBasis : List (RRoot × ℕ) → List (ℝ → ℝ)
  | [] => []
  | (ρ, k) :: rest => (List.range k).flatMap ρ.funs ++ rrBasis rest

/-- `f` lies in `rrBasis rs` exactly when `f ∈ ρ.funs j` for some factor `(ρ, k)` of `rs` and some
`j < k`. -/
theorem mem_rrBasis {f : ℝ → ℝ} :
    ∀ {rs : List (RRoot × ℕ)}, f ∈ rrBasis rs ↔ ∃ e ∈ rs, ∃ j < e.2, f ∈ e.1.funs j
  | [] => by simp [rrBasis]
  | (ρ, k) :: rest => by
    simp only [rrBasis, List.mem_append, List.mem_flatMap, List.mem_range, mem_rrBasis,
      List.mem_cons, exists_eq_or_imp]

/-- Every entry of `rrList rs` is a root of some factor of `rs`. -/
theorem mem_of_mem_rrList {μ : ℂ} :
    ∀ {rs : List (RRoot × ℕ)}, μ ∈ rrList rs → ∃ e ∈ rs, μ ∈ e.1.roots
  | [], h => by simp [rrList] at h
  | (ρ, k) :: rest, h => by
    simp only [rrList, List.mem_append, List.mem_flatten, List.mem_replicate] at h
    rcases h with ⟨R, ⟨-, rfl⟩, hR⟩ | h
    · exact ⟨(ρ, k), by simp, hR⟩
    · obtain ⟨e, he, hμ⟩ := mem_of_mem_rrList h
      exact ⟨e, by simp [he], hμ⟩

/-- A complex number outside `rrAll rs` occurs `0` times in `rrList rs`. -/
theorem count_rrList_eq_zero {μ : ℂ} {rs : List (RRoot × ℕ)} (h : μ ∉ rrAll rs) :
    (rrList rs).count μ = 0 := by
  rw [List.count_eq_zero]
  intro hμ
  obtain ⟨e, he, hμe⟩ := mem_of_mem_rrList hμ
  exact h (List.mem_flatMap.mpr ⟨e, he, hμe⟩)

/-- If the roots `rrAll rs` are pairwise distinct, a root `μ` of a factor `(ρ, k)` of `rs` occurs
exactly `k` times in `rrList rs`. -/
theorem count_rrList_of_mem {μ : ℂ} :
    ∀ {rs : List (RRoot × ℕ)}, (rrAll rs).Nodup → ∀ {ρ : RRoot} {k : ℕ},
      (ρ, k) ∈ rs → μ ∈ ρ.roots → (rrList rs).count μ = k
  | [], _, _, _, hm, _ => by simp at hm
  | (ρ', k') :: rest, hnd, ρ, k, hm, hμ => by
    simp only [rrAll, List.flatMap_cons, List.nodup_append] at hnd
    obtain ⟨hnd₁, hnd₂, hdisj⟩ := hnd
    simp only [rrList, List.count_append, count_flatten_replicate]
    rcases List.mem_cons.mp hm with he | hm'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rw [List.count_eq_one_of_mem hnd₁ hμ, count_rrList_eq_zero fun hμ' ↦ hdisj μ hμ μ hμ' rfl]
      ring
    · have h0 : ρ'.roots.count μ = 0 := List.count_eq_zero.mpr fun hμ' ↦
        hdisj μ hμ' μ (List.mem_flatMap.mpr ⟨(ρ, k), hm', hμ⟩) rfl
      rw [h0, count_rrList_of_mem hnd₂ hm' hμ]
      ring

/-- A root `μ` of a factor `(ρ, k)` of `rs` occurs at least `k` times in `rrList rs`, for every
`rs`, distinct roots or not. -/
theorem le_count_rrList {μ : ℂ} :
    ∀ {rs : List (RRoot × ℕ)} {ρ : RRoot} {k : ℕ}, (ρ, k) ∈ rs → μ ∈ ρ.roots →
      k ≤ (rrList rs).count μ
  | [], _, _, hm, _ => by simp at hm
  | (ρ', k') :: rest, ρ, k, hm, hμ => by
    simp only [rrList, List.count_append, count_flatten_replicate]
    rcases List.mem_cons.mp hm with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      have : 0 < ρ.roots.count μ := List.count_pos_iff.mpr hμ
      nlinarith
    · have := le_count_rrList h hμ
      omega

/-- For real `α`, `β` and `x`, `cMono (α + β i) j x` is
`xʲ e^{α x} cos (β x) + i xʲ e^{α x} sin (β x)`, both parts cast from `ℝ`. -/
theorem cMono_pairR_add (α β : ℝ) (j : ℕ) (x : ℝ) :
    cMono ((α : ℂ) + (β : ℂ) * I) j x =
      ((x ^ j * Real.exp (α * x) * Real.cos (β * x) : ℝ) : ℂ) +
        I * ((x ^ j * Real.exp (α * x) * Real.sin (β * x) : ℝ) : ℂ) := by
  unfold cMono
  have : ((α : ℂ) + (β : ℂ) * I) * (x : ℂ) = ((α * x : ℝ) : ℂ) + ((β * x : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [this, Complex.exp_add_mul_I]
  push_cast
  ring

/-- For real `α`, `β` and `x`, `cMono (α - β i) j x` is
`xʲ e^{α x} cos (β x) - i xʲ e^{α x} sin (β x)`, both parts cast from `ℝ`. -/
theorem cMono_pairR_sub (α β : ℝ) (j : ℕ) (x : ℝ) :
    cMono ((α : ℂ) - (β : ℂ) * I) j x =
      ((x ^ j * Real.exp (α * x) * Real.cos (β * x) : ℝ) : ℂ) -
        I * ((x ^ j * Real.exp (α * x) * Real.sin (β * x) : ℝ) : ℂ) := by
  unfold cMono
  have : ((α : ℂ) - (β : ℂ) * I) * (x : ℂ) =
      ((α * x : ℝ) : ℂ) + ((-(β * x)) : ℝ) * I := by
    push_cast
    ring
  rw [this, Complex.exp_add_mul_I]
  push_cast
  simp only [Complex.cos_neg, Complex.sin_neg]
  ring

/-- For a root `μ` of `ρ`, the exponential monomial `cMono μ j` is `h₁ + i h₂` with `h₁` and `h₂` in
the real span of `ρ.funs j`. -/
theorem RRoot.cMono_eq_of_mem_roots {ρ : RRoot} {μ : ℂ} (hμ : μ ∈ ρ.roots) (j : ℕ) :
    ∃ h₁ ∈ span ℝ {f | f ∈ ρ.funs j}, ∃ h₂ ∈ span ℝ {f | f ∈ ρ.funs j},
      ∀ x, cMono μ j x = (h₁ x : ℂ) + I * (h₂ x : ℂ) := by
  cases ρ with
  | char ρ => exact LinearODE.cMono_eq_of_mem_roots hμ j
  | real r =>
    obtain rfl := List.mem_singleton.mp hμ
    refine ⟨fun x ↦ x ^ j * Real.exp (r * x), subset_span (by simp [RRoot.funs]), 0,
      zero_mem _, fun x ↦ ?_⟩
    rw [cMono_real]
    simp
  | pair α β =>
    simp only [RRoot.roots, List.mem_cons, List.not_mem_nil, or_false] at hμ
    have hc : (fun x : ℝ ↦ x ^ j * Real.exp (α * x) * Real.cos (β * x)) ∈
        span ℝ {f | f ∈ (RRoot.pair α β).funs j} := subset_span (by simp [RRoot.funs])
    have hs : (fun x : ℝ ↦ x ^ j * Real.exp (α * x) * Real.sin (β * x)) ∈
        span ℝ {f | f ∈ (RRoot.pair α β).funs j} := subset_span (by simp [RRoot.funs])
    rcases hμ with rfl | rfl
    · exact ⟨_, hc, _, hs, fun x ↦ cMono_pairR_add α β j x⟩
    · refine ⟨_, hc, _, neg_mem hs, fun x ↦ ?_⟩
      rw [cMono_pairR_sub]
      simp only [Pi.neg_apply, Complex.ofReal_neg]
      ring

/-- Each real solution `f ∈ ρ.funs j`, cast to `ℂ`, lies in the complex span of the exponential
monomials `cMono μ j` at the roots `μ` of `ρ`. -/
theorem RRoot.ofReal_mem_span_of_mem_funs {ρ : RRoot} {j : ℕ} {f : ℝ → ℝ}
    (hf : f ∈ ρ.funs j) :
    (fun x ↦ (f x : ℂ)) ∈ span ℂ ((fun μ ↦ cMono μ j) '' {μ | μ ∈ ρ.roots}) := by
  have mem : ∀ μ ∈ ρ.roots, cMono μ j ∈ span ℂ ((fun μ ↦ cMono μ j) '' {μ | μ ∈ ρ.roots}) :=
    fun μ hμ ↦ subset_span ⟨μ, hμ, rfl⟩
  cases ρ with
  | char ρ => exact LinearODE.ofReal_mem_span_of_mem_funs hf
  | real r =>
    obtain rfl := List.mem_singleton.mp hf
    convert mem (r : ℂ) (by simp [RRoot.roots]) using 1
    exact funext fun x ↦ (cMono_real _ j x).symm
  | pair α β =>
    simp only [RRoot.funs, List.mem_cons, List.not_mem_nil, or_false] at hf
    have h₁ := mem ((α : ℂ) + (β : ℂ) * I) (by simp [RRoot.roots])
    have h₂ := mem ((α : ℂ) - (β : ℂ) * I) (by simp [RRoot.roots])
    rcases hf with rfl | rfl
    · convert add_mem (smul_mem _ (1 / 2 : ℂ) h₁) (smul_mem _ (1 / 2 : ℂ) h₂) using 1
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cMono_pairR_add, cMono_pairR_sub]
      ring
    · convert add_mem (smul_mem _ (-I / 2) h₁) (smul_mem _ (I / 2) h₂) using 1
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cMono_pairR_add, cMono_pairR_sub]
      ring_nf
      rw [Complex.I_sq]
      ring

/-- The functions of the real basis are smooth. -/
theorem RRoot.contDiff_funs (ρ : RRoot) (j : ℕ) : ∀ f ∈ ρ.funs j, ContDiff ℝ ∞ f := by
  cases ρ with
  | char ρ => exact ρ.contDiff_funs j
  | real r =>
    simp only [RRoot.funs, List.mem_singleton, forall_eq]
    fun_prop
  | pair α β =>
    simp only [RRoot.funs, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true]
    constructor <;> fun_prop

/-- Every function of the real span of the basis is smooth. -/
theorem contDiff_of_mem_span_rrBasis (rs : List (RRoot × ℕ)) {y : ℝ → ℝ}
    (hmem : y ∈ span ℝ {f | f ∈ rrBasis rs}) : ContDiff ℝ ∞ y := by
  induction hmem using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨e, -, j, -, hfe⟩ := mem_rrBasis.mp hf
    exact RRoot.contDiff_funs e.1 j f hfe
  | zero => exact contDiff_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact hf.const_smul c

/-- The leading coefficient of `∏ (X - μ)` is `1`. -/
theorem getD_length_of_charC {rs : List (RRoot × ℕ)} {a : List ℚ}
    (hc : ∀ k, charC (rrList rs) k = (a.getD k 0 : ℂ)) : a.getD (rrList rs).length 0 = 1 := by
  have h := hc (rrList rs).length
  rw [charC_length] at h
  exact_mod_cast h.symm

private theorem rLop_eq_zero_iff_rr_of_contDiff (rs : List (RRoot × ℕ)) (hnd : (rrAll rs).Nodup)
    (a : List ℚ) (hc : ∀ k, charC (rrList rs) k = (a.getD k 0 : ℂ)) {y : ℝ → ℝ}
    (hy : ContDiff ℝ (rrList rs).length y) :
    (∀ x, rLop (rrList rs).length (fun k ↦ (a.getD k 0 : ℝ)) y x = 0) ↔
      y ∈ span ℝ {f | f ∈ rrBasis rs} := by
  set z : ℝ → ℂ := fun x ↦ (y x : ℂ) with hz
  have hzc : ContDiff ℝ (rrList rs).length z := Complex.ofRealCLM.contDiff.comp hy
  have hop : ∀ x, pOp (rrList rs) z x =
      ((rLop (rrList rs).length (fun k ↦ (a.getD k 0 : ℝ)) y x : ℝ) : ℂ) := by
    intro x
    rw [pOp_eq_cLop _ hzc x, cLop, rLop, hz]
    simp only [iteratedDeriv_ofReal_comp]
    push_cast
    exact sum_congr rfl fun k _ ↦ by rw [hc k]
  have step₁ : (∀ x, rLop (rrList rs).length (fun k ↦ (a.getD k 0 : ℝ)) y x = 0) ↔
      z ∈ span ℂ (rootBasis (rrList rs)) := by
    rw [← pOp_eq_zero_iff _ hzc, funext_iff]
    simp only [hop, Pi.zero_apply, Complex.ofReal_eq_zero]
  rw [step₁]
  set S := span ℝ {f | f ∈ rrBasis rs}
  have hsub : ∀ e ∈ rs, ∀ j < e.2, span ℝ {f | f ∈ e.1.funs j} ≤ S := fun e he j hj ↦
    span_mono fun f hf ↦ mem_rrBasis.mpr ⟨e, he, j, hj, hf⟩
  constructor
  · intro hmem
    have key : ∀ g ∈ span ℂ (rootBasis (rrList rs)),
        ∃ h₁ ∈ S, ∃ h₂ ∈ S, ∀ x, g x = (h₁ x : ℂ) + I * (h₂ x : ℂ) := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨μ, j, hj, rfl⟩ := hg
        have hpos : 0 < (rrList rs).count μ := by omega
        obtain ⟨e, he, hμ⟩ := mem_of_mem_rrList (List.count_pos_iff.mp hpos)
        have hk := count_rrList_of_mem hnd he hμ
        obtain ⟨h₁, hh₁, h₂, hh₂, hx⟩ := RRoot.cMono_eq_of_mem_roots hμ j
        exact ⟨h₁, hsub e he j (by omega) hh₁, h₂, hsub e he j (by omega) hh₂, hx⟩
      | zero => exact ⟨0, zero_mem _, 0, zero_mem _, fun x ↦ by simp⟩
      | add g g' _ _ hg hg' =>
        obtain ⟨a₁, ha₁, a₂, ha₂, ha⟩ := hg
        obtain ⟨b₁, hb₁, b₂, hb₂, hb⟩ := hg'
        refine ⟨a₁ + b₁, add_mem ha₁ hb₁, a₂ + b₂, add_mem ha₂ hb₂, fun x ↦ ?_⟩
        simp only [Pi.add_apply, ha, hb, Complex.ofReal_add]
        ring
      | smul c g _ hg =>
        obtain ⟨a₁, ha₁, a₂, ha₂, ha⟩ := hg
        refine ⟨c.re • a₁ - c.im • a₂, sub_mem (smul_mem _ _ ha₁) (smul_mem _ _ ha₂),
          c.im • a₁ + c.re • a₂, add_mem (smul_mem _ _ ha₁) (smul_mem _ _ ha₂), fun x ↦ ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, ha, Pi.sub_apply, Pi.add_apply,
          Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
        linear_combination ((a₁ x : ℂ) + I * a₂ x) * (Complex.re_add_im c).symm +
          (c.im : ℂ) * a₂ x * Complex.I_sq
    obtain ⟨h₁, hh₁, h₂, -, hx⟩ := key z hmem
    rwa [show y = h₁ from funext fun x ↦ by simpa [hz] using congrArg Complex.re (hx x)]
  · intro hmem
    have key : ∀ f ∈ S, (fun x ↦ (f x : ℂ)) ∈ span ℂ (rootBasis (rrList rs)) := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨e, he, j, hj, hfe⟩ := mem_rrBasis.mp hf
        refine span_mono ?_ (RRoot.ofReal_mem_span_of_mem_funs hfe)
        rintro g ⟨μ, hμ, rfl⟩
        exact ⟨μ, j, lt_of_lt_of_le hj (le_count_rrList he hμ), rfl⟩
      | zero =>
        convert zero_mem (span ℂ (rootBasis (rrList rs))) using 1
      | add f g _ _ hf hg =>
        convert add_mem hf hg using 1
        exact funext fun x ↦ by simp
      | smul c f _ hf =>
        convert smul_mem _ (c : ℂ) hf using 1
        exact funext fun x ↦ by simp
    exact key y hmem

/-- The real solutions of `∑ aₖ y⁽ᵏ⁾ = 0` when the `aₖ` are the coefficients of `∏ (X - μ)` over
the roots `rrList rs`, which are distinct up to multiplicity, among the functions whose
derivatives below the order are differentiable. -/
theorem rLop_eq_zero_iff_rr (rs : List (RRoot × ℕ)) (hnd : (rrAll rs).Nodup) (a : List ℚ)
    (hc : ∀ k, charC (rrList rs) k = (a.getD k 0 : ℂ)) {y : ℝ → ℝ}
    (hy : ∀ k < (rrList rs).length, Differentiable ℝ (iteratedDeriv k y)) :
    (∀ x, rLop (rrList rs).length (fun k ↦ (a.getD k 0 : ℝ)) y x = 0) ↔
      y ∈ span ℝ {f | f ∈ rrBasis rs} := by
  refine ⟨fun hL ↦ ?_, fun hmem ↦ ?_⟩
  · exact (rLop_eq_zero_iff_rr_of_contDiff rs hnd a hc (contDiff_of_rLop
      (by exact_mod_cast getD_length_of_charC hc) hy continuous_const hL)).mp hL
  · exact (rLop_eq_zero_iff_rr_of_contDiff rs hnd a hc ((contDiff_of_mem_span_rrBasis rs
      hmem).of_le (by exact_mod_cast le_top))).mpr hmem

/-- The general solution of `∑ aₖ y⁽ᵏ⁾ = F` for roots with real data, with a particular
solution `Yp`, among the functions whose derivatives below the order are differentiable. -/
theorem general_iff_rr (rs : List (RRoot × ℕ)) (hnd : (rrAll rs).Nodup) (a : List ℚ)
    (hc : ∀ k, charC (rrList rs) k = (a.getD k 0 : ℂ)) {n : ℕ} (hn : (rrList rs).length = n)
    {Yp F : ℝ → ℝ} (hYp : ContDiff ℝ n Yp)
    (hpart : ∀ x, rLop n (fun k ↦ (a.getD k 0 : ℝ)) Yp x = F x) {y : ℝ → ℝ}
    (hy : ∀ k < n, Differentiable ℝ (iteratedDeriv k y)) :
    (∀ x, rLop n (fun k ↦ (a.getD k 0 : ℝ)) y x = F x) ↔
      (fun x ↦ y x - Yp x) ∈ span ℝ {f | f ∈ rrBasis rs} := by
  subst hn
  have key (hy' : ContDiff ℝ (rrList rs).length y) :
      (∀ x, rLop (rrList rs).length (fun k ↦ (a.getD k 0 : ℝ)) y x = F x) ↔
        (fun x ↦ y x - Yp x) ∈ span ℝ {f | f ∈ rrBasis rs} := by
    rw [← rLop_eq_zero_iff_rr_of_contDiff rs hnd a hc (hy'.sub hYp)]
    exact forall_congr' fun x ↦ by rw [rLop_sub hy' hYp, hpart, sub_eq_zero]
  refine ⟨fun hL ↦ (key (contDiff_of_rLop (by exact_mod_cast getD_length_of_charC hc) hy
    (funext hpart ▸ continuous_rLop _ hYp) hL)).mp hL, fun hmem ↦ (key ?_).mpr hmem⟩
  simpa using ((contDiff_of_mem_span_rrBasis rs hmem).of_le
    (by exact_mod_cast le_top)).add hYp

/-! ## Enclosures of the roots of a squarefree factor -/

/-- Real roots in intervals `(lo, hi)` and complex roots in discs around `u + v i`, with the
bounds `κ, R, L` of `AlgRoot.cCheck`; one root of each conjugate pair. -/
structure Enclosures where
  /-- Intervals `(lo, hi)` around the real roots, in increasing order. -/
  reals : List (ℚ × ℚ)
  /-- `(u, v, ρ, κ, R, L)`: the disc of radius `ρ` around `u + v i` and the bounds `κ, R, L`
  of `AlgRoot.cCheck`. -/
  discs : List (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ)

namespace Enclosures

/-- The intervals are ordered and disjoint, change sign, the discs lie in the upper half plane,
pass `cCheck` and are disjoint, there are as many roots as the degree, and `R` is monic (its last
coefficient is `1`). -/
def check (R : List ℚ) (D : Enclosures) : Bool :=
  D.reals.all (fun I ↦
      decide (I.1 < I.2) && decide (coeffEvalRat R I.1 * coeffEvalRat R I.2 < 0)) &&
    decide (D.reals.Pairwise fun I J ↦ I.2 ≤ J.1) &&
    D.discs.all (fun d ↦ cCheck R d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2.1 d.2.2.2.2.2 &&
      decide (d.2.2.1 < d.2.1)) &&
    decide (D.discs.Pairwise fun d e ↦
      (d.2.2.1 + e.2.2.1) ^ 2 < (d.1 - e.1) ^ 2 + (d.2.1 - e.2.1) ^ 2) &&
    decide (D.reals.length + 2 * D.discs.length + 1 = R.length) &&
    decide (R.getLast? = some 1)

/-- The roots as `RRoot`s, each of multiplicity one. -/
noncomputable def rroots (R : List ℚ) (D : Enclosures) : List (RRoot × ℕ) :=
  D.reals.map (fun I ↦ (RRoot.real (AlgRoot.real R I.1 I.2), 1)) ++
    D.discs.map fun d ↦ (RRoot.pair (AlgRoot.complex R d.1 d.2.1 d.2.2.1).re
      (AlgRoot.complex R d.1 d.2.1 d.2.2.1).im, 1)

end Enclosures

/-- `rrList (r ++ s) = rrList r ++ rrList s`. -/
theorem rrList_append (r s : List (RRoot × ℕ)) : rrList (r ++ s) = rrList r ++ rrList s := by
  induction r with
  | nil => simp [rrList]
  | cons e r ih =>
    obtain ⟨ρ, k⟩ := e
    simp [rrList, ih]

/-- `rrAll (r ++ s) = rrAll r ++ rrAll s`. -/
theorem rrAll_append (r s : List (RRoot × ℕ)) : rrAll (r ++ s) = rrAll r ++ rrAll s := by
  simp [rrAll]

/-- When every multiplicity in `rs` is `1`, the roots with repetitions `rrList rs` are the roots
`rrAll rs`. -/
theorem rrList_of_one : ∀ rs : List (RRoot × ℕ), (∀ e ∈ rs, e.2 = 1) → rrList rs = rrAll rs
  | [], _ => by simp [rrList, rrAll]
  | (ρ, k) :: rest, h => by
    obtain rfl : k = 1 := h (ρ, k) (by simp)
    simp only [rrList, List.replicate_one, List.flatten_cons, List.flatten_nil, List.append_nil,
      rrAll, List.flatMap_cons]
    rw [rrList_of_one rest fun e he ↦ h e (by simp [he])]
    rfl

/-- Lifting the factors of `rs` to `RRoot.char` keeps the roots with repetitions: their `rrList` is
`cList rs`. -/
theorem rrList_char (rs : List (CharRoot × ℕ)) :
    rrList (rs.map fun e ↦ (RRoot.char e.1, e.2)) = cList rs := by
  induction rs with
  | nil => simp [rrList, cList]
  | cons e rs ih =>
    obtain ⟨ρ, k⟩ := e
    simp [rrList, cList, ih, RRoot.roots]

/-- Lifting the factors of `rs` to `RRoot.char` keeps the roots: their `rrAll` is `allRoots rs`. -/
theorem rrAll_char (rs : List (CharRoot × ℕ)) :
    rrAll (rs.map fun e ↦ (RRoot.char e.1, e.2)) = allRoots rs := by
  simp [rrAll, allRoots, RRoot.roots, List.flatMap_map]

/-- For every `z : ℂ`, the roots of `RRoot.pair z.re z.im` are `[z, conj z]`. -/
theorem pair_roots_eq (z : ℂ) :
    (RRoot.pair z.re z.im).roots = [z, (starRingEnd ℂ) z] := by
  simp only [RRoot.roots, List.cons.injEq, and_true]
  constructor
  · exact Complex.re_add_im z
  · apply Complex.ext <;> simp

/-- The roots of the factors `RRoot.real (f I)` of multiplicity one, for `I` in `l`, are the points
`f I` cast to `ℂ`, in the order of `l`. -/
theorem rrAll_reals (l : List (ℚ × ℚ)) (f : ℚ × ℚ → ℝ) :
    rrAll (l.map fun I ↦ (RRoot.real (f I), 1)) = l.map fun I ↦ (f I : ℂ) := by
  induction l with
  | nil => rfl
  | cons I l ih =>
    simp only [List.map_cons, rrAll, List.flatMap_cons] at ih ⊢
    rw [ih]
    rfl

/-- The roots of the factors `RRoot.pair (g d).re (g d).im` of multiplicity one, for `d` in `l`, are
`g d` and `conj (g d)` for each `d`, in the order of `l`. -/
theorem rrAll_discs {δ : Type*} (l : List δ) (g : δ → ℂ) :
    rrAll (l.map fun d ↦ (RRoot.pair (g d).re (g d).im, 1)) =
      l.flatMap fun d ↦ [g d, (starRingEnd ℂ) (g d)] := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    simp only [List.map_cons, rrAll, List.flatMap_cons] at ih ⊢
    rw [ih, pair_roots_eq]

/-- The roots `rrAll (D.rroots R)` are the points `AlgRoot.real R lo hi` of the intervals of `D`,
cast to `ℂ`, followed by the point `AlgRoot.complex R u v ρ` of each disc and its conjugate. No
check of `D` is assumed. -/
theorem Enclosures.rrAll_eq (R : List ℚ) (D : Enclosures) :
    rrAll (D.rroots R) = D.reals.map (fun I ↦ ((AlgRoot.real R I.1 I.2 : ℝ) : ℂ)) ++
      D.discs.flatMap fun d ↦ [AlgRoot.complex R d.1 d.2.1 d.2.2.1,
        (starRingEnd ℂ) (AlgRoot.complex R d.1 d.2.1 d.2.2.1)] := by
  rw [Enclosures.rroots, rrAll_append, rrAll_reals _ (fun I ↦ AlgRoot.real R I.1 I.2)]
  exact congrArg (_ ++ ·) (rrAll_discs D.discs fun d ↦ AlgRoot.complex R d.1 d.2.1 d.2.2.1)

/-- Points of two discs whose centres are farther apart than the sum of the radii differ. -/
theorem ne_of_discs {u v ρ u' v' ρ' : ℚ} {z w : ℂ}
    (hz : z ∈ Metric.closedBall ((u : ℂ) + (v : ℂ) * I) ρ)
    (hw : w ∈ Metric.closedBall ((u' : ℂ) + (v' : ℂ) * I) ρ')
    (h : (ρ + ρ') ^ 2 < (u - u') ^ 2 + (v - v') ^ 2) : z ≠ w := by
  rintro rfl
  rw [Metric.mem_closedBall] at hz hw
  have hsum := (dist_triangle_left ((u : ℂ) + (v : ℂ) * I) ((u' : ℂ) + (v' : ℂ) * I) z).trans
    (add_le_add hz hw)
  rw [dist_eq_norm] at hsum
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hsum 2
  rw [show ((u : ℂ) + (v : ℂ) * I) - ((u' : ℂ) + (v' : ℂ) * I) =
      ((u - u' : ℚ) : ℂ) + ((v - v' : ℚ) : ℂ) * I by push_cast; ring,
    AlgRoot.norm_sq_gauss] at hsq
  have h' : (((ρ + ρ') ^ 2 : ℚ) : ℝ) < (((u - u') ^ 2 + (v - v') ^ 2 : ℚ) : ℝ) := by
    exact_mod_cast h
  push_cast at hsq h'
  linarith

/-- When `D.check R` holds, the enclosed roots `rrAll (D.rroots R)` are pairwise distinct. -/
theorem Enclosures.nodup (R : List ℚ) (D : Enclosures) (h : D.check R = true) :
    (rrAll (D.rroots R)).Nodup := by
  simp only [Enclosures.check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hreal, hsorted⟩, hdisc⟩, hapart⟩, -⟩, -⟩ := h
  rw [Enclosures.rrAll_eq, List.nodup_iff_pairwise_ne, List.pairwise_append]
  have hr : ∀ I ∈ D.reals, AlgRoot.real R I.1 I.2 ∈ Set.Ioo (I.1 : ℝ) I.2 := fun I hI ↦
    (AlgRoot.real_spec R (hreal I hI).1 (hreal I hI).2).1
  have hz : ∀ d ∈ D.discs, (AlgRoot.complex R d.1 d.2.1 d.2.2.1) ∈
      Metric.closedBall ((d.1 : ℂ) + (d.2.1 : ℂ) * I) d.2.2.1 := fun d hd ↦
    (AlgRoot.complex_spec R (hdisc d hd).1).1
  have him : ∀ d ∈ D.discs, 0 < (AlgRoot.complex R d.1 d.2.1 d.2.2.1).im := fun d hd ↦ by
    have := (AlgRoot.re_mem_of_mem_closedBall (hz d hd)).2.1
    have hlt : (d.2.2.1 : ℝ) < d.2.1 := by exact_mod_cast (hdisc d hd).2
    linarith
  -- The roots of a disc and their conjugates have nonzero imaginary parts.
  have hmem : ∀ x ∈ D.discs.flatMap (fun d ↦ [AlgRoot.complex R d.1 d.2.1 d.2.2.1,
      (starRingEnd ℂ) (AlgRoot.complex R d.1 d.2.1 d.2.2.1)]), x.im ≠ 0 := by
    intro x hx
    obtain ⟨d, hd, hx⟩ := List.mem_flatMap.mp hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp [(him d hd).ne']
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ hsorted
    intro I J hI hJ hIJ heq
    have hIJ' : (I.2 : ℝ) ≤ J.1 := by exact_mod_cast hIJ
    linarith [(hr I hI).2, (hr J hJ).1, Complex.ofReal_injective heq]
  · rw [List.pairwise_flatMap]
    constructor
    · intro d hd
      simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
      intro heq
      linarith [him d hd, (congrArg Complex.im heq).trans (Complex.conj_im _)]
    · refine List.Pairwise.imp_of_mem ?_ hapart
      intro d e hd he hde x hx y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      have hne := ne_of_discs (hz d hd) (hz e he) hde
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact hne
      · intro heq
        linarith [him d hd, him e he, (congrArg Complex.im heq).trans (Complex.conj_im _)]
      · intro heq
        linarith [him d hd, him e he, (Complex.conj_im _).symm.trans (congrArg Complex.im heq)]
      · exact fun heq ↦ hne ((starRingEnd ℂ).injective heq)
  · intro x hx y hy heq
    obtain ⟨I, -, rfl⟩ := List.mem_map.mp hx
    exact hmem y hy (by simp [← heq])

/-- When `D.check R` holds, every enclosed root in `rrAll (D.rroots R)` is a root of `polyC R`. -/
theorem Enclosures.roots_eval (R : List ℚ) (D : Enclosures) (h : D.check R = true) :
    ∀ μ ∈ rrAll (D.rroots R), (polyC R).eval μ = 0 := by
  simp only [Enclosures.check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hreal, -⟩, hdisc⟩, -⟩, -⟩, -⟩ := h
  intro μ hμ
  rw [Enclosures.rrAll_eq, List.mem_append] at hμ
  rcases hμ with hμ | hμ
  · obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hμ
    rw [eval_polyC_ofReal, (AlgRoot.real_spec R (hreal I hI).1 (hreal I hI).2).2]
    simp
  · obtain ⟨d, hd, hμ⟩ := List.mem_flatMap.mp hμ
    have h0 := (AlgRoot.complex_spec R (hdisc d hd).1).2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hμ
    rcases hμ with rfl | rfl
    · exact h0
    · rw [eval_conj_polyC, h0, map_zero]

/-- The enclosed roots are all the roots of `R`: `∏ (X - μ) = R`. -/
theorem Enclosures.prod_eq (R : List ℚ) (D : Enclosures) (h : D.check R = true) :
    ((rrList (D.rroots R)).map fun μ ↦ X - C μ).prod = polyC R := by
  have hone : ∀ e ∈ D.rroots R, e.2 = 1 := by
    simp only [Enclosures.rroots, List.forall_mem_append, List.forall_mem_map, implies_true,
      and_self]
  have h' := h
  simp only [Enclosures.check, Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨-, hlen⟩, hlast⟩ := h'
  rw [rrList_of_one _ hone]
  obtain ⟨d, hd⟩ : ∃ d, R.length = d + 1 := ⟨R.length - 1, by omega⟩
  have hlast' : R.getD d 0 = 1 := by
    rw [List.getLast?_eq_getElem?] at hlast
    rw [List.getD_eq_getElem?_getD, show d = R.length - 1 by omega, hlast]
    rfl
  refine prod_eq_polyC R hd hlast' _ ?_ (Enclosures.nodup R D h) (Enclosures.roots_eval R D h)
  rw [Enclosures.rrAll_eq]
  simp only [List.length_append, List.length_map, List.length_flatMap, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, List.map_const', List.sum_replicate, smul_eq_mul]
  omega

/-- The enclosed roots are exactly the complex solutions of `R (z) = 0`. -/
theorem Enclosures.eval_eq_zero_iff (R : List ℚ) (D : Enclosures) (h : D.check R = true)
    (z : ℂ) :
    (polyC R).eval z = 0 ↔ z ∈ D.reals.map (fun I ↦ ((AlgRoot.real R I.1 I.2 : ℝ) : ℂ)) ++
      D.discs.flatMap fun d ↦ [AlgRoot.complex R d.1 d.2.1 d.2.2.1,
        (starRingEnd ℂ) (AlgRoot.complex R d.1 d.2.1 d.2.2.1)] := by
  have hone : ∀ e ∈ D.rroots R, e.2 = 1 := by
    simp only [Enclosures.rroots, List.forall_mem_append, List.forall_mem_map, implies_true,
      and_self]
  rw [← Enclosures.prod_eq R D h, eval_list_prod, List.prod_eq_zero_iff, rrList_of_one _ hone,
    ← Enclosures.rrAll_eq]
  simp only [List.map_map, List.mem_map, Function.comp_apply, eval_sub, eval_X, eval_C,
    sub_eq_zero, exists_eq_right']

/-! ## The whole characteristic polynomial -/

/-- The coefficients of `∏ ρᵏ` as a list. -/
def charList (rs : List (CharRoot × ℕ)) : List ℚ := (List.range (degQ rs + 1)).map (charQ rs)

/-- For factors whose side conditions hold (`CharRoot.Valid`), the product of the `X - μ` over the
roots with repetitions `cList rs` is `polyC (charList rs)`. -/
theorem prod_cList (rs : List (CharRoot × ℕ)) (hv : ∀ e ∈ rs, e.1.Valid) :
    ((cList rs).map fun μ ↦ X - C μ).prod = polyC (charList rs) := by
  ext k
  rw [← charC_eq_coeff, charC_cList rs hv k, coeff_polyC, charList,
    List.getD_eq_getElem?_getD]
  by_cases hk : k < degQ rs + 1
  · rw [List.getElem?_map, List.getElem?_range hk]
    rfl
  · rw [List.getElem?_eq_none (by simp; omega)]
    have h0 := charC_eq_zero (cList rs) (k := k) (by rw [length_cList]; omega)
    rw [charC_cList rs hv k] at h0
    simpa using h0

/-- When every multiplicity in `rs` is positive, every entry of `allRoots rs` is in `cList rs`. -/
theorem mem_cList_of_mem_allRoots {μ : ℂ} :
    ∀ {rs : List (CharRoot × ℕ)}, (∀ e ∈ rs, 0 < e.2) → μ ∈ allRoots rs → μ ∈ cList rs
  | [], _, h => by simp [allRoots] at h
  | (ρ, k) :: rest, hpos, h => by
    simp only [allRoots, List.flatMap_cons, List.mem_append] at h
    simp only [cList, List.mem_append, List.mem_flatten, List.mem_replicate]
    rcases h with h | h
    · exact Or.inl ⟨ρ.roots, ⟨(hpos (ρ, k) (by simp)).ne', rfl⟩, h⟩
    · exact Or.inr (mem_cList_of_mem_allRoots (fun e he ↦ hpos e (by simp [he])) h)

/-- The roots of `(∏ ρᵏ) · R`. -/
noncomputable def combined (rs : List (CharRoot × ℕ)) (R : List ℚ) (D : Enclosures) :
    List (RRoot × ℕ) :=
  rs.map (fun e ↦ (RRoot.char e.1, e.2)) ++ D.rroots R

/-- For valid factors `rs`, `D.check R` and `coeffMul (charList rs) R = a`, the coefficients `charC`
of `∏ (X - μ)` over `rrList (combined rs R D)` are the entries of `a` cast to `ℂ`, and `0` past its
end. -/
theorem charC_combined (rs : List (CharRoot × ℕ)) (hv : ∀ e ∈ rs, e.1.Valid) (R : List ℚ)
    (D : Enclosures) (hD : D.check R = true) (a : List ℚ) (ha : coeffMul (charList rs) R = a) :
    ∀ k, charC (rrList (combined rs R D)) k = (a.getD k 0 : ℂ) := by
  intro k
  rw [charC_eq_coeff, combined, rrList_append, rrList_char, List.map_append, List.prod_append,
    prod_cList rs hv, Enclosures.prod_eq R D hD, ← polyC_coeffMul, ha, coeff_polyC]

/-- The roots `rrAll (combined rs R D)` are pairwise distinct when the factors `rs` are valid,
`separated rs p` holds, every multiplicity in `rs` is positive, `D.check R` holds, and `coeffEq`
accepts the Bézout identity `U ∏ ρᵏ + V R = 1`. -/
theorem nodup_combined (rs : List (CharRoot × ℕ)) (hv : ∀ e ∈ rs, e.1.Valid) {p : ℕ}
    (hsep : separated rs p = true) (hpos : ∀ e ∈ rs, 0 < e.2) (R : List ℚ) (D : Enclosures)
    (hD : D.check R = true) (U V : List ℚ)
    (hb : coeffEq (coeffAdd (coeffMul U (charList rs)) (coeffMul V R)) [1] = true) :
    (rrAll (combined rs R D)).Nodup := by
  rw [combined, rrAll_append, rrAll_char, List.nodup_append]
  refine ⟨nodup_of_separated hsep, Enclosures.nodup R D hD, ?_⟩
  rintro μ hμ _ hν rfl
  have h₁ : (polyC (charList rs)).eval μ = 0 := by
    rw [← prod_cList rs hv, eval_list_prod]
    apply List.prod_eq_zero
    simp only [List.map_map, List.mem_map, Function.comp_apply, eval_sub, eval_X, eval_C]
    exact ⟨μ, mem_cList_of_mem_allRoots hpos hμ, sub_self μ⟩
  have h₂ := Enclosures.roots_eval R D hD μ hν
  have h₃ := congrArg (Polynomial.eval μ) (polyC_eq_of_coeffEq hb)
  rw [polyC_coeffAdd, polyC_coeffMul, polyC_coeffMul, eval_add, eval_mul, eval_mul, h₁, h₂] at h₃
  simp at h₃

/-- When `D.check R` holds, `rrList (combined rs R D)` has `degQ rs + (R.length - 1)` entries, the
degree of `(∏ ρᵏ) · R`. -/
theorem length_rrList_combined (rs : List (CharRoot × ℕ)) (R : List ℚ) (D : Enclosures)
    (hD : D.check R = true) :
    (rrList (combined rs R D)).length = degQ rs + (R.length - 1) := by
  have hone : ∀ e ∈ D.rroots R, e.2 = 1 := by
    simp only [Enclosures.rroots, List.forall_mem_append, List.forall_mem_map, implies_true,
      and_self]
  have h' := hD
  simp only [Enclosures.check, Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨-, hlen⟩, -⟩ := h'
  rw [combined, rrList_append, rrList_char, List.length_append, length_cList,
    rrList_of_one _ hone, Enclosures.rrAll_eq]
  simp only [List.length_append, List.length_map, List.length_flatMap, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, List.map_const', List.sum_replicate, smul_eq_mul]
  omega

/-- For valid factors `rs`, `D.check R` and `coeffMul (charList rs) R = a`, the product of the
`X - μ` over `rrList (combined rs R D)` is `polyC a`. -/
theorem prod_combined (rs : List (CharRoot × ℕ)) (hv : ∀ e ∈ rs, e.1.Valid) (R : List ℚ)
    (D : Enclosures) (hD : D.check R = true) (a : List ℚ) (ha : coeffMul (charList rs) R = a) :
    ((rrList (combined rs R D)).map fun μ ↦ X - C μ).prod = polyC a := by
  rw [combined, rrList_append, rrList_char, List.map_append, List.prod_append, prod_cList rs hv,
    Enclosures.prod_eq R D hD, ← polyC_coeffMul, ha]

/-- For valid factors `rs` with positive multiplicities, `D.check R` and
`coeffMul (charList rs) R = a`, `μ` is a root of `polyC a` exactly when
`μ ∈ rrAll (combined rs R D)`. -/
theorem eval_eq_zero_iff_combined (rs : List (CharRoot × ℕ)) (hv : ∀ e ∈ rs, e.1.Valid)
    (hpos : ∀ e ∈ rs, 0 < e.2) (R : List ℚ) (D : Enclosures) (hD : D.check R = true)
    (a : List ℚ) (ha : coeffMul (charList rs) R = a) (μ : ℂ) :
    (polyC a).eval μ = 0 ↔ μ ∈ rrAll (combined rs R D) := by
  rw [← prod_combined rs hv R D hD a ha, eval_list_prod, List.prod_eq_zero_iff]
  simp only [List.map_map, List.mem_map, Function.comp_apply, eval_sub, eval_X, eval_C,
    sub_eq_zero, exists_eq_right']
  constructor
  · intro h
    obtain ⟨e, he, hμ⟩ := mem_of_mem_rrList h
    simp only [rrAll, List.mem_flatMap]
    exact ⟨e, he, hμ⟩
  · intro h
    rw [combined, rrAll_append, rrAll_char, List.mem_append] at h
    rw [combined, rrList_append, rrList_char, List.mem_append]
    rcases h with h | h
    · exact Or.inl (mem_cList_of_mem_allRoots hpos h)
    · have hone : ∀ e ∈ D.rroots R, e.2 = 1 := by
        simp only [Enclosures.rroots, List.forall_mem_append, List.forall_mem_map, implies_true,
          and_self]
      rw [rrList_of_one _ hone]
      exact Or.inr h

/-! ## Sums over the enclosed roots, by Lagrange interpolation -/

/-- `X ^ j`. -/
def powX (j : ℕ) : List ℚ := List.replicate j 0 ++ [1]

/-- `polyC (powX j) = X ^ j`. -/
theorem polyC_powX (j : ℕ) : polyC (powX j) = X ^ j := by
  induction j with
  | zero => simp [powX]
  | succ j ih =>
    simp only [powX, List.replicate_succ, List.cons_append, polyC_cons] at ih ⊢
    rw [ih]
    simp [pow_succ, mul_comm]

/-- A list of `n` coefficients gives a polynomial of degree less than `n`. -/
theorem degree_polyC_lt (a : List ℚ) : (polyC a).degree < a.length :=
  degree_map_le.trans_lt (CAS.Polynomial.degree_ofCoeffList_lt a)

/-- `∑ P(μ) / R'(μ)` over the distinct roots of `R` is the coefficient of `X ^ (e - 1)` of `P`. -/
theorem sum_div_derivative {L : List ℂ} (hL : L.Nodup) {R : List ℚ}
    (hR : (L.map fun μ ↦ X - C μ).prod = polyC R) {P : ℂ[X]} (hP : P.degree < L.length) :
    (L.map fun μ ↦ P.eval μ / (derivative (polyC R)).eval μ).sum = P.coeff (L.length - 1) := by
  classical
  have hs : L.toFinset.card = L.length := List.toFinset_card_of_nodup hL
  have hnodal : polyC R = Lagrange.nodal L.toFinset id := by
    rw [← hR, Lagrange.nodal_eq, List.prod_toFinset _ hL]
    rfl
  have hcoeff := Lagrange.coeff_eq_sum (s := L.toFinset) (v := id) (Set.injOn_id _)
    (P := P) (by rw [hs]; exact hP)
  rw [hs] at hcoeff
  rw [hcoeff, ← List.sum_toFinset _ hL]
  refine sum_congr rfl fun i hi ↦ ?_
  have h := Lagrange.eval_nodal_derivative_eval_node_eq (v := id) hi
  rw [Lagrange.eval_nodal] at h
  rw [hnodal]
  exact congrArg (P.eval i / ·) h

/-- When `D.check R` holds, there are `R.length - 1` enclosed roots, the degree of `R`. -/
theorem Enclosures.length_rrAll (R : List ℚ) (D : Enclosures) (h : D.check R = true) :
    (rrAll (D.rroots R)).length = R.length - 1 := by
  simp only [Enclosures.check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨-, hlen⟩, -⟩ := h
  rw [Enclosures.rrAll_eq]
  simp only [List.length_append, List.length_map, List.length_flatMap, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, List.map_const', List.sum_replicate, smul_eq_mul]
  omega

/-- `Enclosures.prod_eq` over the roots without repetitions: when `D.check R` holds, the product of
the `X - μ` over `rrAll (D.rroots R)` is `polyC R`. -/
theorem Enclosures.prod_eq' (R : List ℚ) (D : Enclosures) (h : D.check R = true) :
    ((rrAll (D.rroots R)).map fun μ ↦ X - C μ).prod = polyC R := by
  have hone : ∀ e ∈ D.rroots R, e.2 = 1 := by
    simp only [Enclosures.rroots, List.forall_mem_append, List.forall_mem_map, implies_true,
      and_self]
  rw [← rrList_of_one _ hone]
  exact Enclosures.prod_eq R D h

/-- When `D.check R` holds, the derivative of `polyC R` is nonzero at every enclosed root: the roots
are simple. -/
theorem Enclosures.derivative_ne_zero (R : List ℚ) (D : Enclosures) (h : D.check R = true) :
    ∀ μ ∈ rrAll (D.rroots R), (derivative (polyC R)).eval μ ≠ 0 := by
  classical
  intro μ hμ
  have hL := Enclosures.nodup R D h
  have hnodal : polyC R = Lagrange.nodal (rrAll (D.rroots R)).toFinset id := by
    rw [← Enclosures.prod_eq' R D h, Lagrange.nodal_eq, List.prod_toFinset _ hL]
    rfl
  have hi : μ ∈ (rrAll (D.rroots R)).toFinset := List.mem_toFinset.mpr hμ
  have h := Lagrange.eval_nodal_derivative_eval_node_eq (v := id) hi
  rw [Lagrange.eval_nodal] at h
  rw [hnodal]
  refine fun h0 ↦ (prod_ne_zero_iff.mpr fun j hj ↦ sub_ne_zero.mpr
    (Finset.ne_of_mem_erase hj).symm) (h.symm.trans h0)

/-- `∑ G(μ) μʲ` over the enclosed roots, from the remainder `Q` of `G R' Xʲ` by `R`. -/
theorem Enclosures.sum_mul_pow (R : List ℚ) (D : Enclosures) (hD : D.check R = true)
    (G T Q : List ℚ) (j : ℕ)
    (hdiv : coeffEq (coeffMul (coeffMul G (coeffDeriv R)) (powX j)) (coeffAdd (coeffMul T R) Q) =
      true)
    (hQ : Q.length < R.length) :
    ((rrAll (D.rroots R)).map fun μ ↦ (polyC G).eval μ * μ ^ j).sum =
      (Q.getD (R.length - 2) 0 : ℂ) := by
  have hlen := Enclosures.length_rrAll R D hD
  have hP : (polyC Q).degree < (rrAll (D.rroots R)).length :=
    (degree_polyC_lt Q).trans_le (by rw [hlen]; exact_mod_cast (by omega))
  have hsum := sum_div_derivative (Enclosures.nodup R D hD) (Enclosures.prod_eq' R D hD) hP
  rw [hlen, coeff_polyC, show R.length - 1 - 1 = R.length - 2 by omega] at hsum
  rw [← hsum]
  congr 1
  refine List.map_congr_left fun μ hμ ↦ ?_
  have hne := Enclosures.derivative_ne_zero R D hD μ hμ
  have hroot := Enclosures.roots_eval R D hD μ hμ
  have hval := congrArg (eval μ) (polyC_eq_of_coeffEq hdiv)
  simp only [polyC_coeffMul, polyC_coeffAdd, polyC_powX, ← derivative_polyC, eval_mul, eval_add,
    eval_pow, eval_X, hroot, mul_zero, zero_add] at hval
  rw [eq_div_iff hne, ← hval]
  ring

/-- Partial fractions over the enclosed roots: `B / R = ∑ W(μ) / (s - μ)` with
`W R' ≡ B` modulo `R`. -/
theorem Enclosures.partial_fraction (R : List ℚ) (D : Enclosures) (hD : D.check R = true)
    (B W T : List ℚ) (hB : B.length < R.length)
    (hW : coeffEq (coeffMul W (coeffDeriv R)) (coeffAdd B (coeffMul T R)) = true) (s : ℂ)
    (hs : (polyC R).eval s ≠ 0) :
    (polyC B).eval s / (polyC R).eval s =
      ((rrAll (D.rroots R)).map fun μ ↦ (polyC W).eval μ / (s - μ)).sum := by
  classical
  set L := rrAll (D.rroots R)
  have hL : L.Nodup := Enclosures.nodup R D hD
  have hcard : L.toFinset.card = L.length := List.toFinset_card_of_nodup hL
  have hlen := Enclosures.length_rrAll R D hD
  have hnodal : polyC R = Lagrange.nodal L.toFinset id := by
    rw [← Enclosures.prod_eq' R D hD, Lagrange.nodal_eq, List.prod_toFinset _ hL]
    rfl
  have hdeg : (polyC B).degree < L.toFinset.card :=
    (degree_polyC_lt B).trans_le (by rw [hcard, hlen]; exact_mod_cast (by omega))
  have hx : ∀ i ∈ L.toFinset, s ≠ id i := fun i hi h ↦ by
    have := Enclosures.roots_eval R D hD i (List.mem_toFinset.mp hi)
    exact hs (by rw [h]; exact this)
  have hinterp := Lagrange.eq_interpolate (v := id) (Set.injOn_id _) hdeg
  have heval := congrArg (eval s) hinterp
  rw [Lagrange.eval_interpolate_not_at_node _ hx, ← hnodal] at heval
  rw [heval, mul_div_cancel_left₀ _ hs, ← List.sum_toFinset _ hL]
  refine sum_congr rfl fun i hi ↦ ?_
  have hiL : i ∈ L := List.mem_toFinset.mp hi
  have hne := Enclosures.derivative_ne_zero R D hD i hiL
  have hroot := Enclosures.roots_eval R D hD i hiL
  have hval := congrArg (eval i) (polyC_eq_of_coeffEq hW)
  simp only [polyC_coeffMul, polyC_coeffAdd, ← derivative_polyC, eval_mul, eval_add, hroot,
    mul_zero, add_zero] at hval
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal hi, ← hnodal]
  simp only [id]
  rw [← hval]
  field_simp

/-- For real points `r = f I` over a list `l`, the sum in `ℂ` of `G(r) rʲ`, with `G(r)` the value of
`polyC G`, is the cast of the real sum of `coeffEval G r * r ^ j`. -/
theorem sum_reals (l : List (ℚ × ℚ)) (f : ℚ × ℚ → ℝ) (G : List ℚ) (j : ℕ) :
    ((l.map fun I ↦ ((f I : ℝ) : ℂ)).map fun μ ↦ (polyC G).eval μ * μ ^ j).sum =
      (((l.map fun I ↦ coeffEval G (f I) * f I ^ j).sum : ℝ) : ℂ) := by
  induction l with
  | nil => simp
  | cons I l ih =>
    simp only [List.map_cons, List.sum_cons, ih, eval_polyC_ofReal, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_pow]

/-- For complex points `z = g d` over a list `l`, the sum in `ℂ` of `G(μ) μʲ`, with `G(μ)` the value
of `polyC G`, over the points `z` and their conjugates `z̄` is the cast of the real sum of
`2 Re (G(z) zʲ)`. -/
theorem sum_discs {δ : Type*} (l : List δ) (g : δ → ℂ) (G : List ℚ) (j : ℕ) :
    ((l.flatMap fun d ↦ [g d, (starRingEnd ℂ) (g d)]).map
        fun μ ↦ (polyC G).eval μ * μ ^ j).sum =
      (((l.map fun d ↦ 2 * ((polyC G).eval (g d) * g d ^ j).re).sum : ℝ) : ℂ) := by
  induction l with
  | nil => simp
  | cons d l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      eval_conj_polyC]
    rw [← map_pow, ← map_mul, Complex.add_conj]
    push_cast
    ring

/-- A conjugate pair contributes twice the real part. -/
theorem Enclosures.sum_real (R : List ℚ) (D : Enclosures) (G : List ℚ) (j : ℕ) :
    ((rrAll (D.rroots R)).map fun μ ↦ (polyC G).eval μ * μ ^ j).sum =
      (((D.reals.map fun I ↦ coeffEval G (CAS.AlgRoot.real R I.1 I.2) *
          CAS.AlgRoot.real R I.1 I.2 ^ j).sum +
        (D.discs.map fun d ↦ 2 * ((polyC G).eval (CAS.AlgRoot.complex R d.1 d.2.1 d.2.2.1) *
          CAS.AlgRoot.complex R d.1 d.2.1 d.2.2.1 ^ j).re).sum : ℝ) : ℂ) := by
  rw [Enclosures.rrAll_eq, List.map_append, List.sum_append,
    sum_reals _ (fun I ↦ CAS.AlgRoot.real R I.1 I.2),
    sum_discs _ (fun d : ℚ × ℚ × ℚ × ℚ × ℚ × ℚ ↦ CAS.AlgRoot.complex R d.1 d.2.1 d.2.2.1),
    Complex.ofReal_add]

/-- When `D.check R` holds and the constant coefficient `R.headD 0` is nonzero, no enclosed root is
`0`. -/
theorem Enclosures.ne_zero (R : List ℚ) (D : Enclosures) (hD : D.check R = true)
    (h : R.headD 0 ≠ 0) : ∀ μ ∈ rrAll (D.rroots R), μ ≠ 0 := by
  intro μ hμ hzero
  have := Enclosures.roots_eval R D hD μ hμ
  rw [hzero] at this
  cases R with
  | nil => exact h rfl
  | cons c cs =>
    simp only [polyC_cons, eval_add, eval_C, eval_mul, eval_X, zero_mul, add_zero,
      Rat.cast_eq_zero] at this
    exact h this

end CAS.LinearODE

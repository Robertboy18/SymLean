/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.LinearODEComplex
public import CAS.Calculus.ConditionFree
public import CAS.Calculus.Series
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Linear equations of any order with constant rational coefficients

The characteristic polynomial is given factored over `ℚ` by a list of roots with
multiplicities (`CharRoot`): a rational root `r`, a pair of real roots `α ± c √m`, or a pair of
complex roots `α ± i c √m`. When the roots are distinct, the real solutions of
`∑ aₖ y⁽ᵏ⁾ = 0` are exactly the real span of `xʲ e ^ (r x)`, `xʲ e ^ ((α ± c √m) x)`,
`xʲ e ^ (α x) cos (c √m x)` and `xʲ e ^ (α x) sin (c √m x)` with `j` below the multiplicity
(`rLop_eq_zero_iff`). With a particular solution this gives the general solution of
`∑ aₖ y⁽ᵏ⁾ = F` (`general_iff`), and with initial values the only solution (`ivp_general_iff`).

## Main definitions

* `CharRoot`: a rational root, or a pair of real or complex roots `α ± c √m`, `α ± i c √m`.
* `charQ`: the rational coefficients of `∏ ρᵏ`.
* `separated`: rational boxes around all the roots are pairwise apart.
* `ivpCheck`: the decidable check of the initial values of a candidate solution.

## Main results

* `rLop_eq_zero_iff`: for distinct roots, the real solutions of the homogeneous equation form
  the real span of the exponential monomials.
* `eq_zero_of_rLop`: a solution of the homogeneous equation whose derivatives below the order
  vanish at one point vanishes everywhere.
* `general_iff`: `y` solves `∑ aₖ y⁽ᵏ⁾ = F` if and only if `y - Yp` lies in that span.
* `ivp_general_iff`: when `ivpCheck` holds, `Yp + ∑ cᵢ φᵢ (x - x₀)` is the only solution with
  the given initial values at `x₀`.

## Implementation notes

The command `#cas [dsolve y x]` proposes the factors, a particular solution and the constants
of an initial-value problem; the kernel checks them. It recomputes the coefficients of the
factors over `ℚ` (`charQ`), decides `separated` for the distinctness of the roots
(`nodup_of_separated`), and checks the initial values by `ivpCheck`, which evaluates exactly.
For that check we use the basis `ivpFuns` (`cosh`, `sinh / (c √m)`, `cos` and `sin / (c √m)`
instead of the exponentials of the surds): its derivatives at `0` are rational (`ivpVals`, by
iterating `CharRoot.step`), so no square root enters the check. The theorems ask only that
`y, y', …, y⁽ⁿ⁻¹⁾` be differentiable: such a solution is `Cⁿ`, since `y⁽ⁿ⁾` is a continuous
combination of the lower derivatives and the right side (`contDiff_of_rLop`).

The complex theorem `pOp_eq_zero_iff` gives the span for `ofReal ∘ y`, and real and imaginary
parts give the real span, as in Teschl's (3.55). Uniqueness (`eq_zero_of_rLop`) goes through
the first-order system of `(y, y', …, y⁽ⁿ⁻¹⁾)` with the companion matrix (Teschl's (3.50) and
(3.51)) and Mathlib's `ODE_solution_unique_univ`.

## References

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, Graduate Studies in
  Mathematics 140, American Mathematical Society, Providence, 2012,
  <https://doi.org/10.1090/gsm/140>. §3.3: Theorem 3.7 and (3.55) for the basis, (3.50) and
  (3.51) for the companion system; we read them in the author's online version,
  <https://www.mat.univie.ac.at/~gerald/ftp/book-ode/>.
-/

@[expose] public section

namespace CAS.Verified.Expr

/-- The value of `Y` at a rational point, from `exactValue?`. -/
theorem univariateEval_eq_of_exactValue {Y : Verified.Expr (Fin 1)} {x₀ a : ℚ}
    (h : exactValue? (fun _ ↦ x₀) Y = some a) : Y.univariateEval x₀ = a := by
  rw [univariateEval, euclideanSingle_eq_const]
  exact exactValue?_sound (fun _ ↦ x₀) Y a h

end CAS.Verified.Expr

namespace CAS.LinearODE

open Finset Submodule Complex
open scoped ContDiff

/-! ## Roots and coefficients -/

/-- A rational root `r`, a pair of real roots `α ± c √m`, or a pair of complex roots
`α ± i c √m`, with rational `α`, `c` and `m`. -/
inductive CharRoot
  | real (r : ℚ)
  | realPair (α c m : ℚ)
  | pair (α c m : ℚ)
  deriving DecidableEq, Repr

namespace CharRoot

/-- `c √m`. -/
noncomputable def width (c m : ℚ) : ℝ := (c : ℝ) * Real.sqrt m

/-- The roots, as complex numbers. -/
noncomputable def roots : CharRoot → List ℂ
  | real r => [((r : ℝ) : ℂ)]
  | realPair α c m => [(((α : ℝ) + width c m : ℝ) : ℂ), (((α : ℝ) - width c m : ℝ) : ℂ)]
  | pair α c m => [((α : ℝ) : ℂ) + (width c m : ℂ) * I, ((α : ℝ) : ℂ) - (width c m : ℂ) * I]

/-- The degree of the factor. -/
def degree : CharRoot → ℕ
  | real _ => 1
  | realPair .. => 2
  | pair .. => 2

/-- The side conditions: `c ≠ 0` and `m > 0` for a real pair, `c > 0` and `m > 0` for a complex
pair. -/
def Valid : CharRoot → Prop
  | real _ => True
  | realPair _ c m => c ≠ 0 ∧ 0 < m
  | pair _ c m => 0 < c ∧ 0 < m

/-- `DecidablePred Valid`, by cases on the factor and the decidable rational comparisons of each
case. -/
instance : DecidablePred Valid := fun ρ ↦ by
  cases ρ <;> simp only [Valid] <;> infer_instance

/-- The coefficients of `(X - r) q`. -/
def mulRootQ (r : ℚ) (q : ℕ → ℚ) : ℕ → ℚ
  | 0 => -r * q 0
  | k + 1 => q k - r * q (k + 1)

/-- The coefficients of `(X ^ 2 - s X + p) q`. -/
def mulQuadQ (s p : ℚ) (q : ℕ → ℚ) : ℕ → ℚ
  | 0 => p * q 0
  | 1 => -s * q 0 + p * q 1
  | k + 2 => q k - s * q (k + 1) + p * q (k + 2)

/-- Multiplication by the factor. -/
def mul : CharRoot → (ℕ → ℚ) → ℕ → ℚ
  | real r, q => mulRootQ r q
  | realPair α c m, q => mulQuadQ (2 * α) (α ^ 2 - c ^ 2 * m) q
  | pair α c m, q => mulQuadQ (2 * α) (α ^ 2 + c ^ 2 * m) q

end CharRoot

/-- The coefficients of `∏ ρᵏ`. -/
def charQ : List (CharRoot × ℕ) → ℕ → ℚ
  | [] => fun k ↦ if k = 0 then 1 else 0
  | (ρ, k) :: rest => ρ.mul^[k] (charQ rest)

/-- The degree of `∏ ρᵏ`. -/
def degQ : List (CharRoot × ℕ) → ℕ
  | [] => 0
  | (ρ, k) :: rest => k * ρ.degree + degQ rest

/-- The roots with repetitions. -/
noncomputable def cList : List (CharRoot × ℕ) → List ℂ
  | [] => []
  | (ρ, k) :: rest => (List.replicate k ρ.roots).flatten ++ cList rest

/-- `ρ.roots` has `ρ.degree` entries. -/
theorem length_roots (ρ : CharRoot) : ρ.roots.length = ρ.degree := by
  cases ρ <;> rfl

/-- The list of roots with repetitions has the degree of `∏ ρᵏ`: `cList rs` has `degQ rs`
entries. -/
theorem length_cList : ∀ rs : List (CharRoot × ℕ), (cList rs).length = degQ rs
  | [] => rfl
  | (ρ, k) :: rest => by
    simp [cList, degQ, length_cList rest, length_roots, List.length_flatten]

/-- Multiplication by `X - r` for a rational `r` commutes with the cast `ℚ → ℂ`: `mulRoot` at the
cast of `r`, applied to the casts of `q`, gives the casts of `CharRoot.mulRootQ r q`. -/
theorem mulRoot_cast (r : ℚ) (q : ℕ → ℚ) (k : ℕ) :
    mulRoot ((r : ℝ) : ℂ) (fun i ↦ (q i : ℂ)) k = (CharRoot.mulRootQ r q k : ℂ) := by
  cases k <;> simp [mulRoot, CharRoot.mulRootQ]

/-- For complex `z₁`, `z₂` with `z₁ + z₂ = s` and `z₁ * z₂ = p` for rationals `s`, `p`, the
coefficients of `(X - z₁) (X - z₂) q`, computed by two `mulRoot` steps from the casts of `q`, are
the casts of `CharRoot.mulQuadQ s p q`. -/
theorem mulRoot_mulRoot_cast {z₁ z₂ : ℂ} {s p : ℚ} (hs : z₁ + z₂ = s) (hp : z₁ * z₂ = p)
    (q : ℕ → ℚ) (k : ℕ) :
    mulRoot z₁ (mulRoot z₂ fun i ↦ (q i : ℂ)) k = (CharRoot.mulQuadQ s p q k : ℂ) := by
  rcases k with _ | _ | k
  all_goals
    simp only [mulRoot, CharRoot.mulQuadQ]
    push_cast
    simp only [← hp, ← hs]
    ring

/-- For `0 ≤ m`, `(c √m) ^ 2 = c ^ 2 m`: `CharRoot.width c m ^ 2` is the cast of `c ^ 2 * m`. -/
theorem width_sq {c m : ℚ} (hm : 0 ≤ m) : CharRoot.width c m ^ 2 = ((c ^ 2 * m : ℚ) : ℝ) := by
  rw [CharRoot.width, mul_pow, Real.sq_sqrt (by exact_mod_cast hm)]
  push_cast
  ring

/-- For a factor `ρ` with `ρ.Valid` and a list `L` with `charC L i = (q i : ℂ)` for every `i`,
the coefficients `charC (ρ.roots ++ L)` are the casts of `ρ.mul q`. -/
theorem charC_append_roots (ρ : CharRoot) (hρ : ρ.Valid) (L : List ℂ) (q : ℕ → ℚ)
    (h : ∀ i, charC L i = (q i : ℂ)) (k : ℕ) : charC (ρ.roots ++ L) k = (ρ.mul q k : ℂ) := by
  have hL : charC L = fun i ↦ (q i : ℂ) := funext h
  cases ρ with
  | real r =>
    simp only [CharRoot.roots, List.cons_append, List.nil_append, charC, hL, CharRoot.mul]
    exact mulRoot_cast r q k
  | realPair α c m =>
    simp only [CharRoot.roots, List.cons_append, List.nil_append, charC, hL, CharRoot.mul]
    have h2 : ((CharRoot.width c m : ℝ) : ℂ) ^ 2 = (c : ℂ) ^ 2 * m := by
      exact_mod_cast width_sq hρ.2.le
    apply mulRoot_mulRoot_cast <;> push_cast
    · ring
    · linear_combination (-1 : ℂ) * h2
  | pair α c m =>
    simp only [CharRoot.roots, List.cons_append, List.nil_append, charC, hL, CharRoot.mul]
    have h2 : ((CharRoot.width c m : ℝ) : ℂ) ^ 2 = (c : ℂ) ^ 2 * m := by
      exact_mod_cast width_sq hρ.2.le
    apply mulRoot_mulRoot_cast <;> push_cast
    · ring
    · linear_combination h2 - ((CharRoot.width c m : ℝ) : ℂ) ^ 2 * Complex.I_sq

/-- The coefficients of `∏ (X - μ)` over the roots are those of `∏ ρᵏ`. -/
theorem charC_cList : ∀ (rs : List (CharRoot × ℕ)), (∀ e ∈ rs, e.1.Valid) →
    ∀ k, charC (cList rs) k = (charQ rs k : ℂ)
  | [], _, k => by
    simp only [cList, charC, charQ]
    split_ifs <;> simp
  | (ρ, j) :: rest, hv, k => by
    have hρ : ρ.Valid := hv (ρ, j) (by simp)
    have hrest := charC_cList rest (fun e he ↦ hv e (by simp [he]))
    simp only [cList, charQ]
    clear hv
    induction j generalizing k with
    | zero => simpa using hrest k
    | succ j ih =>
      rw [List.replicate_succ, List.flatten_cons, List.append_assoc,
        Function.iterate_succ_apply']
      exact charC_append_roots ρ hρ _ _ ih k

/-! ## Multiplicities -/

/-- All roots, each once. -/
noncomputable def allRoots (rs : List (CharRoot × ℕ)) : List ℂ := rs.flatMap (·.1.roots)

/-- `μ` occurs `k * R.count μ` times in the concatenation of `k` copies of `R`. -/
theorem count_flatten_replicate (μ : ℂ) (R : List ℂ) :
    ∀ k : ℕ, ((List.replicate k R).flatten).count μ = k * R.count μ
  | 0 => by simp
  | k + 1 => by
    rw [List.replicate_succ, List.flatten_cons, List.count_append,
      count_flatten_replicate μ R k]
    ring

/-- Every entry of `cList rs` is a root of the factor `e.1` of some `e ∈ rs`. -/
theorem mem_of_mem_cList {μ : ℂ} :
    ∀ {rs : List (CharRoot × ℕ)}, μ ∈ cList rs → ∃ e ∈ rs, μ ∈ e.1.roots
  | [], h => by simp [cList] at h
  | (ρ, k) :: rest, h => by
    simp only [cList, List.mem_append, List.mem_flatten, List.mem_replicate] at h
    rcases h with ⟨R, ⟨-, rfl⟩, hR⟩ | h
    · exact ⟨(ρ, k), by simp, hR⟩
    · obtain ⟨e, he, hμ⟩ := mem_of_mem_cList h
      exact ⟨e, by simp [he], hμ⟩

/-- A complex number outside `allRoots rs` does not occur in `cList rs`. -/
theorem count_cList_eq_zero {μ : ℂ} {rs : List (CharRoot × ℕ)} (h : μ ∉ allRoots rs) :
    (cList rs).count μ = 0 := by
  rw [List.count_eq_zero]
  intro hμ
  obtain ⟨e, he, hμe⟩ := mem_of_mem_cList hμ
  exact h (List.mem_flatMap.mpr ⟨e, he, hμe⟩)

/-- When `allRoots rs` has no duplicates, a root `μ` of a factor `ρ` with `(ρ, k) ∈ rs` occurs
exactly `k` times in `cList rs`. -/
theorem count_cList_of_mem {μ : ℂ} :
    ∀ {rs : List (CharRoot × ℕ)}, (allRoots rs).Nodup → ∀ {ρ : CharRoot} {k : ℕ},
      (ρ, k) ∈ rs → μ ∈ ρ.roots → (cList rs).count μ = k
  | [], _, _, _, hm, _ => by simp at hm
  | (ρ', k') :: rest, hnd, ρ, k, hm, hμ => by
    simp only [allRoots, List.flatMap_cons, List.nodup_append] at hnd
    obtain ⟨hnd₁, hnd₂, hdisj⟩ := hnd
    simp only [cList, List.count_append, count_flatten_replicate]
    rcases List.mem_cons.mp hm with he | hm'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rw [List.count_eq_one_of_mem hnd₁ hμ, count_cList_eq_zero fun hμ' ↦ hdisj μ hμ μ hμ' rfl]
      ring
    · have h0 : ρ'.roots.count μ = 0 := List.count_eq_zero.mpr fun hμ' ↦
        hdisj μ hμ' μ (List.mem_flatMap.mpr ⟨(ρ, k), hm', hμ⟩) rfl
      rw [h0, count_cList_of_mem hnd₂ hm' hμ]
      ring

/-- A root `μ` of a factor `ρ` with `(ρ, k) ∈ rs` occurs at least `k` times in `cList rs`; the
roots need not be distinct. -/
theorem le_count_cList {μ : ℂ} :
    ∀ {rs : List (CharRoot × ℕ)} {ρ : CharRoot} {k : ℕ}, (ρ, k) ∈ rs → μ ∈ ρ.roots →
      k ≤ (cList rs).count μ
  | [], _, _, hm, _ => by simp at hm
  | (ρ', k') :: rest, ρ, k, hm, hμ => by
    simp only [cList, List.count_append, count_flatten_replicate]
    rcases List.mem_cons.mp hm with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      have : 0 < ρ.roots.count μ := List.count_pos_iff.mpr hμ
      nlinarith
    · have := le_count_cList h hμ
      omega

/-! ## Separating the roots by rational boxes -/

/-- A rectangle `[reLo, reHi] × [imLo, imHi]` in the complex plane. -/
structure Box where
  /-- The lower bound of the real part. -/
  reLo : ℚ
  /-- The upper bound of the real part. -/
  reHi : ℚ
  /-- The lower bound of the imaginary part. -/
  imLo : ℚ
  /-- The upper bound of the imaginary part. -/
  imHi : ℚ
  deriving DecidableEq, Repr

/-- `z` lies in the box. -/
def Box.Contains (B : Box) (z : ℂ) : Prop :=
  (B.reLo : ℝ) ≤ z.re ∧ z.re ≤ B.reHi ∧ (B.imLo : ℝ) ≤ z.im ∧ z.im ≤ B.imHi

/-- The boxes are disjoint, by one of the four separating inequalities. -/
def Box.apart (B C : Box) : Bool :=
  decide (B.reHi < C.reLo) || decide (C.reHi < B.reLo) || decide (B.imHi < C.imLo) ||
    decide (C.imHi < B.imLo)

/-- A point `z` of `B` and a point `w` of `C` are distinct when `B.apart C = true`. -/
theorem Box.ne_of_apart {B C : Box} {z w : ℂ} (hB : B.Contains z) (hC : C.Contains w)
    (h : B.apart C = true) : z ≠ w := by
  rintro rfl
  obtain ⟨b1, b2, b3, b4⟩ := hB
  obtain ⟨c1, c2, c3, c4⟩ := hC
  simp only [Box.apart, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ((h | h) | h) | h <;> linarith [(Rat.cast_lt (K := ℝ)).mpr h]

/-- A lower bound for `√m` with `p` binary digits. -/
def sqrtLo (m : ℚ) (p : ℕ) : ℚ := (Nat.sqrt ⌊m * 4 ^ p⌋₊ : ℚ) / 2 ^ p

/-- An upper bound for `√m` with `p` binary digits. -/
def sqrtHi (m : ℚ) (p : ℕ) : ℚ := ((Nat.sqrt ⌊m * 4 ^ p⌋₊ + 1 : ℕ) : ℚ) / 2 ^ p

/-- `sqrtLo m p ≤ √m` for every rational `m` and every `p`. -/
theorem sqrtLo_le (m : ℚ) (p : ℕ) : (sqrtLo m p : ℝ) ≤ Real.sqrt m := by
  rcases lt_or_ge m 0 with hm | hm
  · have h0 : ⌊m * 4 ^ p⌋₊ = 0 := Nat.floor_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hm.le
      (by positivity))
    simp [sqrtLo, h0, Real.sqrt_nonneg]
  have hN : ((Nat.sqrt ⌊m * 4 ^ p⌋₊ * Nat.sqrt ⌊m * 4 ^ p⌋₊ : ℕ) : ℚ) ≤ m * 4 ^ p :=
    (Nat.cast_le.mpr (Nat.sqrt_le _)).trans (Nat.floor_le (by positivity))
  have h4 : (4 : ℚ) ^ p = (2 ^ p) ^ 2 := by norm_num [sq, ← mul_pow]
  have : (sqrtLo m p) ^ 2 ≤ m := by
    rw [sqrtLo, div_pow, div_le_iff₀ (by positivity), ← h4]
    push_cast at hN
    nlinarith
  exact Real.le_sqrt_of_sq_le (by exact_mod_cast this)

/-- `√m ≤ sqrtHi m p` for every rational `m` and every `p`. -/
theorem le_sqrtHi (m : ℚ) (p : ℕ) : Real.sqrt m ≤ (sqrtHi m p : ℝ) := by
  have hN : m * 4 ^ p < ((Nat.sqrt ⌊m * 4 ^ p⌋₊ + 1) * (Nat.sqrt ⌊m * 4 ^ p⌋₊ + 1) : ℕ) :=
    (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast Nat.lt_succ_sqrt _)
  have h4 : (4 : ℚ) ^ p = (2 ^ p) ^ 2 := by norm_num [sq, ← mul_pow]
  have hsq : m ≤ (sqrtHi m p) ^ 2 := by
    rw [sqrtHi, div_pow, le_div_iff₀ (by positivity), ← h4]
    push_cast at hN ⊢
    nlinarith
  have hnn : (0 : ℝ) ≤ sqrtHi m p := by
    rw [sqrtHi]
    positivity
  exact Real.sqrt_le_iff.mpr ⟨hnn, by exact_mod_cast hsq⟩

/-- A lower bound for `c √m`. -/
def widthLo (c m : ℚ) (p : ℕ) : ℚ := if 0 ≤ c then c * sqrtLo m p else c * sqrtHi m p

/-- An upper bound for `c √m`. -/
def widthHi (c m : ℚ) (p : ℕ) : ℚ := if 0 ≤ c then c * sqrtHi m p else c * sqrtLo m p

/-- `widthLo c m p ≤ c √m` (`CharRoot.width c m`) for all rationals `c`, `m` and every `p`. -/
theorem widthLo_le (c m : ℚ) (p : ℕ) :
    (widthLo c m p : ℝ) ≤ CharRoot.width c m := by
  rw [widthLo, CharRoot.width]
  split_ifs with hc
  · push_cast
    exact mul_le_mul_of_nonneg_left (sqrtLo_le m p) (by exact_mod_cast hc)
  · push_cast
    exact mul_le_mul_of_nonpos_left (le_sqrtHi m p) (by exact_mod_cast (not_le.mp hc).le)

/-- `c √m ≤ widthHi c m p` (`CharRoot.width c m`) for all rationals `c`, `m` and every `p`. -/
theorem le_widthHi (c m : ℚ) (p : ℕ) :
    CharRoot.width c m ≤ (widthHi c m p : ℝ) := by
  rw [widthHi, CharRoot.width]
  split_ifs with hc
  · push_cast
    exact mul_le_mul_of_nonneg_left (le_sqrtHi m p) (by exact_mod_cast hc)
  · push_cast
    exact mul_le_mul_of_nonpos_left (sqrtLo_le m p) (by exact_mod_cast (not_le.mp hc).le)

/-- Boxes around the roots, in the order of `roots`. -/
def CharRoot.boxes (p : ℕ) : CharRoot → List Box
  | real r => [⟨r, r, 0, 0⟩]
  | realPair α c m => [⟨α + widthLo c m p, α + widthHi c m p, 0, 0⟩,
      ⟨α - widthHi c m p, α - widthLo c m p, 0, 0⟩]
  | pair α c m => [⟨α, α, widthLo c m p, widthHi c m p⟩,
      ⟨α, α, -widthHi c m p, -widthLo c m p⟩]

/-- For every `p`, each root in `ρ.roots` lies in the box at the same position of `ρ.boxes p`;
no side condition on `ρ` is needed. -/
theorem CharRoot.forall₂_boxes (ρ : CharRoot) (p : ℕ) :
    List.Forall₂ Box.Contains (ρ.boxes p) ρ.roots := by
  cases ρ with
  | real r =>
    simp only [boxes, roots, List.forall₂_cons, List.Forall₂.nil, and_true]
    simp [Box.Contains]
  | realPair α c m =>
    have h1 := widthLo_le c m p
    have h2 := le_widthHi c m p
    simp only [boxes, roots, List.forall₂_cons, List.Forall₂.nil, and_true]
    simp only [Box.Contains, Complex.ofReal_re, Complex.ofReal_im]
    push_cast
    refine ⟨⟨by linarith, by linarith, le_rfl, le_rfl⟩, by linarith, by linarith, le_rfl, le_rfl⟩
  | pair α c m =>
    have h1 := widthLo_le c m p
    have h2 := le_widthHi c m p
    simp only [boxes, roots, List.forall₂_cons, List.Forall₂.nil, and_true]
    simp only [Box.Contains, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    push_cast
    refine ⟨⟨by linarith, by linarith, by linarith, by linarith⟩,
      by linarith, by linarith, by linarith, by linarith⟩

/-- The boxes of all roots are pairwise apart. -/
def separated (rs : List (CharRoot × ℕ)) (p : ℕ) : Bool :=
  decide ((rs.flatMap fun e ↦ e.1.boxes p).Pairwise fun B C ↦ B.apart C = true)

/-- For every `p`, the boxes of the factors of `rs`, concatenated, contain the entries of
`allRoots rs` position by position. -/
theorem forall₂_flatMap_boxes (p : ℕ) :
    ∀ (rs : List (CharRoot × ℕ)),
      List.Forall₂ Box.Contains (rs.flatMap fun e ↦ e.1.boxes p) (allRoots rs)
  | [] => by simp [allRoots]
  | e :: rest => by
    simp only [List.flatMap_cons, allRoots]
    exact List.rel_append (e.1.forall₂_boxes p) (forall₂_flatMap_boxes p rest)

/-- If each entry of `zs` lies in the box at the same position of `bs` and the boxes are pairwise
apart (`Box.apart`), the entries of `zs` are pairwise distinct. -/
theorem pairwise_ne_of_forall₂ :
    ∀ {bs : List Box} {zs : List ℂ}, List.Forall₂ Box.Contains bs zs →
      bs.Pairwise (fun B C ↦ B.apart C = true) → zs.Pairwise (· ≠ ·)
  | [], [], _, _ => List.Pairwise.nil
  | B :: bs, z :: zs, List.Forall₂.cons hBz hrest, hp => by
    rw [List.pairwise_cons] at hp ⊢
    refine ⟨fun w hw ↦ ?_, pairwise_ne_of_forall₂ hrest hp.2⟩
    obtain ⟨C, hC, hCw⟩ : ∃ C ∈ bs, C.Contains w := by
      clear hp hBz
      induction hrest with
      | nil => simp at hw
      | cons hcw _ ih =>
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact ⟨_, by simp, hcw⟩
        · obtain ⟨C, hC, hCw⟩ := ih hw'
          exact ⟨C, by simp [hC], hCw⟩
    exact Box.ne_of_apart hBz hCw (hp.1 C hC)

/-- Separated boxes make the roots distinct. -/
theorem nodup_of_separated {rs : List (CharRoot × ℕ)} {p : ℕ}
    (h : separated rs p = true) : (allRoots rs).Nodup :=
  pairwise_ne_of_forall₂ (forall₂_flatMap_boxes p rs) (of_decide_eq_true h)

/-! ## Real solutions -/

/-- `∑ₖ₌₀ⁿ aₖ y⁽ᵏ⁾`. -/
noncomputable def rLop (n : ℕ) (a : ℕ → ℝ) (y : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), a k * iteratedDeriv k y x

/-- `∑ aₖ Y⁽ᵏ⁾` is continuous for a `Cⁿ` function `Y`. -/
theorem continuous_rLop {n : ℕ} (a : ℕ → ℝ) {Y : ℝ → ℝ} (hY : ContDiff ℝ n Y) :
    Continuous (rLop n a Y) := by
  have : rLop n a Y = fun x ↦ ∑ k ∈ range (n + 1), a k * iteratedDeriv k Y x := rfl
  rw [this]
  refine continuous_finsetSum _ fun k hk ↦ continuous_const.mul ?_
  exact hY.continuous_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk))

/-- A solution of `∑ aₖ y⁽ᵏ⁾ = F` with `aₙ = 1` and `F` continuous whose derivatives below the
order are differentiable is `Cⁿ`: `y⁽ⁿ⁾` is `F` minus a continuous combination of them. -/
theorem contDiff_of_rLop {n : ℕ} {a : ℕ → ℝ} (ha : a n = 1) {y F : ℝ → ℝ}
    (hy : ∀ k < n, Differentiable ℝ (iteratedDeriv k y)) (hF : Continuous F)
    (h : ∀ x, rLop n a y x = F x) : ContDiff ℝ n y := by
  rw [contDiff_nat_iff_iteratedDeriv]
  refine ⟨fun m hm ↦ ?_, hy⟩
  rcases hm.lt_or_eq with hm | rfl
  · exact (hy m hm).continuous
  · have e : iteratedDeriv m y = fun x ↦ F x - ∑ k ∈ range m, a k * iteratedDeriv k y x := by
      funext x
      have := h x
      rw [rLop, sum_range_succ, ha, one_mul] at this
      linarith
    rw [e]
    exact hF.sub (continuous_finsetSum _ fun k hk ↦
      continuous_const.mul (hy k (mem_range.mp hk)).continuous)

/-- The hypothesis of the theorems below for an equation of order one. -/
theorem forall_lt_one_of_differentiable {y : ℝ → ℝ} (hy : Differentiable ℝ y) :
    ∀ k < 1, Differentiable ℝ (iteratedDeriv k y) := fun k hk ↦ by
  rw [Nat.lt_one_iff.mp hk, iteratedDeriv_zero]
  exact hy

/-- For every `g : ℝ → ℝ`, the derivative of `x ↦ (g x : ℂ)` at `x` is the cast of `deriv g x`
(both are `0` where `g` is not differentiable). -/
theorem deriv_ofReal_comp (g : ℝ → ℝ) (x : ℝ) :
    deriv (fun x ↦ (g x : ℂ)) x = ((deriv g x : ℝ) : ℂ) := by
  by_cases hg : DifferentiableAt ℝ g x
  · exact hg.hasDerivAt.ofReal_comp.deriv
  · have : ¬ DifferentiableAt ℝ (fun x ↦ (g x : ℂ)) x := fun h ↦
      hg (by simpa [Function.comp_def] using Complex.reCLM.differentiableAt.comp x h)
    rw [deriv_zero_of_not_differentiableAt this, deriv_zero_of_not_differentiableAt hg]
    simp

/-- For every `g : ℝ → ℝ` and every `k`, the `k`-th derivative of `x ↦ (g x : ℂ)` is
`x ↦ (iteratedDeriv k g x : ℂ)`. -/
theorem iteratedDeriv_ofReal_comp (g : ℝ → ℝ) :
    ∀ k, iteratedDeriv k (fun x ↦ (g x : ℂ)) = fun x ↦ ((iteratedDeriv k g x : ℝ) : ℂ)
  | 0 => by simp
  | k + 1 => by
    rw [iteratedDeriv_succ, iteratedDeriv_ofReal_comp g k, iteratedDeriv_succ]
    funext x
    exact deriv_ofReal_comp _ x

namespace CharRoot

/-- The real solutions `xʲ e ^ (r x)`, `xʲ e ^ ((α ± c √m) x)`, `xʲ e ^ (α x) cos (c √m x)`,
`xʲ e ^ (α x) sin (c √m x)` of the factor. -/
noncomputable def funs : CharRoot → ℕ → List (ℝ → ℝ)
  | real r, j => [fun x ↦ x ^ j * Real.exp (r * x)]
  | realPair α c m, j => [fun x ↦ x ^ j * Real.exp ((α + width c m) * x),
      fun x ↦ x ^ j * Real.exp ((α - width c m) * x)]
  | pair α c m, j => [fun x ↦ x ^ j * Real.exp (α * x) * Real.cos (width c m * x),
      fun x ↦ x ^ j * Real.exp (α * x) * Real.sin (width c m * x)]

end CharRoot

/-- The real solutions, factor by factor and power by power. -/
noncomputable def basisList : List (CharRoot × ℕ) → List (ℝ → ℝ)
  | [] => []
  | (ρ, k) :: rest => (List.range k).flatMap ρ.funs ++ basisList rest

/-- `f` is an entry of `basisList rs` if and only if `f ∈ e.1.funs j` for some `e ∈ rs` and some
`j < e.2`. -/
theorem mem_basisList {f : ℝ → ℝ} :
    ∀ {rs : List (CharRoot × ℕ)}, f ∈ basisList rs ↔ ∃ e ∈ rs, ∃ j < e.2, f ∈ e.1.funs j
  | [] => by simp [basisList]
  | (ρ, k) :: rest => by
    simp only [basisList, List.mem_append, List.mem_flatMap, List.mem_range, mem_basisList,
      List.mem_cons, exists_eq_or_imp]

/-- `cMono (α + i c √m) j x = xʲ e ^ (α x) cos (c √m x) + i xʲ e ^ (α x) sin (c √m x)`, with
`c √m` written `CharRoot.width c m` and both terms casts of real numbers. -/
theorem cMono_pair_add (α c m : ℚ) (j : ℕ) (x : ℝ) :
    cMono (((α : ℝ) : ℂ) + (CharRoot.width c m : ℂ) * I) j x =
      ((x ^ j * Real.exp (α * x) * Real.cos (CharRoot.width c m * x) : ℝ) : ℂ) +
        I * ((x ^ j * Real.exp (α * x) * Real.sin (CharRoot.width c m * x) : ℝ) : ℂ) := by
  unfold cMono
  have : (((α : ℝ) : ℂ) + (CharRoot.width c m : ℂ) * I) * (x : ℂ) =
      ((α * x : ℝ) : ℂ) + ((CharRoot.width c m * x : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [this, Complex.exp_add_mul_I]
  push_cast
  ring

/-- `cMono (α - i c √m) j x = xʲ e ^ (α x) cos (c √m x) - i xʲ e ^ (α x) sin (c √m x)`, with
`c √m` written `CharRoot.width c m` and both terms casts of real numbers. -/
theorem cMono_pair_sub (α c m : ℚ) (j : ℕ) (x : ℝ) :
    cMono (((α : ℝ) : ℂ) - (CharRoot.width c m : ℂ) * I) j x =
      ((x ^ j * Real.exp (α * x) * Real.cos (CharRoot.width c m * x) : ℝ) : ℂ) -
        I * ((x ^ j * Real.exp (α * x) * Real.sin (CharRoot.width c m * x) : ℝ) : ℂ) := by
  unfold cMono
  have : (((α : ℝ) : ℂ) - (CharRoot.width c m : ℂ) * I) * (x : ℂ) =
      ((α * x : ℝ) : ℂ) + ((-(CharRoot.width c m * x) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [this, Complex.exp_add_mul_I]
  push_cast
  simp only [Complex.cos_neg, Complex.sin_neg]
  ring

/-- At a real root `r`, `cMono r j x` is the cast of the real number `x ^ j * Real.exp (r * x)`. -/
theorem cMono_real (r : ℝ) (j : ℕ) (x : ℝ) :
    cMono (r : ℂ) j x = ((x ^ j * Real.exp (r * x) : ℝ) : ℂ) := by
  unfold cMono
  push_cast
  ring

/-- Each exponential monomial at a root is `h₁ + i h₂` with real solutions `h₁`, `h₂`. -/
theorem cMono_eq_of_mem_roots {ρ : CharRoot} {μ : ℂ} (hμ : μ ∈ ρ.roots) (j : ℕ) :
    ∃ h₁ ∈ span ℝ {f | f ∈ ρ.funs j}, ∃ h₂ ∈ span ℝ {f | f ∈ ρ.funs j},
      ∀ x, cMono μ j x = (h₁ x : ℂ) + I * (h₂ x : ℂ) := by
  cases ρ with
  | real r =>
    simp only [CharRoot.roots, List.mem_singleton] at hμ
    subst hμ
    refine ⟨fun x ↦ x ^ j * Real.exp (r * x), subset_span (by simp [CharRoot.funs]), 0,
      zero_mem _, fun x ↦ ?_⟩
    rw [cMono_real]
    simp
  | realPair α c m =>
    simp only [CharRoot.roots, List.mem_cons, List.not_mem_nil, or_false] at hμ
    rcases hμ with rfl | rfl
    · refine ⟨fun x ↦ x ^ j * Real.exp ((α + CharRoot.width c m) * x),
        subset_span (by simp [CharRoot.funs]), 0, zero_mem _, fun x ↦ ?_⟩
      rw [cMono_real]
      simp
    · refine ⟨fun x ↦ x ^ j * Real.exp ((α - CharRoot.width c m) * x),
        subset_span (by simp [CharRoot.funs]), 0, zero_mem _, fun x ↦ ?_⟩
      rw [cMono_real]
      simp
  | pair α c m =>
    simp only [CharRoot.roots, List.mem_cons, List.not_mem_nil, or_false] at hμ
    have hc : (fun x : ℝ ↦ x ^ j * Real.exp (α * x) * Real.cos (CharRoot.width c m * x)) ∈
        span ℝ {f | f ∈ (CharRoot.pair α c m).funs j} := subset_span (by simp [CharRoot.funs])
    have hs : (fun x : ℝ ↦ x ^ j * Real.exp (α * x) * Real.sin (CharRoot.width c m * x)) ∈
        span ℝ {f | f ∈ (CharRoot.pair α c m).funs j} := subset_span (by simp [CharRoot.funs])
    rcases hμ with rfl | rfl
    · exact ⟨_, hc, _, hs, fun x ↦ cMono_pair_add α c m j x⟩
    · refine ⟨_, hc, _, neg_mem hs, fun x ↦ ?_⟩
      rw [cMono_pair_sub]
      simp only [Pi.neg_apply, Complex.ofReal_neg]
      ring

/-- Each real solution is a complex combination of exponential monomials at the roots. -/
theorem ofReal_mem_span_of_mem_funs {ρ : CharRoot} {j : ℕ} {f : ℝ → ℝ}
    (hf : f ∈ ρ.funs j) :
    (fun x ↦ (f x : ℂ)) ∈ span ℂ ((fun μ ↦ cMono μ j) '' {μ | μ ∈ ρ.roots}) := by
  have mem : ∀ μ ∈ ρ.roots, cMono μ j ∈ span ℂ ((fun μ ↦ cMono μ j) '' {μ | μ ∈ ρ.roots}) :=
    fun μ hμ ↦ subset_span ⟨μ, hμ, rfl⟩
  cases ρ with
  | real r =>
    simp only [CharRoot.funs, List.mem_singleton] at hf
    subst hf
    convert mem ((r : ℝ) : ℂ) (by simp [CharRoot.roots]) using 1
    exact funext fun x ↦ (cMono_real _ j x).symm
  | realPair α c m =>
    simp only [CharRoot.funs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · convert mem (((α : ℝ) + CharRoot.width c m : ℝ) : ℂ) (by simp [CharRoot.roots]) using 1
      exact funext fun x ↦ (cMono_real _ j x).symm
    · convert mem (((α : ℝ) - CharRoot.width c m : ℝ) : ℂ) (by simp [CharRoot.roots]) using 1
      exact funext fun x ↦ (cMono_real _ j x).symm
  | pair α c m =>
    simp only [CharRoot.funs, List.mem_cons, List.not_mem_nil, or_false] at hf
    have h₁ := mem (((α : ℝ) : ℂ) + (CharRoot.width c m : ℂ) * I) (by simp [CharRoot.roots])
    have h₂ := mem (((α : ℝ) : ℂ) - (CharRoot.width c m : ℂ) * I) (by simp [CharRoot.roots])
    rcases hf with rfl | rfl
    · convert add_mem (smul_mem _ (1 / 2 : ℂ) h₁) (smul_mem _ (1 / 2 : ℂ) h₂) using 1
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cMono_pair_add, cMono_pair_sub]
      ring
    · convert add_mem (smul_mem _ (-I / 2) h₁) (smul_mem _ (I / 2) h₂) using 1
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cMono_pair_add, cMono_pair_sub]
      ring_nf
      rw [Complex.I_sq]
      ring

/-- A real function solves `∑ aₖ y⁽ᵏ⁾ = 0` for the coefficients of `∏ ρᵏ` exactly when its complex
image lies in the span of the root basis. -/
theorem rLop_eq_zero_iff_mem_rootSpan (rs : List (CharRoot × ℕ)) (hv : ∀ e ∈ rs, e.1.Valid)
    {y : ℝ → ℝ} (hy : ContDiff ℝ (degQ rs) y) :
    (∀ x, rLop (degQ rs) (fun k ↦ (charQ rs k : ℝ)) y x = 0) ↔
      (fun x ↦ (y x : ℂ)) ∈ span ℂ (rootBasis (cList rs)) := by
  set z : ℝ → ℂ := fun x ↦ (y x : ℂ) with hz
  have hzc : ContDiff ℝ (cList rs).length z := by
    rw [length_cList]
    exact Complex.ofRealCLM.contDiff.comp hy
  have hop : ∀ x, pOp (cList rs) z x =
      ((rLop (degQ rs) (fun k ↦ (charQ rs k : ℝ)) y x : ℝ) : ℂ) := by
    intro x
    rw [pOp_eq_cLop _ hzc x, cLop, rLop, length_cList, hz]
    simp only [iteratedDeriv_ofReal_comp]
    push_cast
    exact sum_congr rfl fun k _ ↦ by rw [charC_cList rs hv k]
  rw [← pOp_eq_zero_iff _ hzc, funext_iff]
  simp only [hop, Pi.zero_apply, Complex.ofReal_eq_zero]

/-- The complex image of every function of the real span of the basis lies in the span of the
root basis; the roots need not be distinct. -/
theorem ofReal_mem_rootSpan_of_mem_span (rs : List (CharRoot × ℕ)) :
    ∀ f ∈ span ℝ {f | f ∈ basisList rs},
      (fun x ↦ (f x : ℂ)) ∈ span ℂ (rootBasis (cList rs)) := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨e, he, j, hj, hfe⟩ := mem_basisList.mp hf
    refine span_mono ?_ (ofReal_mem_span_of_mem_funs hfe)
    rintro g ⟨μ, hμ, rfl⟩
    exact ⟨μ, j, lt_of_lt_of_le hj (le_count_cList he hμ), rfl⟩
  | zero =>
    convert zero_mem (span ℂ (rootBasis (cList rs))) using 1
  | add f g _ _ hf hg =>
    convert add_mem hf hg using 1
    exact funext fun x ↦ by simp
  | smul c f _ hf =>
    convert smul_mem _ (c : ℂ) hf using 1
    exact funext fun x ↦ by simp

/-- The functions of the real basis are smooth. -/
theorem CharRoot.contDiff_funs (ρ : CharRoot) (j : ℕ) : ∀ f ∈ ρ.funs j, ContDiff ℝ ∞ f := by
  cases ρ <;> simp only [funs, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  all_goals and_intros <;> fun_prop

/-- Every function of the real span of the basis is smooth. -/
theorem contDiff_of_mem_span_basisList (rs : List (CharRoot × ℕ)) {y : ℝ → ℝ}
    (hmem : y ∈ span ℝ {f | f ∈ basisList rs}) : ContDiff ℝ ∞ y := by
  induction hmem using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨e, -, j, -, hfe⟩ := mem_basisList.mp hf
    exact e.1.contDiff_funs j f hfe
  | zero => exact contDiff_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact hf.const_smul c

/-- Every function of the real span of the basis solves `∑ aₖ y⁽ᵏ⁾ = 0`, whether or not the
roots are distinct. -/
theorem rLop_eq_zero_of_mem_span (rs : List (CharRoot × ℕ)) (hv : ∀ e ∈ rs, e.1.Valid)
    {y : ℝ → ℝ} (hmem : y ∈ span ℝ {f | f ∈ basisList rs}) :
    ∀ x, rLop (degQ rs) (fun k ↦ (charQ rs k : ℝ)) y x = 0 :=
  (rLop_eq_zero_iff_mem_rootSpan rs hv
      ((contDiff_of_mem_span_basisList rs hmem).of_le (by exact_mod_cast le_top))).mpr
    (ofReal_mem_rootSpan_of_mem_span rs y hmem)

/-- `∏ (X - μᵢ)` is monic: its coefficient `charC ls ls.length` of degree `ls.length` is `1`. -/
theorem charC_length : ∀ ls : List ℂ, charC ls ls.length = 1
  | [] => by simp [charC]
  | μ :: rest => by
    simp only [List.length_cons, charC, mulRoot]
    rw [charC_length rest, charC_eq_zero rest (by omega)]
    ring

/-- The characteristic polynomial is monic. -/
theorem charQ_degQ (rs : List (CharRoot × ℕ)) (hv : ∀ e ∈ rs, e.1.Valid) :
    charQ rs (degQ rs) = 1 := by
  have h := charC_cList rs hv (degQ rs)
  rw [← length_cList, charC_length, length_cList] at h
  exact_mod_cast h.symm

/-- The real solutions of `∑ aₖ y⁽ᵏ⁾ = 0` for the coefficients of `∏ ρᵏ` with distinct roots,
among the functions whose derivatives below the order are differentiable. -/
theorem rLop_eq_zero_iff (rs : List (CharRoot × ℕ)) (hv : ∀ e ∈ rs, e.1.Valid)
    (hnd : (allRoots rs).Nodup) {y : ℝ → ℝ}
    (hy : ∀ k < degQ rs, Differentiable ℝ (iteratedDeriv k y)) :
    (∀ x, rLop (degQ rs) (fun k ↦ (charQ rs k : ℝ)) y x = 0) ↔
      y ∈ span ℝ {f | f ∈ basisList rs} := by
  refine ⟨fun hL ↦ ?_, fun hmem ↦ rLop_eq_zero_of_mem_span rs hv hmem⟩
  have hmem := (rLop_eq_zero_iff_mem_rootSpan rs hv
    (contDiff_of_rLop (by exact_mod_cast charQ_degQ rs hv) hy continuous_const hL)).mp hL
  set z : ℝ → ℂ := fun x ↦ (y x : ℂ) with hz
  set S := span ℝ {f | f ∈ basisList rs}
  have hsub : ∀ e ∈ rs, ∀ j < e.2, span ℝ {f | f ∈ e.1.funs j} ≤ S := fun e he j hj ↦
    span_mono fun f hf ↦ mem_basisList.mpr ⟨e, he, j, hj, hf⟩
  -- Every element of the complex span is `h₁ + i h₂` with `h₁, h₂` in the real span.
  have key : ∀ g ∈ span ℂ (rootBasis (cList rs)),
      ∃ h₁ ∈ S, ∃ h₂ ∈ S, ∀ x, g x = (h₁ x : ℂ) + I * (h₂ x : ℂ) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨μ, j, hj, rfl⟩ := hg
      have hpos : 0 < (cList rs).count μ := by omega
      obtain ⟨e, he, hμ⟩ := mem_of_mem_cList (List.count_pos_iff.mp hpos)
      have hk := count_cList_of_mem hnd he hμ
      obtain ⟨h₁, hh₁, h₂, hh₂, hx⟩ := cMono_eq_of_mem_roots hμ j
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

/-- `g` lies in the real span of the entries of `φ :: L` if and only if, for some real `c`,
`x ↦ g x - c * φ x` lies in the real span of the entries of `L`. -/
theorem mem_span_cons_iff {α : Type*} {φ : α → ℝ} {L : List (α → ℝ)} {g : α → ℝ} :
    g ∈ span ℝ {f | f ∈ φ :: L} ↔ ∃ c : ℝ, (fun x ↦ g x - c * φ x) ∈ span ℝ {f | f ∈ L} := by
  rw [show {f | f ∈ φ :: L} = insert φ {f | f ∈ L} from Set.ext fun _ ↦ by simp,
    mem_span_insert]
  constructor
  · rintro ⟨a, z, hz, rfl⟩
    refine ⟨a, ?_⟩
    convert hz using 1
    exact funext fun x ↦ by simp
  · rintro ⟨c, hc⟩
    exact ⟨c, _, hc, funext fun x ↦ by simp⟩

/-- `g` lies in the real span of the entries of the empty list if and only if `g x = 0` for every
`x`. This restates `Submodule.span_empty` and `Submodule.mem_bot` with `funext_iff`; it is kept
because the proofs generated by `#cas [dsolve y x]` and `#cas [rsolve a n]` (Command/DSolveOrder,
DSolveRoot and RSolve) name it with `mem_span_cons_iff` in their `simp only` set. -/
theorem mem_span_nil_iff {α : Type*} {g : α → ℝ} :
    g ∈ span ℝ {f | f ∈ ([] : List (α → ℝ))} ↔ ∀ x, g x = 0 := by
  simp [funext_iff]

/-! ## Forcing and uniqueness -/

/-- For `y` and `Y` of class `Cⁿ`, `rLop n a` maps `x ↦ y x - Y x` to the difference of the
values: `rLop n a y x - rLop n a Y x`. -/
theorem rLop_sub {n : ℕ} {a : ℕ → ℝ} {y Y : ℝ → ℝ} (hy : ContDiff ℝ n y) (hY : ContDiff ℝ n Y)
    (x : ℝ) : rLop n a (fun x ↦ y x - Y x) x = rLop n a y x - rLop n a Y x := by
  simp only [rLop, ← sum_sub_distrib, ← mul_sub]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk' : (k : ℕ∞ω) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [iteratedDeriv_fun_sub ((hy.of_le hk').contDiffAt) ((hY.of_le hk').contDiffAt)]

/-- For `y` and `Y` of class `Cⁿ`, `rLop n a` maps `x ↦ y x + Y x` to the sum of the values:
`rLop n a y x + rLop n a Y x`. -/
theorem rLop_add {n : ℕ} {a : ℕ → ℝ} {y Y : ℝ → ℝ} (hy : ContDiff ℝ n y) (hY : ContDiff ℝ n Y)
    (x : ℝ) : rLop n a (fun x ↦ y x + Y x) x = rLop n a y x + rLop n a Y x := by
  simp only [rLop, ← sum_add_distrib, ← mul_add]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk' : (k : ℕ∞ω) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [iteratedDeriv_fun_add ((hy.of_le hk').contDiffAt) ((hY.of_le hk').contDiffAt)]

/-- `rLop n a` commutes with translation: for every `y`, `x₀` and `x`, its value on
`x ↦ y (x - x₀)` at `x` is its value on `y` at `x - x₀`. -/
theorem rLop_comp_sub (n : ℕ) (a : ℕ → ℝ) (y : ℝ → ℝ) (x₀ x : ℝ) :
    rLop n a (fun x ↦ y (x - x₀)) x = rLop n a y (x - x₀) := by
  simp only [rLop, iteratedDeriv_comp_sub_const]

/-- A solution of the homogeneous equation with vanishing initial values vanishes, by
uniqueness for the first-order system of `(y, y', …, y⁽ⁿ⁻¹⁾)`. -/
theorem eq_zero_of_rLop {n : ℕ} {a : ℕ → ℝ} (ha : a n = 1) {w : ℝ → ℝ} (hw : ContDiff ℝ n w)
    (hL : ∀ x, rLop n a w x = 0) {x₀ : ℝ} (h0 : ∀ k < n, iteratedDeriv k w x₀ = 0) :
    ∀ x, w x = 0 := by
  obtain _ | m := n
  · intro x
    simpa [rLop, ha] using hL x
  let V : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) := LinearMap.pi fun i ↦
    if h : i.val < m then LinearMap.proj ⟨i.val + 1, by omega⟩
    else -∑ j : Fin (m + 1), a j • LinearMap.proj j
  let Vc : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) := LinearMap.toContinuousLinearMap V
  have hlip : ∀ _t : ℝ, LipschitzOnWith ‖Vc‖₊ (fun Z ↦ Vc Z) Set.univ :=
    fun _ ↦ Vc.lipschitzWith.lipschitzOnWith
  let Y : ℝ → (Fin (m + 1) → ℝ) := fun t i ↦ iteratedDeriv i w t
  have hY (t : ℝ) : HasDerivAt Y (Vc (Y t)) t ∧ Y t ∈ Set.univ := by
    refine ⟨hasDerivAt_pi.mpr fun i ↦ ?_, trivial⟩
    have hd := (hw.differentiable_iteratedDeriv i (by exact_mod_cast i.2) t).hasDerivAt
    rw [← iteratedDeriv_succ] at hd
    convert hd using 1
    simp only [Vc, LinearMap.coe_toContinuousLinearMap', V, LinearMap.pi_apply, Y]
    split_ifs with h
    · rfl
    · have h1 := hL t
      rw [rLop, sum_range_succ, ha, one_mul] at h1
      simp only [LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.proj_apply, smul_eq_mul]
      rw [show i.val = m by omega, Fin.sum_univ_eq_sum_range (fun j ↦ a j * iteratedDeriv j w t)]
      linarith
  have hZ (t : ℝ) : HasDerivAt (fun _ ↦ (0 : Fin (m + 1) → ℝ)) (Vc 0) t ∧
      (0 : Fin (m + 1) → ℝ) ∈ Set.univ :=
    ⟨(map_zero Vc).symm ▸ hasDerivAt_const t _, trivial⟩
  have hsol := ODE_solution_unique_univ (v := fun _ Z ↦ Vc Z) (s := fun _ ↦ Set.univ)
    hlip hY hZ (funext fun i ↦ h0 i i.2)
  exact fun x ↦ by simpa [Y] using congrFun (congrFun hsol x) 0

/-- The initial-value problem: `Y` solves it, so it is the only solution among the functions
whose derivatives below the order are differentiable. -/
theorem ivp_iff {n : ℕ} {a : ℕ → ℝ} (ha : a n = 1) {Y F : ℝ → ℝ} (hY : ContDiff ℝ n Y)
    (hLY : ∀ x, rLop n a Y x = F x) (x₀ : ℝ) {y : ℝ → ℝ}
    (hy : ∀ k < n, Differentiable ℝ (iteratedDeriv k y)) :
    ((∀ x, rLop n a y x = F x) ∧ ∀ k < n, iteratedDeriv k y x₀ = iteratedDeriv k Y x₀) ↔
      ∀ x, y x = Y x := by
  constructor
  · rintro ⟨hL, h0⟩
    have hy' : ContDiff ℝ n y := contDiff_of_rLop ha hy (funext hLY ▸ continuous_rLop a hY) hL
    have hw := eq_zero_of_rLop ha (hy'.sub hY) (fun x ↦ by
      rw [rLop_sub hy' hY, hL, hLY, sub_self])
      (x₀ := x₀) (fun k hk ↦ by
        have hk' : (k : ℕ∞ω) ≤ n := by exact_mod_cast hk.le
        rw [iteratedDeriv_fun_sub ((hy'.of_le hk').contDiffAt) ((hY.of_le hk').contDiffAt),
          h0 k hk, sub_self])
    exact fun x ↦ sub_eq_zero.mp (hw x)
  · intro h
    obtain rfl : y = Y := funext h
    exact ⟨hLY, fun _ _ ↦ rfl⟩

/-! ## Coefficient lists -/

/-- For `k ≤ d`, entry `k` (default `0`) of `(List.range (d + 1)).map f` is `f k`. -/
theorem getD_range_map (f : ℕ → ℚ) {d k : ℕ} (hk : k ≤ d) :
    ((List.range (d + 1)).map f).getD k 0 = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

/-- The general solution of `∑ aₖ y⁽ᵏ⁾ = F` for a characteristic polynomial given by its roots,
with a particular solution `Yp`, among the functions whose derivatives below the order are
differentiable. -/
theorem general_iff (rs : List (CharRoot × ℕ)) (hv : ∀ e ∈ rs, e.1.Valid) {p : ℕ}
    (hsep : separated rs p = true) (a : List ℚ)
    (hc : (List.range (degQ rs + 1)).map (charQ rs) = a) {Yp F : ℝ → ℝ}
    (hYp : ContDiff ℝ (degQ rs) Yp)
    (hpart : ∀ x, rLop (degQ rs) (fun k ↦ (a.getD k 0 : ℝ)) Yp x = F x) {y : ℝ → ℝ}
    (hy : ∀ k < degQ rs, Differentiable ℝ (iteratedDeriv k y)) :
    (∀ x, rLop (degQ rs) (fun k ↦ (a.getD k 0 : ℝ)) y x = F x) ↔
      (fun x ↦ y x - Yp x) ∈ span ℝ {f | f ∈ basisList rs} := by
  have hcoef : ∀ x g, rLop (degQ rs) (fun k ↦ (a.getD k 0 : ℝ)) g x =
      rLop (degQ rs) (fun k ↦ (charQ rs k : ℝ)) g x := by
    intro x g
    refine sum_congr rfl fun k hk ↦ ?_
    simp only [← hc, getD_range_map _ (Nat.lt_succ_iff.mp (mem_range.mp hk))]
  have ha : a.getD (degQ rs) 0 = 1 := by rw [← hc, getD_range_map _ le_rfl, charQ_degQ rs hv]
  have key (hy' : ContDiff ℝ (degQ rs) y) :
      (∀ x, rLop (degQ rs) (fun k ↦ (a.getD k 0 : ℝ)) y x = F x) ↔
        (fun x ↦ y x - Yp x) ∈ span ℝ {f | f ∈ basisList rs} := by
    rw [← rLop_eq_zero_iff rs hv (nodup_of_separated hsep)
      fun k hk ↦ (hy'.sub hYp).differentiable_iteratedDeriv k (by exact_mod_cast hk)]
    simp only [← hcoef]
    exact forall_congr' fun x ↦ by rw [rLop_sub hy' hYp, hpart, sub_eq_zero]
  refine ⟨fun hL ↦ (key (contDiff_of_rLop (by exact_mod_cast ha) hy
    (funext hpart ▸ continuous_rLop _ hYp) hL)).mp hL, fun hmem ↦ (key ?_).mpr hmem⟩
  simpa using ((contDiff_of_mem_span_basisList rs hmem).of_le
    (by exact_mod_cast le_top)).add hYp

/-! ## Initial values -/

namespace CharRoot

/-- Solutions with rational derivatives at `0`, spanning the same space as `funs`:
`xʲ e ^ (r x)`, `xʲ e ^ (α x) cosh (c √m x)`, `xʲ e ^ (α x) sinh (c √m x) / (c √m)`,
`xʲ e ^ (α x) cos (c √m x)` and `xʲ e ^ (α x) sin (c √m x) / (c √m)`. -/
noncomputable def ivpFuns : CharRoot → ℕ → List (ℝ → ℝ)
  | real r, j => [fun x ↦ x ^ j * Real.exp (r * x)]
  | realPair α c m, j => [fun x ↦ x ^ j * (Real.exp (α * x) * Real.cosh (width c m * x)),
      fun x ↦ x ^ j * (Real.exp (α * x) * (Real.sinh (width c m * x) / width c m))]
  | pair α c m, j => [fun x ↦ x ^ j * (Real.exp (α * x) * Real.cos (width c m * x)),
      fun x ↦ x ^ j * (Real.exp (α * x) * (Real.sin (width c m * x) / width c m))]

/-- `(u, v) ↦ (α u + v, κ u + α v)`. -/
def step (α κ : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (α * p.1 + p.2, κ * p.1 + α * p.2)

/-- The values computed for the `k`-th derivatives at `0` of the functions in `ivpFuns ρ j`:
`k.descFactorial j` times `r ^ (k - j)` for a rational root, and for a pair `k.descFactorial j`
times the first components of the `(k - j)`-th iterates from `(1, 0)` and from `(0, 1)` of
`step α (c ^ 2 * m)` (real pair) or `step α (-(c ^ 2 * m))` (complex pair). They are these
derivatives when `ρ.Valid` (`CharRoot.forall₂_ivpVals`). -/
def ivpVals : CharRoot → ℕ → ℕ → List ℚ
  | real r, j, k => [(k.descFactorial j : ℚ) * r ^ (k - j)]
  | realPair α c m, j, k =>
      [(k.descFactorial j : ℚ) * ((step α (c ^ 2 * m))^[k - j] (1, 0)).1,
        (k.descFactorial j : ℚ) * ((step α (c ^ 2 * m))^[k - j] (0, 1)).1]
  | pair α c m, j, k =>
      [(k.descFactorial j : ℚ) * ((step α (-(c ^ 2 * m)))^[k - j] (1, 0)).1,
        (k.descFactorial j : ℚ) * ((step α (-(c ^ 2 * m)))^[k - j] (0, 1)).1]

end CharRoot

/-- `(u, v) ↦ (α u + v, κ u + α v)` over `ℝ`. -/
def stepR (α κ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (α * p.1 + p.2, κ * p.1 + α * p.2)

/-- Both components of the `i`-th iterate of the rational `CharRoot.step α κ` from `(u, v)`, cast
to `ℝ`, are the components of the `i`-th iterate of `stepR α κ` from the cast pair. -/
theorem iterate_step_cast (α κ : ℚ) : ∀ (i : ℕ) (u v : ℚ),
    ((((CharRoot.step α κ)^[i] (u, v)).1 : ℚ) : ℝ) = ((stepR α κ)^[i] (u, v)).1 ∧
      ((((CharRoot.step α κ)^[i] (u, v)).2 : ℚ) : ℝ) = ((stepR α κ)^[i] (u, v)).2
  | 0, u, v => by simp
  | i + 1, u, v => by
    simpa [Function.iterate_succ_apply, CharRoot.step, stepR] using
      iterate_step_cast α κ i (α * u + v) (κ * u + α * v)

/-- The derivatives of `u P + v Q` when `P' = α P + κ Q` and `Q' = P + α Q`. -/
theorem iteratedDeriv_pq {P Q : ℝ → ℝ} {α κ : ℝ} (hP : ∀ x, HasDerivAt P (α * P x + κ * Q x) x)
    (hQ : ∀ x, HasDerivAt Q (P x + α * Q x) x) : ∀ (i : ℕ) (u v : ℝ),
    iteratedDeriv i (fun x ↦ u * P x + v * Q x) =
      fun x ↦ ((stepR α κ)^[i] (u, v)).1 * P x + ((stepR α κ)^[i] (u, v)).2 * Q x
  | 0, u, v => by simp
  | i + 1, u, v => by
    rw [iteratedDeriv_succ']
    have hd : deriv (fun x ↦ u * P x + v * Q x) =
        fun x ↦ (α * u + v) * P x + (κ * u + α * v) * Q x := by
      funext x
      rw [(((hP x).const_mul u).fun_add ((hQ x).const_mul v)).deriv]
      ring
    rw [hd, iteratedDeriv_pq hP hQ i, Function.iterate_succ_apply]
    rfl

/-- For smooth `g`, the `k`-th derivative of `x ↦ x ^ j * g x` at `0` is
`k.descFactorial j * iteratedDeriv (k - j) g 0`, which is `0` for `k < j`. -/
theorem iteratedDeriv_pow_mul_zero {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (j k : ℕ) :
    iteratedDeriv k (fun x ↦ x ^ j * g x) 0 = k.descFactorial j * iteratedDeriv (k - j) g 0 := by
  have hpow : ContDiffAt ℝ k (fun x : ℝ ↦ x ^ j) 0 := (contDiff_id.pow j).contDiffAt
  have hgk : ContDiffAt ℝ k g 0 := (hg.of_le (by exact_mod_cast le_top)).contDiffAt
  rw [show (fun x ↦ x ^ j * g x) = (fun x : ℝ ↦ x ^ j) * g from rfl,
    iteratedDeriv_mul hpow hgk]
  simp only [iteratedDeriv_fun_pow_zero, Nat.cast_ite, Nat.cast_zero, mul_ite, ite_mul,
    mul_zero, zero_mul, sum_ite_eq', mem_range]
  split_ifs with hjk
  · rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

/-- The `i`-th derivative of `x ↦ e ^ (r x)` is `x ↦ r ^ i e ^ (r x)`. -/
theorem iteratedDeriv_exp_mul (r : ℝ) : ∀ i : ℕ,
    iteratedDeriv i (fun x ↦ Real.exp (r * x)) = fun x ↦ r ^ i * Real.exp (r * x)
  | 0 => by simp
  | i + 1 => by
    rw [iteratedDeriv_succ, iteratedDeriv_exp_mul r i]
    funext x
    have := ((((hasDerivAt_id' x).const_mul r).exp).const_mul (r ^ i))
    rw [this.deriv]
    ring

/-- For all real `α`, `w` and `x`, the function `x ↦ e ^ (α x) cosh (w x)` has derivative
`α e ^ (α x) cosh (w x) + w ^ 2 e ^ (α x) sinh (w x) / w` at `x`. -/
theorem hasDerivAt_cosh_pair (α w x : ℝ) :
    HasDerivAt (fun x ↦ Real.exp (α * x) * Real.cosh (w * x))
      (α * (Real.exp (α * x) * Real.cosh (w * x)) +
        w ^ 2 * (Real.exp (α * x) * (Real.sinh (w * x) / w))) x := by
  have h1 := ((hasDerivAt_id' x).const_mul α).exp
  have h2 := ((hasDerivAt_id' x).const_mul w).cosh
  exact (h1.mul h2).congr_deriv (by field_simp)

/-- For `w ≠ 0`, the function `x ↦ e ^ (α x) sinh (w x) / w` has derivative
`e ^ (α x) cosh (w x) + α e ^ (α x) sinh (w x) / w` at every `x`. -/
theorem hasDerivAt_sinh_pair (α w : ℝ) (hw : w ≠ 0) (x : ℝ) :
    HasDerivAt (fun x ↦ Real.exp (α * x) * (Real.sinh (w * x) / w))
      (Real.exp (α * x) * Real.cosh (w * x) +
        α * (Real.exp (α * x) * (Real.sinh (w * x) / w))) x := by
  have h1 := ((hasDerivAt_id' x).const_mul α).exp
  have h2 := (((hasDerivAt_id' x).const_mul w).sinh).div_const w
  exact (h1.mul h2).congr_deriv (by field_simp; ring)

/-- For all real `α`, `w` and `x`, the function `x ↦ e ^ (α x) cos (w x)` has derivative
`α e ^ (α x) cos (w x) - w ^ 2 e ^ (α x) sin (w x) / w` at `x`. -/
theorem hasDerivAt_cos_pair (α w x : ℝ) :
    HasDerivAt (fun x ↦ Real.exp (α * x) * Real.cos (w * x))
      (α * (Real.exp (α * x) * Real.cos (w * x)) +
        -w ^ 2 * (Real.exp (α * x) * (Real.sin (w * x) / w))) x := by
  have h1 := ((hasDerivAt_id' x).const_mul α).exp
  have h2 := ((hasDerivAt_id' x).const_mul w).cos
  exact (h1.mul h2).congr_deriv (by field_simp)

/-- For `w ≠ 0`, the function `x ↦ e ^ (α x) sin (w x) / w` has derivative
`e ^ (α x) cos (w x) + α e ^ (α x) sin (w x) / w` at every `x`. -/
theorem hasDerivAt_sin_pair (α w : ℝ) (hw : w ≠ 0) (x : ℝ) :
    HasDerivAt (fun x ↦ Real.exp (α * x) * (Real.sin (w * x) / w))
      (Real.exp (α * x) * Real.cos (w * x) +
        α * (Real.exp (α * x) * (Real.sin (w * x) / w))) x := by
  have h1 := ((hasDerivAt_id' x).const_mul α).exp
  have h2 := (((hasDerivAt_id' x).const_mul w).sin).div_const w
  exact (h1.mul h2).congr_deriv (by field_simp; ring)

/-- If `P' = α P + κ Q` and `Q' = P + α Q` everywhere, `P 0 = 1` and `Q 0 = 0`, the `i`-th
derivatives of `P` and `Q` at `0` are the first components of the `i`-th iterates of
`stepR α κ` from `(1, 0)` and from `(0, 1)`. -/
theorem iteratedDeriv_pq_zero {P Q : ℝ → ℝ} {α κ : ℝ}
    (hP : ∀ x, HasDerivAt P (α * P x + κ * Q x) x) (hQ : ∀ x, HasDerivAt Q (P x + α * Q x) x)
    (hP0 : P 0 = 1) (hQ0 : Q 0 = 0) (i : ℕ) :
    iteratedDeriv i P 0 = ((stepR α κ)^[i] (1, 0)).1 ∧
      iteratedDeriv i Q 0 = ((stepR α κ)^[i] (0, 1)).1 := by
  exact ⟨by simpa [hP0, hQ0] using congrFun (iteratedDeriv_pq hP hQ i 1 0) 0,
    by simpa [hP0, hQ0] using congrFun (iteratedDeriv_pq hP hQ i 0 1) 0⟩

/-- Every function in `ρ.ivpFuns j` is smooth. -/
theorem CharRoot.contDiff_ivpFuns (ρ : CharRoot) (j : ℕ) :
    ∀ f ∈ ρ.ivpFuns j, ContDiff ℝ ∞ f := by
  cases ρ <;> simp only [ivpFuns, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  all_goals and_intros <;> fun_prop

/-- For a factor with `ρ.Valid` and all `j`, `k`, the `k`-th derivative at `0` of each function
of `ρ.ivpFuns j` is the cast of the rational at the same position of `ρ.ivpVals j k`. -/
theorem CharRoot.forall₂_ivpVals (ρ : CharRoot) (hρ : ρ.Valid) (j k : ℕ) :
    List.Forall₂ (fun f v ↦ iteratedDeriv k f 0 = ((v : ℚ) : ℝ)) (ρ.ivpFuns j) (ρ.ivpVals j k) := by
  cases ρ with
  | real r =>
    simp only [ivpFuns, ivpVals, List.forall₂_cons, List.Forall₂.nil, and_true]
    rw [iteratedDeriv_pow_mul_zero (by fun_prop), iteratedDeriv_exp_mul]
    push_cast
    simp
  | realPair α c m =>
    have hw := width_sq (c := c) hρ.2.le
    have hP : ∀ x, HasDerivAt (fun x ↦ Real.exp (α * x) * Real.cosh (width c m * x))
        (α * (Real.exp (α * x) * Real.cosh (width c m * x)) +
          ((c ^ 2 * m : ℚ) : ℝ) * (Real.exp (α * x) * (Real.sinh (width c m * x) / width c m)))
        x := fun x ↦ by rw [← hw]; exact hasDerivAt_cosh_pair _ _ x
    have hQ := hasDerivAt_sinh_pair (α : ℝ) (width c m)
      (mul_ne_zero (by exact_mod_cast hρ.1) (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hρ.2)))
    have h := fun i ↦ iteratedDeriv_pq_zero hP hQ (by simp) (by simp) i
    simp only [ivpFuns, ivpVals, List.forall₂_cons, List.Forall₂.nil, and_true]
    rw [iteratedDeriv_pow_mul_zero (by fun_prop), iteratedDeriv_pow_mul_zero (by fun_prop),
      (h _).1, (h _).2]
    push_cast
    rw [(iterate_step_cast _ _ _ _ _).1, (iterate_step_cast _ _ _ _ _).1]
    push_cast
    exact ⟨rfl, rfl⟩
  | pair α c m =>
    have hw := width_sq (c := c) hρ.2.le
    have hP : ∀ x, HasDerivAt (fun x ↦ Real.exp (α * x) * Real.cos (width c m * x))
        (α * (Real.exp (α * x) * Real.cos (width c m * x)) +
          ((-(c ^ 2 * m) : ℚ) : ℝ) * (Real.exp (α * x) * (Real.sin (width c m * x) / width c m)))
        x := fun x ↦ by
      rw [Rat.cast_neg, ← hw]
      exact hasDerivAt_cos_pair _ _ x
    have hQ := hasDerivAt_sin_pair (α : ℝ) (width c m)
      (mul_ne_zero (by exact_mod_cast hρ.1.ne') (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hρ.2)))
    have h := fun i ↦ iteratedDeriv_pq_zero hP hQ (by simp) (by simp) i
    simp only [ivpFuns, ivpVals, List.forall₂_cons, List.Forall₂.nil, and_true]
    rw [iteratedDeriv_pow_mul_zero (by fun_prop), iteratedDeriv_pow_mul_zero (by fun_prop),
      (h _).1, (h _).2]
    push_cast
    rw [(iterate_step_cast _ _ _ _ _).1, (iterate_step_cast _ _ _ _ _).1]
    push_cast
    exact ⟨rfl, rfl⟩

/-- Every function in `ρ.ivpFuns j` lies in the real span of the functions of `ρ.funs j`. -/
theorem CharRoot.ivpFuns_mem_span (ρ : CharRoot) (j : ℕ) :
    ∀ f ∈ ρ.ivpFuns j, f ∈ span ℝ {g | g ∈ ρ.funs j} := by
  cases ρ with
  | real r =>
    simp only [ivpFuns, List.mem_singleton, forall_eq]
    exact subset_span (by simp [funs])
  | realPair α c m =>
    have h₁ : (fun x : ℝ ↦ x ^ j * Real.exp ((α + width c m) * x)) ∈
        span ℝ {g | g ∈ (realPair α c m).funs j} := subset_span (by simp [funs])
    have h₂ : (fun x : ℝ ↦ x ^ j * Real.exp ((α - width c m) * x)) ∈
        span ℝ {g | g ∈ (realPair α c m).funs j} := subset_span (by simp [funs])
    simp only [ivpFuns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    constructor
    · convert add_mem (smul_mem _ (1 / 2 : ℝ) h₁) (smul_mem _ (1 / 2 : ℝ) h₂) using 1
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, sub_mul, Real.exp_add,
        Real.exp_sub, Real.cosh_eq, Real.exp_neg]
      ring
    · convert sub_mem (smul_mem _ (1 / (2 * width c m)) h₁)
        (smul_mem _ (1 / (2 * width c m)) h₂) using 1
      funext x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, add_mul, sub_mul, Real.exp_add,
        Real.exp_sub, Real.sinh_eq, Real.exp_neg]
      ring
  | pair α c m =>
    have h₁ : (fun x : ℝ ↦ x ^ j * Real.exp (α * x) * Real.cos (width c m * x)) ∈
        span ℝ {g | g ∈ (pair α c m).funs j} := subset_span (by simp [funs])
    have h₂ : (fun x : ℝ ↦ x ^ j * Real.exp (α * x) * Real.sin (width c m * x)) ∈
        span ℝ {g | g ∈ (pair α c m).funs j} := subset_span (by simp [funs])
    simp only [ivpFuns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    constructor
    · convert h₁ using 1
      funext x
      ring
    · convert smul_mem _ (1 / width c m) h₂ using 1
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring

/-- The solutions with rational initial values, factor by factor. -/
noncomputable def ivpList : List (CharRoot × ℕ) → List (ℝ → ℝ)
  | [] => []
  | (ρ, k) :: rest => (List.range k).flatMap ρ.ivpFuns ++ ivpList rest

/-- Their `k`-th derivatives at `0`. -/
def ivpValues : List (CharRoot × ℕ) → ℕ → List ℚ
  | [], _ => []
  | (ρ, m) :: rest, k => (List.range m).flatMap (fun j ↦ ρ.ivpVals j k) ++ ivpValues rest k

/-- `∑ cᵢ fᵢ`. -/
noncomputable def comb (fs : List (ℝ → ℝ)) (cs : List ℚ) (x : ℝ) : ℝ :=
  (List.zipWith (fun f c ↦ (c : ℝ) * f x) fs cs).sum

/-- If `R` relates `f a` and `g a` position by position for every `a ∈ l`, it relates
`l.flatMap f` and `l.flatMap g` position by position. -/
theorem forall₂_flatMap {α β γ : Type*} {R : α → β → Prop} (l : List γ) (f : γ → List α)
    (g : γ → List β) (h : ∀ a ∈ l, List.Forall₂ R (f a) (g a)) :
    List.Forall₂ R (l.flatMap f) (l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact List.rel_append (h a (by simp)) (ih fun b hb ↦ h b (by simp [hb]))

/-- When every factor of `rs` is `Valid`, the `k`-th derivative at `0` of each function of
`ivpList rs` is the cast of the rational at the same position of `ivpValues rs k`. -/
theorem forall₂_ivpValues (k : ℕ) : ∀ (rs : List (CharRoot × ℕ)), (∀ e ∈ rs, e.1.Valid) →
    List.Forall₂ (fun f v ↦ iteratedDeriv k f 0 = ((v : ℚ) : ℝ)) (ivpList rs) (ivpValues rs k)
  | [], _ => by simp [ivpList, ivpValues]
  | (ρ, m) :: rest, hv => by
    simp only [ivpList, ivpValues]
    exact List.rel_append
      (forall₂_flatMap _ _ _ fun j _ ↦ ρ.forall₂_ivpVals (hv (ρ, m) (by simp)) j k)
      (forall₂_ivpValues k rest fun e he ↦ hv e (by simp [he]))

/-- Every function in `ivpList rs` is smooth. -/
theorem contDiff_ivpList : ∀ (rs : List (CharRoot × ℕ)), ∀ f ∈ ivpList rs, ContDiff ℝ ∞ f
  | [] => by simp [ivpList]
  | (ρ, m) :: rest => by
    intro f hf
    simp only [ivpList, List.mem_append, List.mem_flatMap] at hf
    rcases hf with ⟨j, -, hj⟩ | hf
    · exact ρ.contDiff_ivpFuns j f hj
    · exact contDiff_ivpList rest f hf

/-- Every function in `ivpList rs` lies in the real span of the functions of `basisList rs`. -/
theorem ivpList_mem_span : ∀ (rs : List (CharRoot × ℕ)),
    ∀ f ∈ ivpList rs, f ∈ span ℝ {g | g ∈ basisList rs}
  | [] => by simp [ivpList]
  | (ρ, m) :: rest => by
    intro f hf
    simp only [ivpList, List.mem_append, List.mem_flatMap, List.mem_range] at hf
    rcases hf with ⟨j, hj, hfj⟩ | hf
    · exact span_mono (fun g hg ↦ mem_basisList.mpr ⟨(ρ, m), by simp, j, hj, hg⟩)
        (ρ.ivpFuns_mem_span j f hfj)
    · exact span_mono (fun g hg ↦ by
        obtain ⟨e, he, j, hj, hge⟩ := mem_basisList.mp hg
        exact mem_basisList.mpr ⟨e, by simp [he], j, hj, hge⟩) (ivpList_mem_span rest f hf)

/-- If every function of `fs` lies in the real span of `S`, so does `comb fs cs`, for every list
`cs` of rational coefficients. -/
theorem comb_mem_span {S : Set (ℝ → ℝ)} : ∀ (fs : List (ℝ → ℝ)) (cs : List ℚ),
    (∀ f ∈ fs, f ∈ span ℝ S) → comb fs cs ∈ span ℝ S
  | [], _, _ | _ :: _, [], _ => by
    convert zero_mem (span ℝ S) using 1
    funext x
    simp [comb]
  | f :: fs, c :: cs, h => by
    convert add_mem (smul_mem _ (c : ℝ) (h f (by simp)))
      (comb_mem_span fs cs fun g hg ↦ h g (by simp [hg])) using 1
    funext x
    simp [comb]

/-- If every function of `fs` is smooth, so is `comb fs cs`. -/
theorem contDiff_comb : ∀ (fs : List (ℝ → ℝ)) (cs : List ℚ), (∀ f ∈ fs, ContDiff ℝ ∞ f) →
    ContDiff ℝ ∞ (comb fs cs)
  | [], _, _ | _ :: _, [], _ => by
    convert (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ ↦ (0 : ℝ)) using 1
    funext x
    simp [comb]
  | f :: fs, c :: cs, h => by
    have e : comb (f :: fs) (c :: cs) = fun x ↦ (c : ℝ) * f x + comb fs cs x := by
      funext x
      simp [comb]
    rw [e]
    exact (contDiff_const.mul (h f (by simp))).add
      (contDiff_comb fs cs fun g hg ↦ h g (by simp [hg]))

/-- For smooth functions `fs` whose `k`-th derivatives at `0` are the casts of `vs`, position by
position, the `k`-th derivative of `comb fs cs` at `0` is the cast of
`(List.zipWith (· * ·) vs cs).sum`. -/
theorem iteratedDeriv_comb_zero (k : ℕ) : ∀ {fs : List (ℝ → ℝ)} {vs : List ℚ} (cs : List ℚ),
    (∀ f ∈ fs, ContDiff ℝ ∞ f) →
    List.Forall₂ (fun f v ↦ iteratedDeriv k f 0 = ((v : ℚ) : ℝ)) fs vs →
      iteratedDeriv k (comb fs cs) 0 = (((List.zipWith (· * ·) vs cs).sum : ℚ) : ℝ)
  | [], [], cs, _, _ => by
    have : comb [] cs = fun _ ↦ 0 := by funext x; simp [comb]
    rw [this]
    simp
  | f :: fs, v :: vs, [], _, _ => by
    have : comb (f :: fs) [] = fun _ ↦ 0 := by funext x; simp [comb]
    rw [this]
    simp
  | f :: fs, v :: vs, c :: cs, hs, List.Forall₂.cons hfv hrest => by
    have e : comb (f :: fs) (c :: cs) = fun x ↦ (c : ℝ) * f x + comb fs cs x := by
      funext x
      simp [comb]
    have hf := hs f (by simp)
    have hfs := contDiff_comb fs cs fun g hg ↦ hs g (by simp [hg])
    rw [e, iteratedDeriv_fun_add ((contDiff_const.mul hf).of_le (by exact_mod_cast le_top)
      |>.contDiffAt) ((hfs.of_le (by exact_mod_cast le_top)).contDiffAt),
      iteratedDeriv_const_mul_field, hfv,
      iteratedDeriv_comb_zero k cs (fun g hg ↦ hs g (by simp [hg])) hrest]
    simp only [List.zipWith_cons_cons, List.sum_cons]
    push_cast
    ring

/-- The check of the initial values: at each order `k < v.length`, the exact value at `x₀` of
the `k`-th derivative `Yp.iteratedDiff 0 k` of the particular solution, plus the sum of the
products of `ivpValues rs k` with `cs` for the combination at `0`, equals `v.getD k 0`. The check
fails when `exactValue?` returns `none`. -/
def ivpCheck (Yp : Verified.Expr (Fin 1)) (x₀ : ℚ) (rs : List (CharRoot × ℕ))
    (cs v : List ℚ) : Bool :=
  (List.range v.length).all fun k ↦
    match Verified.Expr.exactValue? (fun _ ↦ x₀) (Yp.iteratedDiff 0 k) with
    | some b => decide (b + (List.zipWith (· * ·) (ivpValues rs k) cs).sum = v.getD k 0)
    | none => false

/-- For a `conditionFree` expression `Y`, the `k`-th derivative of `Y.univariateEval` is the
evaluation of the symbolic `k`-th derivative `Y.iteratedDiff 0 k`. -/
theorem iteratedDeriv_univariateEval {Y : Verified.Expr (Fin 1)}
    (h : Verified.Expr.conditionFree Y = true) :
    ∀ k, iteratedDeriv k Y.univariateEval = (Y.iteratedDiff 0 k).univariateEval
  | 0 => by simp
  | k + 1 => by
    rw [iteratedDeriv_succ, iteratedDeriv_univariateEval h k,
      Verified.Expr.deriv_univariateEval_of_conditionFree
        (Verified.Expr.conditionFree_iteratedDiff h k)]
    rfl

/-- The initial-value problem for a characteristic polynomial given by its roots. -/
theorem ivp_general_iff (rs : List (CharRoot × ℕ)) (hv : ∀ e ∈ rs, e.1.Valid) (a : List ℚ)
    (hc : (List.range (degQ rs + 1)).map (charQ rs) = a) {Yp : Verified.Expr (Fin 1)}
    (hcf : Verified.Expr.conditionFree Yp = true) {F : ℝ → ℝ}
    (hpart : ∀ x, rLop (degQ rs) (fun k ↦ (a.getD k 0 : ℝ)) Yp.univariateEval x = F x)
    (x₀ : ℚ) (cs v : List ℚ) (hlen : v.length = degQ rs)
    (hcheck : ivpCheck Yp x₀ rs cs v = true) {y : ℝ → ℝ}
    (hy : ∀ k < degQ rs, Differentiable ℝ (iteratedDeriv k y)) :
    ((∀ x, rLop (degQ rs) (fun k ↦ (a.getD k 0 : ℝ)) y x = F x) ∧
        ∀ k < degQ rs, iteratedDeriv k y x₀ = ((v.getD k 0 : ℚ) : ℝ)) ↔
      ∀ x, y x = Yp.univariateEval x + comb (ivpList rs) cs (x - x₀) := by
  set d := degQ rs
  set H := comb (ivpList rs) cs
  have hH : ContDiff ℝ ∞ H := contDiff_comb _ _ (contDiff_ivpList rs)
  have hHd : ContDiff ℝ d H := hH.of_le (by exact_mod_cast le_top)
  have hHs : ContDiff ℝ d (fun x ↦ H (x - x₀)) := hHd.comp (contDiff_id.sub contDiff_const)
  have hYp : ContDiff ℝ d Yp.univariateEval := Verified.Expr.contDiff_of_conditionFree hcf d
  have ha : a.getD d 0 = 1 := by rw [← hc, getD_range_map _ le_rfl, charQ_degQ rs hv]
  have hcoef : ∀ x g, rLop d (fun k ↦ (a.getD k 0 : ℝ)) g x =
      rLop d (fun k ↦ (charQ rs k : ℝ)) g x := by
    intro x g
    refine sum_congr rfl fun k hk ↦ ?_
    simp only [← hc, getD_range_map _ (Nat.lt_succ_iff.mp (mem_range.mp hk))]
  have hHL : ∀ x, rLop d (fun k ↦ (a.getD k 0 : ℝ)) H x = 0 := by
    intro x
    rw [hcoef]
    exact rLop_eq_zero_of_mem_span rs hv (comb_mem_span _ _ (ivpList_mem_span rs)) x
  have hLY : ∀ x, rLop d (fun k ↦ (a.getD k 0 : ℝ))
      (fun x ↦ Yp.univariateEval x + H (x - x₀)) x = F x := by
    intro x
    rw [rLop_add hYp hHs, hpart, rLop_comp_sub, hHL, add_zero]
  have hinit : ∀ k < d, iteratedDeriv k (fun x ↦ Yp.univariateEval x + H (x - x₀)) x₀ =
      ((v.getD k 0 : ℚ) : ℝ) := by
    intro k hk
    have hk' : (k : ℕ∞ω) ≤ d := by exact_mod_cast hk.le
    rw [iteratedDeriv_fun_add ((hYp.of_le hk').contDiffAt) ((hHs.of_le hk').contDiffAt),
      iteratedDeriv_comp_sub_const]
    simp only [sub_self]
    rw [iteratedDeriv_univariateEval hcf,
      iteratedDeriv_comb_zero k cs (contDiff_ivpList rs) (forall₂_ivpValues k rs hv)]
    have := List.all_eq_true.mp hcheck k (List.mem_range.mpr (by omega))
    split at this
    · rename_i b hb
      rw [Verified.Expr.univariateEval_eq_of_exactValue hb, ← of_decide_eq_true this]
      push_cast
      ring
    · cases this
  rw [← ivp_iff (by exact_mod_cast ha) (hYp.add hHs) hLY (x₀ : ℝ) hy]
  exact and_congr_right fun _ ↦ forall₂_congr fun k hk ↦ by rw [hinit k hk]

end CAS.LinearODE

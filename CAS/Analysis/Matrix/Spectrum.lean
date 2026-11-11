/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.LinearODERoots
public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# The spectrum of a rational matrix from a factorization of its characteristic polynomial

The characteristic polynomial of a matrix `A` with rational entries is given by its list of
coefficients `a`, lowest degree first: `A.charpoly = Polynomial.ofCoeffList a`. A list `fs` of
monic factors with multiplicities names its roots, and the Boolean `eigenCheck a fs` certifies
it. Then `spectrum_complex_of` gives the spectrum over `ℂ` of the matrix, as the set of the
roots of the factors (`factorRoots`), and the roots of its characteristic polynomial with their
algebraic multiplicities (`rootList`); `spectrum_real_of` gives the same over `ℝ` when
`eigenCheckReal` also shows every root real.
`exists_mem_spectrum_of_signChange` gives a real eigenvalue in an interval where a factor changes
sign, and `eigenspace_basis` a basis of an eigenspace from a row reduction.

## Implementation notes

A factor `EigFactor.char ρ` is a rational root or a pair of quadratic surds
(`CAS.LinearODE.CharRoot`); a factor `EigFactor.enclosed R D` is a square-free polynomial `R`
whose roots are certified by the enclosures `D` (`CAS.LinearODE.Enclosures.check`), the real roots
`AlgRoot.real R lo hi` in rational intervals and the complex roots `AlgRoot.complex R u v ρ` in
discs, with their conjugates. The factors and the enclosures are found outside the kernel
(`CAS.Command.RootSplit.split`, for `#cas [eigenvalues]`); the kernel decides `eigenCheck`,
which checks every factor and the identity `∏ fₖ ^ mₖ = a` over `ℚ`. We multiply the factors
out to `∏ (X - μ)` (`prod_rootList`) and read the spectrum through
`Matrix.mem_spectrum_iff_isRoot_charpoly` and the roots through
`Polynomial.roots_multiset_prod_X_sub_C` (`spectrum_and_roots`). For one factor,
`EigFactor.realCheck f a` checks it, that its roots are all real and that its coefficients are
`a`, and `EigFactor.splits_of_realCheck` then says that `ofCoeffList a` splits over `ℝ`.

In `eigenspace_basis` the row reduction of `M - α • 1` consists of rows `E r` with their pivot
columns and vectors `V i` with their free columns, and its identities hold up to multiples of a
scalar `c = 0`. When `α` is a root of a polynomial `q` and `c = q(α)`, they are identities between
polynomials in `α`, the same for every root of `q`, so that one proof serves all the roots. The
`V i` are independent because each is `1` at its own free column, and they span the kernel
because a kernel vector that vanishes at the free columns also vanishes at the pivot columns.
-/

@[expose] public section

open Polynomial

namespace CAS.Analysis.Matrix

open CAS.AlgRoot (polyC polyC_coeffMul polyC_coeffPow eval_polyC_ofReal)
open CAS.Polynomial (coeffEval coeffEvalRat coeffMul coeffPow eval_map_ofCoeffList)

/-- A monic factor of a characteristic polynomial: a rational root or a pair of quadratic roots
in closed form, or a square-free polynomial with certified enclosures of all its roots. -/
inductive EigFactor
  /-- A factor in closed form: `X - r` for a rational root `r`, or the monic quadratic of a pair
  `α ± c √m` or `α ± i c √m`. -/
  | char (ρ : CAS.LinearODE.CharRoot)
  /-- A polynomial `R`, lowest degree first, with enclosures `D` of its roots; `check` asks for
  `D.check R`. -/
  | enclosed (R : List ℚ) (D : CAS.LinearODE.Enclosures)

namespace EigFactor

/-- The roots of the factor, each once. -/
noncomputable def roots : EigFactor → List ℂ
  | char ρ => ρ.roots
  | enclosed R D => D.reals.map (fun I ↦ ((CAS.AlgRoot.real R I.1 I.2 : ℝ) : ℂ)) ++
      D.discs.flatMap fun d ↦ [CAS.AlgRoot.complex R d.1 d.2.1 d.2.2.1,
        (starRingEnd ℂ) (CAS.AlgRoot.complex R d.1 d.2.1 d.2.2.1)]

/-- The coefficients of the factor, lowest degree first. -/
def coeffs : EigFactor → List ℚ
  | char ρ => CAS.LinearODE.charList [(ρ, 1)]
  | enclosed R _ => R

/-- The side conditions of a closed form, the enclosure check of an enclosed factor. -/
def check : EigFactor → Bool
  | char ρ => decide ρ.Valid
  | enclosed R D => D.check R

/-- For a factor `f` that passes `f.check`, the product of the `X - μ` over its roots `f.roots`,
each once, is `polyC f.coeffs`. -/
theorem prod_roots : ∀ f : EigFactor, f.check = true →
    (f.roots.map fun μ ↦ X - C μ).prod = polyC f.coeffs
  | char ρ, h => by
    have hv : ∀ e ∈ [(ρ, 1)], (e.1 : CAS.LinearODE.CharRoot).Valid := by
      simpa [check] using h
    have := CAS.LinearODE.prod_cList [(ρ, 1)] hv
    simp only [CAS.LinearODE.cList, List.replicate_one, List.flatten_cons, List.flatten_nil,
      List.append_nil] at this
    exact this
  | enclosed R D, h => by
    have h' := CAS.LinearODE.Enclosures.prod_eq R D h
    rw [CAS.LinearODE.rrList_of_one (D.rroots R) (by
      simp only [CAS.LinearODE.Enclosures.rroots, List.forall_mem_append, List.forall_mem_map,
        implies_true, and_self]), CAS.LinearODE.Enclosures.rrAll_eq] at h'
    exact h'

/-- Whether every root of the factor is real. -/
def isReal : EigFactor → Bool
  | char (.pair ..) => false
  | char _ => true
  | enclosed _ D => D.discs.isEmpty

/-- The real roots of the factor, each once. -/
noncomputable def realRoots : EigFactor → List ℝ
  | char (.real r) => [(r : ℝ)]
  | char (.realPair α c m) =>
      [(α : ℝ) + CAS.LinearODE.CharRoot.width c m, (α : ℝ) - CAS.LinearODE.CharRoot.width c m]
  | char (.pair ..) => []
  | enclosed R D => D.reals.map fun I ↦ CAS.AlgRoot.real R I.1 I.2

/-- For a factor with `f.isReal = true`, the complex roots `f.roots` are the real roots
`f.realRoots` cast to `ℂ`, in the same order. No check is assumed. -/
theorem roots_of_isReal : ∀ f : EigFactor, f.isReal = true →
    f.roots = f.realRoots.map fun r : ℝ ↦ (r : ℂ)
  | char (.real _), _ => rfl
  | char (.realPair ..), _ => rfl
  | char (.pair ..), h => by simp [isReal] at h
  | enclosed R D, h => by
    have hd : D.discs = [] := by simpa [isReal] using h
    simp [roots, realRoots, hd]

/-- Whether the factor passes its check, has only real roots and has the coefficients `a`, lowest
degree first. -/
def realCheck (f : EigFactor) (a : List ℚ) : Bool :=
  f.check && f.isReal && decide (f.coeffs = a)

/-- A rational polynomial with the coefficients of a factor that passes `realCheck` splits over
`ℝ`: all its complex roots are real. -/
theorem splits_of_realCheck {q : ℚ[X]} {a : List ℚ} {f : EigFactor} (hq : q = ofCoeffList a)
    (h : f.realCheck a = true) : (q.map (algebraMap ℚ ℝ)).Splits := by
  simp only [realCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hc, hr⟩, ha⟩ := h
  have hprod : q.map (algebraMap ℚ ℝ) = (f.realRoots.map fun r ↦ X - C r).prod := by
    apply Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective
    rw [Polynomial.map_map, hq, ← ha,
      Subsingleton.elim ((algebraMap ℝ ℂ).comp (algebraMap ℚ ℝ)) (algebraMap ℚ ℂ), ← polyC.eq_1,
      ← prod_roots f hc,
      roots_of_isReal f hr, Polynomial.map_list_prod, List.map_map, List.map_map]
    simp [Function.comp_def]
  rw [hprod]
  exact Splits.listProd fun g hg ↦ by
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hg
    exact Splits.X_sub_C r

end EigFactor

/-- The roots of `∏ fₖ ^ mₖ`, each `mₖ` times. -/
noncomputable def rootList : List (EigFactor × ℕ) → List ℂ
  | [] => []
  | e :: rest => e.1.roots.flatMap (List.replicate e.2) ++ rootList rest

/-- The roots of the factors `fₖ` of `∏ fₖ ^ mₖ`, each factor's roots once: the multiplicities
`mₖ` are not used, and a root that two factors share appears twice. -/
noncomputable def factorRoots : List (EigFactor × ℕ) → List ℂ
  | [] => []
  | e :: rest => e.1.roots ++ factorRoots rest

/-- The real roots of `∏ fₖ ^ mₖ`, each `mₖ` times. -/
noncomputable def realRootList : List (EigFactor × ℕ) → List ℝ
  | [] => []
  | e :: rest => e.1.realRoots.flatMap (List.replicate e.2) ++ realRootList rest

/-- The real roots of the factors `fₖ` of `∏ fₖ ^ mₖ`, each factor's roots once: the
multiplicities `mₖ` are not used, and a root that two factors share appears twice. -/
noncomputable def factorRealRoots : List (EigFactor × ℕ) → List ℝ
  | [] => []
  | e :: rest => e.1.realRoots ++ factorRealRoots rest

/-- The coefficients of `∏ fₖ ^ mₖ`. -/
def prodCoeffs : List (EigFactor × ℕ) → List ℚ
  | [] => [1]
  | e :: rest => coeffMul (coeffPow e.1.coeffs e.2) (prodCoeffs rest)

/-- The factors pass their checks, have positive multiplicities and multiply out to `a`. -/
def eigenCheck (a : List ℚ) (fs : List (EigFactor × ℕ)) : Bool :=
  fs.all (fun e ↦ e.1.check && 0 < e.2) && decide (prodCoeffs fs = a)

/-- `eigenCheck`, with every root real. -/
def eigenCheckReal (a : List ℚ) (fs : List (EigFactor × ℕ)) : Bool :=
  eigenCheck a fs && fs.all (·.1.isReal)

/-- Over a commutative ring, the product of the `X - C μ` over `l.flatMap (List.replicate k)`, each
element of `l` repeated `k` times, is the `k`th power of the product over `l`. -/
theorem prod_flatMap_replicate {K : Type*} [CommRing K] (k : ℕ) : ∀ l : List K,
    ((l.flatMap (List.replicate k)).map fun μ ↦ X - C μ).prod =
      ((l.map fun μ ↦ X - C μ).prod) ^ k
  | [] => by simp
  | a :: l => by
    rw [List.flatMap_cons, List.map_append, List.prod_append, prod_flatMap_replicate k l,
      List.map_replicate, List.prod_replicate, List.map_cons, List.prod_cons, mul_pow]

/-- If every factor in `fs` passes its check, the product of the `X - μ` over `rootList fs` is
`polyC (prodCoeffs fs)`, the polynomial `∏ fₖ ^ mₖ`. -/
theorem prod_rootList : ∀ fs : List (EigFactor × ℕ), (∀ e ∈ fs, e.1.check = true) →
    ((rootList fs).map fun μ ↦ X - C μ).prod = polyC (prodCoeffs fs)
  | [], _ => by simp [rootList, prodCoeffs]
  | e :: rest, h => by
    rw [rootList, List.map_append, List.prod_append, prod_flatMap_replicate,
      EigFactor.prod_roots e.1 (h e (by simp)),
      prod_rootList rest fun e' he' ↦ h e' (by simp [he']), prodCoeffs, polyC_coeffMul,
      polyC_coeffPow]

/-- A characteristic polynomial that is the product of the factors `X - μ` over a list `L` has the
elements of `L` as its spectrum and `L` as its multiset of roots. -/
theorem spectrum_and_roots {K : Type*} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (L : List K) (h : M.charpoly = (L.map fun μ ↦ X - C μ).prod) :
    spectrum K M = {μ | μ ∈ L} ∧ M.charpoly.roots = (L : Multiset K) := by
  have hroots : M.charpoly.roots = (L : Multiset K) := by
    rw [h, ← Multiset.prod_coe, ← Multiset.map_coe, Polynomial.roots_multiset_prod_X_sub_C]
  refine ⟨Set.ext fun μ ↦ ?_, hroots⟩
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Set.mem_ofPred_eq,
    ← Polynomial.mem_roots M.charpoly_monic.ne_zero, hroots, Multiset.mem_coe]

/-- If the rational matrix `A` has characteristic polynomial `ofCoeffList a`, then `A` mapped
entrywise to `ℂ` has characteristic polynomial `polyC a`. -/
theorem charpoly_map_complex {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {a : List ℚ}
    (hA : A.charpoly = ofCoeffList a) : (A.map ((↑) : ℚ → ℂ)).charpoly = polyC a := by
  rw [show A.map ((↑) : ℚ → ℂ) = A.map (Rat.castHom ℂ) from rfl, Matrix.charpoly_map, hA,
    Subsingleton.elim (Rat.castHom ℂ) (algebraMap ℚ ℂ), polyC]

/-- When `eigenCheck a fs` holds for the characteristic polynomial `a` of a rational matrix, its
spectrum over `ℂ` is the set of the elements of `rootList fs`, and the roots of its characteristic
polynomial, with their algebraic multiplicities, are the multiset `rootList fs`. -/
theorem spectrum_complex {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {a : List ℚ}
    (hA : A.charpoly = ofCoeffList a) {fs : List (EigFactor × ℕ)} (h : eigenCheck a fs = true) :
    spectrum ℂ (A.map ((↑) : ℚ → ℂ)) = {μ | μ ∈ rootList fs} ∧
      (A.map ((↑) : ℚ → ℂ)).charpoly.roots = (rootList fs : Multiset ℂ) := by
  simp only [eigenCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  apply spectrum_and_roots
  rw [charpoly_map_complex hA, prod_rootList fs fun e he ↦ (h.1 e he).1, h.2]

/-- Repeating every element `k` times commutes with `List.map f`:
`(l.map f).flatMap (List.replicate k) = (l.flatMap (List.replicate k)).map f`. -/
theorem flatMap_replicate_map {α β : Type*} (f : α → β) (k : ℕ) : ∀ l : List α,
    (l.map f).flatMap (List.replicate k) = (l.flatMap (List.replicate k)).map f
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, List.map_append, List.map_replicate,
      flatMap_replicate_map f k l]

/-- If every factor in `fs` has only real roots (`isReal`), `rootList fs` is `realRootList fs` cast
to `ℂ` entry by entry. No check is assumed. -/
theorem rootList_eq_map : ∀ fs : List (EigFactor × ℕ), (∀ e ∈ fs, e.1.isReal = true) →
    rootList fs = (realRootList fs).map fun r : ℝ ↦ (r : ℂ)
  | [], _ => rfl
  | e :: rest, h => by
    rw [rootList, realRootList, List.map_append, EigFactor.roots_of_isReal e.1 (h e (by simp)),
      flatMap_replicate_map, rootList_eq_map rest fun e' he' ↦ h e' (by simp [he'])]

/-- When `eigenCheckReal a fs` holds for the characteristic polynomial `a` of a rational matrix,
all its eigenvalues are real, its spectrum over `ℝ` is the set of the elements of
`realRootList fs`, and the real roots of its characteristic polynomial, with their algebraic
multiplicities, are the multiset `realRootList fs`. -/
theorem spectrum_real {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {a : List ℚ}
    (hA : A.charpoly = ofCoeffList a) {fs : List (EigFactor × ℕ)}
    (h : eigenCheckReal a fs = true) :
    spectrum ℝ (A.map ((↑) : ℚ → ℝ)) = {μ | μ ∈ realRootList fs} ∧
      (A.map ((↑) : ℚ → ℝ)).charpoly.roots = (realRootList fs : Multiset ℝ) := by
  simp only [eigenCheckReal, eigenCheck, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨hcheck', hcoeffs⟩, hreal⟩ := h
  have hcheck : ∀ e ∈ fs, e.1.check = true := fun e he ↦ (hcheck' e he).1
  apply spectrum_and_roots
  apply Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective
  have hM : (A.map ((↑) : ℚ → ℝ)).map (algebraMap ℝ ℂ) = A.map ((↑) : ℚ → ℂ) := by
    ext i j
    simp
  rw [← Matrix.charpoly_map, hM, charpoly_map_complex hA, ← hcoeffs, ← prod_rootList fs hcheck,
    rootList_eq_map fs hreal, Polynomial.map_list_prod, List.map_map, List.map_map]
  simp [Function.comp_def]

/-- A rational matrix literal mapped entrywise by `f` is the literal of the images. -/
theorem map_of_eq {K : Type*} {n : ℕ} (Q : Fin n → Fin n → ℚ) (f : ℚ → K) :
    (Matrix.of Q).map f = Matrix.of (FinVec.map (fun r ↦ FinVec.map f r) Q) := by
  ext i j
  simp [FinVec.map_eq]

/-- For `0 < k`, `μ` lies in `l.flatMap (List.replicate k)` exactly when it lies in `l`. -/
theorem mem_flatMap_replicate {α : Type*} {k : ℕ} (hk : 0 < k) (l : List α) (μ : α) :
    μ ∈ l.flatMap (List.replicate k) ↔ μ ∈ l := by
  simp only [List.mem_flatMap, List.mem_replicate]
  constructor
  · rintro ⟨x, hx, -, rfl⟩
    exact hx
  · intro h
    exact ⟨μ, h, hk.ne', rfl⟩

/-- When every multiplicity in `fs` is positive, `μ` lies in `rootList fs` exactly when it lies in
`factorRoots fs`. -/
theorem mem_rootList : ∀ fs : List (EigFactor × ℕ), (∀ e ∈ fs, 0 < e.2) → ∀ μ : ℂ,
    μ ∈ rootList fs ↔ μ ∈ factorRoots fs
  | [], _, _ => Iff.rfl
  | e :: rest, h, μ => by
    rw [rootList, factorRoots, List.mem_append, List.mem_append,
      mem_flatMap_replicate (h e (by simp)),
      mem_rootList rest (fun e' he' ↦ h e' (by simp [he'])) μ]

/-- When every multiplicity in `fs` is positive, a real `μ` lies in `realRootList fs` exactly when
it lies in `factorRealRoots fs`. -/
theorem mem_realRootList : ∀ fs : List (EigFactor × ℕ), (∀ e ∈ fs, 0 < e.2) → ∀ μ : ℝ,
    μ ∈ realRootList fs ↔ μ ∈ factorRealRoots fs
  | [], _, _ => Iff.rfl
  | e :: rest, h, μ => by
    rw [realRootList, factorRealRoots, List.mem_append, List.mem_append,
      mem_flatMap_replicate (h e (by simp)),
      mem_realRootList rest (fun e' he' ↦ h e' (by simp [he'])) μ]

/-- If `eigenCheck a fs` holds, every multiplicity in `fs` is positive. -/
theorem pos_of_eigenCheck {a : List ℚ} {fs : List (EigFactor × ℕ)} (h : eigenCheck a fs = true) :
    ∀ e ∈ fs, 0 < e.2 := by
  simp only [eigenCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact fun e he ↦ (h.1 e he).2

/-- The spectrum over `ℂ` of the matrix `M` with rational entries `A`, each eigenvalue once, and
its eigenvalues with algebraic multiplicities. -/
theorem spectrum_complex_of {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {M : Matrix (Fin n) (Fin n) ℂ}
    {a : List ℚ} {fs : List (EigFactor × ℕ)} {L D : List ℂ}
    (hA : A.charpoly = ofCoeffList a) (hM : A.map ((↑) : ℚ → ℂ) = M)
    (h : eigenCheck a fs = true) (hL : rootList fs = L) (hD : factorRoots fs = D) :
    spectrum ℂ M = {μ | μ ∈ D} ∧ M.charpoly.roots = (L : Multiset ℂ) := by
  subst hM hL hD
  obtain ⟨hs, hr⟩ := spectrum_complex hA h
  refine ⟨?_, hr⟩
  rw [hs]
  exact Set.ext fun μ ↦ mem_rootList fs (pos_of_eigenCheck h) μ

/-- The spectrum over `ℝ` of the matrix `M` with rational entries `A` when every eigenvalue is
real, each eigenvalue once, and its eigenvalues with algebraic multiplicities. -/
theorem spectrum_real_of {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {M : Matrix (Fin n) (Fin n) ℝ}
    {a : List ℚ} {fs : List (EigFactor × ℕ)} {L D : List ℝ}
    (hA : A.charpoly = ofCoeffList a) (hM : A.map ((↑) : ℚ → ℝ) = M)
    (h : eigenCheckReal a fs = true) (hL : realRootList fs = L)
    (hD : factorRealRoots fs = D) :
    spectrum ℝ M = {μ | μ ∈ D} ∧ M.charpoly.roots = (L : Multiset ℝ) := by
  subst hM hL hD
  obtain ⟨hs, hr⟩ := spectrum_real hA h
  refine ⟨?_, hr⟩
  rw [hs]
  have h' : eigenCheck a fs = true := by
    simp only [eigenCheckReal, Bool.and_eq_true] at h
    exact h.1
  exact Set.ext fun μ ↦ mem_realRootList fs (pos_of_eigenCheck h') μ

/-- A factor `S` of the characteristic polynomial `a = S G` of the matrix `M` with rational
entries `A` that changes sign between `lo < hi` gives a real eigenvalue of `M` in `[lo, hi]`. The
three conditions are one Boolean, decided by the kernel. -/
theorem exists_mem_spectrum_of_signChange {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    {M : Matrix (Fin n) (Fin n) ℝ} {a S G : List ℚ} {lo hi : ℚ}
    (hA : A.charpoly = ofCoeffList a) (hM : A.map ((↑) : ℚ → ℝ) = M)
    (h : (decide (coeffMul S G = a) && decide (lo < hi) &&
      decide (coeffEvalRat S lo * coeffEvalRat S hi < 0)) = true) :
    ∃ t ∈ Set.Icc (lo : ℝ) hi, t ∈ spectrum ℝ M := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hSG, hlt⟩, hsign⟩ := h
  obtain ⟨r, hr, hS⟩ := CAS.AlgRoot.exists_real_root S hlt hsign
  refine ⟨r, Set.Ioo_subset_Icc_self hr, ?_⟩
  subst hM
  apply Matrix.mem_spectrum_of_isRoot_charpoly
  have hS' : ((coeffEval (coeffMul S G) r : ℝ) : ℂ) = 0 := by
    rw [← eval_polyC_ofReal, polyC_coeffMul, Polynomial.eval_mul, eval_polyC_ofReal, hS,
      Complex.ofReal_zero, zero_mul]
  rw [show A.map ((↑) : ℚ → ℝ) = A.map (Rat.castHom ℝ) from rfl, Matrix.charpoly_map, hA,
    Polynomial.IsRoot.def, eval_map_ofCoeffList, ← hSG]
  exact_mod_cast hS'

/-- A basis of the eigenspace of `M` for `α` from identities that hold up to multiples of a scalar
`c = 0`, such as the value at a root `α` of a polynomial `q` (`c = q(α)`). Let the vectors `V i`
satisfy `M V i = α V i + c W i`, and the rows `E r` satisfy `E r M = α E r + T r + c S r`, where
`V i` is `1` at the column `free i` and `0` at the other columns `free j`, `T r` is `1` at
`pivot r` and `0` at the other columns `pivot s`, and every column is a `pivot r` or a `free i`.
Then the `V i` lie in the kernel of `M - α • 1`, are linearly independent, and span it. -/
theorem eigenspace_basis {K : Type*} [Field K] {n k m : ℕ} {M : Matrix (Fin n) (Fin n) K}
    {α : K} {V : Fin k → Fin n → K} (c : K) (W : Fin k → Fin n → K) (E T S : Fin m → Fin n → K)
    (free : Fin k → Fin n) (pivot : Fin m → Fin n) (hc : c = 0)
    (hV : ∀ i, M.mulVec (V i) = α • V i + c • W i)
    (hE : ∀ r, Matrix.vecMul (E r) M = α • E r + T r + c • S r)
    (hfree : ∀ i j, V i (free j) = if i = j then 1 else 0)
    (hT : ∀ r s, T r (pivot s) = if r = s then 1 else 0)
    (hcover : ∀ l, (∃ r, pivot r = l) ∨ ∃ i, free i = l) :
    (∀ i, (M - α • 1).mulVec (V i) = 0) ∧ LinearIndependent K V ∧
      ∀ x : Fin n → K, (M - α • 1).mulVec x = 0 → ∃ a : Fin k → K, x = ∑ i, a i • V i := by
  subst hc
  have hmul : ∀ x, (M - α • 1).mulVec x = M.mulVec x - α • x := fun x ↦ by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hker : ∀ i, (M - α • 1).mulVec (V i) = 0 := fun i ↦ by
    rw [hmul, hV, zero_smul, add_zero, sub_self]
  have hcoord : ∀ (g : Fin k → K) j, (∑ i, g i • V i) (free j) = g j := fun g j ↦ by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hfree, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  refine ⟨hker, ?_, fun x hx ↦ ⟨fun i ↦ x (free i), ?_⟩⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg j
    rw [← hcoord g j, hg, Pi.zero_apply]
  · set y := x - ∑ i, x (free i) • V i with hy
    have hy0 : (M - α • 1).mulVec y = 0 := by
      rw [hy, Matrix.mulVec_sub, hx, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, hker, smul_zero, Finset.sum_const_zero, sub_zero]
    have hfree0 : ∀ j, y (free j) = 0 := fun j ↦ by
      rw [hy, Pi.sub_apply, hcoord, sub_self]
    have hrow : ∀ r, Matrix.vecMul (E r) (M - α • 1) = T r := fun r ↦ by
      rw [Matrix.vecMul_sub, hE, Matrix.vecMul_smul, Matrix.vecMul_one, zero_smul, add_zero,
        add_sub_cancel_left]
    have hpivot0 : ∀ r, y (pivot r) = 0 := fun r ↦ by
      have h := congrArg (dotProduct (E r)) hy0
      simp only [Matrix.dotProduct_mulVec, hrow, dotProduct_zero] at h
      rw [← h, dotProduct, Finset.sum_eq_single (pivot r)]
      · rw [hT, ite_eq_left rfl, one_mul]
      · intro l _ hl
        rcases hcover l with ⟨s, rfl⟩ | ⟨i, rfl⟩
        · rw [hT, ite_eq_right (fun h ↦ hl (congrArg pivot h.symm)), zero_mul]
        · rw [hfree0, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hy' : y = 0 := funext fun l ↦ by
      rcases hcover l with ⟨r, rfl⟩ | ⟨i, rfl⟩
      · exact hpivot0 r
      · exact hfree0 i
    rw [hy, sub_eq_zero] at hy'
    exact hy'

end CAS.Analysis.Matrix

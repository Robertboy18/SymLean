/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Rolle's theorem with repeated zeros

The results use a finite derivative chain `F : ℕ → ℝ → ℝ`: for `k` below the requested
order, `F k` is continuous on `[a, b]` and has derivative `F (k + 1)` on `(a, b)`.
A `C^m` function `f` supplies such a chain through order `m`, with
`F k = iteratedDerivWithin k f (Icc a b)` (`derivative_chain_within` in `Remainder`).
No regularity beyond order `m` or outside `[a, b]` is required.

The generalized Rolle theorem proved here says that if `F 0` has `n + 1` zeros in `[a, b]`
counted with multiplicity, where a zero of multiplicity `m` means that `F 0, …, F (m - 1)`
all vanish there, then `F n` vanishes somewhere in `[a, b]`. Rolle's theorem supplies a zero
of `F 1` between distinct consecutive zeros, and a repeated zero supplies one directly.

## References

* Josef Stoer and Roland Bulirsch, *Introduction to Numerical Analysis*, 3rd ed., Texts in Applied
  Mathematics 12, Springer, New York, 2002, <https://doi.org/10.1007/978-0-387-21738-3>. §2.1.4 and
  §2.1.5 for the repeated use of Rolle's theorem in the remainder of polynomial interpolation.
-/

@[expose] public section

namespace CAS.Continuum

open Set

/-- Between two zeros `l ≤ r` of `F 0` there is a zero of `F 1`, strictly between them when
`l < r`. For `l < r` this is Rolle's theorem, and for `l = r` the hypothesis `F 1 l = 0` is
used directly. -/
theorem exists_between_derivative_zero {a b : ℝ} {F : ℕ → ℝ → ℝ}
    (hcontinuous : ContinuousOn (F 0) (Icc a b))
    (hderiv : ∀ z ∈ Ioo a b, HasDerivAt (F 0) (F 1 z) z)
    {l r : ℝ} (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) (hle : l ≤ r)
    (hlzero : F 0 l = 0) (hrzero : F 0 r = 0)
    (hsame : l = r → F 1 l = 0) :
    ∃ y ∈ Icc l r, F 1 y = 0 ∧ (l < r → y ∈ Ioo l r) := by
  rcases hle.eq_or_lt with heq | hlt
  · exact ⟨l, ⟨le_rfl, heq.le⟩, hsame heq, fun h ↦ (h.ne heq).elim⟩
  · obtain ⟨y, hy, hyzero⟩ := exists_hasDerivAt_eq_zero hlt
      (hcontinuous.mono (Icc_subset_Icc hl.1 hr.2)) (hlzero.trans hrzero.symm)
      (fun z hz ↦ hderiv z ⟨hl.1.trans_lt hz.1, hz.2.trans_le hr.2⟩)
    exact ⟨y, ⟨hy.1.le, hy.2.le⟩, hyzero, fun _ ↦ hy⟩

/-- Generalized Rolle theorem for a derivative chain: `n + 1` zeros of `F 0` in `[a, b]`,
listed in increasing order with repeats allowed, force a zero of `F n` in `[a, b]`. A run of
equal entries from index `i` to `j` must also be a zero of `F (j - i)`, which is how
multiplicity enters. Induction on `n`, passing to the chain `k ↦ F (k + 1)` and the `n`
zeros of `F 1` between consecutive entries. -/
theorem exists_derivative_chain_zero {a b : ℝ} (n : ℕ) (F : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ k < n, ContinuousOn (F k) (Icc a b))
    (hderiv : ∀ k < n, ∀ z ∈ Ioo a b, HasDerivAt (F k) (F (k + 1) z) z)
    (x : Fin (n + 1) → ℝ) (hmonotone : Monotone x)
    (hmem : ∀ i, x i ∈ Icc a b)
    (hzero : ∀ i j, i ≤ j → x i = x j → F (j.val - i.val) (x i) = 0) :
    ∃ z ∈ Icc a b, F n z = 0 := by
  induction n generalizing F with
  | zero =>
    exact ⟨x 0, hmem 0, by simpa using hzero 0 0 le_rfl rfl⟩
  | succ n ih =>
    have hstep (i : Fin (n + 1)) : x i.castSucc ≤ x i.succ := hmonotone (Nat.le_succ _)
    have hbetween (i : Fin (n + 1)) :
        ∃ y ∈ Icc (x i.castSucc) (x i.succ),
          F 1 y = 0 ∧ (x i.castSucc < x i.succ → y ∈ Ioo (x i.castSucc) (x i.succ)) :=
      exists_between_derivative_zero (hcontinuous 0 (by omega))
        (hderiv 0 (by omega)) (hmem i.castSucc) (hmem i.succ) (hstep i)
        (by simpa using hzero i.castSucc i.castSucc le_rfl rfl)
        (by simpa using hzero i.succ i.succ le_rfl rfl)
        fun heq ↦ by simpa using hzero i.castSucc i.succ (Nat.le_succ _) heq
    choose y hy hyzero hystrict using hbetween
    have hsep {i j : Fin (n + 1)} (hij : i < j) : x i.succ ≤ x j.castSucc :=
      hmonotone (by simpa using hij)
    have hymono : Monotone y := monotone_iff_forall_lt.2 fun i j hij ↦
      (hy i).2.trans ((hsep hij).trans (hy j).1)
    have hymem (i : Fin (n + 1)) : y i ∈ Icc a b :=
      ⟨(hmem i.castSucc).1.trans (hy i).1, (hy i).2.trans (hmem i.succ).2⟩
    have hyrepeat (i j : Fin (n + 1)) (hij : i ≤ j) (heq : y i = y j) :
        F (j.val - i.val + 1) (y i) = 0 := by
      rcases hij.eq_or_lt with rfl | hij
      · simpa using hyzero i
      · have hfirst : x i.castSucc = x i.succ := by
          by_contra hne
          linarith [(hystrict i ((hstep i).lt_of_ne hne)).2, (hy j).1, hsep hij]
        have hlast : x j.castSucc = x j.succ := by
          by_contra hne
          linarith [(hy i).2, (hystrict j ((hstep j).lt_of_ne hne)).1, hsep hij]
        have hyleft : y i = x i.castSucc :=
          le_antisymm (by simpa [← hfirst] using (hy i).2) (hy i).1
        have hyright : y j = x j.succ :=
          le_antisymm (hy j).2 (by simpa [hlast] using (hy j).1)
        have hx : x i.castSucc = x j.succ := by rw [← hyleft, ← hyright, heq]
        have hz := hzero i.castSucc j.succ
          (show i.val ≤ j.val + 1 from (Fin.le_iff_val_le_val.mp hij.le).trans
            (Nat.le_succ _)) hx
        have horder : j.succ.val - i.castSucc.val = j.val - i.val + 1 := by
          simp only [Fin.val_succ, Fin.val_castSucc]
          omega
        rwa [horder, ← hyleft] at hz
    exact ih (fun k ↦ F (k + 1))
      (fun k hk ↦ hcontinuous (k + 1) (by omega))
      (fun k hk ↦ hderiv (k + 1) (by omega)) y hymono hymem hyrepeat

/-- Multiset form of the generalized Rolle theorem: if `s` has `n + 1` elements of `[a, b]`
and `F k z = 0` for every `z ∈ s` and every `k` below the multiplicity of `z` in `s`, then
`F n` has a zero in `[a, b]`. Sort `s` and apply `exists_derivative_chain_zero`. -/
theorem exists_derivative_chain_zero_of_multiset {a b : ℝ} (n : ℕ)
    (F : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ k < n, ContinuousOn (F k) (Icc a b))
    (hderiv : ∀ k < n, ∀ z ∈ Ioo a b, HasDerivAt (F k) (F (k + 1) z) z)
    (s : Multiset ℝ) (hcard : s.card = n + 1)
    (hmem : ∀ z ∈ s, z ∈ Icc a b)
    (hzero : ∀ z ∈ s, ∀ k < s.count z, F k z = 0) :
    ∃ z ∈ Icc a b, F n z = 0 := by
  classical
  let v : List.Vector ℝ (n + 1) := ⟨s.sort (· ≤ ·), by simpa using hcard⟩
  have hmono : Monotone v.get := fun i j hij ↦ (s.pairwise_sort (· ≤ ·)).rel_get_of_le hij
  have hvmem (i : Fin (n + 1)) : v.get i ∈ s :=
    (Multiset.mem_sort (· ≤ ·)).mp (List.get_mem _ _)
  apply exists_derivative_chain_zero n F hcontinuous hderiv v.get hmono
    (fun i ↦ hmem _ (hvmem i))
  intro i j hij heq
  apply hzero _ (hvmem i)
  have hsub : Finset.Icc i j ⊆ Finset.univ.filter (fun k ↦ v.get k = v.get i) := fun k hk ↦ by
    obtain ⟨hik, hkj⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ((hmono hkj).trans heq.ge).antisymm (hmono hik)⟩
  have hc := Finset.card_le_card hsub
  rw [Fin.card_Icc, Fin.card_filter_univ_eq_vector_get_eq_count] at hc
  have hcount : v.toList.count (v.get i) = s.count (v.get i) := by
    change (s.sort (· ≤ ·)).count _ = _
    rw [← Multiset.coe_count, Multiset.sort_eq]
  rw [hcount] at hc
  omega

/-- If `F 0` and `F 1` vanish at `n` distinct nodes in `[a, b]` and `F 0` vanishes at one
further point `x`, then `F (2n)` has a zero in `[a, b]`. This is the multiset case with each
node of multiplicity two and `x` of multiplicity one, `2n + 1` zeros in all. It is the form
used for the Gaussian remainder. -/
theorem exists_derivative_chain_zero_of_double_zeros {a b : ℝ} (n : ℕ)
    (F : ℕ → ℝ → ℝ)
    (hcontinuous : ∀ k < 2 * n, ContinuousOn (F k) (Icc a b))
    (hderiv : ∀ k < 2 * n, ∀ z ∈ Ioo a b, HasDerivAt (F k) (F (k + 1) z) z)
    (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (hmem : ∀ i, nodes i ∈ Icc a b)
    (hzero : ∀ i, F 0 (nodes i) = 0 ∧ F 1 (nodes i) = 0)
    (x : ℝ) (hx : x ∈ Icc a b) (hxne : ∀ i, x ≠ nodes i) (hxzero : F 0 x = 0) :
    ∃ z ∈ Icc a b, F (2 * n) z = 0 := by
  classical
  let t : Multiset ℝ := (Finset.univ : Finset (Fin n)).val.map nodes
  have htmem (z : ℝ) : z ∈ t ↔ ∃ i, nodes i = z := by simp [t]
  have htnodup : t.Nodup :=
    Multiset.Nodup.map hnodes Finset.univ.nodup
  have hxnot : x ∉ t := fun h ↦ ((htmem x).1 h).elim fun i hi ↦ hxne i hi.symm
  let s := x ::ₘ (t + t)
  have hscard : s.card = 2 * n + 1 := by simp [s, t]; omega
  have hsmem (z : ℝ) (hz : z ∈ s) : z = x ∨ ∃ i, nodes i = z := by
    simpa [s, htmem] using hz
  apply exists_derivative_chain_zero_of_multiset (2 * n) F hcontinuous hderiv s hscard
  · exact fun z hz ↦ (hsmem z hz).elim (· ▸ hx) fun ⟨i, hi⟩ ↦ hi ▸ hmem i
  · intro z hz k hk
    by_cases hzx : z = x
    · subst z
      have hcount : s.count x = 1 := by simp [s, Multiset.count_eq_zero.mpr hxnot]
      obtain rfl : k = 0 := by omega
      exact hxzero
    · obtain ⟨i, rfl⟩ := (hsmem z hz).resolve_left hzx
      have ht := Multiset.nodup_iff_count_le_one.mp htnodup (nodes i)
      have hcount : s.count (nodes i) ≤ 2 := by
        simp only [s, Multiset.count_cons, Multiset.count_add, hzx, ite_false]
        omega
      obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
      exacts [(hzero i).1, (hzero i).2]

end CAS.Continuum

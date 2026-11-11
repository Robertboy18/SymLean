/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.RealRoot.RootList
public import Mathlib.Data.List.GetD

/-!
# Solution sets of polynomial inequalities

A continuous function whose zeros are `ρ 0 < ⋯ < ρ (k - 1)` has one sign on each gap between
consecutive zeros, the sign at any point of the gap (`pos_iff_pos_of_isPreconnected`). With
cut points `c j` separating the zeros and nonzero there, `f x > 0` holds exactly on the gaps
whose cut point has `f (c j) > 0` (`pos_iff_exists_gap`).

For a polynomial expression, `reduceCheck` combines the complete root list of `exprRootCheck`
with rational cut points and the signs of the polynomial at them, and `of_reduceCheck` states
the solution sets of `f x > 0`, `f x < 0` and `f x = 0`, with the real roots located in their
isolating intervals or given exactly. The formulas `GapsFormula` and `RootsFormula` unfold on
concrete lists to explicit unions of intervals.

## Main results

* `pos_iff_pos_of_isPreconnected`, `pos_iff_exists_gap`, `neg_iff_exists_gap`.
* `of_reduceCheck`: the solution sets of a polynomial inequality in one variable; its
  projections `of_reduceCheck_pos`, … write the rational roots as rationals (`rootVal`).
* `nonneg_of_reduceCheck`, `pos_of_reduceCheck`: a polynomial whose signs at all the cuts are
  positive is nonnegative everywhere, and positive everywhere when it has no real root. These
  are the sign conditions that bare `cas` closes.
* `nonneg_on_Icc_of_reduceCheck`, `pos_on_Icc_of_reduceCheck`: the same on `[a, b]`, where only
  the gaps that meet `[a, b]` count (`gapSignsOn`).
* `solve_of_reduceCheck`: the real points of a polynomial system in triangular form
  `R τ = 0 ∧ Q τ`, one point for each real root of `R`.

## Implementation notes

`reduceCheck` checks the cuts and signs but does not choose them (`sepCheck`): it accepts any
rationals, one below the first location, one between each two consecutive locations and one
above the last, at which the polynomial is nonzero, and it compares the claimed signs with exact
rational evaluations. The commands compute these data in compiled code with `Reduce.rootData`,
from the root list of `RootIsolation.generate` and the cuts of `Reduce.cutsOf`.
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Set

/-- A continuous function without zeros on a preconnected set has one sign there. -/
theorem pos_iff_pos_of_isPreconnected {f : ℝ → ℝ} (hf : Continuous f) {S : Set ℝ}
    (hS : IsPreconnected S) (hz : ∀ y ∈ S, f y ≠ 0) {x c : ℝ} (hx : x ∈ S) (hc : c ∈ S) :
    0 < f x ↔ 0 < f c := by
  have key {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) (h : 0 < f a) : 0 < f b := by
    by_contra hneg
    obtain ⟨y, hy, hy0⟩ := hS.intermediate_value hb ha hf.continuousOn ⟨not_lt.mp hneg, h.le⟩
    exact hz y hy hy0
  exact ⟨key hx hc, key hc hx⟩

/-- The `j`-th gap between the consecutive roots `ρ 0 < ⋯ < ρ (k - 1)`: below `ρ 0` for `j = 0`,
above `ρ (k - 1)` for `j = k`. -/
def Gap (ρ : ℕ → ℝ) (k j : ℕ) (x : ℝ) : Prop :=
  (j = 0 ∨ ρ (j - 1) < x) ∧ (j = k ∨ x < ρ j)

/-- Every gap `Gap ρ k j` is an order-connected set of reals, for all `ρ`, `k` and `j` (no order on
the `ρ i` is assumed). -/
theorem gap_ordConnected (ρ : ℕ → ℝ) (k j : ℕ) : (Set.ofPred (Gap ρ k j)).OrdConnected := by
  constructor
  intro x hx y hy z hz
  exact ⟨hx.1.imp_right fun h ↦ h.trans_le hz.1, hy.2.imp_right fun h ↦ hz.2.trans_lt h⟩

private theorem root_lt_root {k : ℕ} {ρ c : ℕ → ℝ}
    (hsep : ∀ j < k, c j < ρ j ∧ ρ j < c (j + 1)) {i : ℕ} :
    ∀ {i' : ℕ}, i < i' → i' < k → ρ i < ρ i'
  | i' + 1, hii', hk => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hii' with h | rfl
      · exact (root_lt_root hsep h (by omega)).trans
          ((hsep i' (by omega)).2.trans (hsep (i' + 1) hk).1)
      · exact (hsep i (by omega)).2.trans (hsep (i + 1) hk).1

private theorem root_le_root {k : ℕ} {ρ c : ℕ → ℝ}
    (hsep : ∀ j < k, c j < ρ j ∧ ρ j < c (j + 1)) {i i' : ℕ} (h : i ≤ i') (hk : i' < k) :
    ρ i ≤ ρ i' := by
  rcases h.lt_or_eq with h | rfl
  · exact (root_lt_root hsep h hk).le
  · exact le_rfl

/-- **Sign on the gaps.** -/
theorem pos_iff_exists_gap {f : ℝ → ℝ} (hf : Continuous f) {k : ℕ} {ρ c : ℕ → ℝ}
    (hsep : ∀ j < k, c j < ρ j ∧ ρ j < c (j + 1))
    (hzero : ∀ x, f x = 0 ↔ ∃ j < k, x = ρ j) (x : ℝ) :
    0 < f x ↔ ∃ j ≤ k, Gap ρ k j x ∧ 0 < f (c j) := by
  have hcgap (j : ℕ) (hj : j ≤ k) : Gap ρ k j (c j) := by
    refine ⟨(Nat.eq_zero_or_pos j).imp_right fun h ↦ ?_,
      hj.lt_or_eq.symm.imp_right fun h ↦ (hsep j h).1⟩
    simpa [Nat.sub_add_cancel h] using (hsep (j - 1) (by omega)).2
  have hnz (j : ℕ) (hj : j ≤ k) (y : ℝ) (hy : Gap ρ k j y) : f y ≠ 0 := by
    intro h0
    obtain ⟨i, hi, rfl⟩ := (hzero y).mp h0
    rcases lt_or_ge i j with hij | hji
    · exact hy.1.elim (fun h ↦ by omega) fun h ↦
        (h.trans_le (root_le_root hsep (by omega) (by omega))).false
    · exact hy.2.elim (fun h ↦ by omega) fun h ↦ (h.trans_le (root_le_root hsep hji hi)).false
  have hsign (j : ℕ) (hj : j ≤ k) (hgap : Gap ρ k j x) : 0 < f x ↔ 0 < f (c j) :=
    pos_iff_pos_of_isPreconnected hf (gap_ordConnected ρ k j).isPreconnected
      (fun y hy ↦ hnz j hj y hy) hgap (hcgap j hj)
  refine ⟨fun hpos ↦ ?_, fun ⟨j, hj, hgap, hpos⟩ ↦ (hsign j hj hgap).mpr hpos⟩
  have hx0 : ∀ i < k, x ≠ ρ i := fun i hi h ↦ hpos.ne' ((hzero x).mpr ⟨i, hi, h⟩)
  classical
  have hex : ∃ j, j = k ∨ x < ρ j := ⟨k, Or.inl rfl⟩
  have hjk : Nat.find hex ≤ k := Nat.find_min' hex (Or.inl rfl)
  have hlow : Nat.find hex = 0 ∨ ρ (Nat.find hex - 1) < x := by
    refine (Nat.eq_zero_or_pos (Nat.find hex)).imp_right fun h ↦ ?_
    have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push Not at hmin
    exact lt_of_le_of_ne hmin.2 fun h' ↦ hx0 _ (by omega) h'.symm
  have hgap : Gap ρ k (Nat.find hex) x := ⟨hlow, Nat.find_spec hex⟩
  exact ⟨Nat.find hex, hjk, hgap, (hsign _ hjk hgap).mp hpos⟩

/-- The negative part of `pos_iff_exists_gap`. -/
theorem neg_iff_exists_gap {f : ℝ → ℝ} (hf : Continuous f) {k : ℕ} {ρ c : ℕ → ℝ}
    (hsep : ∀ j < k, c j < ρ j ∧ ρ j < c (j + 1))
    (hzero : ∀ x, f x = 0 ↔ ∃ j < k, x = ρ j) (x : ℝ) :
    f x < 0 ↔ ∃ j ≤ k, Gap ρ k j x ∧ f (c j) < 0 := by
  simpa using pos_iff_exists_gap (f := fun y ↦ -f y) hf.neg hsep (fun y ↦ by simpa using hzero y) x

/-- `(s₀ = w ∧ Gap j) ∨ (s₁ = w ∧ Gap (j + 1)) ∨ ⋯` for the signs `s` from position `j`. -/
def GapsFormula (ρ : ℕ → ℝ) (k : ℕ) (x : ℝ) (want : Bool) : ℕ → List Bool → Prop
  | _, [] => False
  | j, s :: rest => (s = want ∧ Gap ρ k j x) ∨ GapsFormula ρ k x want (j + 1) rest

/-- `GapsFormula ρ k x want j signs` holds exactly when, for some `i < signs.length`, `x` lies in
the gap `j + i` and entry `i` of `signs` is `want`. -/
theorem gapsFormula_iff (ρ : ℕ → ℝ) (k : ℕ) (x : ℝ) (want : Bool) :
    ∀ (j : ℕ) (signs : List Bool), GapsFormula ρ k x want j signs ↔
      ∃ i < signs.length, Gap ρ k (j + i) x ∧ signs.getD i false = want := by
  intro j signs
  induction signs generalizing j with
  | nil => simp [GapsFormula]
  | cons s rest ih =>
      rw [GapsFormula, ih, List.length_cons, Nat.exists_lt_succ_left]
      simp only [add_zero, List.getD_cons_zero, List.getD_cons_succ, add_assoc, Nat.add_comm 1]
      exact or_congr and_comm Iff.rfl

/-- `x = r₀ ∨ x = r₁ ∨ ⋯` for the roots `ρ j, ρ (j + 1), …, ρ (k - 1)`. -/
def RootsFormula (ρ : ℕ → ℝ) (x : ℝ) : ℕ → ℕ → Prop
  | _, 0 => False
  | j, n + 1 => x = ρ j ∨ RootsFormula ρ x (j + 1) n

/-- `RootsFormula ρ x j n` holds exactly when `x = ρ (j + i)` for some `i < n`. -/
theorem rootsFormula_iff (ρ : ℕ → ℝ) (x : ℝ) :
    ∀ j n, RootsFormula ρ x j n ↔ ∃ i < n, x = ρ (j + i) := by
  intro j n
  induction n generalizing j with
  | zero => simp [RootsFormula]
  | succ n ih =>
      rw [RootsFormula, ih, Nat.exists_lt_succ_left]
      simp only [add_zero, add_assoc, Nat.add_comm 1]

/-! ## Polynomial inequalities -/

/-- Where a real root lies: in an open rational interval, or at a rational point. -/
inductive RootLoc where
  | interval (lo hi : ℚ)
  | exact (q : ℚ)
  deriving DecidableEq, Repr, Inhabited

namespace RootLoc

/-- The bounds `(lo, hi)` of an interval location; `none` at a rational point. -/
def intervalPart : RootLoc → Option (ℚ × ℚ)
  | interval lo hi => some (lo, hi)
  | exact _ => none

/-- The rational point of an exact location; `none` for an interval. -/
def pointPart : RootLoc → Option ℚ
  | interval _ _ => none
  | exact q => some q

/-- The left end: `lo` for an interval, `q` for a rational point `q`. -/
def lower : RootLoc → ℚ
  | interval lo _ => lo
  | exact q => q

/-- The right end: `hi` for an interval, `q` for a rational point `q`. -/
def upper : RootLoc → ℚ
  | interval _ hi => hi
  | exact q => q

/-- The root `r` lies at the location. -/
def Holds : RootLoc → ℝ → Prop
  | interval lo hi, r => (lo : ℝ) < r ∧ r < hi
  | exact q, r => r = q

/-- The interval bounds of a location; nothing at a rational point. -/
def Bounds : RootLoc → ℝ → Prop
  | interval lo hi, r => (lo : ℝ) < r ∧ r < hi
  | exact _, _ => True

/-- The root at the location: the rational point itself, or `r` in an interval. -/
def value : RootLoc → ℝ → ℝ
  | interval _ _, r => r
  | exact q, _ => q

end RootLoc

/-- The cuts separate the locations and the polynomial is nonzero at every cut, with the signs
`signs` of the polynomial at the cuts. -/
def sepCheck (p : Sparse.Univariate) (locs : List RootLoc) (cuts : List ℚ)
    (signs : List Bool) : Bool :=
  decide (cuts.length = locs.length + 1) &&
    (List.range locs.length).all (fun j ↦
      decide (cuts.getD j 0 ≤ (locs.getD j default).lower) &&
        decide ((locs.getD j default).upper ≤ cuts.getD (j + 1) 0)) &&
    cuts.all (fun c ↦ Sparse.evalRat p c != 0) &&
    decide (signs = cuts.map fun c ↦ decide (0 < Sparse.evalRat p c))

/-- The complete root list of `expr`, its locations in order, the cuts and the signs. -/
def reduceCheck (expr : Verified.Expr (Fin 1)) (cert : RootListCertificate)
    (locs : List RootLoc) (cuts : List ℚ) (signs : List Bool) : Bool :=
  exprRootCheck expr cert (locs.filterMap RootLoc.intervalPart)
      (locs.filterMap RootLoc.pointPart) &&
    match Verified.Expr.Alg.mvPolyOf? expr with
    | some p => sepCheck p locs cuts signs
    | none => false

/-- `l₀ holds at ρ j ∧ l₁ holds at ρ (j + 1) ∧ ⋯`. -/
def HoldsAll (ρ : ℕ → ℝ) : ℕ → List RootLoc → Prop
  | _, [] => True
  | j, l :: rest => l.Holds (ρ j) ∧ HoldsAll ρ (j + 1) rest

/-- If entry `i` of `locs` holds at `ρ (j + i)` for every `i < locs.length`, then
`HoldsAll ρ j locs`. -/
theorem holdsAll_of (ρ : ℕ → ℝ) :
    ∀ (j : ℕ) (locs : List RootLoc), (∀ i < locs.length, (locs.getD i default).Holds (ρ (j + i))) →
      HoldsAll ρ j locs
  | _, [], _ => trivial
  | j, l :: rest, h => by
      refine ⟨by simpa using h 0 (by simp), holdsAll_of ρ (j + 1) rest fun i hi ↦ ?_⟩
      have := h (i + 1) (by simpa using hi)
      rwa [show j + (i + 1) = j + 1 + i by omega] at this

/-- `l₀` bounds `ρ j`, `l₁` bounds `ρ (j + 1)`, and so on; rational points carry no condition. -/
def BoundsAll (ρ : ℕ → ℝ) : ℕ → List RootLoc → Prop
  | _, [] => True
  | j, l :: rest => l.Bounds (ρ j) ∧ BoundsAll ρ (j + 1) rest

/-- The roots with the rational ones written as rationals: `rootVal ρ locs j` is the point of
`locs` at a rational location and `ρ j` otherwise. -/
def rootVal (ρ : ℕ → ℝ) (locs : List RootLoc) (j : ℕ) : ℝ :=
  (locs.getD j default).value (ρ j)

/-- If `HoldsAll ρ j locs`, then entry `i` of `locs` holds at `ρ (j + i)` for every
`i < locs.length`. -/
theorem holds_of_holdsAll (ρ : ℕ → ℝ) :
    ∀ (j : ℕ) (locs : List RootLoc), HoldsAll ρ j locs →
      ∀ i < locs.length, (locs.getD i default).Holds (ρ (j + i))
  | _, [], _, _, hi => absurd hi (by simp)
  | j, l :: rest, ⟨hl, hrest⟩, i, hi => by
      rcases i with _ | i
      · simpa using hl
      · have := holds_of_holdsAll ρ (j + 1) rest hrest i (by simpa using hi)
        simpa [show j + (i + 1) = j + 1 + i by omega] using this

/-- `HoldsAll ρ j locs` implies `BoundsAll ρ j locs`: a root at its location satisfies the interval
bounds of the location. -/
theorem boundsAll_of_holdsAll (ρ : ℕ → ℝ) :
    ∀ (j : ℕ) (locs : List RootLoc), HoldsAll ρ j locs → BoundsAll ρ j locs
  | _, [], _ => trivial
  | j, l :: rest, ⟨hl, hrest⟩ => by
      refine ⟨?_, boundsAll_of_holdsAll ρ (j + 1) rest hrest⟩
      cases l with
      | interval lo hi => exact hl
      | exact q => trivial

/-- If `HoldsAll ρ 0 locs`, then `rootVal ρ locs = ρ`: at a rational location the root is the
rational point. -/
theorem rootVal_eq {ρ : ℕ → ℝ} {locs : List RootLoc} (h : HoldsAll ρ 0 locs) :
    rootVal ρ locs = ρ := by
  funext j
  unfold rootVal
  by_cases hj : j < locs.length
  · have hholds := holds_of_holdsAll ρ 0 locs h j hj
    rw [zero_add] at hholds
    generalize locs.getD j default = l at hholds ⊢
    cases l
    · rfl
    · exact hholds.symm
  · rw [List.getD_eq_default _ _ (by omega)]
    rfl

private theorem getD_mem {locs : List RootLoc} {j : ℕ} (hj : j < locs.length) :
    locs.getD j default ∈ locs :=
  List.getD_eq_getElem _ _ hj ▸ List.getElem_mem hj

private theorem exists_index_of_mem {locs : List RootLoc} {l : RootLoc} (h : l ∈ locs) :
    ∃ j < locs.length, locs.getD j default = l := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h
  exact ⟨j, hj, List.getD_eq_getElem _ _ hj⟩

/-- **Solution sets of a polynomial inequality.** The roots `ρ j` of `expr` lie at the listed
locations, and `expr > 0`, `expr < 0`, `expr ≥ 0`, `expr ≤ 0` and `expr = 0` hold exactly on the
listed gaps and roots. -/
theorem of_reduceCheck (expr : Verified.Expr (Fin 1)) (cert : RootListCertificate)
    (locs : List RootLoc) (cuts : List ℚ) (signs : List Bool)
    (h : reduceCheck expr cert locs cuts signs = true) :
    ∃ ρ : ℕ → ℝ, HoldsAll ρ 0 locs ∧
      (∀ x, 0 < expr.eval ![x] ↔ GapsFormula ρ locs.length x true 0 signs) ∧
      (∀ x, expr.eval ![x] < 0 ↔ GapsFormula ρ locs.length x false 0 signs) ∧
      (∀ x, 0 ≤ expr.eval ![x] ↔
        GapsFormula ρ locs.length x true 0 signs ∨ RootsFormula ρ x 0 locs.length) ∧
      (∀ x, expr.eval ![x] ≤ 0 ↔
        GapsFormula ρ locs.length x false 0 signs ∨ RootsFormula ρ x 0 locs.length) ∧
      (∀ x, expr.eval ![x] = 0 ↔ RootsFormula ρ x 0 locs.length) := by
  unfold reduceCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hroots, hrest⟩ := h
  split at hrest
  · rename_i p hp
    unfold sepCheck at hrest
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      bne_iff_ne, ne_eq] at hrest
    obtain ⟨⟨⟨hlen, hord⟩, hnz⟩, hsigns⟩ := hrest
    obtain ⟨hA, hB, hC⟩ := of_exprRootCheck hroots
    set f : ℝ → ℝ := fun x ↦ expr.eval ![x]
    have hfp : ∀ x, f x = Sparse.evalReal p x := fun x ↦
      (evalReal_eq_eval_of_mvPolyOf? expr p hp x).symm
    have hcont : Continuous f := (Sparse.continuous_evalReal p).congr fun x ↦ (hfp x).symm
    -- Each location carries a root.
    have hexists : ∀ j < locs.length, ∃ r, (locs.getD j default).Holds r ∧ f r = 0 := by
      intro j hj
      have hmem := getD_mem hj
      generalize locs.getD j default = l at hmem ⊢
      cases l with
      | interval lo hi =>
          obtain ⟨r, ⟨hr, hr0⟩, _⟩ := hA _ (List.mem_filterMap.mpr ⟨_, hmem, rfl⟩)
          exact ⟨r, hr, hr0⟩
      | exact q => exact ⟨q, rfl, hB q (List.mem_filterMap.mpr ⟨_, hmem, rfl⟩)⟩
    choose! ρ hρ using hexists
    have hcut : ∀ j, j ≤ locs.length → f (cuts.getD j 0) ≠ 0 := by
      intro j hj
      have hjc : j < cuts.length := by omega
      rw [hfp, Sparse.evalReal_ratCast, Rat.cast_ne_zero, List.getD_eq_getElem _ _ hjc]
      exact hnz _ (List.getElem_mem hjc)
    have hsep : ∀ j < locs.length, ((cuts.getD j 0 : ℚ) : ℝ) < ρ j ∧
        ρ j < ((cuts.getD (j + 1) 0 : ℚ) : ℝ) := by
      intro j hj
      obtain ⟨hlo, hhi⟩ := hord j hj
      obtain ⟨hholds, hzero⟩ := hρ j hj
      have hne1 := hcut j hj.le
      have hne2 := hcut (j + 1) hj
      generalize locs.getD j default = l at hlo hhi hholds
      cases l with
      | interval lo hi =>
          simp only [RootLoc.lower, RootLoc.upper, RootLoc.Holds] at hlo hhi hholds
          exact ⟨lt_of_le_of_lt (by exact_mod_cast hlo) hholds.1,
            hholds.2.trans_le (by exact_mod_cast hhi)⟩
      | exact q =>
          simp only [RootLoc.lower, RootLoc.upper, RootLoc.Holds] at hlo hhi hholds
          rw [hholds] at hzero ⊢
          exact ⟨(by exact_mod_cast hlo : ((cuts.getD j 0 : ℚ) : ℝ) ≤ q).lt_of_ne
              fun heq ↦ hne1 (heq ▸ hzero),
            (by exact_mod_cast hhi : (q : ℝ) ≤ cuts.getD (j + 1) 0).lt_of_ne
              fun heq ↦ hne2 (heq ▸ hzero)⟩
    have hzeros : ∀ x, f x = 0 ↔ ∃ j < locs.length, x = ρ j := by
      refine fun x ↦ ⟨fun hx ↦ ?_, fun ⟨j, hj, hx⟩ ↦ hx ▸ (hρ j hj).2⟩
      rcases hC x hx with ⟨r, hr, rfl⟩ | ⟨I, hI, hxI⟩
      · obtain ⟨l, hl, hlr⟩ := List.mem_filterMap.mp hr
        obtain ⟨j, hj, rfl⟩ := exists_index_of_mem hl
        have hholds := (hρ j hj).1
        cases hloc : locs.getD j default <;>
          simp only [hloc, RootLoc.pointPart, RootLoc.Holds, reduceCtorEq, Option.some.injEq]
            at hlr hholds
        exact ⟨j, hj, hlr ▸ hholds.symm⟩
      · obtain ⟨l, hl, hlI⟩ := List.mem_filterMap.mp hI
        obtain ⟨j, hj, rfl⟩ := exists_index_of_mem hl
        have hholds := (hρ j hj).1
        cases hloc : locs.getD j default <;>
          simp only [hloc, RootLoc.intervalPart, RootLoc.Holds, reduceCtorEq, Option.some.injEq]
            at hlI hholds
        subst hlI
        obtain ⟨r, _, huniq⟩ := hA _ hI
        exact ⟨j, hj, (huniq x ⟨hxI, hx⟩).trans (huniq (ρ j) ⟨hholds, (hρ j hj).2⟩).symm⟩
    have hsignpos : ∀ j ≤ locs.length, (0 < f (cuts.getD j 0) ↔ signs.getD j false = true) := by
      intro j hj
      have hjc : j < cuts.length := by omega
      simp [hfp, Sparse.evalReal_ratCast, hsigns, List.getD_eq_getElem?_getD, hjc]
    have hsignneg : ∀ j ≤ locs.length, (f (cuts.getD j 0) < 0 ↔ signs.getD j false = false) := by
      intro j hj
      rw [← Bool.not_eq_true, ← hsignpos j hj, not_lt]
      exact (hcut j hj).le_iff_lt.symm
    have hslen : signs.length = locs.length + 1 := by simp [hsigns, hlen]
    have hpos : ∀ x, 0 < f x ↔ GapsFormula ρ locs.length x true 0 signs := by
      intro x
      rw [pos_iff_exists_gap hcont hsep hzeros x, gapsFormula_iff]
      simp only [zero_add]
      exact ⟨fun ⟨j, hj, hg, hs⟩ ↦ ⟨j, by omega, hg, (hsignpos j hj).mp hs⟩,
        fun ⟨j, hj, hg, hs⟩ ↦ ⟨j, by omega, hg, (hsignpos j (by omega)).mpr hs⟩⟩
    have hneg : ∀ x, f x < 0 ↔ GapsFormula ρ locs.length x false 0 signs := by
      intro x
      rw [neg_iff_exists_gap hcont hsep hzeros x, gapsFormula_iff]
      simp only [zero_add]
      exact ⟨fun ⟨j, hj, hg, hs⟩ ↦ ⟨j, by omega, hg, (hsignneg j hj).mp hs⟩,
        fun ⟨j, hj, hg, hs⟩ ↦ ⟨j, by omega, hg, (hsignneg j (by omega)).mpr hs⟩⟩
    have hzero : ∀ x, f x = 0 ↔ RootsFormula ρ x 0 locs.length := by
      intro x
      rw [hzeros x, rootsFormula_iff]
      simp
    refine ⟨ρ, holdsAll_of ρ 0 locs fun i hi ↦ by simpa using (hρ i hi).1, hpos, hneg,
      fun x ↦ ?_, fun x ↦ ?_, hzero⟩
    · rw [le_iff_lt_or_eq, hpos x, eq_comm, hzero x]
    · rw [le_iff_lt_or_eq, hneg x, hzero x]
  · cases hrest

/-! ## Quotients have the sign of products -/

/-- For real `a` and `b`, `0 < a / b ↔ 0 < a * b`, from Mathlib's `div_pos_iff` and `mul_pos_iff`.
It is kept as a single iff because `#cas [reduce x]` rewrites with it right to left (`reversed` in
`Digits.cleanProof`) to state the sign of a product as that of a quotient. -/
theorem div_pos_iff_mul_pos {a b : ℝ} : 0 < a / b ↔ 0 < a * b := by
  rw [div_pos_iff, mul_pos_iff]

/-- For real `a` and `b`, `a / b < 0 ↔ a * b < 0`, from Mathlib's `div_neg_iff` and `mul_neg_iff`.
It is kept as a single iff because `#cas [reduce x]` rewrites with it right to left (`reversed` in
`Digits.cleanProof`) to state the sign of a product as that of a quotient. -/
theorem div_neg_iff_mul_neg {a b : ℝ} : a / b < 0 ↔ a * b < 0 := by
  rw [div_neg_iff, mul_neg_iff]

/-- For real `a` and `b`, `0 ≤ a / b ↔ 0 ≤ a * b`, from Mathlib's `div_nonneg_iff` and
`mul_nonneg_iff`. It is kept as a single iff because `#cas [reduce x]` rewrites with it right to
left (`reversed` in `Digits.cleanProof`) to state the sign of a product as that of a quotient. -/
theorem div_nonneg_iff_mul_nonneg {a b : ℝ} : 0 ≤ a / b ↔ 0 ≤ a * b := by
  rw [div_nonneg_iff, mul_nonneg_iff]

/-- For real `a` and `b`, `a / b ≤ 0 ↔ a * b ≤ 0`, from Mathlib's `div_nonpos_iff` and
`mul_nonpos_iff`. It is kept as a single iff because `#cas [reduce x]` rewrites with it right to
left (`reversed` in `Digits.cleanProof`) to state the sign of a product as that of a quotient. -/
theorem div_nonpos_iff_mul_nonpos {a b : ℝ} : a / b ≤ 0 ↔ a * b ≤ 0 := by
  rw [div_nonpos_iff, mul_nonpos_iff]

/-- For real `a` and `b`, `a / b = 0 ↔ a * b = 0`, from Mathlib's `div_eq_zero_iff` and
`mul_eq_zero`. It is kept as a single iff because `#cas [reduce x]` rewrites with it right to left
(`reversed` in `Digits.cleanProof`) to state a product equation as a quotient equation. -/
theorem div_eq_zero_iff_mul_eq_zero {a b : ℝ} : a / b = 0 ↔ a * b = 0 := by
  rw [div_eq_zero_iff, mul_eq_zero]

section Projections

/-! The statements below write the rational roots as rationals (`rootVal`) and keep the
interval bounds of the others (`BoundsAll`). -/

variable (expr : Verified.Expr (Fin 1)) (cert : RootListCertificate) (locs : List RootLoc)
  (cuts : List ℚ) (signs : List Bool)

/-- If `reduceCheck` accepts, there are roots `ρ` within the interval bounds of `locs` such that
`0 < expr x` holds exactly on the gaps whose cut sign is `true`, with the rational roots written as
rationals (`rootVal`). -/
theorem of_reduceCheck_pos (h : reduceCheck expr cert locs cuts signs = true) :
    ∃ ρ : ℕ → ℝ, BoundsAll ρ 0 locs ∧
      ∀ x, 0 < expr.eval ![x] ↔ GapsFormula (rootVal ρ locs) locs.length x true 0 signs := by
  obtain ⟨ρ, h1, h2, -⟩ := of_reduceCheck expr cert locs cuts signs h
  exact ⟨ρ, boundsAll_of_holdsAll ρ 0 locs h1, by rwa [rootVal_eq h1]⟩

/-- If `reduceCheck` accepts, there are roots `ρ` within the interval bounds of `locs` such that
`expr x < 0` holds exactly on the gaps whose cut sign is `false`, with the rational roots written as
rationals (`rootVal`). -/
theorem of_reduceCheck_neg (h : reduceCheck expr cert locs cuts signs = true) :
    ∃ ρ : ℕ → ℝ, BoundsAll ρ 0 locs ∧
      ∀ x, expr.eval ![x] < 0 ↔ GapsFormula (rootVal ρ locs) locs.length x false 0 signs := by
  obtain ⟨ρ, h1, -, h3, -⟩ := of_reduceCheck expr cert locs cuts signs h
  exact ⟨ρ, boundsAll_of_holdsAll ρ 0 locs h1, by rwa [rootVal_eq h1]⟩

/-- If `reduceCheck` accepts, there are roots `ρ` within the interval bounds of `locs` such that
`0 ≤ expr x` holds exactly on the gaps whose cut sign is `true` and at the roots, with the rational
roots written as rationals (`rootVal`). -/
theorem of_reduceCheck_nonneg (h : reduceCheck expr cert locs cuts signs = true) :
    ∃ ρ : ℕ → ℝ, BoundsAll ρ 0 locs ∧
      ∀ x, 0 ≤ expr.eval ![x] ↔ GapsFormula (rootVal ρ locs) locs.length x true 0 signs ∨
        RootsFormula (rootVal ρ locs) x 0 locs.length := by
  obtain ⟨ρ, h1, -, -, h4, -⟩ := of_reduceCheck expr cert locs cuts signs h
  exact ⟨ρ, boundsAll_of_holdsAll ρ 0 locs h1, by rwa [rootVal_eq h1]⟩

/-- If `reduceCheck` accepts, there are roots `ρ` within the interval bounds of `locs` such that
`expr x ≤ 0` holds exactly on the gaps whose cut sign is `false` and at the roots, with the rational
roots written as rationals (`rootVal`). -/
theorem of_reduceCheck_nonpos (h : reduceCheck expr cert locs cuts signs = true) :
    ∃ ρ : ℕ → ℝ, BoundsAll ρ 0 locs ∧
      ∀ x, expr.eval ![x] ≤ 0 ↔ GapsFormula (rootVal ρ locs) locs.length x false 0 signs ∨
        RootsFormula (rootVal ρ locs) x 0 locs.length := by
  obtain ⟨ρ, h1, -, -, -, h5, -⟩ := of_reduceCheck expr cert locs cuts signs h
  exact ⟨ρ, boundsAll_of_holdsAll ρ 0 locs h1, by rwa [rootVal_eq h1]⟩

/-- If `reduceCheck` accepts, there are roots `ρ` within the interval bounds of `locs` such that
`expr x = 0` holds exactly at the roots, with the rational roots written as rationals
(`rootVal`). -/
theorem of_reduceCheck_zero (h : reduceCheck expr cert locs cuts signs = true) :
    ∃ ρ : ℕ → ℝ, BoundsAll ρ 0 locs ∧
      ∀ x, expr.eval ![x] = 0 ↔ RootsFormula (rootVal ρ locs) x 0 locs.length := by
  obtain ⟨ρ, h1, -, -, -, -, h6⟩ := of_reduceCheck expr cert locs cuts signs h
  exact ⟨ρ, boundsAll_of_holdsAll ρ 0 locs h1, by rwa [rootVal_eq h1]⟩

/-- If `reduceCheck` accepts, there are roots `ρ` within the interval bounds of `locs` such that
`expr x ≠ 0` holds exactly away from the roots, with the rational roots written as rationals
(`rootVal`). -/
theorem of_reduceCheck_ne (h : reduceCheck expr cert locs cuts signs = true) :
    ∃ ρ : ℕ → ℝ, BoundsAll ρ 0 locs ∧
      ∀ x, expr.eval ![x] ≠ 0 ↔ ¬ RootsFormula (rootVal ρ locs) x 0 locs.length := by
  obtain ⟨ρ, h1, h6⟩ := of_reduceCheck_zero expr cert locs cuts signs h
  exact ⟨ρ, h1, fun x ↦ (h6 x).not⟩

end Projections

/-! ## Polynomials of one sign -/

/-- `GapsFormula` holds nowhere when no sign equals `want`. -/
theorem not_gapsFormula_of_all_ne (ρ : ℕ → ℝ) (k : ℕ) (x : ℝ) (want : Bool) :
    ∀ (j : ℕ) (signs : List Bool), signs.all (· != want) = true →
      ¬ GapsFormula ρ k x want j signs
  | _, [], _ => fun h ↦ h
  | j, s :: rest, h => by
      simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rintro (⟨hs, -⟩ | hrest)
      · exact h.1 hs
      · exact not_gapsFormula_of_all_ne ρ k x want (j + 1) rest h.2 hrest

namespace RootLoc

/-- The location lies below `a`: `hi ≤ a` for an interval, `q < a` for a rational point. -/
def before (a : ℚ) : RootLoc → Bool
  | interval _ hi => decide (hi ≤ a)
  | exact q => decide (q < a)

/-- The location lies above `b`: `b ≤ lo` for an interval, `b < q` for a rational point. -/
def after (b : ℚ) : RootLoc → Bool
  | interval lo _ => decide (b ≤ lo)
  | exact q => decide (b < q)

/-- A root `r` at the location `l` is at most its right end `l.upper`. -/
theorem le_upper {l : RootLoc} {r : ℝ} (h : l.Holds r) : r ≤ l.upper := by
  cases l with
  | interval lo hi => exact h.2.le
  | exact q => exact h.le

/-- A root `r` at the location `l` is at least its left end `l.lower`. -/
theorem lower_le {l : RootLoc} {r : ℝ} (h : l.Holds r) : (l.lower : ℝ) ≤ r := by
  cases l with
  | interval lo hi => exact h.1.le
  | exact q => exact h.ge

/-- If the root `r` lies at `l` and `l.before a` holds, then `r < a`. -/
theorem lt_of_before {l : RootLoc} {a : ℚ} {r : ℝ} (h : l.Holds r) (hb : l.before a = true) :
    r < a := by
  cases l with
  | interval lo hi =>
      simp only [before, decide_eq_true_eq] at hb
      exact h.2.trans_le (by exact_mod_cast hb)
  | exact q =>
      simp only [before, decide_eq_true_eq] at hb
      rw [show r = q from h]
      exact_mod_cast hb

/-- If the root `r` lies at `l` and `l.after b` holds, then `b < r`. -/
theorem lt_of_after {l : RootLoc} {b : ℚ} {r : ℝ} (h : l.Holds r) (ha : l.after b = true) :
    (b : ℝ) < r := by
  cases l with
  | interval lo hi =>
      simp only [after, decide_eq_true_eq] at ha
      exact (by exact_mod_cast ha : (b : ℝ) ≤ lo).trans_lt h.1
  | exact q =>
      simp only [after, decide_eq_true_eq] at ha
      rw [show r = q from h]
      exact_mod_cast ha

end RootLoc

/-- The gaps whose cut has a negative sign avoid `[a, b]`: each ends at or below `a` (the gap
below location `j`, with `upper ≤ a`) or starts at or above `b` (the gap above location
`j - 1`, with `b ≤ lower`). -/
def gapSignsOn (locs : List RootLoc) (signs : List Bool) (a b : ℚ) : Bool :=
  (List.range (locs.length + 1)).all fun j ↦
    signs.getD j false ||
      (decide (j < locs.length) && decide ((locs.getD j default).upper ≤ a)) ||
      (decide (0 < j) && decide (b ≤ (locs.getD (j - 1) default).lower))

section OneSign

variable {expr : Verified.Expr (Fin 1)} {cert : RootListCertificate} {locs : List RootLoc}
  {cuts : List ℚ} {signs : List Bool}

/-- **A polynomial without negative cuts is nonnegative.** If the polynomial is positive at every
cut, it is negative on no gap, so it is nonnegative everywhere. -/
theorem nonneg_of_reduceCheck (h : reduceCheck expr cert locs cuts signs = true)
    (hs : signs.all (· != false) = true) (x : ℝ) : 0 ≤ expr.eval ![x] := by
  obtain ⟨ρ, -, -, hneg, -⟩ := of_reduceCheck expr cert locs cuts signs h
  exact not_lt.mp fun hlt ↦ not_gapsFormula_of_all_ne ρ _ x false 0 signs hs ((hneg x).mp hlt)

/-- **A polynomial without real roots and negative cuts is positive.** -/
theorem pos_of_reduceCheck (h : reduceCheck expr cert [] cuts signs = true)
    (hs : signs.all (· != false) = true) (x : ℝ) : 0 < expr.eval ![x] := by
  obtain ⟨ρ, -, -, -, -, -, hzero⟩ := of_reduceCheck expr cert [] cuts signs h
  refine lt_of_le_of_ne (nonneg_of_reduceCheck h hs x) fun h0 ↦ ?_
  simpa [RootsFormula] using (hzero x).mp h0.symm

/-- If `reduceCheck` accepts, there is one sign for each of the `locs.length + 1` gaps:
`signs.length = locs.length + 1`. -/
theorem length_signs_of_reduceCheck (h : reduceCheck expr cert locs cuts signs = true) :
    signs.length = locs.length + 1 := by
  unfold reduceCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, hrest⟩ := h
  split at hrest
  · unfold sepCheck at hrest
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
    obtain ⟨⟨⟨hlen, -⟩, -⟩, hsigns⟩ := hrest
    simp [hsigns, hlen]
  · cases hrest

/-- **A polynomial without negative gaps in `[a, b]` is nonnegative there.** Every gap whose
cut has a negative sign ends at or below `a` or starts at or above `b`. -/
theorem nonneg_on_Icc_of_reduceCheck (h : reduceCheck expr cert locs cuts signs = true)
    {a b : ℚ} (hs : gapSignsOn locs signs a b = true) :
    ∀ x ∈ Icc (a : ℝ) b, 0 ≤ expr.eval ![x] := by
  obtain ⟨ρ, hholds, -, hneg, -⟩ := of_reduceCheck expr cert locs cuts signs h
  have hlen := length_signs_of_reduceCheck h
  intro x hx
  refine not_lt.mp fun hlt ↦ ?_
  obtain ⟨i, hi, hgap, hsign⟩ := (gapsFormula_iff ρ _ x false 0 signs).mp ((hneg x).mp hlt)
  rw [zero_add] at hgap
  simp only [gapSignsOn, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hs
  rcases hs i (by omega) with (hs1 | ⟨hik, hup⟩) | ⟨hi0, hlow⟩
  · rw [hsign] at hs1
    exact Bool.false_ne_true hs1
  · have hxlt : x < ρ i := hgap.2.resolve_left (by omega)
    have hl := holds_of_holdsAll ρ 0 locs hholds i hik
    rw [zero_add] at hl
    have hup' : (((locs.getD i default).upper : ℚ) : ℝ) ≤ a := by exact_mod_cast hup
    linarith [(locs.getD i default).le_upper hl, hx.1]
  · have hxgt : ρ (i - 1) < x := hgap.1.resolve_left (by omega)
    have hl := holds_of_holdsAll ρ 0 locs hholds (i - 1) (by omega)
    rw [zero_add] at hl
    have hlow' : (b : ℝ) ≤ (((locs.getD (i - 1) default).lower : ℚ) : ℝ) := by
      exact_mod_cast hlow
    linarith [(locs.getD (i - 1) default).lower_le hl, hx.2]

/-- **A polynomial without negative gaps and roots in `[a, b]` is positive there.** Every
root location lies below `a` or above `b`. -/
theorem pos_on_Icc_of_reduceCheck (h : reduceCheck expr cert locs cuts signs = true)
    {a b : ℚ} (hs : gapSignsOn locs signs a b = true)
    (hr : locs.all (fun l ↦ l.before a || l.after b) = true) :
    ∀ x ∈ Icc (a : ℝ) b, 0 < expr.eval ![x] := by
  obtain ⟨ρ, hholds, -, -, -, -, hzero⟩ := of_reduceCheck expr cert locs cuts signs h
  intro x hx
  refine lt_of_le_of_ne (nonneg_on_Icc_of_reduceCheck h hs x hx) fun h0 ↦ ?_
  obtain ⟨i, hi, hxi⟩ := (rootsFormula_iff ρ x 0 locs.length).mp ((hzero x).mp h0.symm)
  rw [zero_add] at hxi
  have hl := holds_of_holdsAll ρ 0 locs hholds i hi
  rw [zero_add, ← hxi] at hl
  have hloc := List.all_eq_true.mp hr _ (getD_mem hi)
  simp only [Bool.or_eq_true] at hloc
  rcases hloc with hb | ha
  · exact absurd hx.1 (not_le.mpr ((locs.getD i default).lt_of_before hl hb))
  · exact absurd hx.2 (not_le.mpr ((locs.getD i default).lt_of_after hl ha))

/-- Transport `0 ≤ expr` to `a ≤ b` through `expr = b - a`. -/
theorem le_of_eval_nonneg {x a b : ℝ} (h : 0 ≤ expr.eval ![x])
    (hx : expr.eval ![x] = b - a) : a ≤ b :=
  sub_nonneg.mp (hx ▸ h)

/-- Transport `0 < expr` to `a < b` through `expr = b - a`. -/
theorem lt_of_eval_pos {x a b : ℝ} (h : 0 < expr.eval ![x])
    (hx : expr.eval ![x] = b - a) : a < b :=
  sub_pos.mp (hx ▸ h)

end OneSign

/-! ## Systems in triangular form -/

/-- `Q (σ j) ∨ Q (σ (j + 1)) ∨ ⋯`, with `n` disjuncts. -/
def PointsFormula (σ : ℕ → ℝ) (Q : ℝ → Prop) : ℕ → ℕ → Prop
  | _, 0 => False
  | j, n + 1 => Q (σ j) ∨ PointsFormula σ Q (j + 1) n

/-- `PointsFormula σ Q j n` holds exactly when `Q (σ (j + i))` holds for some `i < n`. -/
theorem pointsFormula_iff (σ : ℕ → ℝ) (Q : ℝ → Prop) :
    ∀ j n, PointsFormula σ Q j n ↔ ∃ i < n, Q (σ (j + i)) := by
  intro j n
  induction n generalizing j with
  | zero => simp [PointsFormula]
  | succ n ih =>
      rw [PointsFormula, ih, Nat.exists_lt_succ_left]
      simp only [add_zero, add_assoc, Nat.add_comm 1]

/-- **Solutions of a system in triangular form.** Let the real roots of `R` be certified by
`reduceCheck`. A point of a system equivalent to `R τ = 0 ∧ Q τ`, where `Q s` fixes every
coordinate in terms of `s` and `Q s` forces `τ = s` on the roots of `R`, is one of the points
`Q (ρ j)`. -/
theorem solve_of_reduceCheck (expr : Verified.Expr (Fin 1)) (cert : RootListCertificate)
    (locs : List RootLoc) (cuts : List ℚ) (signs : List Bool)
    (h : reduceCheck expr cert locs cuts signs = true) {R : ℝ → ℝ}
    (hR : ∀ s, expr.eval ![s] = R s) :
    ∃ ρ : ℕ → ℝ, BoundsAll ρ 0 locs ∧ ∀ (τ : ℝ) (Q : ℝ → Prop),
      (∀ s, R s = 0 → Q s → τ = s) →
        (R τ = 0 ∧ Q τ ↔ PointsFormula (rootVal ρ locs) Q 0 locs.length) := by
  obtain ⟨ρ, hb, hzero⟩ := of_reduceCheck_zero expr cert locs cuts signs h
  refine ⟨ρ, hb, fun τ Q hτ ↦ ?_⟩
  have hroots (s : ℝ) : R s = 0 ↔ ∃ i < locs.length, s = rootVal ρ locs i := by
    simp [← hR, hzero, rootsFormula_iff]
  rw [pointsFormula_iff]
  simp only [zero_add]
  constructor
  · rintro ⟨hτ0, hQ⟩
    obtain ⟨i, hi, rfl⟩ := (hroots τ).mp hτ0
    exact ⟨i, hi, hQ⟩
  · rintro ⟨i, hi, hQ⟩
    have h0 : R (rootVal ρ locs i) = 0 := (hroots _).mpr ⟨i, hi, rfl⟩
    obtain rfl := hτ _ h0 hQ
    exact ⟨h0, hQ⟩

end CAS.Polynomial.RealRoot

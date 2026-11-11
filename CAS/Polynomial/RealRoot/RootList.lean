/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.RealRoot.CauchyBound
public import CAS.Polynomial.RealRoot.Interval
public import CAS.Polynomial.RealRoot.RadicalGenerator

/-!
# Complete lists of real roots

A finite check that lists every real root of a rational polynomial `p`. `of_realRootCheck`
turns one Boolean check of a certificate (`RootListCertificate`) into the statement that each
listed interval contains exactly one root, that each listed rational is a root, and that every
real root is one of these. The check also asks that the listed intervals and rationals be
pairwise disjoint (`separatedCheck`), so that the lists count the real roots. The certificate is
found in compiled code (`CAS.Command.RootIsolation`); the kernel only checks it.

## Main results

* `of_rootCellCheck_root`, `of_rootCellCheck_exact`: the root of one cell.
* `of_rootCoverCheck`: the roots in `(a, b]`.
* `of_realRootCheck`, `of_exprRootCheck`: all real roots of a polynomial or of a polynomial
  expression.
* `separatedCheck_of_realRootCheck`, `separatedCheck_of_exprRootCheck`: the listed roots are
  distinct.
* `eval_eq_zero_of_covered`, `eval_eq_zero_of_covered_of_exprRootCheck`: a root of the covered
  polynomial is a root of the original one.
* `evalReal_eq_eval_of_mvPolyOf?`: the polynomial of a one-variable expression.

## Implementation notes

The certificate splits off the rational roots by the identity `p = c · ∏ (X - rᵢ) · q`, checked
on coefficient lists. The quotient `q`, or its square-free radical (`RadicalCertificate`) when
`q` has repeated factors, has the remaining real roots; a Cauchy bound (`CauchyBoundCertificate`)
puts them in `(-B, B)`. We cover `[-B, B]` by consecutive cells of three kinds for this covered
polynomial (`covered`).

* A free cell: the enclosure of the polynomial on the cell excludes zero (`rootFree`).
* A refined root cell: a root bracket on the cell (opposite endpoint signs and a strict sign of
  the derivative enclosure), and a second bracket on a subinterval `[lo, hi]` whose endpoints
  are not roots. The cell has exactly one root, and it lies in `(lo, hi)`.
* An exact root cell: a root bracket on the cell and a rational point `r` of the cell with
  `p r = 0`. The cell has exactly one root, `r`.
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Set
open CAS.Continuum

/-- The interval `[a, b]` when `a ≤ b`, and the point `a` otherwise. -/
def cellInterval (a b : ℚ) : RationalInterval :=
  if h : a ≤ b then RationalInterval.ofBounds a b h else RationalInterval.const a

/-- For `a ≤ b`, the lower endpoint of `cellInterval a b` is `a`. -/
theorem cellInterval_lo {a b : ℚ} (h : a ≤ b) : (cellInterval a b).lo = a := by
  simp [cellInterval, h, RationalInterval.ofBounds]

/-- For `a ≤ b`, the upper endpoint of `cellInterval a b` is `b`. -/
theorem cellInterval_hi {a b : ℚ} (h : a ≤ b) : (cellInterval a b).hi = b := by
  simp [cellInterval, h, RationalInterval.ofBounds]

/-- The kind of a cell of a root cover. -/
inductive RootCell where
  /-- No root in the cell. -/
  | free
  /-- One root, in `(lo, hi)`. -/
  | root (direction : Direction) (lo hi : ℚ)
  /-- One root, the rational `r`. -/
  | exact (direction : Direction) (r : ℚ)
  deriving DecidableEq, Repr

/-- The check of one cell `[a, t]`. -/
def rootCellCheck (p : Sparse.Univariate) (a t : ℚ) : RootCell → Bool
  | .free => rootFree p (cellInterval a t)
  | .root direction lo hi =>
      RootBracket.valid p ⟨cellInterval a t, direction⟩ && decide (a ≤ lo) &&
        decide (lo ≤ hi) && decide (hi ≤ t) &&
        RootBracket.valid p ⟨cellInterval lo hi, direction⟩ &&
        decide (Sparse.evalRat p lo ≠ 0) && decide (Sparse.evalRat p hi ≠ 0)
  | .exact direction r =>
      RootBracket.valid p ⟨cellInterval a t, direction⟩ && decide (a ≤ r) && decide (r ≤ t) &&
        decide (Sparse.evalRat p r = 0)

/-- Consecutive cells `[a, t₁], [t₁, t₂], …` ending at `b`, each cell checked. -/
def rootCoverCheck (p : Sparse.Univariate) : ℚ → List (ℚ × RootCell) → ℚ → Bool
  | a, [], b => decide (a = b)
  | a, (t, cell) :: rest, b =>
      decide (a < t) && rootCellCheck p a t cell && rootCoverCheck p t rest b

/-- The refinements of the refined root cells. -/
def rootIntervals : List (ℚ × RootCell) → List (ℚ × ℚ)
  | [] => []
  | (_, .root _ lo hi) :: rest => (lo, hi) :: rootIntervals rest
  | _ :: rest => rootIntervals rest

/-- The exact roots. -/
def rootPoints : List (ℚ × RootCell) → List ℚ
  | [] => []
  | (_, .exact _ r) :: rest => r :: rootPoints rest
  | _ :: rest => rootPoints rest

private theorem mem_cell {a t : ℚ} (hat : a ≤ t) {x : ℝ} (hx : x ∈ Icc (a : ℝ) t) :
    x ∈ Icc ((cellInterval a t).lo : ℝ) ((cellInterval a t).hi : ℝ) := by
  rwa [cellInterval_lo hat, cellInterval_hi hat]

/-- A root bracket on `[a, t]` makes the polynomial injective on its zeros in `[a, t]`. -/
private theorem eq_of_bracket {p : Sparse.Univariate} {a t : ℚ} (hat : a ≤ t)
    {direction : Direction} (h : RootBracket.valid p ⟨cellInterval a t, direction⟩ = true)
    {x y : ℝ} (hx : x ∈ Icc (a : ℝ) t) (hy : y ∈ Icc (a : ℝ) t)
    (hx0 : Sparse.evalReal p x = 0) (hy0 : Sparse.evalReal p y = 0) : x = y := by
  obtain ⟨z, _, hz⟩ := RootBracket.existsUnique_root p _ h
  exact (hz x ⟨mem_cell hat hx, hx0⟩).trans (hz y ⟨mem_cell hat hy, hy0⟩).symm

/-- A refined root cell: exactly one root in `(lo, hi)`, and every root of the cell lies
there. -/
theorem of_rootCellCheck_root {p : Sparse.Univariate} {a t lo hi : ℚ}
    {direction : Direction} (h : rootCellCheck p a t (.root direction lo hi) = true) :
    (∃! x, x ∈ Ioo (lo : ℝ) hi ∧ Sparse.evalReal p x = 0) ∧
      ∀ x ∈ Icc (a : ℝ) t, Sparse.evalReal p x = 0 → x ∈ Ioo (lo : ℝ) hi := by
  simp only [rootCellCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hcell, halo⟩, hlohi⟩, hhit⟩, hsub⟩, hlo0⟩, hhi0⟩ := h
  have hat : a ≤ t := halo.trans (hlohi.trans hhit)
  obtain ⟨z, ⟨hzI, hz0⟩, _⟩ := RootBracket.existsUnique_root p _ hsub
  rw [cellInterval_lo hlohi, cellInterval_hi hlohi] at hzI
  have hlo' : (a : ℝ) ≤ lo := by exact_mod_cast halo
  have hhi' : (hi : ℝ) ≤ t := by exact_mod_cast hhit
  have hzcell : z ∈ Icc (a : ℝ) t := ⟨hlo'.trans hzI.1, hzI.2.trans hhi'⟩
  have hzlo : z ≠ lo := fun heq ↦ hlo0 (by
    exact_mod_cast (Sparse.evalReal_ratCast p lo).symm.trans (heq ▸ hz0))
  have hzhi : z ≠ hi := fun heq ↦ hhi0 (by
    exact_mod_cast (Sparse.evalReal_ratCast p hi).symm.trans (heq ▸ hz0))
  have hzopen : z ∈ Ioo (lo : ℝ) hi :=
    ⟨lt_of_le_of_ne hzI.1 (Ne.symm hzlo), lt_of_le_of_ne hzI.2 hzhi⟩
  refine ⟨⟨z, ⟨hzopen, hz0⟩, fun w hw ↦ ?_⟩, fun x hx hx0 ↦ ?_⟩
  · exact eq_of_bracket hat hcell ⟨hlo'.trans hw.1.1.le, hw.1.2.le.trans hhi'⟩ hzcell hw.2 hz0
  · rw [eq_of_bracket hat hcell hx hzcell hx0 hz0]
    exact hzopen

/-- An exact root cell: `r` is a root, and every root of the cell is `r`. -/
theorem of_rootCellCheck_exact {p : Sparse.Univariate} {a t r : ℚ}
    {direction : Direction} (h : rootCellCheck p a t (.exact direction r) = true) :
    Sparse.evalReal p r = 0 ∧
      ∀ x ∈ Icc (a : ℝ) t, Sparse.evalReal p x = 0 → x = r := by
  simp only [rootCellCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hcell, har⟩, hrt⟩, hr0⟩ := h
  have hat : a ≤ t := har.trans hrt
  have hroot : Sparse.evalReal p r = 0 := by
    rw [Sparse.evalReal_ratCast, hr0, Rat.cast_zero]
  refine ⟨hroot, fun x hx hx0 ↦ ?_⟩
  exact eq_of_bracket hat hcell hx ⟨by exact_mod_cast har, by exact_mod_cast hrt⟩ hx0 hroot

/-- A checked cover lists the roots in `(a, b]`. -/
theorem of_rootCoverCheck {p : Sparse.Univariate} :
    ∀ {a b : ℚ} {cells : List (ℚ × RootCell)}, rootCoverCheck p a cells b = true →
      (∀ I ∈ rootIntervals cells, ∃! x, x ∈ Ioo (I.1 : ℝ) I.2 ∧ Sparse.evalReal p x = 0) ∧
      (∀ r ∈ rootPoints cells, Sparse.evalReal p r = 0) ∧
      ∀ x ∈ Ioc (a : ℝ) b, Sparse.evalReal p x = 0 →
        (∃ r ∈ rootPoints cells, x = r) ∨ ∃ I ∈ rootIntervals cells, x ∈ Ioo (I.1 : ℝ) I.2
  | a, b, [], h => by
      simp only [rootCoverCheck, decide_eq_true_eq] at h
      subst h
      simp [rootIntervals, rootPoints]
  | a, b, (t, cell) :: rest, h => by
      simp only [rootCoverCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hat, hcell⟩, hrest⟩ := h
      obtain ⟨ihIntervals, ihPoints, ihRoots⟩ := of_rootCoverCheck hrest
      cases cell with
      | free =>
          refine ⟨ihIntervals, ihPoints, fun x hx hx0 ↦ ?_⟩
          by_cases hxt : x ≤ t
          · exact absurd hx0 (nonzeroOn_of_rootFree_eq_true p _ hcell x
              (mem_cell hat.le ⟨hx.1.le, hxt⟩))
          · exact ihRoots x ⟨lt_of_not_ge hxt, hx.2⟩ hx0
      | root direction lo hi =>
          have hroot := of_rootCellCheck_root hcell
          refine ⟨List.forall_mem_cons.2 ⟨hroot.1, ihIntervals⟩, ihPoints, fun x hx hx0 ↦ ?_⟩
          by_cases hxt : x ≤ t
          · exact Or.inr ⟨(lo, hi), List.mem_cons_self, hroot.2 x ⟨hx.1.le, hxt⟩ hx0⟩
          · rcases ihRoots x ⟨lt_of_not_ge hxt, hx.2⟩ hx0 with hpoint | ⟨I, hI, hxI⟩
            · exact Or.inl hpoint
            · exact Or.inr ⟨I, List.mem_cons_of_mem _ hI, hxI⟩
      | exact direction r =>
          have hexact := of_rootCellCheck_exact hcell
          refine ⟨ihIntervals, List.forall_mem_cons.2 ⟨hexact.1, ihPoints⟩, fun x hx hx0 ↦ ?_⟩
          by_cases hxt : x ≤ t
          · exact Or.inl ⟨r, List.mem_cons_self, hexact.2 x ⟨hx.1.le, hxt⟩ hx0⟩
          · rcases ihRoots x ⟨lt_of_not_ge hxt, hx.2⟩ hx0 with ⟨s, hs, hxs⟩ | hinterval
            · exact Or.inl ⟨s, List.mem_cons_of_mem _ hs, hxs⟩
            · exact Or.inr hinterval

/-- A certificate for the complete list of real roots of a polynomial `p`. The identity
`p = content · ∏ (X - rᵢ) · quotient` splits off the rational roots `rᵢ`, with multiplicity.
The real roots of the quotient are those of `covered`: the quotient itself, or its radical
`radical` when the quotient is not square-free. `bound` is a Cauchy bound `B` of `covered`, and
`cells` cover `[-B, B]`. -/
structure RootListCertificate where
  /-- The constant factor. -/
  content : ℚ
  /-- The rational roots, with multiplicity. -/
  roots : List ℚ
  /-- The quotient by the linear factors, as a coefficient list, constant term first. -/
  quotient : List ℚ
  /-- A radical certificate for the quotient, absent when the quotient is square-free. -/
  radical : Option RadicalCertificate := none
  /-- A Cauchy bound of the covered polynomial. -/
  bound : CauchyBoundCertificate
  /-- A root cover of `[-B, B]` for the covered polynomial. -/
  cells : List (ℚ × RootCell)

namespace RootListCertificate

/-- The polynomial the cells cover: the radical of the quotient, or the quotient itself. -/
def covered (cert : RootListCertificate) : Sparse.Univariate :=
  match cert.radical with
  | some radical => radical.radical
  | none => Sparse.ofCoeffs cert.quotient

/-- The roots of `p = content · ∏ (X - rᵢ) · quotient` are the `rᵢ` and the roots of the covered
polynomial. -/
theorem evalReal_eq_zero_iff {p : Sparse.Univariate} {cert : RootListCertificate}
    (hc : cert.content ≠ 0)
    (hid : coeffEq (Sparse.coeffs p)
      (coeffScale cert.content (coeffProdLinear cert.roots cert.quotient)) = true)
    (hrad : cert.radical.all (·.valid (Sparse.ofCoeffs cert.quotient)) = true) (x : ℝ) :
    Sparse.evalReal p x = 0 ↔ (∃ r ∈ cert.roots, x = r) ∨ Sparse.evalReal cert.covered x = 0 := by
  have hq : coeffEval cert.quotient x = 0 ↔ Sparse.evalReal cert.covered x = 0 := by
    unfold covered
    cases hr : cert.radical with
    | none => simp [Sparse.evalReal_ofCoeffs]
    | some radical =>
        rw [hr, Option.all_some] at hrad
        rw [← Sparse.evalReal_ofCoeffs]
        exact radical.evalReal_eq_zero_iff _ hrad x
  rw [← Sparse.coeffEval_coeffs, coeffEval_eq_of_coeffEq hid, coeffEval_coeffScale,
    coeffEval_coeffProdLinear, mul_eq_zero, mul_eq_zero, ← hq]
  simp [hc, List.prod_eq_zero_iff, sub_eq_zero]

end RootListCertificate

/-- The listed rational points and open rational intervals are pairwise disjoint. -/
def separatedCheck (intervals : List (ℚ × ℚ)) (points : List ℚ) : Bool :=
  decide (intervals.Pairwise fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1) && decide points.Nodup &&
    points.all fun r ↦ intervals.all fun I ↦ decide (r ≤ I.1 ∨ I.2 ≤ r)

/-- The check of a root-list certificate for `original`, listing the root intervals `intervals`
of its refined root cells and the rational roots `points`: the identity, the radical, the bound
and the cover, the rational roots outside the root intervals, `points` the rational roots of the
identity and of the cover, and the listed intervals and rationals pairwise disjoint. -/
def realRootCheck (original : Sparse.Univariate) (cert : RootListCertificate)
    (intervals : List (ℚ × ℚ)) (points : List ℚ) : Bool :=
  decide (cert.content ≠ 0) &&
    coeffEq (Sparse.coeffs original)
      (coeffScale cert.content (coeffProdLinear cert.roots cert.quotient)) &&
    cert.radical.all (·.valid (Sparse.ofCoeffs cert.quotient)) &&
    cert.bound.valid cert.covered &&
    rootCoverCheck cert.covered (-cert.bound.bound) cert.cells cert.bound.bound &&
    decide (rootIntervals cert.cells = intervals) &&
    points.all (fun r ↦ cert.roots.contains r || (rootPoints cert.cells).contains r) &&
    cert.roots.all points.contains && (rootPoints cert.cells).all points.contains &&
    (cert.roots.all fun r ↦ intervals.all fun I ↦ decide (r ≤ I.1) || decide (I.2 ≤ r)) &&
    separatedCheck intervals points

private theorem realRootCheck_spec {original : Sparse.Univariate} {cert : RootListCertificate}
    {intervals : List (ℚ × ℚ)} {points : List ℚ}
    (h : realRootCheck original cert intervals points = true) :
    cert.content ≠ 0 ∧
      coeffEq (Sparse.coeffs original)
        (coeffScale cert.content (coeffProdLinear cert.roots cert.quotient)) = true ∧
      cert.radical.all (·.valid (Sparse.ofCoeffs cert.quotient)) = true ∧
      cert.bound.valid cert.covered = true ∧
      rootCoverCheck cert.covered (-cert.bound.bound) cert.cells cert.bound.bound = true ∧
      rootIntervals cert.cells = intervals ∧
      (∀ r ∈ points, r ∈ cert.roots ∨ r ∈ rootPoints cert.cells) ∧
      (∀ r ∈ cert.roots, r ∈ points) ∧ (∀ r ∈ rootPoints cert.cells, r ∈ points) ∧
      (∀ r ∈ cert.roots, ∀ I ∈ intervals, r ≤ I.1 ∨ I.2 ≤ r) ∧
      separatedCheck intervals points = true := by
  simpa only [realRootCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, List.contains_iff_mem, and_assoc] using h

/-- A root of the covered polynomial of an accepted certificate is a root of `original`. -/
theorem eval_eq_zero_of_covered {original : Sparse.Univariate} {cert : RootListCertificate}
    {intervals : List (ℚ × ℚ)} {points : List ℚ}
    (h : realRootCheck original cert intervals points = true) {x : ℝ}
    (hx : Sparse.evalReal cert.covered x = 0) : Sparse.evalReal original x = 0 := by
  obtain ⟨hc, hid, hrad, -⟩ := realRootCheck_spec h
  exact (RootListCertificate.evalReal_eq_zero_iff hc hid hrad x).mpr (Or.inr hx)

/-- All real roots of `original` from an accepted certificate: each listed interval contains
exactly one, each listed rational is one, and there are no others. -/
theorem of_realRootCheck (original : Sparse.Univariate) (cert : RootListCertificate)
    (intervals : List (ℚ × ℚ)) (points : List ℚ)
    (h : realRootCheck original cert intervals points = true) :
    (∀ I ∈ intervals, ∃! x, x ∈ Ioo (I.1 : ℝ) I.2 ∧ Sparse.evalReal original x = 0) ∧
      (∀ r ∈ points, Sparse.evalReal original r = 0) ∧
      ∀ x, Sparse.evalReal original x = 0 →
        (∃ r ∈ points, x = r) ∨ ∃ I ∈ intervals, x ∈ Ioo (I.1 : ℝ) I.2 := by
  obtain ⟨hc, hid, hrad, hbound, hcover, rfl, hpoints, hroots, hcells, hout, -⟩ :=
    realRootCheck_spec h
  have hiff := RootListCertificate.evalReal_eq_zero_iff hc hid hrad
  obtain ⟨hI, hP, hR⟩ := of_rootCoverCheck hcover
  have houtside : ∀ r ∈ cert.roots, ∀ I ∈ rootIntervals cert.cells,
      (r : ℝ) ∉ Ioo (I.1 : ℝ) I.2 := by
    intro r hr I hI hmem
    rcases hout r hr I hI with h1 | h2
    · exact absurd hmem.1 (not_lt.mpr (by exact_mod_cast h1))
    · exact absurd hmem.2 (not_lt.mpr (by exact_mod_cast h2))
  refine ⟨fun I hmem ↦ ?_, fun r hr ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨z, hz, hzu⟩ := hI I hmem
    refine ⟨z, ⟨hz.1, (hiff z).mpr (Or.inr hz.2)⟩, fun w hw ↦ hzu w ⟨hw.1, ?_⟩⟩
    rcases (hiff w).mp hw.2 with ⟨r, hr, rfl⟩ | hw0
    · exact absurd hw.1 (houtside r hr I hmem)
    · exact hw0
  · rcases hpoints r hr with h1 | h2
    · exact (hiff r).mpr (Or.inl ⟨r, h1, rfl⟩)
    · exact (hiff r).mpr (Or.inr (hP r h2))
  · rcases (hiff x).mp hx with ⟨r, hr, rfl⟩ | hx'
    · exact Or.inl ⟨r, hroots r hr, rfl⟩
    · have habs := cert.bound.abs_lt_bound hbound hx'
      rcases hR x ⟨by simpa using (abs_lt.mp habs).1, (abs_lt.mp habs).2.le⟩ hx' with
        ⟨r, hr, rfl⟩ | hinterval
      · exact Or.inl ⟨r, hcells r hr, rfl⟩
      · exact Or.inr hinterval

/-- The intervals and rationals of an accepted certificate are pairwise disjoint, so each real
root of `original` is listed once. -/
theorem separatedCheck_of_realRootCheck {original : Sparse.Univariate}
    {cert : RootListCertificate} {intervals : List (ℚ × ℚ)} {points : List ℚ}
    (h : realRootCheck original cert intervals points = true) :
    separatedCheck intervals points = true := by
  simp only [realRootCheck, Bool.and_eq_true] at h
  exact h.2

/-- The sparse polynomial of a one-variable expression evaluates to the expression. -/
theorem evalReal_eq_eval_of_mvPolyOf? (expr : Verified.Expr (Fin 1)) (poly : Sparse.Univariate)
    (h : Verified.Expr.Alg.mvPolyOf? expr = some poly) (x : ℝ) :
    Sparse.evalReal poly x = expr.eval ![x] := by
  rw [Sparse.evalReal_eq_mvPolyVal, Verified.Expr.Alg.mvPolyVal_eq_eval_of_mvPolyOf? _ expr poly h]
  congr 1
  funext i
  fin_cases i
  simp

/-- The root check of a one-variable expression, through its sparse polynomial. -/
def exprRootCheck (expr : Verified.Expr (Fin 1)) (cert : RootListCertificate)
    (intervals : List (ℚ × ℚ)) (points : List ℚ) : Bool :=
  match Verified.Expr.Alg.mvPolyOf? expr with
  | none => false
  | some poly => realRootCheck poly cert intervals points

/-- All real solutions of `expr = 0` for a polynomial expression in one variable: each listed
interval contains exactly one, each listed rational is one, and there are no others. -/
theorem of_exprRootCheck {expr : Verified.Expr (Fin 1)} {cert : RootListCertificate}
    {intervals : List (ℚ × ℚ)} {points : List ℚ}
    (h : exprRootCheck expr cert intervals points = true) :
    (∀ I ∈ intervals, ∃! x, x ∈ Ioo (I.1 : ℝ) I.2 ∧ expr.eval ![x] = 0) ∧
      (∀ r ∈ points, expr.eval ![(r : ℝ)] = 0) ∧
      ∀ x, expr.eval ![x] = 0 →
        (∃ r ∈ points, x = r) ∨ ∃ I ∈ intervals, x ∈ Ioo (I.1 : ℝ) I.2 := by
  unfold exprRootCheck at h
  split at h
  · cases h
  · rename_i poly hpoly
    have heval := evalReal_eq_eval_of_mvPolyOf? expr poly hpoly
    simpa only [heval] using of_realRootCheck poly cert intervals points h

/-- The intervals and rationals of an accepted expression certificate are pairwise disjoint. -/
theorem separatedCheck_of_exprRootCheck {expr : Verified.Expr (Fin 1)}
    {cert : RootListCertificate} {intervals : List (ℚ × ℚ)} {points : List ℚ}
    (h : exprRootCheck expr cert intervals points = true) :
    separatedCheck intervals points = true := by
  unfold exprRootCheck at h
  split at h
  · cases h
  · exact separatedCheck_of_realRootCheck h

/-- A root of the covered polynomial of an accepted expression certificate solves the
expression. -/
theorem eval_eq_zero_of_covered_of_exprRootCheck {expr : Verified.Expr (Fin 1)}
    {cert : RootListCertificate} {intervals : List (ℚ × ℚ)} {points : List ℚ}
    (h : exprRootCheck expr cert intervals points = true) {x : ℝ}
    (hx : Sparse.evalReal cert.covered x = 0) : expr.eval ![x] = 0 := by
  unfold exprRootCheck at h
  split at h
  · cases h
  · rename_i poly hpoly
    rw [← evalReal_eq_eval_of_mvPolyOf? expr poly hpoly]
    exact eval_eq_zero_of_covered h hx

end CAS.Polynomial.RealRoot

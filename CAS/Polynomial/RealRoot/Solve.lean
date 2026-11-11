/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.RealRoot.SignReduce

/-!
# Exact real solutions of polynomial equations

`solve_of_solveCheck` states the real solution set of a polynomial equation in one variable,
`expr = 0 ↔ x = r₁ ∨ ⋯ ∨ x = rₖ`, with each root a rational or an algebraic number
`AlgRoot.real a lo hi`, the root of the polynomial `a` in the rational interval `(lo, hi)`.
Mathematica's `Root[f, k]` names such a number by the index `k` of the root instead of an
interval. The check is the root-list certificate of `exprRootCheck`, the coefficient list `a` of
its covered polynomial, and the sign change of `a` across each interval.
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Set

/-- The real number at a location: the rational point, or the root of `a` in the interval. -/
noncomputable def RootLoc.real (a : List ℚ) : RootLoc → ℝ
  | .interval lo hi => AlgRoot.real a lo hi
  | .exact q => q

/-- The root certificate of `expr` with the locations `locs`, `a` the coefficient list of the
covered polynomial, and a sign change of `a` across each interval location. -/
def solveCheck (expr : Verified.Expr (Fin 1)) (cert : RootListCertificate)
    (locs : List RootLoc) (a : List ℚ) : Bool :=
  exprRootCheck expr cert (locs.filterMap RootLoc.intervalPart)
      (locs.filterMap RootLoc.pointPart) &&
    decide (Sparse.coeffs cert.covered = a) &&
    (locs.filterMap RootLoc.intervalPart).all fun I ↦
      decide (I.1 < I.2) && decide (coeffEvalRat a I.1 * coeffEvalRat a I.2 < 0)

/-- **The real solutions of a polynomial equation.** Each location bounds its root, and the
solutions of `expr = 0` are exactly the roots at the locations. -/
theorem solve_of_solveCheck {expr : Verified.Expr (Fin 1)} {cert : RootListCertificate}
    {locs : List RootLoc} {a : List ℚ} (h : solveCheck expr cert locs a = true) :
    (∀ l ∈ locs, l.Bounds (l.real a)) ∧
      ∀ x : ℝ, expr.eval ![x] = 0 ↔ ∃ l ∈ locs, x = l.real a := by
  simp only [solveCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hroots, rfl⟩, hsigns⟩ := h
  obtain ⟨hA, hB, hC⟩ := of_exprRootCheck hroots
  -- The algebraic number of an interval location is the root there.
  have hreal : ∀ lo hi : ℚ, RootLoc.interval lo hi ∈ locs →
      AlgRoot.real (Sparse.coeffs cert.covered) lo hi ∈ Ioo (lo : ℝ) hi ∧
        expr.eval ![AlgRoot.real (Sparse.coeffs cert.covered) lo hi] = 0 := by
    intro lo hi hmem
    obtain ⟨hlt, hsign⟩ := hsigns (lo, hi) (List.mem_filterMap.mpr ⟨_, hmem, rfl⟩)
    obtain ⟨hI, h0⟩ := AlgRoot.real_spec _ hlt hsign
    rw [Sparse.coeffEval_coeffs] at h0
    exact ⟨hI, eval_eq_zero_of_covered_of_exprRootCheck hroots h0⟩
  refine ⟨fun l hl ↦ ?_, fun x ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
  · cases l with
    | interval lo hi => exact (hreal lo hi hl).1
    | exact q => trivial
  · rcases hC x hx with ⟨r, hr, rfl⟩ | ⟨I, hI, hxI⟩
    · obtain ⟨l, hl, hlr⟩ := List.mem_filterMap.mp hr
      cases l with
      | interval lo hi => cases hlr
      | exact q =>
          simp only [RootLoc.pointPart, Option.some.injEq] at hlr
          exact ⟨_, hl, by rw [← hlr]; rfl⟩
    · obtain ⟨l, hl, hlI⟩ := List.mem_filterMap.mp hI
      cases l with
      | exact q => cases hlI
      | interval lo hi =>
          simp only [RootLoc.intervalPart, Option.some.injEq] at hlI
          subst hlI
          obtain ⟨hmem, h0⟩ := hreal lo hi hl
          refine ⟨_, hl, ?_⟩
          obtain ⟨z, -, hz⟩ := hA _ hI
          exact (hz x ⟨hxI, hx⟩).trans (hz _ ⟨hmem, h0⟩).symm
  · rintro ⟨l, hl, rfl⟩
    cases l with
    | interval lo hi => exact (hreal lo hi hl).2
    | exact q => exact hB q (List.mem_filterMap.mpr ⟨_, hl, rfl⟩)

end CAS.Polynomial.RealRoot

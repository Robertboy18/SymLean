/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Piecewise-polynomial spline spaces

A `StrictKnotMesh panels` is a strictly increasing finite sequence of knots. A
`PolynomialSplineData mesh degree` carries a polynomial of degree at most `degree` on every panel,
and a `PolynomialSpline mesh degree smoothness` adds, as a proof field, that the polynomial jets
(`polynomialJet`) of adjacent panels agree through order `smoothness` at every interior knot. The
jet condition is monotone in the smoothness (`MatchesJetsThrough.mono`), jets above the degree
vanish (`polynomialJet_eq_zero_of_degree_lt`), and the evaluator of two adjacent panels is
`C^smoothness` across their common knot (`PolynomialSpline.contDiff_adjacentEvaluator`).

The representation is panelwise, so a global evaluator can choose any endpoint convention
without changing the spline data.

## References

* I. J. Schoenberg, "Contributions to the problem of approximation of equidistant data by
  analytic functions. Part A. On the problem of smoothing or graduation. A first class of
  analytic approximation formulae", *Quarterly of Applied Mathematics* 4 (1946), pp. 45-99,
  <https://doi.org/10.1090/qam/15914>. Spline curves of order `k` are defined in §3.11.
-/

@[expose] public section

noncomputable section

namespace CAS.Splines

open scoped _root_.Polynomial

/-- A finite knot vector defining `panels` nondegenerate intervals. -/
abbrev StrictKnotMesh (panels : ℕ) :=
  {knot : Fin (panels + 1) → ℝ // StrictMono knot}

namespace StrictKnotMesh

variable {panels : ℕ} (mesh : StrictKnotMesh panels)

/-- The `panels + 1` knot locations. -/
abbrev knot : Fin (panels + 1) → ℝ :=
  mesh.1

/-- No panel is degenerate and the knot ordering is globally consistent. -/
theorem strictMono_knot : StrictMono mesh.knot :=
  mesh.2

/-- Left endpoint of a panel. -/
def panelLeft (panel : Fin panels) : ℝ :=
  mesh.knot panel.castSucc

/-- Right endpoint of a panel. -/
def panelRight (panel : Fin panels) : ℝ :=
  mesh.knot panel.succ

/-- Every panel of a strict mesh has positive length. -/
theorem panelLeft_lt_panelRight (panel : Fin panels) :
    mesh.panelLeft panel < mesh.panelRight panel :=
  mesh.strictMono_knot panel.castSucc_lt_succ

/-- The right-hand neighboring panel, when it exists. -/
def rightNeighbor (panel : Fin panels)
    (hasRight : panel.val + 1 < panels) : Fin panels :=
  ⟨panel.val + 1, hasRight⟩

/-- The value of the right neighboring panel is one more than the original panel. -/
@[simp]
theorem rightNeighbor_val (panel : Fin panels)
    (hasRight : panel.val + 1 < panels) :
    (rightNeighbor panel hasRight).val = panel.val + 1 :=
  rfl

/-- Adjacent panels share exactly one knot. -/
theorem panelRight_eq_panelLeft_rightNeighbor
    (panel : Fin panels) (hasRight : panel.val + 1 < panels) :
    mesh.panelRight panel =
      mesh.panelLeft (rightNeighbor panel hasRight) := by
  apply congrArg mesh.knot
  apply Fin.ext
  rfl

end StrictKnotMesh

/-- The `order`-th algebraic derivative of a polynomial, evaluated at `x`. -/
def polynomialJet (order : ℕ) (polynomial : ℝ[X]) (x : ℝ) : ℝ :=
  (Polynomial.derivative^[order] polynomial).eval x

/-- A zeroth-order polynomial jet is ordinary polynomial evaluation. -/
@[simp]
theorem polynomialJet_zero (polynomial : ℝ[X]) (x : ℝ) :
    polynomialJet 0 polynomial x = polynomial.eval x := by
  simp [polynomialJet]

/-- A successor-order polynomial jet is a jet of the polynomial derivative. -/
@[simp]
theorem polynomialJet_succ (order : ℕ) (polynomial : ℝ[X]) (x : ℝ) :
    polynomialJet (order + 1) polynomial x =
      polynomialJet order polynomial.derivative x := by
  simp [polynomialJet, Function.iterate_succ_apply]

/-- Polynomial jets preserve addition. -/
theorem polynomialJet_add (order : ℕ)
    (left right : ℝ[X]) (x : ℝ) :
    polynomialJet order (left + right) x =
      polynomialJet order left x + polynomialJet order right x := by
  simp [polynomialJet, iterate_map_add]

/-- If `(X - a)^(smoothness + 1)` divides `left - right`, then `left` and `right` have equal
jets at `a` through order `smoothness`. -/
theorem polynomialJet_eq_of_pow_dvd_sub
    {left right : ℝ[X]} {a : ℝ} {smoothness order : ℕ}
    (hfactor :
      (Polynomial.X - Polynomial.C a) ^ (smoothness + 1) ∣
        left - right)
    (horder : order ≤ smoothness) :
    polynomialJet order left a = polynomialJet order right a := by
  have hroot : (Polynomial.derivative^[order] (left - right)).IsRoot a :=
    Polynomial.dvd_iff_isRoot.mp ((dvd_pow_self _ (by omega)).trans
      (Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd order hfactor))
  simpa [polynomialJet, Polynomial.iterate_derivative_sub, sub_eq_zero] using hroot.eq_zero

/-- Every derivative strictly above the degree bound vanishes identically. -/
theorem polynomialJet_eq_zero_of_degree_lt
    {degree order : ℕ} {polynomial : ℝ[X]}
    (hdegree : polynomial.natDegree ≤ degree)
    (horder : degree < order) (x : ℝ) :
    polynomialJet order polynomial x = 0 := by
  rw [polynomialJet,
    Polynomial.iterate_derivative_eq_zero (hdegree.trans_lt horder)]
  simp

/-- Degree-bounded polynomial pieces on every panel of a finite mesh. -/
structure PolynomialSplineData {panels : ℕ}
    (mesh : StrictKnotMesh panels) (degree : ℕ) where
  /-- Polynomial carried by each panel. -/
  piece : Fin panels → ℝ[X]
  /-- Uniform degree bound for all panel polynomials. -/
  degree_le : ∀ panel, (piece panel).natDegree ≤ degree

namespace PolynomialSplineData

variable {panels degree : ℕ} {mesh : StrictKnotMesh panels}

/-- Two neighboring pieces have equal jets through `smoothness` at their common knot. -/
def MatchesJetsThrough (data : PolynomialSplineData mesh degree)
    (smoothness : ℕ) : Prop :=
  ∀ (panel : Fin panels) (hasRight : panel.val + 1 < panels)
    (order : ℕ), order ≤ smoothness →
      polynomialJet order (data.piece panel) (mesh.panelRight panel) =
        polynomialJet order
          (data.piece (StrictKnotMesh.rightNeighbor panel hasRight))
          (mesh.panelRight panel)

/-- Requiring more matched jets implies every lower smoothness requirement. -/
theorem MatchesJetsThrough.mono
    {data : PolynomialSplineData mesh degree}
    {lower higher : ℕ} (hmatch : data.MatchesJetsThrough higher)
    (hle : lower ≤ higher) :
    data.MatchesJetsThrough lower :=
  fun panel hasRight order horder ↦ hmatch panel hasRight order (horder.trans hle)

/-- Junction values agree whenever zeroth-order jets are required. -/
theorem value_eq_of_matchesJetsThrough
    {data : PolynomialSplineData mesh degree} {smoothness : ℕ}
    (hmatch : data.MatchesJetsThrough smoothness)
    (panel : Fin panels) (hasRight : panel.val + 1 < panels) :
    (data.piece panel).eval (mesh.panelRight panel) =
      (data.piece (StrictKnotMesh.rightNeighbor panel hasRight)).eval
        (mesh.panelRight panel) := by
  simpa using hmatch panel hasRight 0 (Nat.zero_le smoothness)

/-- The two-polynomial evaluator obtained by cutting at an interior mesh knot. -/
def adjacentEvaluator (data : PolynomialSplineData mesh degree)
    (panel : Fin panels) (hasRight : panel.val + 1 < panels) (x : ℝ) : ℝ :=
  if x ≤ mesh.panelRight panel then
    Polynomial.aeval x (data.piece panel)
  else
    Polynomial.aeval x
      (data.piece (StrictKnotMesh.rightNeighbor panel hasRight))

/-- The piecewise evaluator of the `order`-th polynomial jets of two adjacent panels. -/
def adjacentJetEvaluator (data : PolynomialSplineData mesh degree)
    (panel : Fin panels) (hasRight : panel.val + 1 < panels)
    (order : ℕ) (x : ℝ) : ℝ :=
  if x ≤ mesh.panelRight panel then
    polynomialJet order (data.piece panel) x
  else
    polynomialJet order
      (data.piece (StrictKnotMesh.rightNeighbor panel hasRight)) x

/-- The zeroth adjacent jet evaluator is the adjacent piece evaluator. -/
@[simp]
theorem adjacentJetEvaluator_zero
    (data : PolynomialSplineData mesh degree)
    (panel : Fin panels) (hasRight : panel.val + 1 < panels) :
    data.adjacentJetEvaluator panel hasRight 0 =
      data.adjacentEvaluator panel hasRight := by
  funext x
  simp [adjacentJetEvaluator, adjacentEvaluator, polynomialJet,
    Polynomial.aeval_def, Algebra.algebraMap_self]

/-- One polynomial jet differentiates to the next polynomial jet. -/
theorem hasDerivAt_polynomialJet (order : ℕ)
    (polynomial : ℝ[X]) (x : ℝ) :
    HasDerivAt (polynomialJet order polynomial)
      (polynomialJet (order + 1) polynomial x) x := by
  change
    HasDerivAt (fun y ↦ polynomialJet order polynomial y)
      (polynomialJet (order + 1) polynomial x) x
  simpa [polynomialJet, Function.iterate_succ_apply'] using
    (Polynomial.derivative^[order] polynomial).hasDerivAt x

/-- Polynomial jets are continuous functions of the evaluation point. -/
theorem continuous_polynomialJet (order : ℕ) (polynomial : ℝ[X]) :
    Continuous (polynomialJet order polynomial) :=
  continuous_iff_continuousAt.mpr fun x ↦
    (hasDerivAt_polynomialJet order polynomial x).continuousAt

/-- Matching one jet makes the corresponding adjacent jet evaluator continuous. -/
theorem continuous_adjacentJetEvaluator
    {data : PolynomialSplineData mesh degree}
    (panel : Fin panels) (hasRight : panel.val + 1 < panels)
    (order : ℕ)
    (hmatch :
      polynomialJet order (data.piece panel) (mesh.panelRight panel) =
        polynomialJet order
          (data.piece (StrictKnotMesh.rightNeighbor panel hasRight))
          (mesh.panelRight panel)) :
    Continuous (data.adjacentJetEvaluator panel hasRight order) := by
  refine Continuous.if (fun x hx ↦ ?_) (continuous_polynomialJet _ _)
    (continuous_polynomialJet _ _)
  obtain rfl := Set.mem_singleton_iff.mp (frontier_Iic_subset _ hx)
  exact hmatch

/-- If consecutive jets match, the adjacent `order`-jet evaluator has derivative equal
to the adjacent successor-jet evaluator at every point, including the junction. -/
theorem hasDerivAt_adjacentJetEvaluator
    {data : PolynomialSplineData mesh degree}
    (panel : Fin panels) (hasRight : panel.val + 1 < panels)
    (order : ℕ)
    (hvalue :
      polynomialJet order (data.piece panel) (mesh.panelRight panel) =
        polynomialJet order
          (data.piece (StrictKnotMesh.rightNeighbor panel hasRight))
          (mesh.panelRight panel))
    (hderivative :
      polynomialJet (order + 1) (data.piece panel) (mesh.panelRight panel) =
        polynomialJet (order + 1)
          (data.piece (StrictKnotMesh.rightNeighbor panel hasRight))
          (mesh.panelRight panel))
    (x : ℝ) :
    HasDerivAt (data.adjacentJetEvaluator panel hasRight order)
      (data.adjacentJetEvaluator panel hasRight (order + 1) x) x := by
  rcases lt_trichotomy x (mesh.panelRight panel) with hleft | rfl | hright
  · exact ((hasDerivAt_polynomialJet order (data.piece panel) x).congr_of_eventuallyEq
      ((eventually_lt_nhds hleft).mono fun y hy ↦ ite_eq_left hy.le)).congr_deriv
        (ite_eq_left hleft.le).symm
  · have hc := le_refl (mesh.panelRight panel)
    rw [← hasDerivWithinAt_univ, ← Set.Iic_union_Ioi (a := mesh.panelRight panel)]
    refine HasDerivWithinAt.union ?_ ?_
    · refine HasDerivWithinAt.congr_deriv ?_ (ite_eq_left hc).symm
      exact (hasDerivAt_polynomialJet order (data.piece panel) _).hasDerivWithinAt.congr
        (fun y (hy : y ≤ _) ↦ ite_eq_left hy) (ite_eq_left hc)
    · refine HasDerivWithinAt.congr_deriv ?_ ((ite_eq_left hc).trans hderivative).symm
      exact (hasDerivAt_polynomialJet order _ _).hasDerivWithinAt.congr
        (fun y (hy : _ < y) ↦ ite_eq_right (not_le_of_gt hy)) ((ite_eq_left hc).trans hvalue)
  · exact ((hasDerivAt_polynomialJet order _ x).congr_of_eventuallyEq
      ((eventually_gt_nhds hright).mono fun y hy ↦ ite_eq_right (not_le_of_gt hy))).congr_deriv
        (ite_eq_right (not_le_of_gt hright)).symm

/-- The ordinary derivative of a matched adjacent jet evaluator. -/
theorem deriv_adjacentJetEvaluator
    {data : PolynomialSplineData mesh degree}
    (panel : Fin panels) (hasRight : panel.val + 1 < panels)
    (order : ℕ)
    (hvalue :
      polynomialJet order (data.piece panel) (mesh.panelRight panel) =
        polynomialJet order
          (data.piece (StrictKnotMesh.rightNeighbor panel hasRight))
          (mesh.panelRight panel))
    (hderivative :
      polynomialJet (order + 1) (data.piece panel) (mesh.panelRight panel) =
        polynomialJet (order + 1)
          (data.piece (StrictKnotMesh.rightNeighbor panel hasRight))
          (mesh.panelRight panel)) :
    deriv (data.adjacentJetEvaluator panel hasRight order) =
      data.adjacentJetEvaluator panel hasRight (order + 1) :=
  funext fun x ↦ (data.hasDerivAt_adjacentJetEvaluator panel hasRight order hvalue
    hderivative x).deriv

/-- Iterated analytic derivatives of an adjacent evaluator agree with its algebraic
polynomial jets as long as all intervening junction jets match. -/
theorem iteratedDeriv_adjacentEvaluator
    {data : PolynomialSplineData mesh degree} {smoothness : ℕ}
    (hmatch : data.MatchesJetsThrough smoothness)
    (panel : Fin panels) (hasRight : panel.val + 1 < panels)
    (order : ℕ) (horder : order ≤ smoothness) :
    iteratedDeriv order (data.adjacentEvaluator panel hasRight) =
      data.adjacentJetEvaluator panel hasRight order := by
  induction order with
  | zero => exact (data.adjacentJetEvaluator_zero panel hasRight).symm
  | succ order ih =>
      rw [iteratedDeriv_succ, ih (by omega)]
      exact data.deriv_adjacentJetEvaluator panel hasRight order
        (hmatch panel hasRight order (by omega)) (hmatch panel hasRight (order + 1) horder)

/-- Matching polynomial jets through `smoothness` makes the full adjacent evaluator
globally `C^smoothness`, not merely differentiable away from the junction. -/
theorem contDiff_adjacentEvaluator
    {data : PolynomialSplineData mesh degree} {smoothness : ℕ}
    (hmatch : data.MatchesJetsThrough smoothness)
    (panel : Fin panels) (hasRight : panel.val + 1 < panels) :
    ContDiff ℝ smoothness (data.adjacentEvaluator panel hasRight) := by
  refine contDiff_nat_iff_iteratedDeriv.mpr ⟨fun order horder ↦ ?_, fun order horder ↦ ?_⟩
  · rw [data.iteratedDeriv_adjacentEvaluator hmatch panel hasRight order horder]
    exact data.continuous_adjacentJetEvaluator panel hasRight order
      (hmatch panel hasRight order horder)
  · rw [data.iteratedDeriv_adjacentEvaluator hmatch panel hasRight order horder.le]
    exact fun x ↦ (data.hasDerivAt_adjacentJetEvaluator panel hasRight order
      (hmatch panel hasRight order horder.le) (hmatch panel hasRight (order + 1) horder)
        x).differentiableAt

end PolynomialSplineData

/-- A certified degree-`degree` piecewise-polynomial spline with junction jets matched through
`smoothness`. -/
structure PolynomialSpline {panels : ℕ}
    (mesh : StrictKnotMesh panels) (degree smoothness : ℕ)
    extends PolynomialSplineData mesh degree where
  /-- The panel polynomials satisfy the defining spline junction conditions. -/
  matchesJets : toPolynomialSplineData.MatchesJetsThrough smoothness

namespace PolynomialSpline

variable {panels degree smoothness : ℕ} {mesh : StrictKnotMesh panels}

/-- Every adjacent evaluator of a certified spline is globally `C^smoothness`. -/
theorem contDiff_adjacentEvaluator
    (spline : PolynomialSpline mesh degree smoothness)
    (panel : Fin panels) (hasRight : panel.val + 1 < panels) :
    ContDiff ℝ smoothness
      (spline.toPolynomialSplineData.adjacentEvaluator panel hasRight) :=
  spline.toPolynomialSplineData.contDiff_adjacentEvaluator
    spline.matchesJets panel hasRight

end PolynomialSpline

end CAS.Splines

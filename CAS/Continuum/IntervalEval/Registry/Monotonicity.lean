/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.AutoRange
public import CAS.Continuum.IntervalEval.Validity
public import CAS.Continuum.IntervalEval.Registry.Planner

/-!
# Monotonicity-aware interval evaluation on boxes

Enclosures on rational boxes of any literal dimension are sharpened by
coordinatewise face reduction. When the interval evaluator encloses the symbolic
partial derivative `∂ᵢ f` on the whole box with one sign, `f` is monotone along
every coordinate line in direction `i`, so its range over the box is the hull of
its ranges over the two faces `xᵢ = loᵢ` and `xᵢ = hiᵢ`. Each face is again a
rational box with one coordinate fewer free, on which a caller-supplied planner
encloses the expression; iterating the reduction ends at corners of the box,
where evaluation is exact up to the elementary-function brackets.

## Main definitions

* `boxDomain`, `faceBox`, `boxRegistry`: the Euclidean box of a rational
  interval environment, its faces, and its checked registry.
* `CertifiedEvalRegistry.signedPartialPlan?`, `partialPlan?`,
  `partialAttemptOfPlan`: proof-free selection and checked construction of a
  partial-derivative enclosure.
* `CertifiedEvalRegistry.faceReductionAttempt`: the certificate of one face reduction.
* `CertifiedEvalRegistry.monotonicityEnclosurePreview?`,
  `monotonicityEnclosureAttempt?`: the planner-facing route, parameterized by
  the planner used on the faces.

## Main results

* `memReal_hull_of_signed_partial`: if `expr` is valid on the box and an interval with
  `0 ≤ lo` or `hi ≤ 0` encloses `∂ᵢ expr` on the box, then the hull of enclosures of `expr` on
  the two faces of coordinate `i` encloses `expr` on the box.

## Implementation notes

The monotonicity test is classical in interval global optimization: in Hansen's algorithm, when the
enclosure of `∂ᵢ f` over a box is nonnegative, the minimum lies on the face `xᵢ = loᵢ` and the rest
of the box is deleted. We want the range, not a minimum, so we keep both faces and take the hull of
their enclosures; the caller reruns its whole planner on each face, so reductions nest. Every
reduction has three independently checked ingredients: analytic validity of the expression on the
whole box (`CertifiedEvalRegistry.validOn?`), which the derivative theorem requires; a nonnegative
or nonpositive enclosure of the symbolic partial derivative, found directly, after unconditional
polynomial normalization, or after checked side-conditioned normalization; and ordinary enclosures
of the expression on the two faces. Along a coordinate line the expression has derivative `∂ᵢ expr`
by `Verified.Expr.hasDerivAt_eval_add_smul_single`, and Mathlib's
`monotoneOn_of_hasDerivWithinAt_nonneg` and `antitoneOn_of_hasDerivWithinAt_nonpos`, consequences of
the mean value theorem, turn the sign into monotonicity. The theorem is proved once for every
dimension; the one-dimensional route is the case `n = 1`, where the faces are the two endpoints.

The previews only choose the coordinate and the derivative route. `monotonicityEnclosureAttempt?`
decides the sign again on the constructed derivative certificate and fails closed if it does
not hold. Planner failure is harmless: callers retain the natural, affine or centered route. The
route fails closed whenever a partial derivative cannot be enclosed, for instance across a
division or logarithm whose argument panel contains zero or a real power whose base panel is not
strictly positive.

## References

* Eldon Hansen, "Global Optimization Using Interval Analysis - The Multi-Dimensional Case",
  *Numerische Mathematik* 34 (1980), pp. 247-270, <https://doi.org/10.1007/BF01396702>.
  Section 9 for the monotonicity test.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open Set
open CAS.Certificate
open CAS.Verified

/-! ## Rational boxes, faces, and coordinate lines -/

/-- The Euclidean box determined by a rational interval environment. -/
def boxDomain {n : ℕ} (box : Fin n → RationalInterval) : Set (ℝ^n) :=
  { point | ∀ i, (box i).MemReal (point i) }

/-- The face of a box on which coordinate `i` is fixed at the rational value `q`. -/
def faceBox {n : ℕ} (box : Fin n → RationalInterval) (i : Fin n) (q : ℚ) :
    Fin n → RationalInterval :=
  Function.update box i (const q)

/-- The checked registry of an exact rational box, with no manually supplied facts. -/
def boxRegistry {n : ℕ} (box : Fin n → RationalInterval) (precision : Precision) :
    CertifiedEvalRegistry (boxDomain box) (fun x : ℝ^n ↦ fun i ↦ x i) :=
  CertifiedEvalRegistry.ofEnvironment box (fun _ hx i ↦ hx i) precision

/--
Moving a box point along coordinate `i` keeps it in the box as long as that
coordinate stays in its interval.
-/
theorem mem_boxDomain_add_smul_single {n : ℕ} {box : Fin n → RationalInterval} {x : ℝ^n}
    (hx : x ∈ boxDomain box) (i : Fin n) {s : ℝ} (hs : (box i).MemReal (x i + s)) :
    x + s • EuclideanSpace.single i (1 : ℝ) ∈ boxDomain box := by
  intro j
  by_cases hj : j = i
  · subst hj
    simpa using hs
  · simpa [hj] using hx j

/-- Moving a box point along coordinate `i` to the value `q` lands on the corresponding face. -/
theorem mem_faceBox_add_smul_single {n : ℕ} {box : Fin n → RationalInterval} {x : ℝ^n}
    (hx : x ∈ boxDomain box) (i : Fin n) (q : ℚ) :
    x + ((q : ℝ) - x i) • EuclideanSpace.single i (1 : ℝ) ∈ boxDomain (faceBox box i q) := by
  intro j
  by_cases hj : j = i
  · subst hj
    simp [faceBox, MemReal]
  · simpa [faceBox, hj] using hx j

/-! ## Structural planner gates -/

/-- Detect derivative expressions whose square-root obligations are too costly for the
derivative routes. -/
def containsSquareRoot {ι : Type*} : Verified.Expr ι → Bool
  | .sqrt _ => true
  | .add a b | .mul a b | .sub a b | .div a b =>
      containsSquareRoot a || containsSquareRoot b
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a =>
      containsSquareRoot a
  | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ => false
  | .rpow a b => containsSquareRoot a || containsSquareRoot b

/--
Detect quotients and trigonometric nodes, the only nodes on which the
side-conditioned interval normalizer can change an expression beyond ordinary
simplification.
-/
def containsQuotientOrTrig {ι : Type*} : Verified.Expr ι → Bool
  | .div _ _ | .sin _ | .cos _ => true
  | .add a b | .mul a b | .sub a b | .rpow a b =>
      containsQuotientOrTrig a || containsQuotientOrTrig b
  | .neg a | .pow a _ | .atan a | .asin a | .acos a | .exp a | .log a | .sqrt a =>
      containsQuotientOrTrig a
  | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ => false

/-- Count syntactic uses of one coordinate before deciding whether dependency needs sharpening. -/
def variableOccurrenceCount {ι : Type*} [DecidableEq ι]
    (coordinate : ι) : Verified.Expr ι → Nat
  | .var i => if i = coordinate then 1 else 0
  | .add a b | .mul a b | .sub a b | .div a b =>
      variableOccurrenceCount coordinate a + variableOccurrenceCount coordinate b
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a |
      .sqrt a =>
      variableOccurrenceCount coordinate a
  | .nat _ | .int _ | .rat _ _ | .pi | .e => 0
  | .rpow a b =>
      variableOccurrenceCount coordinate a + variableOccurrenceCount coordinate b

/--
Coordinates along which a box may be reduced to its faces: the coordinate occurs
in the expression, its interval is not degenerate, and its partial derivative is
free of square roots, whose branch obligations are disproportionately expensive.
-/
def reducibleCoordinates {n : ℕ} (box : Fin n → RationalInterval)
    (expr : Verified.Expr (Fin n)) : List (Fin n) :=
  (List.finRange n).filter fun i ↦
    expr.containsVar i && decide ((box i).lo < (box i).hi) &&
      !containsSquareRoot (expr.diff i)

/--
Whether the derivative routes may sharpen a simplified expression on a box.

Expressions using every coordinate once already propagate their intervals
directly, and a box that is degenerate in every coordinate of the expression
leaves nothing for a derivative argument to improve.
-/
def derivativeRoutesApply {n : ℕ} (box : Fin n → RationalInterval)
    (expr : Verified.Expr (Fin n)) : Bool :=
  (List.finRange n).any (fun i ↦ 1 < variableOccurrenceCount i expr) &&
    (List.finRange n).any fun i ↦ expr.containsVar i && decide ((box i).lo < (box i).hi)

/-! ## Partial-derivative enclosures -/

namespace CertifiedEvalRegistry

variable {α : Type*} {n : ℕ} {s : Set α} {ρ : α → Fin n → ℝ}

/--
The symbolic partial derivative after unconditional simplification.

Symbolic differentiation leaves the units and zeros of the product and chain
rules in place; removing them first makes every derivative preview cheaper
without changing the intervals of the routes that follow.
-/
def simplifiedPartial (expr : Verified.Expr (Fin n)) (i : Fin n) : Verified.Expr (Fin n) :=
  Verified.Expr.simplify (expr.diff i)

/-- Transport an enclosure of a simplified partial derivative back to the derivative. -/
noncomputable def transportPartialAttempt {expr : Verified.Expr (Fin n)} {i : Fin n}
    {target : Verified.Expr (Fin n)}
    (heval : ∀ ρ : Fin n → ℝ, target.eval ρ = (expr.diff i).eval ρ)
    (result : EnclosureAttempt α s (fun x ↦ target.eval (ρ x))) :
    EnclosureAttempt α s (fun x ↦ (expr.diff i).eval (ρ x)) :=
  result.congr fun x _ ↦ (heval (ρ x)).symm

/-- Enclose a symbolic partial derivative directly after simplification. -/
noncomputable def directPartialAttempt?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr (Fin n)) (i : Fin n) :
    Option (EnclosureAttempt α s (fun x ↦ (expr.diff i).eval (ρ x))) :=
  (r.selectFiniteEnclosureAttempt? (simplifiedPartial expr i)).map
    (transportPartialAttempt fun ρ ↦ Verified.Expr.eval_simplify ρ (expr.diff i))

/--
Enclose a symbolic partial derivative after unconditional algebraic normalization.

For polynomial and rational derivatives this route is much smaller than the
full side-conditioned simplification pipeline. Sparse polynomial-fragment
normalization is an unconditional semantic equality, so no denominator
cancellation or additional side-condition proof is hidden in this fast path.
-/
noncomputable def algebraicPartialAttempt?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr (Fin n)) (i : Fin n) :
    Option (EnclosureAttempt α s (fun x ↦ (expr.diff i).eval (ρ x))) :=
  (r.selectFiniteEnclosureAttempt?
    (normalizePolynomialFragments (simplifiedPartial expr i))).map fun result ↦
    { transportPartialAttempt
        (fun ρ ↦
          (eval_normalizePolynomialFragments (WithLp.toLp 2 ρ) (simplifiedPartial expr i)).trans
            (Verified.Expr.eval_simplify ρ (expr.diff i)))
        result with
      steps := .exactNormalization :: result.steps }

/-- The compact side-conditioned route used only for partial-derivative recovery. -/
def partialSideRoute (expr : Verified.Expr (Fin n)) (i : Fin n) :
    Verified.Expr.SideClaimRoute (Fin n) :=
  let derivative := expr.diff i
  let normalized := intervalNormalizeWithSide derivative
  { lhs := derivative
    rhs := normalized.expr
    nonzero := normalized.nonzero
    sound := fun ρ hside ↦ eval_intervalNormalizeWithSide ρ derivative hside }

/-- Enclose a symbolic partial derivative after checked side-conditioned normalization. -/
noncomputable def sideNormalizedPartialAttempt?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr (Fin n)) (i : Fin n) :
    Option (EnclosureAttempt α s (fun x ↦ (expr.diff i).eval (ρ x))) :=
  autoSideRouteEnclosureAttempt? (partialSideRoute expr i) r.env r.hvars r.precision

/-- Whether a planner summary's interval is entirely nonnegative or entirely nonpositive. -/
def summaryHasFixedSign (summary : PlannerSummary) : Bool :=
  decide (0 ≤ summary.interval.lo) ||
    decide (summary.interval.hi ≤ 0)

/-- The checked route by which a partial derivative is enclosed, selected by a proof-free
preview. -/
inductive DerivativePlan where
  /-- The simplified derivative expression. -/
  | direct
  /-- The derivative after unconditional sparse-polynomial normalization. -/
  | algebraic
  /-- The derivative after checked side-conditioned normalization. -/
  | sideNormalized

/--
Proof-free previews of the derivative routes for `∂ᵢ expr`, in order of
increasing cost.

The summaries carry no certificate. The plan selectors use them to choose a
route before any proof object is built, and a caller that stops at the first
acceptable entry never evaluates the later previews. The side-conditioned
normalizer is previewed only when the derivative contains a quotient or a
trigonometric node; elsewhere it coincides with the simplified direct route.
-/
def partialPreviews (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr (Fin n)) (i : Fin n) :
    List (DerivativePlan × PlannerSummary) :=
  let derivative := simplifiedPartial expr i
  [(r.selectFiniteEnclosurePreview? derivative).map
      fun summary ↦ (DerivativePlan.direct, summary),
    (r.selectFiniteEnclosurePreview? (normalizePolynomialFragments derivative)).map
      fun summary ↦ (DerivativePlan.algebraic, summary),
    if containsQuotientOrTrig derivative then
      (r.selectFiniteEnclosurePreview? (partialSideRoute expr i).rhs).map
        fun summary ↦ (DerivativePlan.sideNormalized, summary)
    else
      none].reduceOption

/-- Select the first derivative route whose preview keeps one sign, without constructing a
proof object. -/
def signedPartialPlan? (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr (Fin n))
    (i : Fin n) : Option (DerivativePlan × PlannerSummary) :=
  (partialPreviews r expr i).find? fun candidate ↦ summaryHasFixedSign candidate.2

/-- Keep the candidate with the sharper enclosure preview. -/
def sharperCandidate {β : Type*}
    (best candidate : Option (β × PlannerSummary)) : Option (β × PlannerSummary) :=
  match best, candidate with
  | some best, some candidate =>
      if candidate.2.enclosureBetterThan best.2 then some candidate else some best
  | some best, none => some best
  | none, candidate => candidate

/--
Select the narrowest derivative route without constructing its proof.

Unlike the sign selector, the centered form uses the derivative range whatever
its sign, so the candidates are ranked by width alone.
-/
def partialPlan? (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr (Fin n)) (i : Fin n) :
    Option (DerivativePlan × PlannerSummary) :=
  (partialPreviews r expr i).foldl
    (fun best candidate ↦ sharperCandidate best (some candidate)) none

/-- Construct the partial-derivative enclosure of one selected route. -/
noncomputable def partialAttemptOfPlan
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr (Fin n)) (i : Fin n) :
    DerivativePlan → Option (EnclosureAttempt α s (fun x ↦ (expr.diff i).eval (ρ x)))
  | .direct => directPartialAttempt? r expr i
  | .algebraic => algebraicPartialAttempt? r expr i
  | .sideNormalized => sideNormalizedPartialAttempt? r expr i

/-- Construct only the sharpest partial-derivative certificate selected by the preview. -/
noncomputable def partialAttempt?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr (Fin n)) (i : Fin n) :
    Option (EnclosureAttempt α s (fun x ↦ (expr.diff i).eval (ρ x))) := do
  let plan ← partialPlan? r expr i
  partialAttemptOfPlan r expr i plan.1

end CertifiedEvalRegistry

/-! ## Face reduction -/

/--
The range of an expression over a box lies in the hull of its ranges over the
two faces of a coordinate whose partial derivative keeps one sign on the box.

Along the coordinate line through a box point, evaluation is differentiable
with derivative `∂ᵢ expr` by `Verified.Expr.hasDerivAt_eval_add_smul_single`;
Mathlib's mean value theorem makes it monotone or antitone between the two
faces, which are reached at the endpoints of that line.
-/
theorem memReal_hull_of_signed_partial {n : ℕ} (box : Fin n → RationalInterval)
    (expr : Verified.Expr (Fin n)) (i : Fin n)
    (hvalid : ∀ y ∈ boxDomain box, expr.ValidAt fun j ↦ y j)
    {D : RationalInterval}
    (hD : ∀ y ∈ boxDomain box, D.MemReal ((expr.diff i).eval fun j ↦ y j))
    (hsign : 0 ≤ D.lo ∨ D.hi ≤ 0)
    {lower upper : RationalInterval}
    (hlower : ∀ y ∈ boxDomain (faceBox box i (box i).lo),
      lower.MemReal (expr.eval fun j ↦ y j))
    (hupper : ∀ y ∈ boxDomain (faceBox box i (box i).hi),
      upper.MemReal (expr.eval fun j ↦ y j))
    {x : ℝ^n} (hx : x ∈ boxDomain box) :
    (lower.hull upper).MemReal (expr.eval fun j ↦ x j) := by
  let a : ℝ := ((box i).lo : ℝ) - x i
  let b : ℝ := ((box i).hi : ℝ) - x i
  let line : ℝ → ℝ^n := fun t ↦ x + t • EuclideanSpace.single i (1 : ℝ)
  let g : ℝ → ℝ := fun t ↦ expr.eval (line t)
  let g' : ℝ → ℝ := fun t ↦ (expr.diff i).eval (line t)
  have hxi : ((box i).lo : ℝ) ≤ x i ∧ x i ≤ ((box i).hi : ℝ) := hx i
  have hline : ∀ t ∈ Icc a b, line t ∈ boxDomain box := fun t ht ↦
    mem_boxDomain_add_smul_single hx i ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hderiv : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t := fun t ht ↦
    Verified.Expr.hasDerivAt_eval_add_smul_single expr x i t (hvalid _ (hline t ht))
  have hcont : ContinuousOn g (Icc a b) := fun t ht ↦
    (hderiv t ht).continuousAt.continuousWithinAt
  have hab : a ≤ b := sub_le_sub_right (by exact_mod_cast (box i).hle) _
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  have h0 : (0 : ℝ) ∈ Icc a b := ⟨sub_nonpos.mpr hxi.1, sub_nonneg.mpr hxi.2⟩
  have hga : lower.MemReal (g a) := hlower _ (mem_faceBox_add_smul_single hx i (box i).lo)
  have hgb : upper.MemReal (g b) := hupper _ (mem_faceBox_add_smul_single hx i (box i).hi)
  have hg0 : g 0 = expr.eval fun j ↦ x j := by simp [g, line]
  rw [← hg0]
  rcases hsign with hnonneg | hnonpos
  · have hmono : MonotoneOn g (Icc a b) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hcont
        (fun t ht ↦ (hderiv t (interior_subset ht)).hasDerivWithinAt)
        (fun t ht ↦
          le_trans (by exact_mod_cast hnonneg) (hD _ (hline t (interior_subset ht))).1)
    exact ⟨(memReal_hull_left (J := upper) hga).1.trans (hmono ha h0 h0.1),
      (hmono h0 hb h0.2).trans (memReal_hull_right (I := lower) hgb).2⟩
  · have hanti : AntitoneOn g (Icc a b) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hcont
        (fun t ht ↦ (hderiv t (interior_subset ht)).hasDerivWithinAt)
        (fun t ht ↦
          (hD _ (hline t (interior_subset ht))).2.trans (by exact_mod_cast hnonpos))
    exact ⟨(memReal_hull_right (I := lower) hgb).1.trans (hanti h0 hb h0.2),
      (hanti ha h0 h0.1).trans (memReal_hull_left (J := upper) hga).2⟩

namespace CertifiedEvalRegistry

/-- The route step recorded for one face reduction, chosen by the sign of the derivative
enclosure. -/
def faceReductionStep (derivative : RationalInterval) : RouteStep :=
  if 0 ≤ derivative.lo then .monotoneIncreasingRange else .monotoneDecreasingRange

/--
Certify the range of `expr` on a box from a fixed-sign enclosure of its `i`-th
partial derivative and checked enclosures on the two faces `xᵢ = loᵢ` and
`xᵢ = hiᵢ`.

`validity` certifies that `expr` is valid, hence differentiable, on the whole
box. The sign hypothesis is not a soundness assumption of the planner: the
stored derivative enclosure and the rational endpoint inequality decide it.
-/
noncomputable def faceReductionAttempt {n : ℕ} (box : Fin n → RationalInterval)
    (expr : Verified.Expr (Fin n)) (i : Fin n)
    (validity : CertificateRoute (∀ x, x ∈ boxDomain box → expr.ValidAt fun j ↦ x j))
    (derivative : EnclosureAttempt (ℝ^n) (boxDomain box)
      (fun x ↦ (expr.diff i).eval fun j ↦ x j))
    (lower : EnclosureAttempt (ℝ^n) (boxDomain (faceBox box i (box i).lo))
      (fun x ↦ expr.eval fun j ↦ x j))
    (upper : EnclosureAttempt (ℝ^n) (boxDomain (faceBox box i (box i).hi))
      (fun x ↦ expr.eval fun j ↦ x j))
    (hsign : 0 ≤ derivative.interval.lo ∨ derivative.interval.hi ≤ 0) :
    EnclosureAttempt (ℝ^n) (boxDomain box) (fun x ↦ expr.eval fun j ↦ x j) where
  interval := lower.interval.hull upper.interval
  sound := fun _ hx ↦
    memReal_hull_of_signed_partial box expr i validity.cert
      (fun _ hy ↦ derivative.memReal hy) hsign
      (fun _ hy ↦ lower.memReal hy) (fun _ hy ↦ upper.memReal hy) hx
  steps := faceReductionStep derivative.interval ::
    (validity.steps ++ derivative.steps ++ lower.steps ++ upper.steps)

/--
Select the first reducible coordinate whose partial derivative keeps one sign
on the box, with the derivative route and preview that established the sign.

The choice is greedy: a face reduction is exact whichever coordinate is taken,
so the order only decides which faces the caller's planner sees next.
-/
def faceReductionPlan? {n : ℕ} (box : Fin n → RationalInterval) (precision : Precision)
    (expr : Verified.Expr (Fin n)) : Option (Fin n × DerivativePlan × PlannerSummary) :=
  let registry := boxRegistry box precision
  (reducibleCoordinates box expr).findSome? fun i ↦
    (signedPartialPlan? registry expr i).map fun plan ↦ (i, plan.1, plan.2)

/--
Preview the hull of the two face enclosures available from a fixed-sign partial
derivative, using `facePreview` for the faces.

This function contains no certificate fields. It lets a caller compare the
monotonicity route with the natural, affine, and centered routes before
constructing the selected proof object.
-/
noncomputable def monotonicityEnclosurePreview? {n : ℕ} (precision : Precision)
    (facePreview : (Fin n → RationalInterval) → Option PlannerSummary)
    (box : Fin n → RationalInterval) (expr : Verified.Expr (Fin n)) :
    Option PlannerSummary := do
  let (i, _, derivative) ← faceReductionPlan? box precision expr
  let lower ← facePreview (faceBox box i (box i).lo)
  let upper ← facePreview (faceBox box i (box i).hi)
  pure {
    kind := .easy
    interval := lower.interval.hull upper.interval
    stepCount := derivative.stepCount + lower.stepCount + upper.stepCount + 1 }

/--
Try to certify the box range of `expr` by one face reduction along the first
coordinate whose partial derivative keeps one sign, enclosing the faces with
`faceAttempt`.

Every ingredient is a checked certificate. The sign is re-decided on the
constructed derivative enclosure, so a preview that disagrees with the
certificate fails closed instead of selecting a branch. The plan is recomputed
here by the same terms as in the preview, which the kernel evaluator then reads
from its cache instead of re-evaluating.
-/
noncomputable def monotonicityEnclosureAttempt? {n : ℕ} (precision : Precision)
    (box : Fin n → RationalInterval) (expr : Verified.Expr (Fin n))
    (faceAttempt : (face : Fin n → RationalInterval) →
      Option (EnclosureAttempt (ℝ^n) (boxDomain face) (fun x ↦ expr.eval fun j ↦ x j))) :
    Option (EnclosureAttempt (ℝ^n) (boxDomain box) (fun x ↦ expr.eval fun j ↦ x j)) := do
  let registry := boxRegistry box precision
  let (i, plan, _) ← faceReductionPlan? box precision expr
  let validity ← registry.validOn? expr
  let derivative ← partialAttemptOfPlan registry expr i plan
  let lower ← faceAttempt (faceBox box i (box i).lo)
  let upper ← faceAttempt (faceBox box i (box i).hi)
  if hsign : 0 ≤ derivative.interval.lo ∨ derivative.interval.hi ≤ 0 then
    some (faceReductionAttempt box expr i validity derivative lower upper hsign)
  else
    none

end CertifiedEvalRegistry
end RationalInterval
end CAS.Continuum

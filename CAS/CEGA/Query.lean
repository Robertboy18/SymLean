/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.Configured
public import CAS.Continuum.IntervalEval.Digits
public import CAS.Continuum.IntervalEval.Registry.CenteredForm

/-!
# Checked CEGA range queries

Theorem-facing interval queries, independent of command elaboration and InfoView rendering.
`encloseOn?` encloses an expression on an arbitrary proved coordinate domain, and
`encloseBoxWith?` on a rational box in `ℝ^n`, the domain of the `cega` tactics. A successful
query returns one `EnclosureAttempt`, indexed by the function it certifies and carrying its route
metadata; ordinary bounds, absolute bounds and midpoint approximations are read off its interval.
Every query takes a `Precision` policy, which the `...With?` variants expose. The `..._of_check`
theorems turn a Boolean comparison of a query's result with stated rationals, which the kernel
evaluates, into the stated proposition.

## Main definitions

* `encloseOn?`: the query on a proved domain: the side-condition-aware normalization when the
  expression contains `exp (log _)`, and otherwise, or when that fails, the registry planner.
* `encloseBoxWith?`, `encloseBox?`: the box planner with `n` nested face reductions on a box in
  `ℝ^n`, at a given precision policy or at the default one.
* `bisectRationalBox`: the bisection of one coordinate at its exact midpoint, with the proof that
  the two halves cover the box.
* `encloseBoxSubdividedAtWith?`: the planner on the two halves of a split at a given coordinate,
  each refined up to `precision.depth - 1` more times by `encloseBoxAdaptive?`, or on the whole
  box when that is sharper.
* `polynomialBoxAttempt`: the enclosure given by an equation
  `RationalInterval.evalPolynomial box expr = some I`, however that equation was checked.

## Main results

* `enclosedOn_of_check`, `boundOn_of_check`, `lt_of_check`, `le_of_check_lower`,
  `lt_of_check_lower`, `boundOn_abs_of_check`, `abs_lt_of_check`, `approxOn_of_check`: a query
  whose result passes the Boolean test of a stated bound proves that bound on the domain.
* `check_and_left`, `check_and_right`: each half of a joint test.

## Implementation notes

One planner level (`encloseBoxLevel?`) first tries the precision-parametric evaluator
`DigitsEval.eval` when the policy sets `digits`, then a correlated hyperbolic route. Otherwise we
preview three routes without building proofs: the finite-chart extension of the registry; the
monotonicity route, which reduces the box to the two faces of a coordinate whose partial
derivative keeps one sign and reruns the whole level on each face; and the multivariate centered
mean-value form. We build certificates in order of previewed sharpness (`rankRoutes`: width, then
magnitude, then route length) until one succeeds, fall back to the finite chart, and keep the
sharper of that result and the `exp (log _)` normalization route. The derivative routes run on
`Verified.Expr.simplify expr` and are transported back by `Verified.Expr.eval_simplify`. A face
fixes one coordinate, so `n` nested levels suffice on `ℝ^n` (`encloseBoxWithFuel?`).
`encloseBoxAdaptive?` bisects where the sensitivity heuristic `selectVariableSubdivisionChoice?`
points, only when the previewed hull of the halves is sharper, and joins the halves by
`EnclosureAttempt.ofBinaryCover` with the cover proof of `bisectRationalBox`.

The previews, the ranking and the choice of split only order the work and are not trusted. Every
returned interval carries its proof (`EnclosureAttempt.sound`) about the total values
`expr.eval`, not about analytic differentiability; each route proves its own denominator and
range conditions, and a query that finds no route returns `none`, which proves nothing, in
particular no singularity. The planner functions are `noncomputable`, so no compiled code runs
them; the kernel evaluates them, when `CAS.CEGA.Elaboration` reduces a query and checks the
theorem built from its result, or inside one `..._of_check` theorem whose test is proved by
`Eq.refl true`. Since every route returns its proof with its interval, no separate checker needs
a soundness theorem and nothing about the search is trusted. The price is that the kernel runs
the search itself, which is why `CAS.CEGA.Elaboration` bounds the size of a query before any
kernel work. The route proofs live with the routes: `memReal_hull_of_signed_partial`
(`CAS.Continuum.IntervalEval.Registry.Monotonicity`), `exists_mem_boxDomain_eval_eq_add_sum`
(`CAS.Continuum.IntervalEval.Registry.CenteredForm`), `DigitsEval.eval_sound`
(`CAS.Continuum.IntervalEval.Digits`) and `RationalInterval.evalPolynomial_sound`
(`CAS.Continuum.IntervalEval.Soundness`). Interval extensions, their refinement by subdivision
and centered mean-value forms are classical; the planner that previews and ranks them and that
the kernel runs is ours.

## References

* Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud, *Introduction to Interval Analysis*,
  SIAM, Philadelphia, 2009, <https://doi.org/10.1137/1.9780898717716>. Chapter 5 for interval
  extensions of real functions, Chapter 6 for the refinement of interval extensions and for
  centered forms.
* Ramon E. Moore, *Interval Analysis*, Prentice-Hall, Englewood Cliffs, N.J., 1966,
  <https://zbmath.org/?q=an:0176.13301>. Interval mean value theorems for functions of one and
  several variables.
-/

@[expose] public section

namespace CAS.CEGA

open CAS.Certificate
open CAS.Verified
open CAS.Continuum
open CAS.Continuum.RationalInterval

/-! ## General semantic-domain queries -/

/-- Detect expressions for which the positive-branch inverse pass can improve an enclosure. -/
def containsExpLog {ι : Type*} : Expr ι → Bool
  | .exp (.log _) => true
  | .add a b | .mul a b | .sub a b | .div a b =>
      containsExpLog a || containsExpLog b
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a |
      .sqrt a =>
      containsExpLog a
  | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ => false
  | .rpow a b => containsExpLog a || containsExpLog b

/--
Certify a two-sided enclosure on an arbitrary proved coordinate domain.

For expressions containing `exp (log _)`, the query first tries checked
side-condition-aware normalization. If that route fails, or no such subexpression
occurs, it uses the registry's enclosure planner. Every successful route
certifies the original expression.
-/
noncomputable def encloseOn?
    {α : Type*} {ι : Type*} [DecidableEq ι] {s : Set α} {ρ : α → ι → ℝ}
    (env : ι → RationalInterval)
    (hvars : ∀ x, x ∈ s → ∀ i, (env i).MemReal (ρ x i))
    (expr : Expr ι) (precision : Precision := {}) :
    Option (EnclosureAttempt α s (fun x ↦ expr.eval (ρ x))) := do
  let registry := CertifiedEvalRegistry.ofEnvironment env hvars precision
  if containsExpLog expr then
    let route := Verified.Expr.simplifySideClaimRoute expr
    match autoSideRouteEnclosureAttempt? route env hvars precision with
    | some result => some result
    | none => registry.selectEnclosureAttempt? expr
  else
    registry.selectEnclosureAttempt? expr

/-! ## Finite-dimensional Euclidean boxes -/

/-- Turn a checked computation of the natural interval evaluator into a box enclosure.
The equality can be checked in the kernel or, by explicit opt-in, by native evaluation. -/
noncomputable def polynomialBoxAttempt {n : ℕ}
    (box : Fin n → RationalInterval) (expr : Expr (Fin n)) (interval : RationalInterval)
    (h : RationalInterval.evalPolynomial box expr = some interval) :
    EnclosureAttempt (ℝ^n) (boxDomain box) (fun x ↦ expr.eval fun i ↦ x i) where
  interval := interval
  sound := by
    intro x hx
    exact RationalInterval.evalPolynomial_sound box (fun i ↦ x i) hx expr interval h

/-- Transport a derivative-route result on the simplified expression back to the query. -/
noncomputable def transportSimplifiedAttempt {n : ℕ}
    (box : Fin n → RationalInterval) (expr : Expr (Fin n))
    (result : EnclosureAttempt (ℝ^n) (boxDomain box)
      (fun x ↦ (Verified.Expr.simplify expr).eval fun i ↦ x i)) :
    EnclosureAttempt (ℝ^n) (boxDomain box) (fun x ↦ expr.eval fun i ↦ x i) :=
  result.congr fun point _ ↦ (Verified.Expr.eval_simplify (fun i ↦ point i) expr).symm

/-- The enclosure routes compared by the box planner. -/
inductive BoxRoute where
  /-- The finite-chart extension: exact normalization, affine, hyperbolic, or easy route. -/
  | finite
  /-- Coordinatewise face reduction from a fixed-sign partial derivative. -/
  | monotonicity
  /-- The multivariate centered mean-value form. -/
  | centered

/-- Insert a previewed route into a list already ordered with the sharpest preview first. -/
def insertRanked (candidate : BoxRoute × PlannerSummary) :
    List (BoxRoute × PlannerSummary) → List (BoxRoute × PlannerSummary)
  | [] => [candidate]
  | head :: tail =>
      if candidate.2.enclosureBetterThan head.2 then
        candidate :: head :: tail
      else
        head :: insertRanked candidate tail

/--
Rank previewed routes with the sharpest first; certificates are constructed in this order.

The insertion sort is structurally recursive, so the kernel evaluator reduces it.
-/
def rankRoutes (candidates : List (BoxRoute × PlannerSummary)) : List BoxRoute :=
  (candidates.foldr insertRanked []).map Prod.fst

/-- Select the sharper of two proof-free enclosure previews. -/
def selectSharperPreview?
    (first second : Option PlannerSummary) : Option PlannerSummary :=
  match first, second with
  | some first, some second =>
      if second.enclosureBetterThan first then some second else some first
  | some result, none | none, some result => some result
  | none, none => none

/-- Select the sharper of two already checked enclosure attempts. -/
noncomputable def selectSharperEnclosure?
    {α : Type*} {s : Set α} {fn : α → ℝ}
    (first second : Option (EnclosureAttempt α s fn)) :
    Option (EnclosureAttempt α s fn) :=
  match first, second with
  | some first, some second =>
      let firstSummary : PlannerSummary :=
        { kind := .easy
          interval := first.interval
          stepCount := first.steps.length }
      let secondSummary : PlannerSummary :=
        { kind := .easy
          interval := second.interval
          stepCount := second.steps.length }
      if secondSummary.enclosureBetterThan firstSummary then
        some second
      else
        some first
  | some result, none | none, some result => some result
  | none, none => none

/--
Proof-free preview of one planner level: the best of the finite-chart
extension, the monotonicity route with `facePreview` on the faces, and the
centered form, the derivative routes running on the simplified expression.
-/
noncomputable def encloseBoxLevelPreview? {n : ℕ} (precision : Precision)
    (facePreview : (Fin n → RationalInterval) → Expr (Fin n) → Option PlannerSummary)
    (box : Fin n → RationalInterval) (expr : Expr (Fin n)) : Option PlannerSummary :=
  let registry := boxRegistry box precision
  let simplified := Verified.Expr.simplify expr
  PlannerSummary.bestEnclosure?
    [registry.selectFiniteEnclosurePreview? expr,
      if derivativeRoutesApply box simplified then
        CertifiedEvalRegistry.monotonicityEnclosurePreview? precision
          (facePreview · simplified) box simplified
      else
        none,
      if CertifiedEvalRegistry.centeredFormApplies box simplified then
        CertifiedEvalRegistry.centeredFormEnclosurePreview? precision box simplified
      else
        none].reduceOption

/-- The enclosure of an expression on a box by the precision-parametric evaluator
`DigitsEval.eval`, at the working precision for `digits` decimal digits. -/
noncomputable def digitsEnclosureAttempt? {n : ℕ} (digits : ℕ)
    (box : Fin n → RationalInterval) (expr : Expr (Fin n)) :
    Option (EnclosureAttempt (ℝ^n) (boxDomain box) (fun x ↦ expr.eval fun i ↦ x i)) :=
  match h : DigitsEval.eval (DigitsEval.precisionFor digits) box expr with
  | some I =>
      some { interval := I
             sound := fun x hx ↦ DigitsEval.eval_sound (DigitsEval.precisionFor digits) box
               (fun i ↦ x i) hx expr h }
  | none => none

/--
One level of the box planner.

When the policy requests digits, the precision-parametric evaluator is tried first. A
correlated hyperbolic route is preferred next. Otherwise the level
previews the finite-chart extension, the monotonicity route with `faceAttempt`
enclosing the two faces, and the centered form, constructs certificates in order
of previewed sharpness, and finally compares the result with the branch-aware
`exp (log _)` normalization route. The derivative routes run on the simplified
expression and are transported back to the query.
-/
noncomputable def encloseBoxLevel? {n : ℕ} (precision : Precision)
    (facePreview : (Fin n → RationalInterval) → Expr (Fin n) → Option PlannerSummary)
    (faceAttempt : (face : Fin n → RationalInterval) → (target : Expr (Fin n)) →
      Option (EnclosureAttempt (ℝ^n) (boxDomain face)
        (fun x ↦ target.eval fun i ↦ x i)))
    (box : Fin n → RationalInterval) (expr : Expr (Fin n)) :
    Option (EnclosureAttempt (ℝ^n) (boxDomain box) (fun x ↦ expr.eval fun i ↦ x i)) :=
  match precision.digits.bind fun digits ↦ digitsEnclosureAttempt? digits box expr with
  | some result => some result
  | none =>
  let registry := boxRegistry box precision
  match registry.toContext.hyperbolicEnclosureAttempt? expr precision.expOrder.toPNat' with
  | some result => some result
  | none =>
    let side :=
      if containsExpLog expr then
        autoSideRouteEnclosureAttempt? (Verified.Expr.simplifySideClaimRoute expr) box
          registry.hvars precision
      else
        none
    let finite := registry.selectFiniteEnclosureAttempt? expr
    let simplified := Verified.Expr.simplify expr
    let candidates : List (BoxRoute × PlannerSummary) :=
      [(registry.selectFiniteEnclosurePreview? expr).map fun summary ↦ (BoxRoute.finite, summary),
        (if derivativeRoutesApply box simplified then
            CertifiedEvalRegistry.monotonicityEnclosurePreview? precision
              (facePreview · simplified) box simplified
          else
            none).map fun summary ↦ (BoxRoute.monotonicity, summary),
        (if CertifiedEvalRegistry.centeredFormApplies box simplified then
            CertifiedEvalRegistry.centeredFormEnclosurePreview? precision box simplified
          else
            none).map fun summary ↦ (BoxRoute.centered, summary)].reduceOption
    let construct : BoxRoute →
        Option (EnclosureAttempt (ℝ^n) (boxDomain box) (fun x ↦ expr.eval fun i ↦ x i))
      | .finite => finite
      | .monotonicity =>
          (CertifiedEvalRegistry.monotonicityEnclosureAttempt? precision box simplified
            (faceAttempt · simplified)).map (transportSimplifiedAttempt box expr)
      | .centered =>
          (CertifiedEvalRegistry.centeredFormEnclosureAttempt? precision box simplified).map
            (transportSimplifiedAttempt box expr)
    let primary := ((rankRoutes candidates).findSome? construct).or finite
    selectSharperEnclosure? side primary

/-- Proof-free preview of the box planner with at most `fuel` nested face reductions. -/
noncomputable def encloseBoxPreviewWithFuel? {n : ℕ} (precision : Precision) :
    ℕ → (box : Fin n → RationalInterval) → (expr : Expr (Fin n)) → Option PlannerSummary
  | 0, box, expr => encloseBoxLevelPreview? precision (fun _ _ ↦ none) box expr
  | fuel + 1, box, expr =>
      encloseBoxLevelPreview? precision (encloseBoxPreviewWithFuel? precision fuel) box expr

/--
The box planner with at most `fuel` nested face reductions; every face reruns
the complete level, so the reductions nest until the fuel or the fixed-sign
coordinates are exhausted.
-/
noncomputable def encloseBoxWithFuel? {n : ℕ} (precision : Precision) :
    ℕ → (box : Fin n → RationalInterval) → (expr : Expr (Fin n)) →
      Option (EnclosureAttempt (ℝ^n) (boxDomain box) (fun x ↦ expr.eval fun i ↦ x i))
  | 0, box, expr => encloseBoxLevel? precision (fun _ _ ↦ none) (fun _ _ ↦ none) box expr
  | fuel + 1, box, expr =>
      encloseBoxLevel? precision (encloseBoxPreviewWithFuel? precision fuel)
        (encloseBoxWithFuel? precision fuel) box expr

/--
Certify an enclosure on an arbitrary finite-dimensional rational box at a
requested precision.

Each face reduction fixes one coordinate, so `n` nested levels suffice for a box
in `ℝ^n`.
-/
noncomputable def encloseBoxWith? {n : ℕ} (precision : Precision)
    (box : Fin n → RationalInterval) (expr : Expr (Fin n)) :
    Option
      (EnclosureAttempt (ℝ^n) (boxDomain box)
        (fun x ↦ expr.eval fun i ↦ x i)) :=
  encloseBoxWithFuel? precision n box expr

/-- Certify an enclosure on an arbitrary finite-dimensional rational box at default precision. -/
noncomputable def encloseBox? {n : ℕ}
    (box : Fin n → RationalInterval) (expr : Expr (Fin n)) :
    Option
      (EnclosureAttempt (ℝ^n) (boxDomain box)
        (fun x ↦ expr.eval fun i ↦ x i)) :=
  encloseBoxWith? {} box expr

/-- A midpoint bisection of one rational box, including its semantic cover. -/
structure RationalBoxBisection {n : ℕ}
    (box : Fin n → RationalInterval) where
  /-- Left child box. -/
  left : Fin n → RationalInterval
  /-- Right child box. -/
  right : Fin n → RationalInterval
  /-- The two child boxes cover the parent box. -/
  cover : boxDomain box ⊆
    boxDomain left ∪ boxDomain right

/-- Bisect one coordinate of a rational box at its exact midpoint. -/
def bisectRationalBox {n : ℕ}
    (box : Fin n → RationalInterval) (coordinate : Fin n) :
    RationalBoxBisection box :=
  let source := box coordinate
  let split := source.center
  let leftInterval : RationalInterval :=
    { lo := source.lo
      hi := split
      hle := by
        dsimp [split]
        unfold RationalInterval.center
        linarith [source.hle] }
  let rightInterval : RationalInterval :=
    { lo := split
      hi := source.hi
      hle := by
        dsimp [split]
        unfold RationalInterval.center
        linarith [source.hle] }
  let leftBox := Function.update box coordinate leftInterval
  let rightBox := Function.update box coordinate rightInterval
  { left := leftBox
    right := rightBox
    cover := by
      intro point hpoint
      by_cases hleft : point coordinate ≤ (split : ℝ)
      · left
        intro i
        by_cases hi : i = coordinate
        · subst i
          simp only [leftBox, Function.update_self, RationalInterval.MemReal,
            leftInterval]
          exact ⟨(hpoint coordinate).1, hleft⟩
        · simpa [leftBox, Function.update_of_ne hi] using hpoint i
      · right
        intro i
        by_cases hi : i = coordinate
        · subst i
          simp only [rightBox, Function.update_self, RationalInterval.MemReal,
            rightInterval]
          exact ⟨le_of_not_ge hleft, (hpoint coordinate).2⟩
        · simpa [rightBox, Function.update_of_ne hi] using hpoint i }


/-- Proof-free preview of the full ordinary box planner. -/
noncomputable def encloseBoxPreview? {n : ℕ} (precision : Precision)
    (box : Fin n → RationalInterval) (expr : Expr (Fin n)) :
    Option PlannerSummary :=
  encloseBoxPreviewWithFuel? precision n box expr

/-- Hull two child previews and record the covering refinement step. -/
def hullPreview (left right : PlannerSummary) : PlannerSummary :=
  { kind := .easy
    interval := left.interval.hull right.interval
    stepCount := left.stepCount + right.stepCount + 1 }

/-- Preview recursive refinement without constructing any certificate proof. -/
noncomputable def encloseBoxAdaptivePreview? {n : ℕ} (precision : Precision) :
    ℕ → (box : Fin n → RationalInterval) → (expr : Expr (Fin n)) →
      Option PlannerSummary
  | 0, box, expr => encloseBoxPreview? precision box expr
  | fuel + 1, box, expr =>
      let base := encloseBoxPreview? precision box expr
      match (boxRegistry box precision).selectVariableSubdivisionChoice?
          (List.finRange n) expr with
      | none => base
      | some choice =>
          let bisection := bisectRationalBox box choice.coordinate
          let refined := do
            let left ← encloseBoxAdaptivePreview? precision fuel bisection.left expr
            let right ← encloseBoxAdaptivePreview? precision fuel bisection.right expr
            pure (hullPreview left right)
          selectSharperPreview? base refined

/--
Recursively refine a box, rerunning the full CEGA planner on every child.

Unlike the finite-chart one-step route, this includes the derivative
routes on child boxes. The sensitivity heuristic chooses only where to split;
every returned result is justified by the stored binary-cover proofs.
-/
noncomputable def encloseBoxAdaptive? {n : ℕ} (precision : Precision) :
    ℕ → (box : Fin n → RationalInterval) → (expr : Expr (Fin n)) →
      Option
        (EnclosureAttempt (ℝ^n) (boxDomain box)
          (fun x ↦ expr.eval fun i ↦ x i))
  | 0, box, expr => encloseBoxWith? precision box expr
  | fuel + 1, box, expr =>
      let base := encloseBoxWith? precision box expr
      let basePreview := encloseBoxPreview? precision box expr
      match (boxRegistry box precision).selectVariableSubdivisionChoice?
          (List.finRange n) expr with
      | none => base
      | some choice =>
          let bisection := bisectRationalBox box choice.coordinate
          let refinedPreview := do
            let left ← encloseBoxAdaptivePreview? precision fuel bisection.left expr
            let right ← encloseBoxAdaptivePreview? precision fuel bisection.right expr
            pure (hullPreview left right)
          let shouldRefine :=
            match basePreview, refinedPreview with
            | none, some _ => true
            | some baseSummary, some refinedSummary =>
                refinedSummary.enclosureBetterThan baseSummary
            | _, _ => false
          if shouldRefine then
            match encloseBoxAdaptive? precision fuel bisection.left expr,
                encloseBoxAdaptive? precision fuel bisection.right expr with
            | some left, some right =>
                selectSharperEnclosure? base <|
                  some (EnclosureAttempt.ofBinaryCover bisection.cover left right)
            | _, _ => base
          else
            base

/--
Certify an enclosure after bisecting one explicitly selected coordinate.

The coordinate selects the first split. Each child receives
`precision.depth - 1` additional sensitivity-guided refinements and reruns the
complete planner. The returned attempt carries every checked binary-cover proof.
-/
noncomputable def encloseBoxSubdividedAtWith? {n : ℕ} (precision : Precision)
    (coordinate : Fin n)
    (box : Fin n → RationalInterval) (expr : Expr (Fin n)) :
    Option
      (EnclosureAttempt (ℝ^n) (boxDomain box)
        (fun x ↦ expr.eval fun i ↦ x i)) :=
  let base := encloseBoxWith? precision box expr
  let bisection := bisectRationalBox box coordinate
  match encloseBoxAdaptive? precision (precision.depth - 1) bisection.left expr,
      encloseBoxAdaptive? precision (precision.depth - 1) bisection.right expr with
  | some left, some right =>
      selectSharperEnclosure? base <|
        some (EnclosureAttempt.ofBinaryCover bisection.cover left right)
  | _, _ => base

/-! ## Stated bounds

A goal that states its bounds with rational numbers, such as `EnclosedOn f s (-1) 1` or
`f x ≤ 1 / 4`, needs no endpoint read-back. The kernel can evaluate the query and compare the
interval it returns with the stated numbers in one check, a Boolean test of the query's result
that must reduce to `true`. Each theorem below turns one such test into the stated proposition.
A query that returns `none` fails every test. Several bounds on one query join their tests with
`&&`, so that the kernel evaluates the query once; `check_and_left` and `check_and_right` split
such a joint test. -/

/-- The stated enclosure `[lo, hi]` contains the query's interval. -/
theorem enclosedOn_of_check {α : Type*} {s : Set α} {fn : α → ℝ}
    (q : Option (EnclosureAttempt α s fn)) (lo hi : ℚ)
    (h : (q.any fun a ↦ decide (lo ≤ a.interval.lo) && decide (a.interval.hi ≤ hi)) = true) :
    EnclosedOn fn s (lo : ℝ) (hi : ℝ) := by
  obtain _ | a := q
  · simp at h
  · simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h
    exact enclosedOn_mono a.sound (by exact_mod_cast h.1) (by exact_mod_cast h.2)

/-- The query's upper endpoint is at most the stated bound. -/
theorem boundOn_of_check {α : Type*} {s : Set α} {fn : α → ℝ}
    (q : Option (EnclosureAttempt α s fn)) (c : ℚ)
    (h : (q.any fun a ↦ decide (a.interval.hi ≤ c)) = true) :
    BoundOn fn s (c : ℝ) := by
  obtain _ | a := q
  · simp at h
  · simp only [Option.any_some, decide_eq_true_eq] at h
    exact boundOn_mono a.boundOn (by exact_mod_cast h)

/-- The query's upper endpoint is below the stated bound. -/
theorem lt_of_check {α : Type*} {s : Set α} {fn : α → ℝ}
    (q : Option (EnclosureAttempt α s fn)) (c : ℚ)
    (h : (q.any fun a ↦ decide (a.interval.hi < c)) = true) :
    ∀ x ∈ s, fn x < (c : ℝ) := by
  obtain _ | a := q
  · simp at h
  · simp only [Option.any_some, decide_eq_true_eq] at h
    exact fun x hx ↦ (a.sound x hx).2.trans_lt (by exact_mod_cast h)

/-- The query's lower endpoint is at least the stated bound. -/
theorem le_of_check_lower {α : Type*} {s : Set α} {fn : α → ℝ}
    (q : Option (EnclosureAttempt α s fn)) (c : ℚ)
    (h : (q.any fun a ↦ decide (c ≤ a.interval.lo)) = true) :
    ∀ x ∈ s, (c : ℝ) ≤ fn x := by
  obtain _ | a := q
  · simp at h
  · simp only [Option.any_some, decide_eq_true_eq] at h
    exact fun x hx ↦ (show (c : ℝ) ≤ a.interval.lo by exact_mod_cast h).trans (a.sound x hx).1

/-- The query's lower endpoint is above the stated bound. -/
theorem lt_of_check_lower {α : Type*} {s : Set α} {fn : α → ℝ}
    (q : Option (EnclosureAttempt α s fn)) (c : ℚ)
    (h : (q.any fun a ↦ decide (c < a.interval.lo)) = true) :
    ∀ x ∈ s, (c : ℝ) < fn x := by
  obtain _ | a := q
  · simp at h
  · simp only [Option.any_some, decide_eq_true_eq] at h
    exact fun x hx ↦ (show (c : ℝ) < a.interval.lo by exact_mod_cast h).trans_le (a.sound x hx).1

/-- The largest absolute endpoint of the query's interval is at most the stated bound. -/
theorem boundOn_abs_of_check {α : Type*} {s : Set α} {fn : α → ℝ}
    (q : Option (EnclosureAttempt α s fn)) (c : ℚ)
    (h : (q.any fun a ↦ decide (a.interval.absMax ≤ c)) = true) :
    BoundOn (fun x ↦ |fn x|) s (c : ℝ) := by
  obtain _ | a := q
  · simp at h
  · simp only [Option.any_some, decide_eq_true_eq] at h
    exact boundOn_mono a.boundOn_abs (by exact_mod_cast h)

/-- The largest absolute endpoint of the query's interval is below the stated bound. -/
theorem abs_lt_of_check {α : Type*} {s : Set α} {fn : α → ℝ}
    (q : Option (EnclosureAttempt α s fn)) (c : ℚ)
    (h : (q.any fun a ↦ decide (a.interval.absMax < c)) = true) :
    ∀ x ∈ s, |fn x| < (c : ℝ) := by
  obtain _ | a := q
  · simp at h
  · simp only [Option.any_some, decide_eq_true_eq] at h
    exact fun x hx ↦ (a.boundOn_abs x hx).trans_lt (by exact_mod_cast h)

/-- The stated center is the midpoint of the query's interval and the stated radius is at least
its radius. -/
theorem approxOn_of_check {α : Type*} {s : Set α} {fn : α → ℝ}
    (q : Option (EnclosureAttempt α s fn)) (center radius : ℚ)
    (h : (q.any fun a ↦
      decide (a.interval.center = center) && decide (a.interval.radius ≤ radius)) = true) :
    ApproxOn fn (fun _ ↦ (center : ℝ)) s (radius : ℝ) := by
  obtain _ | a := q
  · simp at h
  · simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1 ▸ approxOn_mono_error a.approxOn_center (by exact_mod_cast h.2)

/-- The first of two tests that a query passes together. -/
theorem check_and_left {α : Type*} {s : Set α} {fn : α → ℝ}
    (q : Option (EnclosureAttempt α s fn)) (t u : EnclosureAttempt α s fn → Bool)
    (h : (q.any fun a ↦ t a && u a) = true) : q.any t = true := by
  cases q <;> simp_all

/-- The second of two tests that a query passes together. -/
theorem check_and_right {α : Type*} {s : Set α} {fn : α → ℝ}
    (q : Option (EnclosureAttempt α s fn)) (t u : EnclosureAttempt α s fn → Bool)
    (h : (q.any fun a ↦ t a && u a) = true) : q.any u = true := by
  cases q <;> simp_all

end CAS.CEGA

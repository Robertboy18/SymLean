/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.AdvancedPasses
public import CAS.ClosedForm.Pipeline.ExactRoutes
public import CAS.ClosedForm.Pipeline.Passes.Elementary
public import CAS.ClosedForm.Pipeline.Passes.Normalization
public import CAS.ClosedForm.Pipeline.Passes.Pythagorean
public import CAS.ClosedForm.Pipeline.Passes.RealPower
public import CAS.ClosedForm.Pipeline.Passes.SqrtNumeral
public import CAS.ClosedForm.RationalCanonical
public import CAS.ClosedForm.Canonical
public import CAS.Expr.Substitution

/-!
# Configured simplification routes

The standard plain and side-conditioned pipelines of the computer algebra system, assembled
from checked passes, with their fuel bounds and the proofs that each configured route preserves
real evaluation under its reported side conditions.

## Main definitions

* `simplifyPipeline`: the unconditional fixed-point pipeline of `checkedPasses`.
* `configuredSidePipeline`, `sideConditionPipeline`: the side passes run before and after the
  base pipeline, in their fixed order.
* `essentialSide`: the recorded conditions that the structural sign checker does not prove.
* `summandRun`, `abstractedSummandRun`: the certification data for a finite sum normalized
  summand by summand, optionally with a shared radicand replaced by a variable.
* `SidePipeline.claimRoute`, `SidePipeline.finClaimRoute`: a run of a side-conditioned pipeline
  as a `SideClaimRoute`, followed, for one coordinate, by the univariate rational canonical form
  and, for two or more, by `Alg.canonical`.
* `simplifySideClaimRoute`, `simplifyFinSideClaimRoute`: these routes for
  `sideConditionPipeline`, the normal form of zero tests and `cas_nf`.
* `simplifyFinDisplayRoute`: the route of a displayed simplification, which keeps cosines unless
  the Pythagorean elimination gives a smaller result.

## Main results

* `eval_eq_of_sideConditionPipeline_run_essential`: a run of `sideConditionPipeline` that
  normalizes `lhs - rhs` to `0` proves `lhs = rhs` wherever the essential conditions hold.
* `eval_eq_of_summandRun_essential`, `eval_eq_of_abstractedSummandRun_essential`: the same for
  sums normalized summand by summand.
* `eval_eq_of_simplifyPipeline_runFixed_eq`, `eval_eq_of_sideConditionPipeline_run_result`: a
  checked equation between a run and its quoted result gives the equality of evaluations, the
  form `cas_nf` uses.

## Implementation notes

We prove an identity as a zero test. The pipeline runs on `lhs - rhs`, and the kernel checks
two facts about the run: its expression is the literal `0`, and `essentialSide` of its recorded
list is the stated `side`. The rest of the proof is `SidePipeline.eval_run` together with the
soundness of the sign checker, `AutomaticSign.eval_ne_zero_of_nonzero_eq_true`, for the
conditions that `essentialSide` drops.

The base pipeline `checkedPasses` (`structural`, `trig`, `algebra`, `factor-common`) is
unconditional, so every condition of a pipeline run comes from a side pass. Side passes record:

* each cancelled factor `≠ 0`: `deep-factor-cancel`;
* the denominators `≠ 0`: `fraction-normal-form`, `rational-side`;
* `0 < a`, as the entry `sqrt a`: `inverse-elementary` for `exp (log a)`, `sqrt-square` and
  `sqrt-product-collect` for `(sqrt a)^2` and `sqrt a * sqrt a`, and `real-power` for each base
  rewritten by a Mathlib lemma with a sign hypothesis that the structural sign checker does not
  prove;
* nothing: `sqrt-numeral`, `pythagorean`, `unit-ratio`, `common-add-factor`.
-/

@[expose] public section

namespace CAS.Verified.Expr

/-- Default number of fixed-point simplification rounds. -/
def defaultFuel : Nat := 6

/-- The default side-condition-free simplification pipeline.

This excludes denominator-clearing across unrelated factors.  Use
`Alg.normalizeWithSide` or the side-condition pipeline for that stronger
side-condition-aware pass.  It includes checked trig cleanup so the
calculator and theorem tactics use the same normal form for common identities
such as `sin(x)^2 + cos(x)^2 = 1`. -/
def simplifyPipeline {ι : Type*} [DecidableEq ι] : Pipeline ι where
  name := "simplify"
  passes := checkedPasses
  fuel := defaultFuel

/-- Assemble the shared side-condition stages around an ordinary base pipeline.

The real-power pass runs before and after the base normalization, and before the fraction
normal form, so that quotients by powers are absorbed into exponents instead of becoming
denominator obligations. The numeral square-root and Pythagorean passes follow the square-root
square cleanup; neither records an obligation. With `pythagorean := false` the Pythagorean pass
is left out, so that cosines are not rewritten as `1 - sin u ^ 2`. -/
def configuredSidePipeline {ι : Type*} [DecidableEq ι] (base : Pipeline ι)
    (pythagorean : Bool := true) : SidePipeline ι where
  name := base.name ++
    "+inverse-elementary+real-power+fraction-normal-form+rational-side+sqrt-square+" ++
      "sqrt-numeral+" ++ (if pythagorean then "pythagorean+" else "") ++
        "sqrt-product-collect+common-add-factor+deep-factor-cancel+unit-ratio"
  base := base
  preSidePasses := [deepFactorCancelSidePass, elementarySidePass, realPowerSidePass]
  sidePasses := [elementarySidePass, realPowerSidePass, fractionSidePass, rationalSidePass,
    sqrtSquareSidePass, sqrtNumeralSidePass] ++
    (if pythagorean then [pythagoreanSidePass] else []) ++
    [sqrtProductCollectSidePass, commonAddFactorSidePass, deepFactorCancelSidePass,
      unitRatioSidePass]

/-- The default side-condition-aware simplification pipeline. -/
def sideConditionPipeline {ι : Type*} [DecidableEq ι] : SidePipeline ι :=
  configuredSidePipeline simplifyPipeline

/-- The default simplification pipeline preserves denotation after fixed-point execution. -/
@[simp] theorem eval_simplifyPipeline_runFixed {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
  (expr : Verified.Expr ι) :
    ((simplifyPipeline (ι := ι)).runFixed expr).eval ρ = expr.eval ρ :=
  eval_runFixed ρ _ _ _

deriving instance DecidableEq for Alg.NormResult

/-- A checked equality with a quoted normal form transports the fixed-point pipeline's
soundness without asking an elaborator to unfold the pipeline during unification. -/
theorem eval_eq_of_simplifyPipeline_runFixed_eq {ι : Type*} [DecidableEq ι]
    (ρ : ι → ℝ) (expr result : Verified.Expr ι)
    (h : (simplifyPipeline (ι := ι)).runFixed expr = result) :
    expr.eval ρ = result.eval ρ := by
  rw [← h]
  exact (eval_simplifyPipeline_runFixed ρ expr).symm

/-- A quoted side-conditioned normal form is sound after its complete data and required
nonzero conditions have been checked. The computation equality is separate from evaluation. -/
theorem eval_eq_of_sideConditionPipeline_run_result {ι : Type*} [DecidableEq ι]
    (ρ : ι → ℝ) (expr result : Verified.Expr ι) (side : List (Verified.Expr ι))
    (h : (sideConditionPipeline (ι := ι)).run expr = ⟨result, side⟩)
    (hside : Alg.SideHolds ρ side) :
    expr.eval ρ = result.eval ρ := by
  have sound := SidePipeline.eval_run (sideConditionPipeline (ι := ι)) ρ expr (by rwa [h])
  rw [h] at sound
  exact sound.symm

/-- The recorded side conditions of a normalizer run that the structural sign checker
`AutomaticSign.nonzero` does not already prove: the conditions a caller has to discharge. A
run whose conditions are all structurally nonzero, such as sums of exponentials and positive
numerals, has an empty essential list. -/
def essentialSide {ι : Type*} [DecidableEq ι] (side : List (Verified.Expr ι)) :
    List (Verified.Expr ι) :=
  side.filter fun condition ↦ !AutomaticSign.nonzero condition

/-- The essential conditions imply every recorded condition: a dropped condition is proved
nonzero by the structural sign checker. -/
theorem sideHolds_of_essentialSide {ι : Type*} [DecidableEq ι] {ρ : ι → ℝ}
    {side : List (Verified.Expr ι)} (h : Alg.SideHolds ρ (essentialSide side)) :
    Alg.SideHolds ρ side := by
  intro d hd
  by_cases hauto : AutomaticSign.nonzero d = true
  · exact AutomaticSign.eval_ne_zero_of_nonzero_eq_true ρ d hauto
  · exact h d (List.mem_filter.mpr ⟨hd, by simpa using hauto⟩)

/-- A run without essential conditions has all its recorded conditions satisfied everywhere. -/
theorem sideHolds_of_essentialSide_eq_nil {ι : Type*} [DecidableEq ι]
    {side : List (Verified.Expr ι)} (h : essentialSide side = []) (ρ : ι → ℝ) :
    Alg.SideHolds ρ side :=
  sideHolds_of_essentialSide (by simp [h, Alg.SideHolds])

/--
The certification statement of the checked identity routes: the side-conditioned pipeline
normalizes `lhs - rhs` to the literal zero and its essential side conditions are the list
`side`. Wherever `side` holds, the two expressions evaluate equally. Tactics guess `side = []`
first, which one kernel evaluation certifies for unconditional identities and for residuals
whose recorded conditions are all structurally nonzero, and read the list back only when that
guess fails.
-/
theorem eval_eq_of_sideConditionPipeline_run_essential {ι : Type*} [DecidableEq ι]
    (lhs rhs : Verified.Expr ι) (ρ : ι → ℝ) (side : List (Verified.Expr ι))
    (hrun : ((sideConditionPipeline (ι := ι)).run (.sub lhs rhs)).expr = .nat 0 ∧
      essentialSide ((sideConditionPipeline (ι := ι)).run (.sub lhs rhs)).nonzero = side)
    (hside : Alg.SideHolds ρ side) :
    lhs.eval ρ = rhs.eval ρ := by
  have hrunEval := SidePipeline.eval_run (sideConditionPipeline (ι := ι)) ρ (.sub lhs rhs)
    (sideHolds_of_essentialSide (by rwa [hrun.2]))
  rw [hrun.1] at hrunEval
  simp only [Verified.Expr.eval, Nat.cast_zero] at hrunEval
  exact (sub_eq_zero.mp hrunEval.symm)

/-! ### Sums normalized summand by summand

A Laplacian is a finite sum of second derivatives. Normalizing the whole sum against a stated
value cross-multiplies the denominators of every summand in the fraction normal form, and the
expansion of the resulting powers of the radicands dominates the run time. Each summand is
therefore normalized on its own, first with the ordinary fixed-point pipeline and then with the
side-conditioned pipeline, before the sum of the normal forms is compared with the stated
value. -/

/-- The normal form of one summand: the ordinary fixed-point pipeline followed by the
side-conditioned pipeline. -/
def summandNormalForm {ι : Type*} [DecidableEq ι] (summand : Verified.Expr ι) :
    Alg.NormResult ι :=
  (sideConditionPipeline (ι := ι)).run ((simplifyPipeline (ι := ι)).runFixed summand)

/-- A summand's normal form evaluates to the summand wherever its recorded conditions hold. -/
theorem eval_summandNormalForm {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (summand : Verified.Expr ι) (hside : Alg.SideHolds ρ (summandNormalForm summand).nonzero) :
    (summandNormalForm summand).expr.eval ρ = summand.eval ρ :=
  (SidePipeline.eval_run (sideConditionPipeline (ι := ι)) ρ _ hside).trans
    (eval_simplifyPipeline_runFixed ρ summand)

/-- The normal forms of the summands of a sum, with the union of their recorded conditions. -/
def normalizeSummands {ι : Type*} [DecidableEq ι] (summands : List (Verified.Expr ι)) :
    Alg.NormResult ι :=
  { expr := Verified.Expr.addList (summands.map fun summand ↦ (summandNormalForm summand).expr)
    nonzero := Alg.cleanSide (summands.flatMap fun summand ↦ (summandNormalForm summand).nonzero) }

/-- The sum of the evaluated summand normal forms is the sum of the evaluated summands wherever
the conditions of every summand hold. Stated with explicit lambdas so that every unification
against it is syntactic: comparing `eval` applications up to definitional unfolding would
evaluate the pipeline. -/
theorem sum_map_eval_summandNormalForm {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (summands : List (Verified.Expr ι))
    (hall : ∀ summand ∈ summands, Alg.SideHolds ρ (summandNormalForm summand).nonzero) :
    (summands.map fun summand ↦ (summandNormalForm summand).expr.eval ρ).sum =
      (summands.map fun summand ↦ summand.eval ρ).sum :=
  congrArg List.sum (List.map_congr_left fun summand hsummand ↦
    eval_summandNormalForm ρ summand (hall summand hsummand))

/-- The normalized summands evaluate to the original sum wherever their conditions hold. -/
theorem eval_normalizeSummands {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (summands : List (Verified.Expr ι))
    (hside : Alg.SideHolds ρ (normalizeSummands summands).nonzero) :
    (normalizeSummands summands).expr.eval ρ = (Verified.Expr.addList summands).eval ρ := by
  have hall : ∀ summand ∈ summands, Alg.SideHolds ρ (summandNormalForm summand).nonzero :=
    fun summand hsummand d hd ↦
      Alg.sideHolds_of_cleanSide hside d (List.mem_flatMap.mpr ⟨summand, hsummand, hd⟩)
  simp only [normalizeSummands, Verified.Expr.eval_addList, List.map_map, Function.comp_def,
    sum_map_eval_summandNormalForm ρ summands hall]

/-- The certification data for a sum against a stated value: each summand normalized first,
then the difference of the normalized sum and the stated value, with all recorded conditions
collected. -/
def summandRun {ι : Type*} [DecidableEq ι] (summands : List (Verified.Expr ι))
    (stated : Verified.Expr ι) : Alg.NormResult ι :=
  { expr := ((sideConditionPipeline (ι := ι)).run
      (.sub (normalizeSummands summands).expr stated)).expr
    nonzero := Alg.cleanSide ((normalizeSummands summands).nonzero ++
      ((sideConditionPipeline (ι := ι)).run
        (.sub (normalizeSummands summands).expr stated)).nonzero) }

/-- The certification statement for a sum: the summand run has the normal form `0` and the
essential side list `side`; wherever `side` holds, the sum evaluates to the stated value. -/
theorem eval_eq_of_summandRun_essential {ι : Type*} [DecidableEq ι]
    (summands : List (Verified.Expr ι)) (stated : Verified.Expr ι) (ρ : ι → ℝ)
    (side : List (Verified.Expr ι))
    (hrun : (summandRun summands stated).expr = .nat 0 ∧
      essentialSide (summandRun summands stated).nonzero = side)
    (hside : Alg.SideHolds ρ side) :
    (Verified.Expr.addList summands).eval ρ = stated.eval ρ := by
  simp only [summandRun] at hrun
  have hboth : Alg.SideHolds ρ ((normalizeSummands summands).nonzero ++
      ((sideConditionPipeline (ι := ι)).run
        (.sub (normalizeSummands summands).expr stated)).nonzero) :=
    Alg.sideHolds_of_cleanSide (sideHolds_of_essentialSide (by rwa [hrun.2]))
  have hfinalEval := SidePipeline.eval_run (sideConditionPipeline (ι := ι)) ρ _ hboth.append_right
  rw [hrun.1] at hfinalEval
  simp only [Verified.Expr.eval, Nat.cast_zero] at hfinalEval
  rw [← eval_normalizeSummands ρ summands hboth.append_left]
  exact (sub_eq_zero.mp hfinalEval.symm)

/-! ### Sums with a shared radicand abstracted

The summands of a Laplacian of a radial function share one radicand `r = q₀² + q₁² + …`, which
occurs under every square root and real power. Normalizing a summand expands the powers of `r`
that the derivative rules produce, and the recorded conditions come out as expanded polynomials
that the side-condition finishers do not relate to `0 < r`. The fold therefore replaces every
occurrence of `r` by a fresh variable `u` before normalizing, so that `u` is an atom of the
normal forms and of the conditions, and substitutes `r` back into the small normal form of the
difference at the end. Soundness needs only that the environment sends `u` to the value of
`r`. -/

/-- Replace `expr` by the variable `u` when it is exactly the pattern. -/
def replaceEqual {ι : Type*} [DecidableEq ι] (pattern : Verified.Expr ι) (u : ι)
    (expr : Verified.Expr ι) : Verified.Expr ι :=
  if expr = pattern then .var u else expr

/-- An expression that is the pattern evaluates to `ρ u` wherever `ρ u` is the pattern's value. -/
theorem eval_replaceEqual {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) (pattern : Verified.Expr ι)
    (u : ι) (hu : ρ u = pattern.eval ρ) (expr : Verified.Expr ι) :
    (replaceEqual pattern u expr).eval ρ = expr.eval ρ := by
  unfold replaceEqual
  split_ifs with hequal
  · simpa [hequal] using hu
  · rfl

/-- Replace every occurrence of `pattern` in an expression by the variable `u`, bottom-up. -/
def abstractSubterm {ι : Type*} [DecidableEq ι] (pattern : Verified.Expr ι) (u : ι) :
    Verified.Expr ι → Verified.Expr ι
  | .nat n => replaceEqual pattern u (.nat n)
  | .int n => replaceEqual pattern u (.int n)
  | .rat a b => replaceEqual pattern u (.rat a b)
  | .pi => replaceEqual pattern u .pi
  | .e => replaceEqual pattern u .e
  | .var i => replaceEqual pattern u (.var i)
  | .add a b =>
      replaceEqual pattern u (.add (abstractSubterm pattern u a) (abstractSubterm pattern u b))
  | .mul a b =>
      replaceEqual pattern u (.mul (abstractSubterm pattern u a) (abstractSubterm pattern u b))
  | .sub a b =>
      replaceEqual pattern u (.sub (abstractSubterm pattern u a) (abstractSubterm pattern u b))
  | .div a b =>
      replaceEqual pattern u (.div (abstractSubterm pattern u a) (abstractSubterm pattern u b))
  | .neg a => replaceEqual pattern u (.neg (abstractSubterm pattern u a))
  | .pow a n => replaceEqual pattern u (.pow (abstractSubterm pattern u a) n)
  | .sin a => replaceEqual pattern u (.sin (abstractSubterm pattern u a))
  | .cos a => replaceEqual pattern u (.cos (abstractSubterm pattern u a))
  | .atan a => replaceEqual pattern u (.atan (abstractSubterm pattern u a))
  | .asin a => replaceEqual pattern u (.asin (abstractSubterm pattern u a))
  | .acos a => replaceEqual pattern u (.acos (abstractSubterm pattern u a))
  | .exp a => replaceEqual pattern u (.exp (abstractSubterm pattern u a))
  | .log a => replaceEqual pattern u (.log (abstractSubterm pattern u a))
  | .sqrt a => replaceEqual pattern u (.sqrt (abstractSubterm pattern u a))
  | .rpow a b =>
      replaceEqual pattern u (.rpow (abstractSubterm pattern u a) (abstractSubterm pattern u b))

/-- Abstracting the pattern preserves evaluation wherever `ρ u` is the pattern's value. -/
theorem eval_abstractSubterm {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (pattern : Verified.Expr ι) (u : ι) (hu : ρ u = pattern.eval ρ) (expr : Verified.Expr ι) :
    (abstractSubterm pattern u expr).eval ρ = expr.eval ρ := by
  induction expr <;> simp [abstractSubterm, eval_replaceEqual ρ pattern u hu, *]

/-- Substitute the pattern back for the variable `u`. -/
def restoreSubterm {ι : Type*} [DecidableEq ι] (pattern : Verified.Expr ι) (u : ι) :
    Verified.Expr ι → Verified.Expr ι :=
  Verified.Expr.mapVars fun i ↦ if i = u then pattern else .var i

/-- Restoring the pattern preserves evaluation wherever `ρ u` is the pattern's value. -/
theorem eval_restoreSubterm {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (pattern : Verified.Expr ι) (u : ι) (hu : ρ u = pattern.eval ρ) (expr : Verified.Expr ι) :
    (restoreSubterm pattern u expr).eval ρ = expr.eval ρ := by
  rw [restoreSubterm, Verified.Expr.eval_mapVars]
  congr 1
  funext i
  split_ifs with hi
  · exact hi ▸ hu.symm
  · rfl

/-- The summands with the pattern abstracted. -/
def abstractedSummands {ι : Type*} [DecidableEq ι] (summands : List (Verified.Expr ι))
    (pattern : Verified.Expr ι) (u : ι) : List (Verified.Expr ι) :=
  summands.map (abstractSubterm pattern u)

/-- The difference of the normalized abstracted summands and the abstracted stated value, run
through the side-conditioned pipeline over the abstraction variable. -/
def abstractedDifference {ι : Type*} [DecidableEq ι] (summands : List (Verified.Expr ι))
    (stated pattern : Verified.Expr ι) (u : ι) : Alg.NormResult ι :=
  (sideConditionPipeline (ι := ι)).run
    (.sub (normalizeSummands (abstractedSummands summands pattern u)).expr
      (abstractSubterm pattern u stated))

/-- The normal form of the abstracted difference with the pattern restored: the plain pipeline
first, so that a difference that is zero once the relation `u = pattern` is visible records no
condition, then the side-conditioned pipeline. -/
def restoredDifference {ι : Type*} [DecidableEq ι] (summands : List (Verified.Expr ι))
    (stated pattern : Verified.Expr ι) (u : ι) : Alg.NormResult ι :=
  (sideConditionPipeline (ι := ι)).run
    ((simplifyPipeline (ι := ι)).runFixed
      (restoreSubterm pattern u (abstractedDifference summands stated pattern u).expr))

/-- The certification data for a sum against a stated value with a shared radicand abstracted:
the recorded conditions of the abstracted summands, of the abstracted difference, and of the
restored difference, with the normal form of the restored difference. -/
def abstractedSummandRun {ι : Type*} [DecidableEq ι] (summands : List (Verified.Expr ι))
    (stated pattern : Verified.Expr ι) (u : ι) : Alg.NormResult ι :=
  { expr := (restoredDifference summands stated pattern u).expr
    nonzero := Alg.cleanSide
      ((normalizeSummands (abstractedSummands summands pattern u)).nonzero ++
        (abstractedDifference summands stated pattern u).nonzero ++
          (restoredDifference summands stated pattern u).nonzero) }

/-- The certification statement for a sum with a shared radicand abstracted: wherever the
environment sends the abstraction variable to the value of the pattern and the essential side
list holds, a run with the normal form `0` shows that the sum evaluates to the stated value. -/
theorem eval_eq_of_abstractedSummandRun_essential {ι : Type*} [DecidableEq ι]
    (summands : List (Verified.Expr ι)) (stated pattern : Verified.Expr ι) (u : ι)
    (ρ : ι → ℝ) (side : List (Verified.Expr ι))
    (hrun : (abstractedSummandRun summands stated pattern u).expr = .nat 0 ∧
      essentialSide (abstractedSummandRun summands stated pattern u).nonzero = side)
    (hu : ρ u = pattern.eval ρ) (hside : Alg.SideHolds ρ side) :
    (Verified.Expr.addList summands).eval ρ = stated.eval ρ := by
  simp only [abstractedSummandRun] at hrun
  have hthree : Alg.SideHolds ρ
      ((normalizeSummands (abstractedSummands summands pattern u)).nonzero ++
        (abstractedDifference summands stated pattern u).nonzero ++
          (restoredDifference summands stated pattern u).nonzero) :=
    Alg.sideHolds_of_cleanSide (sideHolds_of_essentialSide (by rwa [hrun.2]))
  have hzero : ((sideConditionPipeline (ι := ι)).run _).expr = .nat 0 := hrun.1
  have hfinal := SidePipeline.eval_run (sideConditionPipeline (ι := ι)) ρ _ hthree.append_right
  have hsplit : (abstractedDifference summands stated pattern u).expr.eval ρ =
      (normalizeSummands (abstractedSummands summands pattern u)).expr.eval ρ -
        (abstractSubterm pattern u stated).eval ρ :=
    SidePipeline.eval_run (sideConditionPipeline (ι := ι)) ρ _ hthree.append_left.append_right
  rw [hzero, eval_simplifyPipeline_runFixed, eval_restoreSubterm ρ pattern u hu, hsplit,
    eval_normalizeSummands ρ _ hthree.append_left.append_left] at hfinal
  simp only [abstractedSummands, Verified.Expr.eval_addList, List.map_map, Function.comp_def,
    eval_abstractSubterm ρ pattern u hu, Verified.Expr.eval, Nat.cast_zero] at hfinal ⊢
  exact (sub_eq_zero.mp hfinal.symm)

/-- The run of a side-conditioned pipeline on `expr` as a checked route, recording every generated
side condition. -/
def SidePipeline.claimRoute {ι : Type*} [DecidableEq ι] (pipeline : SidePipeline ι)
    (expr : Verified.Expr ι) : SideClaimRoute ι :=
  let out := pipeline.run expr
  { lhs := expr
    rhs := out.expr
    nonzero := out.nonzero
    steps := pipeline.passInfo
    sound := fun ρ hside ↦ SidePipeline.eval_run pipeline ρ expr hside }

/--
A side-conditioned pipeline run on a finite-coordinate expression, followed by an exact canonical
form. With one coordinate this is the univariate rational canonicalizer, which also writes an
improper fraction in mixed form for interval evaluation. With two or more coordinates it is the
multivariate canonical form `Alg.canonical`, which cancels the polynomial gcd of numerator and
denominator over the atoms of the expression.
-/
def SidePipeline.finClaimRoute :
    {n : Nat} → SidePipeline (Fin n) → Verified.Expr (Fin n) → SideClaimRoute (Fin n)
  | 0, pipeline, expr => pipeline.claimRoute expr
  | 1, pipeline, expr =>
      let structural := pipeline.claimRoute expr
      let rational := RationalCanonical.route structural.rhs
      structural.trans rational (RationalCanonical.route_lhs structural.rhs)
  | _ + 2, pipeline, expr =>
      let structural := pipeline.claimRoute expr
      structural.trans (Alg.canonical structural.rhs) (Alg.canonical_lhs structural.rhs)

/-- A checked simplification route that records every generated side condition. -/
def simplifySideClaimRoute {ι : Type*} [DecidableEq ι] (expr : Verified.Expr ι) :
    SideClaimRoute ι :=
  (sideConditionPipeline (ι := ι)).claimRoute expr

/-- Checked simplification for finite-coordinate calculator expressions: `sideConditionPipeline`
followed by the exact canonical form of `SidePipeline.finClaimRoute`. -/
def simplifyFinSideClaimRoute {n : Nat} (expr : Verified.Expr (Fin n)) :
    SideClaimRoute (Fin n) :=
  (sideConditionPipeline (ι := Fin n)).finClaimRoute expr

/-- The number of nodes of an expression tree, the size by which display routes compare
candidate results. -/
def nodeCount {ι : Type*} : Verified.Expr ι → Nat
  | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ => 1
  | .add a b | .mul a b | .sub a b | .div a b | .rpow a b => nodeCount a + nodeCount b + 1
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a
  | .sqrt a => nodeCount a + 1

/--
Checked simplification for a displayed result. Zero tests and `cas_nf` use
`simplifyFinSideClaimRoute`, whose Pythagorean pass rewrites `cos u ^ 2` as `1 - sin u ^ 2` so
that `sin u ^ 2 + cos u ^ 2` cancels. A displayed result keeps its cosines instead: this route
runs the pipeline without that pass, and when the pass would still rewrite the result it also
runs `simplifyFinSideClaimRoute` and keeps the elimination only if it has fewer nodes.
-/
def simplifyFinDisplayRoute {n : Nat} (expr : Verified.Expr (Fin n)) :
    SideClaimRoute (Fin n) :=
  let kept :=
    (configuredSidePipeline (simplifyPipeline (ι := Fin n)) (pythagorean := false)).finClaimRoute
      expr
  if pythagoreanRewrite kept.rhs = kept.rhs then
    kept
  else
    let eliminated := simplifyFinSideClaimRoute expr
    if nodeCount eliminated.rhs < nodeCount kept.rhs then eliminated else kept

/-- A pipeline run starts at its input. -/
@[simp] theorem SidePipeline.claimRoute_lhs {ι : Type*} [DecidableEq ι] (pipeline : SidePipeline ι)
    (expr : Verified.Expr ι) : (pipeline.claimRoute expr).lhs = expr :=
  rfl

/-- A finite-coordinate pipeline run starts at its input, whichever canonical form follows. -/
@[simp] theorem SidePipeline.finClaimRoute_lhs :
    {n : Nat} → (pipeline : SidePipeline (Fin n)) → (expr : Verified.Expr (Fin n)) →
      (pipeline.finClaimRoute expr).lhs = expr
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | _ + 2, _, _ => rfl

/-- The checked simplification route starts at its input. -/
@[simp] theorem simplifySideClaimRoute_lhs {ι : Type*} [DecidableEq ι] (expr : Verified.Expr ι) :
    (simplifySideClaimRoute expr).lhs = expr :=
  rfl

private theorem lhs_ite {ι : Type*} {p : Prop} [Decidable p] {a b : SideClaimRoute ι}
    {expr : Verified.Expr ι} (ha : a.lhs = expr) (hb : b.lhs = expr) :
    (if p then a else b).lhs = expr := by
  by_cases h : p
  · rw [ite_eq_left h]
    exact ha
  · rw [ite_eq_right h]
    exact hb

/-- The route of a displayed simplification starts at its input, whether or not it keeps the
Pythagorean elimination. -/
@[simp] theorem simplifyFinDisplayRoute_lhs {n : Nat} (expr : Verified.Expr (Fin n)) :
    (simplifyFinDisplayRoute expr).lhs = expr :=
  lhs_ite (SidePipeline.finClaimRoute_lhs _ _)
    (lhs_ite (SidePipeline.finClaimRoute_lhs _ _) (SidePipeline.finClaimRoute_lhs _ _))

end CAS.Verified.Expr

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.Residual
public import CAS.Continuum.IntervalEval.Normalization
public import CAS.Continuum.IntervalEval.Soundness
public import CAS.Continuum.IntervalEval.WellFormed
public import CAS.Route.Core

/-!
# Certified interval-evaluation contexts

A certified context bundles a rational interval environment with proofs for its
variables, denominators, and branch-sensitive unary operations. Successful
evaluation is exposed through typed attempts whose certificates refer to the
displayed intervals and original functions. Route steps are diagnostic metadata.

## Main definitions

* `CertifiedEvalContext`: an interval environment with its variable enclosure
  proof, a denominator provider, and a unary range provider tied to it.
* `CertifiedEvalContext.eval`, `evalSimplified`, `evalNormalized`: the bundled
  evaluator, the simplify-first variant, and the side-condition-aware exact
  normalization variant (which can certify cancellations such as `x / x = 1`
  when the context proves `x ≠ 0`).
* `EnclosureAttempt`, `ResidualBoundAttempt`, `ZeroResidualAttempt`: the
  certificate-carrying result types, and the constructors
  `enclosureAttemptSimplified?` and `enclosureAttemptNormalized?` that produce
  enclosure attempts.

## Main results

* `CertifiedEvalContext.sound`, `sound_simplified`, `sound_normalized`: each
  successful evaluation encloses `expr.eval (ρ x)` at every chart point.
* `CertifiedEvalContext.eval_ne_zero_of_certifiesNonzero`: a successful nonzero
  check proves the expression nonzero on the whole chart.

## Implementation notes

Computable previews are kept separate from the attempts. A preview may guide search, but only a
certificate-producing operation supports a mathematical conclusion: an `EnclosureAttempt` stores
its interval with `EnclosedOn fn s lo hi` for the function named in its type, and all three
evaluators rest on `evalWithLookups_sound`. Simplifying before evaluation removes cancellations
such as `x - x`, whose interval evaluation is `[lo - hi, hi - lo]` rather than `0`; it is an
unconditional equality of semantics. The normalization `intervalNormalizeWithSide` may also
cancel a common factor, and `evalNormalized` uses its result only after `certifiesSideConditions`
proves every emitted `e ≠ 0` on the chart, by a registered lower bound on `|e|` or by an interval
of `e` that excludes zero.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Certificate
open CAS.Verified

/-! ## Certified evaluation plans and successful attempts -/

/-
The attempt records of this section are structures whose mathematical content is stated
directly for the indexed function and displayed interval, so function and
endpoint coherence hold by construction. Route steps only record how the
attempt was found.
-/

/-- A bundled CEGA plan for certified interval evaluation on one chart.

The registry planner synthesizes this certified evaluation context. It carries:

* a variable interval environment;
* a theorem that every point of the chart satisfies that environment;
* a denominator provider for division side conditions;
* a unary-operation provider for branch-sensitive functions such as `sqrt` and `log`.

Its evaluator and soundness methods bundle these providers into one
certificate-producing API, with `evalWithLookups_sound` as the underlying soundness theorem.
-/
structure CertifiedEvalContext {α : Type*} {ι : Type*} (s : Set α) (ρ : α → ι → ℝ) where
  /-- Rational interval environment for the chart variables. -/
  env : ι → RationalInterval
  /-- Every chart point satisfies the variable interval environment. -/
  hvars : ∀ x, x ∈ s → ∀ i, (env i).MemReal (ρ x i)
  /-- Certified denominator lower-bound provider. -/
  divProvider : ExprAbsLowerProvider s ρ
  /-- Certified unary range provider tied to this exact evaluator. -/
  unaryProvider : UnaryRangeProvider env divProvider.lookup

/-- A successful enclosure attempt for `fn`, with its checked interval and construction steps. -/
structure EnclosureAttempt (α : Type*) (s : Set α) (fn : α → ℝ) where
  /-- The interval computed by the evaluator. -/
  interval : RationalInterval
  /-- The displayed interval encloses the function named by the attempt type. -/
  sound : EnclosedOn fn s (interval.lo : ℝ) (interval.hi : ℝ)
  /-- Route steps used to assemble the plan. -/
  steps : List RouteStep := []

/--
A successful exact-zero residual attempt.

The trusted payload is a routed residual certificate whose error is exactly
zero, so no interval or endpoint equations are stored.
-/
abbrev ZeroResidualAttempt (α : Type*) (s : Set α) :=
  CertificateRoute { cert : ResidualCert α ℝ s // cert.eps = 0 }

namespace ZeroResidualAttempt

/-- The checked residual certificate carried by an exact-zero attempt. -/
def toResidualCert {α : Type*} {s : Set α}
    (a : ZeroResidualAttempt α s) : ResidualCert α ℝ s :=
  a.cert.1

end ZeroResidualAttempt

/--
A successful residual-bound attempt.

The residual function and its semantic bound are stored directly.  The
`ResidualCert` used by CEGA is derived in `Attempt.lean`, so the error budget
is `interval.absMax` by definition rather than by a separate equation.
-/
structure ResidualBoundAttempt (α : Type*) (s : Set α) where
  /-- The interval computed by the evaluator. -/
  interval : RationalInterval
  /-- The residual function checked by the evaluator. -/
  residual : α → ℝ
  /-- The interval's absolute endpoint maximum bounds the residual. -/
  sound : ResidualBound residual s (interval.absMax : ℝ)
  /-- Route steps used to assemble the plan. -/
  steps : List RouteStep := []

/-! ## Route-plan previews and certified attempts -/

namespace CertifiedEvalContext

variable {α : Type*} {ι : Type*} {s : Set α} {ρ : α → ι → ℝ}

/-- Build a certified evaluation plan from finite planner-output entries.

The denominator entries are compiled first.  Unary entries are then tied to the
exact denominator lookup used by the evaluator, which keeps recursive soundness
obligations aligned with the plan that will actually run.
-/
def fromRouteEntries [DecidableEq ι]
    (env : ι → RationalInterval)
    (hvars : ∀ x, x ∈ s → ∀ i, (env i).MemReal (ρ x i))
    (divEntries : List (ExprAbsLowerRouteEntry s ρ))
    (unaryEntries :
      List (UnaryRangeRouteEntry env
        (ExprAbsLowerProvider.fromRouteEntries divEntries).lookup)) :
    CertifiedEvalContext s ρ where
  env := env
  hvars := hvars
  divProvider := ExprAbsLowerProvider.fromRouteEntries divEntries
  unaryProvider := UnaryRangeProvider.fromRouteEntries unaryEntries

/-- Collect the route steps used to assemble a finite planner-output plan. -/
def routeEntrySteps [DecidableEq ι]
    (env : ι → RationalInterval)
    (divEntries : List (ExprAbsLowerRouteEntry s ρ))
    (unaryEntries :
      List (UnaryRangeRouteEntry env
        (ExprAbsLowerProvider.fromRouteEntries divEntries).lookup)) :
    List RouteStep :=
  ExprAbsLowerProvider.routeEntrySteps divEntries ++
    UnaryRangeProvider.routeEntrySteps unaryEntries

/-- Run the certified interval evaluator using all providers in the plan. -/
def eval (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι) : Option RationalInterval :=
  evalWithLookups p.env p.divProvider.lookup p.unaryProvider.lookup expr

/-- Check intrinsic syntax, simplify, then run the certified interval evaluator.

This is the dependency-aware planner entry point: exact symbolic rewriting gets
the first chance to remove cancellations such as `x - x`, and only the simplified
expression is sent to interval evaluation. The well-formedness check happens
first, so simplification cannot erase a malformed rational literal.
-/
def evalSimplified [DecidableEq ι]
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι) : Option RationalInterval :=
  if expr.isWellFormed then
    p.eval (Verified.Expr.simplify expr)
  else
    none

/--
Check one nonzero obligation using all evidence already in the context.

A registered absolute lower bound is preferred. If no such entry exists, the
ordinary interval evaluator may still prove nonvanishing by placing the whole
range strictly to one side of zero.
-/
def certifiesNonzero
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι) : Bool :=
  match p.divProvider.lookup expr with
  | some _ => true
  | none =>
      match p.eval expr with
      | some I => decide (I.hi < 0 ∨ 0 < I.lo)
      | none => false

/-- Check every nonzero obligation, allowing a different evidence source for
each expression. -/
def certifiesSideConditions
    (p : CertifiedEvalContext s ρ) (side : List (Verified.Expr ι)) : Bool :=
  side.all p.certifiesNonzero

/-- Run the checked side-aware simplification pipeline only after proving every emitted
side condition, then evaluate the transformed expression.

This is stronger than `evalSimplified`: it can certify cancellations such as
`x / x = 1` on a chart where the registry proves `x ≠ 0`. Intrinsically
malformed expressions and unproved side conditions are rejected.
-/
def evalNormalized [DecidableEq ι]
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι) :
    Option RationalInterval :=
  if expr.isWellFormed then
    let result := intervalNormalizeWithSide expr
    if p.certifiesSideConditions result.nonzero then
      p.eval result.expr
    else
      none
  else
    none

/-- Soundness of the bundled evaluator at a concrete chart point. -/
theorem sound (p : CertifiedEvalContext s ρ) (x : α) (hx : x ∈ s)
    (expr : Verified.Expr ι) (I : RationalInterval)
    (hEval : p.eval expr = some I) :
    I.MemReal (expr.eval (ρ x)) :=
  evalWithLookups_sound p.env p.divProvider.lookup p.unaryProvider.lookup (ρ x) (p.hvars x hx)
    (p.divProvider.sound x hx) p.unaryProvider.sound expr I hEval

/-- A successful combined check proves one expression nonzero throughout the
context domain. -/
theorem eval_ne_zero_of_certifiesNonzero
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι)
    (hcheck : p.certifiesNonzero expr = true)
    (x : α) (hx : x ∈ s) : expr.eval (ρ x) ≠ 0 := by
  unfold certifiesNonzero at hcheck
  cases hlookup : p.divProvider.lookup expr with
  | some cert =>
      exact abs_pos.mp
        ((Rat.cast_pos.mpr cert.pos).trans_le (p.divProvider.sound x hx expr cert hlookup))
  | none =>
      cases hEval : p.eval expr with
      | none => simp [hlookup, hEval] at hcheck
      | some I =>
          have hmem := p.sound x hx expr I hEval
          have houtside : I.hi < 0 ∨ 0 < I.lo := by simpa [hlookup, hEval] using hcheck
          rcases houtside with hneg | hpos
          · exact (hmem.2.trans_lt (Rat.cast_lt_zero.mpr hneg)).ne
          · exact ((Rat.cast_pos.mpr hpos).trans_le hmem.1).ne'

/-- A successful combined check discharges every exact-normalization side
condition throughout the context domain. -/
theorem sideHolds_of_certifiesSideConditions
    (p : CertifiedEvalContext s ρ) (side : List (Verified.Expr ι))
    (hcheck : p.certifiesSideConditions side = true)
    (x : α) (hx : x ∈ s) :
    Verified.Expr.Alg.SideHolds (ρ x) side := fun expr hexpr ↦
  p.eval_ne_zero_of_certifiesNonzero expr (List.all_eq_true.mp hcheck expr hexpr) x hx

/-- Soundness of the simplify-then-evaluate path at a concrete chart point. -/
theorem sound_simplified [DecidableEq ι]
    (p : CertifiedEvalContext s ρ) (x : α) (hx : x ∈ s)
    (expr : Verified.Expr ι) (I : RationalInterval)
    (hEval : p.evalSimplified expr = some I) :
    I.MemReal (expr.eval (ρ x)) := by
  unfold evalSimplified at hEval
  split_ifs at hEval
  simpa using p.sound x hx _ I hEval

/-- Soundness of checked side-condition-aware normalization followed by
interval evaluation. -/
theorem sound_normalized [DecidableEq ι]
    (p : CertifiedEvalContext s ρ) (x : α) (hx : x ∈ s)
    (expr : Verified.Expr ι) (I : RationalInterval)
    (hEval : p.evalNormalized expr = some I) :
    I.MemReal (expr.eval (ρ x)) := by
  unfold evalNormalized at hEval
  dsimp only at hEval
  split_ifs at hEval with hwf hcovered
  exact eval_intervalNormalizeWithSide (ρ x) expr
    (p.sideHolds_of_certifiesSideConditions _ hcovered x hx) ▸ p.sound x hx _ I hEval

/-- Bundled certified interval evaluation gives a CEGA two-sided enclosure. -/
theorem enclosedOn (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι) (I : RationalInterval)
    (hEval : p.eval expr = some I) :
    EnclosedOn (fun x ↦ expr.eval (ρ x)) s (I.lo : ℝ) (I.hi : ℝ) :=
  RealIntervalBackend.enclosedOn_of_memReal (I := I) fun x hx ↦ p.sound x hx expr I hEval

/-- Simplify-then-evaluate gives a CEGA two-sided enclosure for the original expression. -/
theorem enclosedOn_simplified [DecidableEq ι]
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι) (I : RationalInterval)
    (hEval : p.evalSimplified expr = some I) :
    EnclosedOn (fun x ↦ expr.eval (ρ x)) s (I.lo : ℝ) (I.hi : ℝ) :=
  RealIntervalBackend.enclosedOn_of_memReal (I := I) fun x hx ↦ p.sound_simplified x hx expr I hEval

/-- Simplify and enclose an expression while certifying the original expression. -/
noncomputable def enclosureAttemptSimplified? [DecidableEq ι]
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι)
    (steps : List RouteStep := []) :
    Option (EnclosureAttempt α s (fun x ↦ expr.eval (ρ x))) :=
  match hEval : p.evalSimplified expr with
  | some I =>
      some
        { interval := I
          sound := p.enclosedOn_simplified expr I hEval
          steps := steps }
  | none => none

/-- Normalize with checked side conditions and enclose the original
expression. -/
noncomputable def enclosureAttemptNormalized? [DecidableEq ι]
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι)
    (steps : List RouteStep := []) :
    Option (EnclosureAttempt α s (fun x ↦ expr.eval (ρ x))) :=
  match hEval : p.evalNormalized expr with
  | some I =>
      some
        { interval := I
          sound :=
            RealIntervalBackend.enclosedOn_of_memReal (I := I)
              (fun x hx ↦ p.sound_normalized x hx expr I hEval)
          steps := .exactNormalization :: steps }
  | none => none

end CertifiedEvalContext

end RationalInterval
end CAS.Continuum

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.CEGA.Syntax
public meta import CAS.CEGA.Syntax
public meta import CAS.Tactic.ProofCarrier
public import CAS.Tactic.RealExpression
public meta import CAS.Tactic.RealExpression

/-!
# Ordinary inequalities on rational boxes

A working formalizer states a bound as an ordinary inequality, `x * (1 - x) ≤ 1 / 4` under
`h0 : 0 ≤ x` and `h1 : x ≤ 1`, not as the certificate proposition
`BoundOn (fun p : ℝ^1 ↦ p 0 * (1 - p 0)) {p | 0 ≤ p 0 ∧ p 0 ≤ 1} (1 / 4)` that the CEGA box
queries certify. The box route of `cega` and `cas` connects the two: it reads an ordinary
inequality whose real variables are bounded by rational literal hypotheses, runs the checked box
query (`CAS.CEGA.Elaboration.runBoxQuery`) on the reflected expression and the box the
hypotheses describe, and transports the certificate back to the stated inequality through the
soundness lemmas of the first section.

Recognized goals are `f x ≤ c`, `f x < c`, `c ≤ f x`, `c < f x`, `|f x| ≤ c`, `|f x| < c`,
`a ≤ f x ∧ f x ≤ b`, `f x ∈ Set.Icc a b`, and `f x ≤ g x` or `f x < g x` with both sides
depending on the variables (proved through `f x - g x ≤ 0`), where `c`, `a`, `b` are closed
terms and every opaque real term `x` of the expression is bounded by hypotheses `a ≤ x` and
`x ≤ b` (also `a < x`, `x < b`, `x ∈ Set.Icc a b`, `Set.Ico`, `Set.Ioc`, `Set.Ioo`, and the
`≥`/`>` spellings) whose endpoints are rational literals. A box has at most `cega.maxDimension`
coordinates (8 by default), and a closed expression uses the box with none. Applied terms such
as `f x` can be coordinates when hypotheses bound those exact terms. An unsupported closed
subterm or a coordinate without rational bounds makes the route refuse, naming the subterm.

A goal with variables may also be a conjunction of these relations, with strict two-sided bounds
`a < f x ∧ f x < b` and the memberships `f x ∈ Set.Ioo a b`, `Set.Ico` and `Set.Ioc` read as the
conjunctions they unfold to. Two or more relations on the same expression that state their bounds
with closed numerals share one box query, and their bounds are checked together in one kernel
check (`checkStatedBounds`), except in native `cega [fast]`. Every other relation, and every
relation of a group whose check fails, is proved on its own. A certificate goal `EnclosedOn`,
`BoundOn`, `ApproxOn` or `ResidualBound` whose domain is a coordinate box becomes such an
ordinary goal through `prepareCertificateGoal`.

Bounds may also be grouped in nested conjunctions, such as `0 ≤ x ∧ x ≤ 1`. Their proofs
are projected from the hypotheses, and the sharpest endpoints are retained across all conjuncts.
An absolute upper bound `|x| ≤ r` or `|x| < r` supplies the closed interval `[-r, r]`,
with both endpoint proofs obtained from Mathlib's absolute-value inequalities.

Strict hypotheses contribute non-strict bounds to the closed query box. Thus `0 < x` and
`x ≤ 1` give `[0, 1]`, which does not keep a reciprocal denominator away from zero.
Likewise, `x < 1` does not turn a certified upper endpoint of `1` into a strict upper bound.
Strict goals require a strict comparison with the certified endpoint; stronger precision or
subdivision need not supply that gap. The query certifies total expression values and does
not establish the `ValidAt` hypotheses used by differentiation.

## Main definitions

* `recognize?`: the shape (`Shape`) of a recognized relation and the real term its query encloses.
* `variableBoundSides`, `variableBounds?`: the sharpest rational bounds that the hypotheses give
  a real term, with their proofs.
* `reflectOverBoundedVariables`: a real term as a `Verified.Expr (Fin n)` over its bounded
  coordinates.
* `closeMainGoal`: the box route on one relation or on a conjunction of relations.
* `closeWithExplicitQuery`, `closeWithStatedQuery`: an ordinary goal closed by an explicit
  `cega [enclose x in [a, b]] e` query.
* `prepareCertificateGoal`: a certificate goal on a coordinate box unfolded to an ordinary goal.
* `bareSyntax`, `querySyntax`: the calls that replay a proof.

## Main results

* `toLp_mem_boxDomain`: a coordinate vector whose entries lie in the intervals of a box is a
  point of the box.
* `le_of_boundOn_box`, `lt_of_boundOn_box`, `le_of_enclosedOn_box_lower`,
  `lt_of_enclosedOn_box_lower`, `mem_of_enclosedOn_box`, `mem_Icc_of_enclosedOn_box`,
  `abs_le_of_boundOn_abs_box`, `abs_lt_of_boundOn_abs_box`, `abs_sub_le_of_approxOn_box`: a
  certificate on `boxDomain box` gives the ordinary bound of a term at a coordinate vector in the
  box, when the reflected expression evaluates to the term there and the certified endpoint
  compares with the stated one.
* `le_of_boundOn_box_sub`, `lt_of_boundOn_box_sub`: `f ≤ g` or `f < g` from an upper bound of
  the difference that is at most `0`, or below `0`.
* `lt_of_forall_lt_box`, `lt_of_forall_lt_box_sub`, `le_of_forall_le_box_lower`,
  `lt_of_forall_lt_box_lower`, `abs_lt_of_forall_lt_box`: the same transports from the strict
  and lower bounds at every point of the box that the stated-bound route checks.

## Implementation notes

The box route computes no enclosure itself. `CAS/CEGA/Elaboration.lean` quotes the query,
enforces its admission budgets and has the kernel evaluate it, and the planner that the kernel
runs, with its monotonicity faces, centered forms and checked bisection, lives in
`CAS/CEGA/Query.lean`, which cites the classical interval methods. Bare `cega`, except native
`cega [fast]`, follows a query that falls short with the subdivided query of the same mode, to
the depth of the precision policy (two by default); `cas` runs the first query only. What we add
is the reading of goals and hypotheses and the transport of the checked theorem, through
elementary order lemmas, to the inequality as it is stated.

The transport is proof-producing at every step: the box membership of the variables is proved
from the hypotheses (`norm_num` on each endpoint, then `fin_cases`), the evaluation of the
reflected expression is identified with the stated term by `rfl` or by unfolding
`Verified.Expr.eval` with the lowerings of `tan`, the hyperbolic functions and `abs`, and the
certified rational bound is compared with the stated bound by `norm_num`. When the stated
endpoint is a closed nonrational expression, its comparison is proved by enclosing the difference
on the zero-dimensional box, using the same evaluator and precision policy (`proveComparison`).
Nothing is trusted from syntax comparison; when any step fails the goal is left untouched and the
message names the shape or the hypothesis the route wanted. The same transport serves the
explicit `cega [enclose x in [a, b]] expr` query on an ordinary goal, where the box and the
expression come from the user and the hypotheses must imply the stated box.

When the stated constants are closed numeral expressions, as in `x * (1 - x) ≤ 1 / 4`, the
route checks the stated bound itself, in one kernel check of the query
(`CAS.CEGA.Elaboration.checkStatedBounds`), and transports that theorem in the same way, then,
when the kernel rejects it and the route would subdivide, the subdivided query. When the kernel
rejects these checks, the route refuses without a search: one kernel evaluation reads the values
the query certifies (`CAS.CEGA.Elaboration.readQueryDisplay?`), and the refusal compares them
with the stated bound. A closed bound that is not a numeral expression is checked once through
the difference `f x - c`, and its replay is bare `cega`; when that check fails, and when the
stated route does not apply, for example because a kernel route finds the query memoized, the
search runs, with its diagnostics.

We keep the soundness lemmas next to the tactic rather than in `CAS.Certificate` because they
mention the checked evaluator and the rational box, which the certificate vocabulary does not.
-/

@[expose] public section

namespace CAS.Tactic.BoxInequality

open CAS.Certificate
open CAS.Continuum
open CAS.Continuum.RationalInterval
open CAS.CEGA
open CAS.Exact

/-- A coordinate vector whose entries lie in the intervals of a box is a point of the box. -/
theorem toLp_mem_boxDomain {n : ℕ} (box : Fin n → RationalInterval) (ρ : Fin n → ℝ)
    (h : ∀ i, (box i).MemReal (ρ i)) :
    (WithLp.toLp 2 ρ : ℝ^n) ∈ boxDomain box :=
  h

/-- An upper bound certified on the box transports to an ordinary inequality: the variables lie
in the box, the evaluation of the reflected expression is the stated term, and the certified
bound is at most the stated one. -/
theorem le_of_boundOn_box {n : ℕ} {expr : Verified.Expr (Fin n)} {box : Fin n → RationalInterval}
    {bound c v : ℝ}
    (h : BoundOn (exprFn expr) (boxDomain box) bound) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).MemReal (ρ i)) (hv : expr.eval ρ = v) (hc : bound ≤ c) : v ≤ c :=
  hv ▸ (h (WithLp.toLp 2 ρ) (toLp_mem_boxDomain box ρ hρ)).trans hc

/-- Strict form of `le_of_boundOn_box`: a certified bound strictly below the stated one. -/
theorem lt_of_boundOn_box {n : ℕ} {expr : Verified.Expr (Fin n)} {box : Fin n → RationalInterval}
    {bound c v : ℝ}
    (h : BoundOn (exprFn expr) (boxDomain box) bound) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).MemReal (ρ i)) (hv : expr.eval ρ = v) (hc : bound < c) : v < c :=
  hv ▸ (h (WithLp.toLp 2 ρ) (toLp_mem_boxDomain box ρ hρ)).trans_lt hc

/-- A comparison `f ≤ g` of two variable-dependent terms is proved from a certified upper
bound of the difference by a nonpositive number. -/
theorem le_of_boundOn_box_sub {n : ℕ} {expr : Verified.Expr (Fin n)}
    {box : Fin n → RationalInterval} {bound f g : ℝ}
    (h : BoundOn (exprFn expr) (boxDomain box) bound) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).MemReal (ρ i)) (hv : expr.eval ρ = f - g) (hc : bound ≤ 0) : f ≤ g :=
  sub_nonpos.mp (le_of_boundOn_box h ρ hρ hv hc)

/-- Strict form of `le_of_boundOn_box_sub`. -/
theorem lt_of_boundOn_box_sub {n : ℕ} {expr : Verified.Expr (Fin n)}
    {box : Fin n → RationalInterval} {bound f g : ℝ}
    (h : BoundOn (exprFn expr) (boxDomain box) bound) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).MemReal (ρ i)) (hv : expr.eval ρ = f - g) (hc : bound < 0) : f < g :=
  sub_neg.mp (lt_of_boundOn_box h ρ hρ hv hc)

/-- The lower endpoint of a certified enclosure transports to an ordinary lower bound. -/
theorem le_of_enclosedOn_box_lower {n : ℕ} {expr : Verified.Expr (Fin n)}
    {box : Fin n → RationalInterval} {lo hi c v : ℝ}
    (h : EnclosedOn (exprFn expr) (boxDomain box) lo hi) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).MemReal (ρ i)) (hv : expr.eval ρ = v) (hc : c ≤ lo) : c ≤ v :=
  hv ▸ hc.trans (h (WithLp.toLp 2 ρ) (toLp_mem_boxDomain box ρ hρ)).1

/-- Strict form of `le_of_enclosedOn_box_lower`. -/
theorem lt_of_enclosedOn_box_lower {n : ℕ} {expr : Verified.Expr (Fin n)}
    {box : Fin n → RationalInterval} {lo hi c v : ℝ}
    (h : EnclosedOn (exprFn expr) (boxDomain box) lo hi) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).MemReal (ρ i)) (hv : expr.eval ρ = v) (hc : c < lo) : c < v :=
  hv ▸ hc.trans_le (h (WithLp.toLp 2 ρ) (toLp_mem_boxDomain box ρ hρ)).1

/-- A certified enclosure transports to a two-sided ordinary bound. -/
theorem mem_of_enclosedOn_box {n : ℕ} {expr : Verified.Expr (Fin n)}
    {box : Fin n → RationalInterval} {lo hi a b v : ℝ}
    (h : EnclosedOn (exprFn expr) (boxDomain box) lo hi) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).MemReal (ρ i)) (hv : expr.eval ρ = v) (ha : a ≤ lo) (hb : hi ≤ b) :
    a ≤ v ∧ v ≤ b := by
  have hx := h (WithLp.toLp 2 ρ) (toLp_mem_boxDomain box ρ hρ)
  exact hv ▸ ⟨ha.trans hx.1, hx.2.trans hb⟩

/-- `mem_of_enclosedOn_box` stated as membership in a closed interval. -/
theorem mem_Icc_of_enclosedOn_box {n : ℕ} {expr : Verified.Expr (Fin n)}
    {box : Fin n → RationalInterval} {lo hi a b v : ℝ}
    (h : EnclosedOn (exprFn expr) (boxDomain box) lo hi) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).MemReal (ρ i)) (hv : expr.eval ρ = v) (ha : a ≤ lo) (hb : hi ≤ b) :
    v ∈ Set.Icc a b :=
  Set.mem_Icc.mpr (mem_of_enclosedOn_box h ρ hρ hv ha hb)

/-- A certified absolute bound transports to an ordinary bound on the absolute value. -/
theorem abs_le_of_boundOn_abs_box {n : ℕ} {expr : Verified.Expr (Fin n)}
    {box : Fin n → RationalInterval} {bound c v : ℝ}
    (h : BoundOn (fun p ↦ |exprFn expr p|) (boxDomain box) bound) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).MemReal (ρ i)) (hv : expr.eval ρ = v) (hc : bound ≤ c) : |v| ≤ c :=
  hv ▸ (h (WithLp.toLp 2 ρ) (toLp_mem_boxDomain box ρ hρ)).trans hc

/-- Strict form of `abs_le_of_boundOn_abs_box`. -/
theorem abs_lt_of_boundOn_abs_box {n : ℕ} {expr : Verified.Expr (Fin n)}
    {box : Fin n → RationalInterval} {bound c v : ℝ}
    (h : BoundOn (fun p ↦ |exprFn expr p|) (boxDomain box) bound) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).MemReal (ρ i)) (hv : expr.eval ρ = v) (hc : bound < c) : |v| < c :=
  hv ▸ (h (WithLp.toLp 2 ρ) (toLp_mem_boxDomain box ρ hρ)).trans_lt hc

/-- A certified approximation by a constant transports to an ordinary bound on the distance from
a stated center, when the stated interval `[c - r, c + r]` contains the certified interval
`[center - radius, center + radius]`. -/
theorem abs_sub_le_of_approxOn_box {n : ℕ} {expr : Verified.Expr (Fin n)}
    {box : Fin n → RationalInterval} {center radius c r v : ℝ}
    (h : ApproxOn (exprFn expr) (fun _ ↦ center) (boxDomain box) radius) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).MemReal (ρ i)) (hv : expr.eval ρ = v)
    (hlower : c - r ≤ center - radius) (hupper : center + radius ≤ c + r) : |v - c| ≤ r := by
  have hx : |expr.eval ρ - center| ≤ radius := h (WithLp.toLp 2 ρ) (toLp_mem_boxDomain box ρ hρ)
  rw [hv, abs_le] at hx
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

/-! The strict and lower bounds below are what the stated-bound route
(`CAS.CEGA.Elaboration.checkStatedBounds`) has the kernel check on the box; the non-strict upper,
absolute and two-sided bounds are certificate propositions and use the lemmas above. -/

/-- A strict upper bound on the box transports to a strict ordinary upper bound. -/
theorem lt_of_forall_lt_box {n : ℕ} {expr : Verified.Expr (Fin n)}
    {box : Fin n → RationalInterval} {bound c v : ℝ}
    (h : ∀ x ∈ boxDomain box, exprFn expr x < bound) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).MemReal (ρ i)) (hv : expr.eval ρ = v) (hc : bound ≤ c) : v < c :=
  hv ▸ (h (WithLp.toLp 2 ρ) (toLp_mem_boxDomain box ρ hρ)).trans_le hc

/-- A strict comparison `f < g` from a strict bound of the difference by a nonpositive number. -/
theorem lt_of_forall_lt_box_sub {n : ℕ} {expr : Verified.Expr (Fin n)}
    {box : Fin n → RationalInterval} {bound f g : ℝ}
    (h : ∀ x ∈ boxDomain box, exprFn expr x < bound) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).MemReal (ρ i)) (hv : expr.eval ρ = f - g) (hc : bound ≤ 0) : f < g :=
  sub_neg.mp (lt_of_forall_lt_box h ρ hρ hv hc)

/-- A lower bound on the box transports to an ordinary lower bound. -/
theorem le_of_forall_le_box_lower {n : ℕ} {expr : Verified.Expr (Fin n)}
    {box : Fin n → RationalInterval} {bound c v : ℝ}
    (h : ∀ x ∈ boxDomain box, bound ≤ exprFn expr x) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).MemReal (ρ i)) (hv : expr.eval ρ = v) (hc : c ≤ bound) : c ≤ v :=
  hv ▸ hc.trans (h (WithLp.toLp 2 ρ) (toLp_mem_boxDomain box ρ hρ))

/-- Strict form of `le_of_forall_le_box_lower`. -/
theorem lt_of_forall_lt_box_lower {n : ℕ} {expr : Verified.Expr (Fin n)}
    {box : Fin n → RationalInterval} {bound c v : ℝ}
    (h : ∀ x ∈ boxDomain box, bound < exprFn expr x) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).MemReal (ρ i)) (hv : expr.eval ρ = v) (hc : c ≤ bound) : c < v :=
  hv ▸ hc.trans_lt (h (WithLp.toLp 2 ρ) (toLp_mem_boxDomain box ρ hρ))

/-- A strict absolute bound on the box transports to a strict ordinary absolute bound. -/
theorem abs_lt_of_forall_lt_box {n : ℕ} {expr : Verified.Expr (Fin n)}
    {box : Fin n → RationalInterval} {bound c v : ℝ}
    (h : ∀ x ∈ boxDomain box, |exprFn expr x| < bound) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).MemReal (ρ i)) (hv : expr.eval ρ = v) (hc : bound ≤ c) : |v| < c :=
  hv ▸ (h (WithLp.toLp 2 ρ) (toLp_mem_boxDomain box ρ hρ)).trans_le hc

end CAS.Tactic.BoxInequality

end

public meta section

namespace CAS.Tactic.BoxInequality

open Lean Elab Tactic Meta
open CAS.CEGA.Elaboration
open CAS.Continuum

/-! ## Goal shapes -/

/-- The relation shapes the box route recognizes. -/
inductive Shape where
  /-- `v ≤ c` or, when `strict`, `v < c`, with `c` closed. -/
  | upper (strict : Bool)
  /-- `c ≤ v` or `c < v`, with `c` closed. -/
  | lower (strict : Bool)
  /-- `f ≤ g` or `f < g` with both sides depending on the variables. -/
  | difference (strict : Bool)
  /-- `|v| ≤ c` or `|v| < c`. -/
  | absUpper (strict : Bool)
  /-- `a ≤ v ∧ v ≤ b`, or `v ∈ Set.Icc a b` when `viaIcc`. -/
  | twoSided (viaIcc : Bool)
  deriving Repr, BEq

namespace Shape

/-- The query mode the route runs for a shape. -/
def mode : Shape → BoxQueryMode
  | .upper _ | .difference _ => .bound
  | .lower _ | .twoSided _ => .enclose
  | .absUpper _ => .absBound

/-- The user-facing description of a shape, for messages. -/
def describe : Shape → String
  | .upper false => "an upper bound `f x ≤ c`"
  | .upper true => "a strict upper bound `f x < c`"
  | .lower false => "a lower bound `c ≤ f x`"
  | .lower true => "a strict lower bound `c < f x`"
  | .difference false => "a comparison `f x ≤ g x` of two variable-dependent terms"
  | .difference true => "a strict comparison `f x < g x` of two variable-dependent terms"
  | .absUpper false => "an absolute bound `|f x| ≤ c`"
  | .absUpper true => "a strict absolute bound `|f x| < c`"
  | .twoSided false => "a two-sided bound `a ≤ f x ∧ f x ≤ b`"
  | .twoSided true => "an interval membership `f x ∈ Set.Icc a b`"

end Shape

/-- An ordinary inequality goal read as a box query. The stated constants are not recorded:
the soundness lemma recovers them by unification with the goal. -/
structure Recognized where
  /-- The relation shape. -/
  shape : Shape
  /-- The real term that is reflected and enclosed on the box: `f x`, `f x - g x` for a
  difference, or the argument of the absolute value. -/
  expression : Expr

/-- The relations that one box query proves, for the message of a refusal of an explicit
query. -/
def relationShapes : String :=
  "`f x ≤ c`, `f x < c`, `c ≤ f x`, `c < f x`, `|f x| ≤ c`, `|f x| < c`, \
   `a ≤ f x ∧ f x ≤ b`, `f x ∈ Set.Icc a b`, or `f x ≤ g x`, with `c`, `a`, `b` closed and \
   every real variable bounded by hypotheses `a ≤ x` and `x ≤ b`, `x ∈ Set.Icc a b`, or \
   `|x| ≤ r` with rational literal endpoints"

/-- The list of shapes, for the message of a refusal. -/
def supportedShapes : String :=
  "`f x ≤ c`, `f x < c`, `c ≤ f x`, `c < f x`, `|f x| ≤ c`, `|f x| < c`, \
   `a ≤ f x ∧ f x ≤ b` (also with `<`), `f x ∈ Set.Icc a b` (also `Set.Ioo`, `Set.Ico`, \
   `Set.Ioc`), `f x ≤ g x`, and conjunctions of these, with `c`, `a`, `b` closed and every \
   real variable bounded by hypotheses `a ≤ x` and `x ≤ b`, `x ∈ Set.Icc a b`, or `|x| ≤ r` \
   with rational literal endpoints"

/-- A readable name for the head of a proposition, for messages that name what was found. -/
def describeHead (target : Expr) : MetaM String := do
  let target := target.consumeMData
  match target with
  | .forallE _ _ _ _ =>
      return "a universally quantified statement or implication"
  | _ =>
      match target.getAppFn.consumeMData with
      | .const name _ =>
          return s!"the head symbol `{name}`"
      | _ =>
          return s!"the proposition{(← Meta.ppExpr target).pretty}"

private def isRealComparison (type : Expr) : MetaM Bool :=
  isDefEq type (mkConst ``Real)

/-- The argument of a real absolute value `|a|`. -/
private def absArgument? (term : Expr) : Option Expr :=
  let term := term.consumeMData
  if term.getAppFn.consumeMData.isConstOf ``abs ∧ !term.getAppArgs.isEmpty then
    some term.appArg!
  else
    none

/-- Read `lhs ≤ rhs` (or `<`) as a one-sided shape. -/
private def recognizeComparison (strict : Bool) (lhs rhs : Expr) : Option Recognized :=
  let lhs := lhs.consumeMData
  let rhs := rhs.consumeMData
  if rhs.hasFVar then
    if lhs.hasFVar then
      none
    else
      some { shape := .lower strict, expression := rhs }
  else
    match absArgument? lhs with
    | some argument => some { shape := .absUpper strict, expression := argument }
    | none => some { shape := .upper strict, expression := lhs }

/-- Read `lhs ≤ rhs` (or `<`) with both sides variable-dependent as a difference shape. -/
private def recognizeDifference (strict : Bool) (lhs rhs : Expr) : MetaM (Option Recognized) := do
  let lhs := lhs.consumeMData
  let rhs := rhs.consumeMData
  unless lhs.hasFVar ∧ rhs.hasFVar do
    return none
  let difference ← mkAppM ``HSub.hSub #[lhs, rhs]
  return some { shape := .difference strict, expression := difference }

/-- The set and element of a membership `v ∈ s`. -/
private def membership? (target : Expr) : Option (Expr × Expr) :=
  let target := target.consumeMData
  if target.isAppOfArity ``Membership.mem 5 then
    let arguments := target.getAppArgs
    some (arguments[3]!, arguments[4]!)
  else
    none

/-- The endpoints of a closed interval `Set.Icc a b`. -/
private def iccEndpoints? (set : Expr) : Option (Expr × Expr) :=
  let set := set.consumeMData
  if set.isAppOfArity ``Set.Icc 4 then
    let arguments := set.getAppArgs
    some (arguments[2]!, arguments[3]!)
  else
    none

/-- The strictness of the lower and upper endpoints of an interval `Set.Icc a b`, `Set.Ico a b`,
`Set.Ioc a b` or `Set.Ioo a b`. -/
private def intervalStrictness? (set : Expr) : Option (Bool × Bool) :=
  let set := set.consumeMData
  if set.isAppOfArity ``Set.Icc 4 then some (false, false)
  else if set.isAppOfArity ``Set.Ico 4 then some (false, true)
  else if set.isAppOfArity ``Set.Ioc 4 then some (true, false)
  else if set.isAppOfArity ``Set.Ioo 4 then some (true, true)
  else none

/--
Read an ordinary inequality goal as a box query, or return `none` when the outer shape is not
one of the recognized forms. This is shape reading only; nothing here is trusted.
-/
def recognize? (target : Expr) : MetaM (Option Recognized) := do
  let target := target.consumeMData
  if let some (type, lhs, rhs) := target.le? then
    unless ← isRealComparison type do return none
    match recognizeComparison false lhs rhs with
    | some recognized => return some recognized
    | none => recognizeDifference false lhs rhs
  else if let some (type, lhs, rhs) := target.lt? then
    unless ← isRealComparison type do return none
    match recognizeComparison true lhs rhs with
    | some recognized => return some recognized
    | none => recognizeDifference true lhs rhs
  else if target.isAppOfArity ``GE.ge 4 then
    let arguments := target.getAppArgs
    unless ← isRealComparison arguments[0]! do return none
    match recognizeComparison false arguments[3]! arguments[2]! with
    | some recognized => return some recognized
    | none => recognizeDifference false arguments[3]! arguments[2]!
  else if target.isAppOfArity ``GT.gt 4 then
    let arguments := target.getAppArgs
    unless ← isRealComparison arguments[0]! do return none
    match recognizeComparison true arguments[3]! arguments[2]! with
    | some recognized => return some recognized
    | none => recognizeDifference true arguments[3]! arguments[2]!
  else if let some (left, right) := target.and? then
    let some (type, a, v) := left.consumeMData.le? | return none
    let some (type', v', b) := right.consumeMData.le? | return none
    unless ← isRealComparison type do return none
    unless ← isRealComparison type' do return none
    let v := v.consumeMData
    unless v == v'.consumeMData ∧ !a.hasFVar ∧ !b.hasFVar do
      return none
    return some { shape := .twoSided false, expression := v }
  else if let some (set, v) := membership? target then
    let some (a, b) := iccEndpoints? set | return none
    unless ← isRealComparison (← inferType v) do return none
    let v := v.consumeMData
    unless !a.hasFVar ∧ !b.hasFVar do
      return none
    return some { shape := .twoSided true, expression := v }
  else
    return none

/-! ## Bounds of the variables -/

/-- One rational bound of a real variable found in the local context: the rational value of
the endpoint, the endpoint as written, and a proof of `endpoint ≤ x` or `x ≤ endpoint`. -/
structure Endpoint where
  /-- The exact rational value of the written endpoint. -/
  value : ℚ
  /-- The endpoint term as written in the hypothesis. -/
  term : Expr
  /-- A proof of the non-strict inequality between the endpoint and the variable. -/
  proof : Expr

/-- The rational bounds of one variable. -/
structure VariableBounds where
  /-- The variable. -/
  atom : Expr
  /-- The largest lower bound found. -/
  lower : Endpoint
  /-- The smallest upper bound found. -/
  upper : Endpoint

private def betterLower (current : Option Endpoint) (candidate : Endpoint) : Option Endpoint :=
  match current with
  | none => some candidate
  | some current => if current.value < candidate.value then some candidate else some current

private def betterUpper (current : Option Endpoint) (candidate : Endpoint) : Option Endpoint :=
  match current with
  | none => some candidate
  | some current => if candidate.value < current.value then some candidate else some current

/-- Read one hypothesis as a lower or upper rational bound of `variable`. A strict inequality
is weakened with `le_of_lt`; an interval membership contributes both endpoints through
`Set.mem_Icc` and its half-open and open variants. An absolute upper bound supplies the
endpoints of a symmetric interval through `neg_le_of_abs_le` and `le_of_abs_le`. -/
private def endpointsOfHypothesis (atom proof type : Expr) :
    MetaM (Option Endpoint × Option Endpoint) := do
  let type := type.consumeMData
  let asLower (endpoint proof : Expr) : MetaM (Option Endpoint) := do
    match ← Classify.rationalLiteral? endpoint with
    | some value => return some { value, term := endpoint, proof }
    | none => return none
  let asUpper := asLower
  let comparison (strict : Bool) (lhs rhs : Expr) :
      MetaM (Option Endpoint × Option Endpoint) := do
    let weakened ← if strict then mkAppM ``le_of_lt #[proof] else pure proof
    if rhs.consumeMData == atom then
      return (← asLower lhs weakened, none)
    else if lhs.consumeMData == atom then
      return (none, ← asUpper rhs weakened)
    if let some argument := absArgument? lhs then
      if argument.consumeMData == atom then
        let some upper ← asUpper rhs (← mkAppM ``le_of_abs_le #[weakened])
          | return (none, none)
        let lowerTerm ← mkAppM ``Neg.neg #[rhs]
        let lowerProof ← mkAppM ``neg_le_of_abs_le #[weakened]
        return (some { value := -upper.value, term := lowerTerm, proof := lowerProof }, some upper)
    return (none, none)
  if let some (_, lhs, rhs) := type.le? then
    return ← comparison false lhs rhs
  if let some (_, lhs, rhs) := type.lt? then
    return ← comparison true lhs rhs
  if type.isAppOfArity ``GE.ge 4 then
    let arguments := type.getAppArgs
    return ← comparison false arguments[3]! arguments[2]!
  if type.isAppOfArity ``GT.gt 4 then
    let arguments := type.getAppArgs
    return ← comparison true arguments[3]! arguments[2]!
  let some (set, element) := membership? type | return (none, none)
  unless element.consumeMData == atom do
    return (none, none)
  let set := set.consumeMData
  -- Membership in an interval unfolds definitionally to the conjunction of its two endpoint
  -- comparisons, so the components are the two projections of the hypothesis.
  let some (strictLower, strictUpper) := intervalStrictness? set | return (none, none)
  let arguments := set.getAppArgs
  let a := arguments[2]!
  let b := arguments[3]!
  let lowerProof ← mkAppM ``And.left #[proof]
  let upperProof ← mkAppM ``And.right #[proof]
  let lowerProof ← if strictLower then mkAppM ``le_of_lt #[lowerProof] else pure lowerProof
  let upperProof ← if strictUpper then mkAppM ``le_of_lt #[upperProof] else pure upperProof
  return (← asLower a lowerProof, ← asUpper b upperProof)

/-- The sharpest rational lower and upper bounds of a real variable in the local context, each
`none` when no hypothesis gives that side. Nested conjunctions and absolute upper bounds supply
their endpoint proofs. Strict inequalities are weakened, so the resulting closed interval can
contain boundary points excluded by the original hypotheses. -/
def variableBoundSides (atom : Expr) : MetaM (Option Endpoint × Option Endpoint) := do
  let mut lower : Option Endpoint := none
  let mut upper : Option Endpoint := none
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then
      continue
    let type ← instantiateMVars declaration.type
    let mut pending := [(mkFVar declaration.fvarId, type)]
    while !pending.isEmpty do
      let (proof, type) :: rest := pending | break
      pending := rest
      if let some (left, right) := type.consumeMData.and? then
        let leftProof ← mkAppM ``And.left #[proof]
        let rightProof ← mkAppM ``And.right #[proof]
        pending := (leftProof, left) :: (rightProof, right) :: pending
        continue
      let (lowerCandidate, upperCandidate) ←
        try
          endpointsOfHypothesis atom proof type
        catch _ =>
          pure (none, none)
      if let some candidate := lowerCandidate then
        lower := betterLower lower candidate
      if let some candidate := upperCandidate then
        upper := betterUpper upper candidate
  return (lower, upper)

/-- Find rational bounds of a real variable in the local context, or `none` when a side is
missing (`variableBoundSides`). Several hypotheses on the same side are reconciled by taking the
sharpest. -/
def variableBounds? (atom : Expr) : MetaM (Option VariableBounds) := do
  match ← variableBoundSides atom with
  | (some lower, some upper) => return some { atom, lower, upper }
  | _ => return none

/-- The refusal for a real term `atom` whose bounds `sides` (`variableBoundSides`) miss a side. -/
def missingBoundsMessage (atom : Expr) (sides : Option Endpoint × Option Endpoint) :
    MessageData :=
  let wanted : MessageData := m!"the route needs hypotheses `a ≤ x` and `x ≤ b`, \
    `x ∈ Set.Icc a b`, or `|x| ≤ r` with rational literal endpoints"
  match sides with
  | (some lower, none) =>
      m!"no rational bounds on `{atom}`: the hypotheses give the lower bound `{lower.term}` but \
        no upper bound; {wanted}"
  | (none, some upper) =>
      m!"no rational bounds on `{atom}`: the hypotheses give the upper bound `{upper.term}` but \
        no lower bound; {wanted}"
  | _ => m!"no rational bounds on `{atom}` in the hypotheses; {wanted}"

/-! ## Reflection over the bounded variables -/

/-- The reflected expression over `Fin dimension`, its real atoms, and
the rational bounds the hypotheses give them, in atom order. -/
structure ReflectedQuery (dimension : Nat) where
  /-- The reflected expression; `dimension` is the number of atoms. -/
  expression : Verified.Expr (Fin dimension)
  /-- The real terms used as coordinates, each with proved rational bounds. -/
  atoms : Array Expr
  /-- The bounds of each atom. -/
  bounds : Array VariableBounds

private def refuse {α : Type} (operation : String) (message : MessageData) : MetaM α :=
  throwError "{operation} box route: {message}"

/-- Reflect an ordinary real term over the checked identity route's atom table.
Every opaque real term needs proved rational bounds; a closed elementary expression
uses the zero-dimensional box. -/
def reflectOverBoundedVariables (operation : String) (expression : Expr) :
    MetaM ((n : Nat) × ReflectedQuery n) := do
  let reification ←
    try
      CAS.Elaboration.RealExpression.reify {
        operation
        opaque? := fun term ↦ pure (RealExpression.isAtomHead term)
        exponentAllowed := fun _ ↦ pure true
        symbolicExponentsAsRealPowers := true
        rationalLiterals := true
        unfoldLimit := RealExpression.localUnfoldLimit
      } expression
    catch error =>
      refuse operation m!"the expression could not be reflected into the checked language.\
        {indentD error.toMessageData}"
  let atoms := reification.coordinates
  let mut bounds : Array VariableBounds := #[]
  for atom in atoms do
    unless ← Elaboration.RealExpression.hasType atom (mkConst ``Real) do
      refuse operation m!"the subterm{indentExpr atom}\nis not real"
    let sides ← variableBoundSides atom
    match sides with
    | (some lower, some upper) => bounds := bounds.push { atom, lower, upper }
    | _ =>
        unless atom.hasFVar do
          refuse operation m!"unsupported closed subterm{indentExpr atom}\nThe checked elementary \
            expression language cannot evaluate this subterm, and no rational enclosure of \
            it was supplied by hypotheses."
        refuse operation (missingBoundsMessage atom sides)
  let some checked ← reification.toVerifiedExpr?
    | refuse operation m!"the expression has a symbolic natural exponent, which the kernel \
        evaluator cannot reduce; a literal exponent is needed"
  return ⟨reification.dimension, { expression := checked, atoms, bounds }⟩

/-! ## Presentation -/

/-- Quote a rational endpoint using only integer numerals and division. -/
private def rationalSyntax (q : ℚ) : CoreM (TSyntax `term) := do
  let magnitude := Syntax.mkNumLit (toString q.num.natAbs)
  let numerator ← if q.num < 0 then `(term| -$magnitude) else `(term| $magnitude)
  if q.den = 1 then return numerator
  let denominator := Syntax.mkNumLit (toString q.den)
  `(term| $numerator / $denominator)

/-- The configuration item `(name := value)`. -/
private def configItemSyntax (name : Name) (value : Nat) : MetaM Syntax := do
  let field := mkIdent name
  let literal := Syntax.mkNumLit (toString value)
  -- `optConfig` and the configured bare form parse each item as a `configItem` node around
  -- the `valConfigItem`; without that node the replay does not pretty-print.
  let value ← `(Lean.Parser.Term.valConfigItem| ($field:ident := $literal))
  return mkNode ``Lean.Parser.Term.configItem #[value.raw]

/-- The configuration items `(name := n)` of the fields of `precision` that differ from the
default policy, in the order `parsePrecision` reads them: one `(prec := n)` when the three
precision fields agree, as `(prec := n)` sets them, and otherwise each field that differs. The
depth is always included for a subdivided query, which subdivides because it is set, and for the
replay of bare `cega` (`method = none`) when it differs from the default. -/
private def precisionItems (precision : Continuum.RationalInterval.Precision)
    (method : Option EnclosureMethod) : MetaM (Array Syntax) := do
  let defaults : Continuum.RationalInterval.Precision := {}
  let mut items := #[]
  if precision.expOrder = precision.sqrtDigits ∧ precision.sqrtDigits = precision.logTerms ∧
      precision.expOrder ≠ defaults.expOrder then
    items := items.push (← configItemSyntax `prec precision.expOrder)
  else
    if precision.expOrder ≠ defaults.expOrder then
      items := items.push (← configItemSyntax `expOrder precision.expOrder)
    if precision.sqrtDigits ≠ defaults.sqrtDigits then
      items := items.push (← configItemSyntax `sqrtDigits precision.sqrtDigits)
    if precision.logTerms ≠ defaults.logTerms then
      items := items.push (← configItemSyntax `logTerms precision.logTerms)
  if method = some .subdivided ∨ (method = none ∧ precision.depth ≠ defaults.depth) then
    items := items.push (← configItemSyntax `depth precision.depth)
  if let some digits := precision.digits then
    items := items.push (← configItemSyntax `digits digits)
  return items

/-- Bare `cega` with the fields of `precision` that differ from the default policy and, when
given, the panels `(panels := n)` of an integral bound: the replay of the bare route itself. -/
def bareSyntax (precision : Continuum.RationalInterval.Precision)
    (panels? : Option Nat := none) : MetaM (TSyntax `tactic) := do
  let mut items ← precisionItems precision none
  if let some panels := panels? then
    items := items.push (← configItemSyntax `panels panels)
  if items.isEmpty then
    return ← `(tactic| cega)
  return ⟨mkNode ``CAS.CEGA.tacticCega
    #[mkAtom "cega", mkNullNode #[mkNode ``CAS.CEGA.cegaConfigured #[mkNullNode items]]]⟩

/-- Construct an explicit CEGA replay of the query that computes its enclosure by `method` from
the original term and its proved coordinate bounds, with the fields of `precision` that differ
from the default policy as configuration items.
The syntax is retained through reporting; pretty printing never feeds back into parsing. -/
def querySyntax (method : EnclosureMethod) (atoms : Array Expr)
    (box : Array (ℚ × ℚ)) (expression : Expr)
    (precision : Continuum.RationalInterval.Precision := {}) : MetaM (TSyntax `tactic) := do
  -- Explicit bindings name local variables. Bare CEGA retains the original context and
  -- therefore also replays a query whose bounded coordinates are applications such as `f x`,
  -- with the same precision policy.
  unless atoms.all Expr.isFVar do
    return ← bareSyntax precision
  let bindings ← (atoms.zip box).mapM fun (atom, (lo, hi)) ↦ do
    let name := mkIdent (← atom.fvarId!.getUserName)
    let lower ← rationalSyntax lo
    let upper ← rationalSyntax hi
    `(cegaIntervalBinding| $name:ident in [$lower, $upper])
  let term ← PrettyPrinter.delab expression
  -- The expression is parenthesized as in the documented form `cega [enclose ...] (expr)`.
  let term ← if term.raw.isIdent then pure term else `(($term))
  let cfg : TSyntax ``Lean.Parser.Term.optConfig :=
    ⟨mkNode ``Lean.Parser.Term.optConfig
      #[mkNullNode (← precisionItems precision (some method))]⟩
  `(tactic| cega $cfg:optConfig [enclose $bindings:cegaIntervalBinding,*] $term)

/-! ## Transport -/

/-- Prove a closed arithmetic comparison such as `bound ≤ c` between the certified rational
bound and the stated one. -/
private def proveArithmeticComparison
    (operation description : String) (goal : Expr) : TacticM Expr := do
  let proof ← mkFreshExprMVar goal
  let remaining ← proof.mvarId!.withContext do
    evalTacticAt (← `(tactic| norm_num)) proof.mvarId!
  unless remaining.isEmpty do
    refuse operation m!"{description}: the certified value does not give the stated bound.\
      {indentExpr goal}\nExact rational arithmetic did not close this comparison."
  Tactic.ProofCarrier.checkCompletedProof description proof

/-- Prove `((lo : ℚ) : ℝ) ≤ x ∧ x ≤ ((hi : ℚ) : ℝ)` for one coordinate from the hypotheses
found for the variable, comparing the box endpoint with the written endpoint by `norm_num`. -/
private def proveCoordinateMembership
    (operation : String) (interval : RationalInterval) (bounds : VariableBounds) :
    TacticM Expr := do
  let castLower ← mkAppOptM ``Rat.cast #[some (mkConst ``Real), none, some (toExpr interval.lo)]
  let castUpper ← mkAppOptM ``Rat.cast #[some (mkConst ``Real), none, some (toExpr interval.hi)]
  unless interval.lo ≤ bounds.lower.value ∧ bounds.upper.value ≤ interval.hi do
    refuse operation m!"the hypotheses bound `{bounds.atom}` to \
      [{renderRational bounds.lower.value}, {renderRational bounds.upper.value}], which does \
      not lie inside the coordinate interval [{renderRational interval.lo}, \
      {renderRational interval.hi}] of the query box"
  let lowerStep ← proveArithmeticComparison operation "lower endpoint of the box"
    (← mkAppM ``LE.le #[castLower, bounds.lower.term])
  let upperStep ← proveArithmeticComparison operation "upper endpoint of the box"
    (← mkAppM ``LE.le #[bounds.upper.term, castUpper])
  let lowerProof ← mkAppM ``le_trans #[lowerStep, bounds.lower.proof]
  let upperProof ← mkAppM ``le_trans #[bounds.upper.proof, upperStep]
  mkAppM ``And.intro #[lowerProof, upperProof]

/-- Prove `∀ i, (box i).MemReal (ρ i)` for the quoted box and coordinate vector of a query
result: each coordinate is proved separately and the finite quantifier is split by cases. -/
private def proveBoxMembership
    (operation : String) (membershipGoal : MVarId) (box : Array RationalInterval)
    (bounds : Array VariableBounds) : TacticM Unit := do
  let mut hypotheses : Array Hypothesis := #[]
  unless box.size = bounds.size do
    refuse operation m!"internal error: the box has {box.size} coordinates but bounds were \
      found for {bounds.size} variables"
  for h : index in [:box.size] do
    let some found := bounds[index]?
      | refuse operation m!"internal error: no bounds for coordinate {index}"
    let proof ← proveCoordinateMembership operation box[index] found
    hypotheses := hypotheses.push {
      userName := Name.mkSimple s!"hcasBox{index}"
      type := ← inferType proof
      value := proof
    }
  let (_, goal) ← membershipGoal.assertHypotheses hypotheses
  let remaining ← goal.withContext do
    evalTacticAt
      (← `(tactic|
        (intro i
         fin_cases i <;>
           first
             | assumption
             | (simp only [CAS.Continuum.RationalInterval.MemReal,
                  CAS.Continuum.RationalInterval.ofBounds, List.get,
                  Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
                  Matrix.head_cons, Matrix.cons_val_succ, Fin.isValue, Fin.zero_eta,
                  Fin.mk_one, Fin.reduceFinMk] at *
                assumption))))
      goal
  unless remaining.isEmpty do
    refuse operation m!"internal error: the box membership of the coordinates was not closed"

/-- Prove `Verified.Expr.eval ρ e = term`, the identification of the reflected expression with
the stated term: definitional unfolding, or the unfolding of the evaluator and the coordinate
vector together with the checked lowerings of `tan`, the hyperbolic functions, and `abs`,
and exact normalization of scientific literals. -/
private def proveEvaluation (operation : String) (evaluationGoal : MVarId) : TacticM Unit := do
  let remaining ← try
    evaluationGoal.withContext do
      evalTacticAt
        (← `(tactic|
          first
            | rfl
            | (simp only [Verified.Expr.eval, Matrix.cons_val_zero, Matrix.cons_val_one,
                Matrix.cons_val_two, Matrix.head_cons, Matrix.cons_val_succ, Fin.isValue,
                Fin.reduceFinMk, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat,
                Int.cast_zero, Int.cast_one, Int.cast_neg, Int.cast_natCast, one_div,
                Real.tan_eq_sin_div_cos, Real.sinh_eq, Real.cosh_eq, Real.tanh_eq,
                Real.sqrt_sq_eq_abs, ← Real.rpow_natCast, Real.rpow_intCast]
               done)
            | (norm_num [Verified.Expr.eval, Real.tan_eq_sin_div_cos, Real.sinh_eq, Real.cosh_eq,
                Real.tanh_eq, Real.sqrt_sq_eq_abs]
               done)))
        evaluationGoal
    catch error =>
      if error.isRuntime then
        throw error
      let target ← instantiateMVars (← evaluationGoal.getType)
      refuse operation m!"the reflected expression could not be identified with the stated term\
        {indentExpr target}"
  unless remaining.isEmpty do
    let target ← instantiateMVars (← evaluationGoal.getType)
    refuse operation m!"the reflected expression could not be identified with the stated term\
      {indentExpr target}"

/-- The soundness lemma that transports the certificate of the query mode of a shape
(`Shape.mode`) to the goal. -/
private def transportLemma : Shape → Name
  | .upper strict => if strict then ``lt_of_boundOn_box else ``le_of_boundOn_box
  | .difference strict => if strict then ``lt_of_boundOn_box_sub else ``le_of_boundOn_box_sub
  | .lower strict =>
      if strict then ``lt_of_enclosedOn_box_lower else ``le_of_enclosedOn_box_lower
  | .twoSided viaIcc => if viaIcc then ``mem_Icc_of_enclosedOn_box else ``mem_of_enclosedOn_box
  | .absUpper strict =>
      if strict then ``abs_lt_of_boundOn_abs_box else ``abs_le_of_boundOn_abs_box

/--
Close the main goal, a recognized ordinary inequality, from a kernel-checked statement
`certificate` about a box query whose box is `box` (in coordinate order) and whose coordinates
are the local variables `atoms` with the hypotheses `bounds`, through the soundness lemma
`lemmaName`.

The soundness lemma is applied to the certificate and the coordinate vector `![x₀, …]`; its
conclusion is unified with the goal, which fixes the stated term and constants; then the box
membership, the evaluation identity, and the endpoint comparisons are proved in turn. The
completed proof is checked before it is assigned.
-/
private def closeRecognizedGoalWith
    (operation : String) (lemmaName : Name) (certificate : Expr) (atoms : Array Expr)
    (box : Array RationalInterval) (bounds : Array VariableBounds)
    (proveEndpoint : String → Expr → TacticM Expr) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let coordinateVector ← RealExpression.parameterVector atoms
  -- The lemma is applied through a metavariable telescope: the certificate fixes the
  -- expression, the box, and the certified bound, the goal fixes the stated term and constants,
  -- and the remaining explicit hypotheses are proved afterwards.
  let lemmaConstant ← mkConstWithFreshMVarLevels lemmaName
  let (arguments, binderInfos, conclusion) ←
    forallMetaTelescopeReducing (← inferType lemmaConstant)
  let explicitArguments := (arguments.zip binderInfos).filterMap fun (argument, info) ↦
    if info.isExplicit then some argument else none
  let some certificateArgument := explicitArguments[0]?
    | refuse operation m!"internal error: the transport lemma has no certificate argument"
  let some vectorArgument := explicitArguments[1]?
    | refuse operation m!"internal error: the transport lemma has no coordinate argument"
  let some membership := explicitArguments[2]?
    | refuse operation m!"internal error: the transport lemma has no membership argument"
  let some evaluation := explicitArguments[3]?
    | refuse operation m!"internal error: the transport lemma has no evaluation argument"
  unless ← isDefEq certificateArgument certificate do
    refuse operation m!"the certificate{indentExpr (← inferType certificate)}\ndoes not have the \
      shape the transport lemma expects"
  unless ← isDefEq vectorArgument coordinateVector do
    refuse operation m!"internal error: the coordinate vector did not unify"
  unless ← isDefEq conclusion target do
    refuse operation m!"the transported certificate proves{indentExpr conclusion}\nbut the goal \
      is{indentExpr target}"
  proveBoxMembership operation membership.mvarId! box bounds
  proveEvaluation operation evaluation.mvarId!
  for comparison in explicitArguments[4:] do
    let comparisonType ← instantiateMVars (← inferType comparison)
    let proof ← proveEndpoint "comparison with the stated bound" comparisonType
    unless ← isDefEq comparison proof do
      refuse operation m!"internal error: the endpoint comparison did not unify"
  let proof ← instantiateMVars (mkAppN lemmaConstant arguments)
  let proof ← Tactic.ProofCarrier.checkCompletedProof s!"{operation} box route" proof
  goal.assign proof
  replaceMainGoal []

/-- `closeRecognizedGoalWith` for a checked result of the query mode of the shape, with the
soundness lemma of the shape (`transportLemma`). -/
private def closeRecognizedGoalCore
    (operation : String) (recognized : Recognized)
    (result : BoxQueryResult) (atoms : Array Expr) (box : Array RationalInterval)
    (bounds : Array VariableBounds)
    (proveEndpoint : String → Expr → TacticM Expr) : TacticM Unit :=
  closeRecognizedGoalWith operation (transportLemma recognized.shape) result.proof atoms box
    bounds proveEndpoint

/-- Prove a comparison with a closed endpoint by exact arithmetic or by enclosing the
difference on the zero-dimensional box. The second query uses the same checked evaluator,
soundness transport, and precision policy as the original query. Its final comparison is
rational arithmetic, so endpoint enclosure does not recurse. -/
def proveComparison (operation description : String) (target : Expr)
    (precision : Continuum.RationalInterval.Precision := {}) : TacticM Expr := do
  try
    return ← Tactic.ProofCarrier.preservingStateOnFailure
      (proveArithmeticComparison operation description target)
  catch arithmeticError =>
    if target.hasFVar then
      throw arithmeticError
    let proof ← mkFreshExprMVar target
    let savedGoals ← getGoals
    setGoals [proof.mvarId!]
    -- Certificates display rational endpoints through integer/natural casts. Normalize
    -- those casts by a proof before asking the elementary-expression reifier to read them.
    evalTactic (← `(tactic| norm_num only))
    if (← getGoals).isEmpty then
      setGoals savedGoals
      return ← Tactic.ProofCarrier.checkCompletedProof description proof
    let normalized ← instantiateMVars (← getMainTarget)
    let (strict, lhs, rhs) ←
      if let some (_, lhs, rhs) := normalized.le? then pure (false, lhs, rhs)
      else if let some (_, lhs, rhs) := normalized.lt? then pure (true, lhs, rhs)
      else throw arithmeticError
    let expression ← mkAppM ``HSub.hSub #[lhs, rhs]
    let ⟨_, reflected⟩ ← reflectOverBoundedVariables operation expression
    unless reflected.atoms.isEmpty do
      refuse operation m!"{description}: the endpoint is not a closed elementary expression"
    let some result ← runBoxQuery .bound .plain precision [] reflected.expression
      | refuse operation m!"{description}: the closed endpoint query found no certificate. \
          {boxQueryFailureMessage .plain reflected.expression}"
    closeRecognizedGoalCore operation { shape := .difference strict, expression }
      result #[] #[] #[] (proveArithmeticComparison operation)
    setGoals savedGoals
    Tactic.ProofCarrier.checkCompletedProof s!"{operation} closed endpoint" proof

/-- Transport a checked query to an ordinary inequality, enclosing any closed nonrational
endpoints with the same precision policy. Applied real coordinates use the
hypothesis proofs from the context, without generalizing or adding assumptions. -/
def closeRecognizedGoal
    (operation : String) (recognized : Recognized)
    (result : BoxQueryResult) (atoms : Array Expr) (box : Array RationalInterval)
    (bounds : Array VariableBounds)
    (precision : Continuum.RationalInterval.Precision := {}) : TacticM Unit :=
  closeRecognizedGoalCore operation recognized result atoms box bounds
    (fun description target ↦ proveComparison operation description target precision)

/-! ## Stated bounds

A goal such as `x * (1 - x) ≤ 1 / 4` states its bound. The stated-bound route checks that bound
with one kernel check of the query and the stated rational (`checkStatedBounds`) instead of
running the search in the elaborator and reading the certified endpoints back, then transports
the checked theorem to the goal as the search route does, with the stated constants compared
with their rational values by exact arithmetic. When the kernel rejects the check, the route
refuses with the values the query certifies, read in one kernel evaluation; when the query is
memoized, the check is inconclusive or the transport fails, it declines and the search route
runs, with its diagnostics. -/

/-- Run a route that may decline: an ordinary failure or an exhausted recursion depth becomes
`false`, and the caller restores the state. Heartbeat exhaustion and interrupts propagate, since
they end the whole declaration. -/
def falseOnFailure (action : TacticM Bool) : TacticM Bool :=
  tryCatchRuntimeEx action fun error ↦ do
    if error.isInterrupt || (error.isRuntime && !error.isMaxRecDepth) then
      throw error
    return false

/-- Read a closed numeral expression as a rational: what `Classify.rationalLiteral?` reads
(numerals, decimals with a decimal exponent of at most `4096`, negation, inversion, the four
operations, casts), also with natural powers `a ^ k` of literal exponent `k ≤ 4096` anywhere
inside, as long as the numerator and denominator of each power stay below `2 ^ 65536`. The value
is a proposal only: the route proves each stated term equal to its value by `norm_num`. -/
def statedRational? (term : Expr) : MetaM (Option ℚ) := do
  -- `Classify.rationalLiteral?` computes decimal exponents without a bound.
  let largeExponent := term.find? fun e ↦
    e.isAppOfArity ``OfScientific.ofScientific 5 &&
      match e.appArg!.consumeMData.rawNatLit? <|> e.appArg!.consumeMData.nat? with
      | some exponent => 4096 < exponent
      | none => true
  if largeExponent.isSome then
    return none
  go (term.sizeWithoutSharing + 1) term
where
  /-- The reader, with fuel bounded by the size of the term. -/
  go : Nat → Expr → MetaM (Option ℚ)
    | 0, _ => return none
    | fuel + 1, term => do
      if let some value ← Classify.rationalLiteral? term then
        return some value
      let binary (operation : ℚ → ℚ → Option ℚ) (a b : Expr) : MetaM (Option ℚ) := do
        let some x ← go fuel a | return none
        let some y ← go fuel b | return none
        return operation x y
      match_expr term.consumeMData with
      | HPow.hPow _ exponentType _ _ base exponent =>
          unless exponentType.consumeMData.isConstOf ``Nat do return none
          let some k := exponent.consumeMData.nat? <|> exponent.consumeMData.rawNatLit?
            | return none
          unless k ≤ 4096 do return none
          let some value ← go fuel base | return none
          -- Bound the size of the power before computing it.
          unless k * (value.num.natAbs.log2 + value.den.log2 + 2) ≤ 65536 do return none
          return some (value ^ k)
      | Neg.neg _ _ a => return (← go fuel a).map (- ·)
      | Inv.inv _ _ a => return (← go fuel a).bind fun x ↦ if x = 0 then none else some x⁻¹
      | HAdd.hAdd _ _ _ _ a b => binary (fun x y ↦ some (x + y)) a b
      | HSub.hSub _ _ _ _ a b => binary (fun x y ↦ some (x - y)) a b
      | HMul.hMul _ _ _ _ a b => binary (fun x y ↦ some (x * y)) a b
      | HDiv.hDiv _ _ _ _ a b => binary (fun x y ↦ if y = 0 then none else some (x / y)) a b
      | _ => return none

/-- A closed term read by `statedRational?`; `none` for a term with variables. -/
private def closedRational? (term : Expr) : MetaM (Option ℚ) :=
  if term.hasFVar ∨ term.hasMVar then pure none else statedRational? term

/-- The two sides of `a ≤ b`, `a < b`, `b ≥ a` or `b > a`, smaller first. -/
private def comparisonSides? (target : Expr) : Option (Expr × Expr) :=
  let target := target.consumeMData
  if let some (_, lhs, rhs) := target.le? then some (lhs, rhs)
  else if let some (_, lhs, rhs) := target.lt? then some (lhs, rhs)
  else if target.isAppOfArity ``GE.ge 4 ∨ target.isAppOfArity ``GT.gt 4 then
    let arguments := target.getAppArgs
    some (arguments[3]!, arguments[2]!)
  else
    none

/-- The endpoints `a` and `b` of a two-sided goal `a ≤ v ∧ v ≤ b`, or `v ∈ Set.Icc a b` when
`viaIcc`. -/
private def twoSidedEndpoints? (target : Expr) (viaIcc : Bool) : Option (Expr × Expr) := do
  let target := target.consumeMData
  if viaIcc then
    let (set, _) ← membership? target
    iccEndpoints? set
  else
    let (left, right) ← target.and?
    let (_, a, _) ← left.consumeMData.le?
    let (_, _, b) ← right.consumeMData.le?
    pure (a, b)

/-- The rational bound that a recognized goal states, and the lemma that transports its
kernel-checked form to the goal: the lemma `transportLemma` selects for a non-strict upper,
difference, absolute or two-sided goal, whose checked form is a certificate proposition, and one
of the `forall` lemmas for a strict or lower goal. `none` when a stated constant is not a closed
numeral expression. -/
private def statedTransport? (recognized : Recognized) (target : Expr) :
    MetaM (Option (StatedBound × Name)) := do
  match recognized.shape with
  | .upper strict =>
      let some (_, larger) := comparisonSides? target | return none
      let some c ← closedRational? larger | return none
      return some (.upper c strict, if strict then ``lt_of_forall_lt_box else ``le_of_boundOn_box)
  | .difference strict =>
      return some (.upper 0 strict,
        if strict then ``lt_of_forall_lt_box_sub else ``le_of_boundOn_box_sub)
  | .lower strict =>
      let some (smaller, _) := comparisonSides? target | return none
      let some c ← closedRational? smaller | return none
      return some (.lower c strict,
        if strict then ``lt_of_forall_lt_box_lower else ``le_of_forall_le_box_lower)
  | .absUpper strict =>
      let some (_, larger) := comparisonSides? target | return none
      let some c ← closedRational? larger | return none
      return some (.absolute c strict,
        if strict then ``abs_lt_of_forall_lt_box else ``abs_le_of_boundOn_abs_box)
  | .twoSided viaIcc =>
      let some (a, b) := twoSidedEndpoints? target viaIcc | return none
      let some lo ← closedRational? a | return none
      let some hi ← closedRational? b | return none
      return some (.enclosure lo hi,
        if viaIcc then ``mem_Icc_of_enclosedOn_box else ``mem_of_enclosedOn_box)

/-- The shape and the stated bound of a recognized relation whose constants are closed numeral
expressions, as `statedTransport?` reads them; `none` otherwise. -/
def statedBound? (target : Expr) : MetaM (Option (Recognized × StatedBound)) := do
  let some recognized ← recognize? target | return none
  let some (stated, _) ← statedTransport? recognized target | return none
  return some (recognized, stated)

/-- The outcome of one attempt of the stated-bound route. -/
private inductive StatedOutcome where
  /-- The kernel checked the stated bound, and the goal is closed. -/
  | closed
  /-- The kernel rejected the stated bound: the query found no interval, or its interval does not
  give the bound. -/
  | rejected
  /-- The route does not apply, the search has the query memoized, or the transport of a checked
  theorem failed; the search runs as if the route did not exist. -/
  | declined

/-- Whether this is native `cega [fast]`, which keeps its native polynomial certificate. -/
private def nativeFastMode : CoreM Bool := do
  let options ← getOptions
  return options.getBool `cega.nativePolynomial false &&
    options.getBool `cega.nativeCertificates false

/--
Close the main goal, a recognized ordinary inequality, by the stated-bound route for the query of
the shape's mode on `expression` over `box` that computes its enclosure by `method`, whose
coordinates are `atoms` with the hypotheses `bounds`.
Unless the goal is closed, the state is restored. The route declines when the goal does not state
its bound with closed numerals, when a kernel route finds the reduction of this query memoized
(and so cheaper), and when the transport fails. Native `cega [fast]` checks nothing here: it
only reuses a kernel theorem of the same bound for the same query, from earlier in this
environment, so that it does not add a native certificate for a goal a kernel route has proved.
-/
private def closeStated
    (operation : String) (recognized : Recognized) (method : EnclosureMethod) {n : Nat}
    (expression : Verified.Expr (Fin n)) (atoms : Array Expr) (box : Array RationalInterval)
    (bounds : Array VariableBounds) (precision : Continuum.RationalInterval.Precision) :
    TacticM StatedOutcome := do
  let saved ← saveState
  let attempt : TacticM StatedOutcome := withMainContext do
    let native ← nativeFastMode
    let target ← instantiateMVars (← getMainTarget)
    let some (stated, lemmaName) ← statedTransport? recognized target
      | return .declined
    -- The transport needs the hypotheses' interval of each coordinate inside the query box; an
    -- explicit box that is too small is left to the search, which names the coordinate.
    unless (box.zip bounds).all fun (interval, found) ↦
        interval.lo ≤ found.lower.value ∧ found.upper.value ≤ interval.hi do
      return .declined
    -- Native evaluation does not use the search's memo table, so only a kernel route defers to it.
    if !native &&
        (← boxQueryMemoized recognized.shape.mode method precision box.toList expression) then
      return .declined
    match ← checkStatedBounds method precision box.toList expression #[stated] native with
    | .checked proofs =>
        let some proof := proofs[0]? | return .declined
        try
          closeRecognizedGoalWith operation lemmaName proof atoms box bounds
            (proveArithmeticComparison operation)
          return .closed
        catch error =>
          trace[cega.stated] "the checked theorem does not transport to the goal; the search \
            runs:{indentD error.toMessageData}"
          return .declined
    | .rejected => return if native then .declined else .rejected
    | .inconclusive => return .declined
  let outcome ← tryCatchRuntimeEx attempt fun error ↦ do
    if error.isInterrupt || (error.isRuntime && !error.isMaxRecDepth) then
      saved.restore
      throw error
    return .declined
  unless outcome matches .closed do
    saved.restore
  return outcome

/-- Introduce the leading universal quantifiers and hypotheses of the goal, keeping the
binder names so that the introduced variables can be named in a suggested `cega` call. -/
def introduceBinders : TacticM Unit := do
  let mut fuel := 64
  while fuel > 0 do
    fuel := fuel - 1
    let target ← withMainContext do instantiateMVars (← getMainTarget)
    let .forallE name _ _ _ := target.consumeMData | return
    let name := if name.hasMacroScopes ∨ name.isAnonymous then `hcasBox else name.eraseMacroScopes
    evalTactic (← `(tactic| intro $(mkIdent name):ident))

/-- The text of bare `cega` with the policy `precision`, the call that reruns the bare route with
that policy. -/
private def configuredCega (precision : Continuum.RationalInterval.Precision) : String :=
  "cega" ++ renderConfig precision

/-- What to try when a box query falls short of the stated bound: bare `cega` with the current
policy and one field increased, as a call that parses, when the admission budgets allow it, and
otherwise the budget to raise. A goal without variables has nothing to subdivide; more digits,
through the precision-parametric evaluator, are what can tighten it. Nothing is promised: the
bound may be false. -/
private def refinementAdvice (closed : Bool)
    (precision : Continuum.RationalInterval.Precision) : MetaM MessageData := do
  let options ← getOptions
  if closed then
    let limit := CAS.Command.cas.maxDigits.get options
    let current := precision.digits.getD 0
    let digits := min limit (max 30 (2 * current))
    if digits ≤ current then
      return m!"The goal has no variables, so subdivision does not apply; more digits than the \
        {current} requested exceed `cas.maxDigits` ({limit}), which can be raised."
    return m!"The goal has no variables, so subdivision does not apply; if the bound is true, \
      more digits may prove it, as in `{configuredCega { precision with digits := digits }}`."
  let deeper : Continuum.RationalInterval.Precision :=
    { precision with depth := precision.depth + 2 }
  let finer := raisedPrecision precision
  let prec := finer.expOrder
  let refinementLimit := cega.maxRefinementWork.get options
  let precisionLimit := cega.maxPrecision.get options
  let deeperAdmitted := (refinementWorkWithin? refinementLimit deeper.depth).isSome
  let finerAdmitted := prec ≤ precisionLimit
  let deeperCall := configuredCega deeper
  let finerCall := configuredCega finer
  let calls : List MessageData :=
    (if deeperAdmitted then [m!"`{deeperCall}`"] else []) ++
    (if finerAdmitted then [m!"`{finerCall}`"] else [])
  if calls.isEmpty then
    return m!"A deeper subdivision or a higher precision exceeds `cega.maxRefinementWork` \
      ({refinementLimit}) or `cega.maxPrecision` ({precisionLimit}), which can be raised."
  return m!"If the bound is true, a deeper subdivision or a higher precision may prove it, as in \
    {MessageData.joinSep calls " or "}."

/-- The closed query box of the bounds found for the coordinates, refusing an empty interval. -/
private def queryBox (operation : String) (bounds : Array VariableBounds) :
    MetaM (Array RationalInterval) :=
  bounds.mapM fun found ↦ do
    if h : found.lower.value ≤ found.upper.value then
      return RationalInterval.ofBounds found.lower.value found.upper.value h
    else
      refuse operation m!"the hypotheses on `{found.atom}` give the empty interval \
        [{renderRational found.lower.value}, {renderRational found.upper.value}]"

/-- Whether `closeMainGoal` follows a query that falls short with the subdivided query: on a box
with coordinates, within the admission budgets. -/
private def subdivisionAdmitted {n : Nat} (subdivide : Bool)
    (box : Array RationalInterval) (expression : Verified.Expr (Fin n))
    (precision : Continuum.RationalInterval.Precision) : TermElabM Bool := do
  unless subdivide && !box.isEmpty do
    return false
  tryCatch
    (do
      discard <| validateQueryInput .subdivided precision expression
      validateQueryBox box.toList expression
      pure true)
    fun _ ↦ pure false

/-- The outcome of the stated-bound route of `closeMainGoal` (`closeStatedMainGoal`). -/
private inductive StatedMainOutcome where
  /-- The goal is closed; `replay` is the call that reruns the check that closed it. -/
  | closed (replay : TSyntax `tactic)
  /-- The kernel rejected the stated bound on the box and, when `subdivided`, also for the
  subdivided query, so the search would find nothing better. -/
  | rejected (subdivided : Bool)
  /-- The route does not apply or decided nothing; the search runs. -/
  | declined

/--
The stated-bound route of `closeMainGoal`, tried before its search; `query` and `subdivided` are
the replays of the search's first and subdivided queries. The bound the goal states is checked on
the box, and, when the kernel rejects that and `closeMainGoal` would subdivide, on the subdivided
query, as the search would run them. The result is `rejected` when the kernel rejected every check
it was given, and `declined` when an attempt declined, so that the search runs. A goal whose closed
bound `c` is not a numeral expression, in `f x ≤ c`, `f x < c`, `c ≤ f x` or `c < f x`, is read as
the difference `f x - c` (or `c - f x`) bounded by `0`, which the search compares by a second,
zero-dimensional query; that check is made on the box only, its replay is bare `cega`, which
reruns it, and a rejection declines, since the search's second query may still compare the bound.
Unless the goal is closed, the state is unchanged.
-/
private def closeStatedMainGoal
    (operation : String) (target : Expr) (recognized : Recognized) {n : Nat}
    (reflected : ReflectedQuery n) (box : Array RationalInterval)
    (precision : Continuum.RationalInterval.Precision) (subdivide : Bool)
    (query : TSyntax `tactic) (subdivided : MetaM (TSyntax `tactic)) :
    TacticM StatedMainOutcome := do
  let saved ← saveState
  let attempt : TacticM StatedMainOutcome := do
    let stated ← try
        Option.isSome <$> statedTransport? recognized target
      catch _ => pure false
    if stated then
      match ← closeStated operation recognized .plain reflected.expression reflected.atoms box
          reflected.bounds precision with
      | .closed => return .closed query
      | .declined => return .declined
      | .rejected => pure ()
      unless ← subdivisionAdmitted subdivide box reflected.expression precision do
        return .rejected false
      match ← closeStated operation recognized .subdivided reflected.expression
          reflected.atoms box reflected.bounds precision with
      | .closed => return .closed (← subdivided)
      | .rejected => return .rejected true
      | .declined => return .declined
    -- A closed bound that is not a numeral expression: the difference form, on the box only. The
    -- search compares the bound by a second query, so a difference that falls short goes to it.
    let strict? := match recognized.shape with
      | .upper strict | .lower strict => some strict
      | _ => none
    let some strict := strict? | return .declined
    let some (smaller, larger) := comparisonSides? target | return .declined
    let variant? ← try
        let difference ← mkAppM ``HSub.hSub #[smaller, larger]
        let ⟨_, reflected⟩ ← reflectOverBoundedVariables operation difference
        pure (some (⟨_, reflected⟩ : (m : Nat) × ReflectedQuery m), difference,
          ← queryBox operation reflected.bounds)
      catch _ => pure (none, smaller, #[])
    let (some ⟨_, reflected⟩, difference, box) := variant? | return .declined
    match ← closeStated operation { shape := .difference strict, expression := difference }
        .plain reflected.expression reflected.atoms box reflected.bounds precision with
    | .closed => return .closed (← bareSyntax precision)
    | _ => return .declined
  let outcome ← tryCatchRuntimeEx attempt fun error ↦ do
    saved.restore
    throw error
  unless outcome matches .closed _ do
    saved.restore
  return outcome

/-- The values a query certifies, as a phrase for messages. -/
private def describeDisplay : BoxQueryDisplay ℚ → String
  | .enclosure lower upper => s!"range [{renderRational lower}, {renderRational upper}]"
  | .upperBound upper => s!"upper bound {renderRational upper}"
  | .absoluteBound upper => s!"absolute bound {renderRational upper}"
  | .midpointApprox center radius =>
      s!"approximation {renderRational center} ± {renderRational radius}"

/-- The comparison between the value `display` certifies and the bound of `target` that the
transport of the search states for the shape of `recognized`, the first one that exact arithmetic
does not prove; `none` when the shape and the values do not match. -/
private def rejectedComparison (recognized : Recognized) (target : Expr)
    (display : BoxQueryDisplay ℚ) : MetaM (Option Expr) := do
  let relation (strict : Bool) (l r : Expr) : MetaM Expr :=
    mkAppM (if strict then ``LT.lt else ``LE.le) #[l, r]
  match recognized.shape, display with
  | .upper strict, .upperBound u | .absUpper strict, .absoluteBound u =>
      let some (_, larger) := comparisonSides? target | return none
      return some (← relation strict (← rationalTerm u) larger)
  | .difference strict, .upperBound u =>
      return some (← relation strict (← rationalTerm u) (← mkNumeral (mkConst ``Real) 0))
  | .lower strict, .enclosure lo _ =>
      let some (smaller, _) := comparisonSides? target | return none
      return some (← relation strict smaller (← rationalTerm lo))
  | .twoSided viaIcc, .enclosure lo hi =>
      let some (a, b) := twoSidedEndpoints? target viaIcc | return none
      if (← closedRational? a).any fun s ↦ decide (s ≤ lo) then
        return some (← relation false (← rationalTerm hi) b)
      return some (← relation false a (← rationalTerm lo))
  | _, _ => return none

/-- Why the query that computes its enclosure by `method`, replayed as `query`, does not prove
the stated bound of `target`: it found no enclosure, or the value it certifies, `display?`, does
not give the bound. The text is that of the search. -/
private def rejectionCause {n : Nat} (operation : String) (recognized : Recognized)
    (target : Expr) (method : EnclosureMethod) (query : TSyntax `tactic)
    (expression : Verified.Expr (Fin n)) (display? : Option (BoxQueryDisplay ℚ)) :
    MetaM MessageData := do
  match display? with
  | none =>
      let which : MessageData := match method with
        | .plain => m!"the query `{query}`"
        | .subdivided => m!"the subdivided query"
      return m!"{operation} box route: {which} found no certificate: \
        {boxQueryFailureMessage method expression}"
  | some display =>
      let comparison? ← rejectedComparison recognized target display
      let comparison : MessageData := match comparison? with
        | some comparison => indentExpr comparison
        | none => m!""
      return m!"{operation} box route: comparison with the stated bound: the certified value \
        does not give the stated bound.{comparison}\nExact rational arithmetic did not close \
        this comparison."

/-- The refusal of a goal whose stated bound the kernel rejected, in the words of the search:
built from the values that the plain query and, when `subdivided`, the subdivided query certify,
each read in one kernel evaluation (`readQueryDisplay?`), without a search. `query` and
`subdividedQuery` are their replays. `none` when a read fails, so that the search runs. -/
private def rejectionMessage? (operation : String) (target : Expr) (recognized : Recognized)
    {n : Nat} (reflected : ReflectedQuery n) (box : Array RationalInterval)
    (precision : Continuum.RationalInterval.Precision) (subdivided : Bool)
    (query : TSyntax `tactic) (subdividedQuery : MetaM (TSyntax `tactic)) :
    TacticM (Option MessageData) := do
  let mode := recognized.shape.mode
  let read (method : EnclosureMethod) : TacticM (Option (Option (BoxQueryDisplay ℚ))) :=
    tryCatch
      (do return some (← readQueryDisplay? mode method precision box.toList
        reflected.expression))
      fun _ ↦ pure none
  let some display? ← read .plain | return none
  let mut message ← rejectionCause operation recognized target .plain query
    reflected.expression display?
  if let some display := display? then
    message := m!"{message}\nThe query run was `{query}`; its certified \
      {describeDisplay display} may be too weak for the stated bound. \
      {← refinementAdvice box.isEmpty precision}"
  if subdivided then
    let some display? ← read .subdivided | return none
    let replay ← subdividedQuery
    let cause ← rejectionCause operation recognized target .subdivided replay
      reflected.expression display?
    message := m!"{message}\nSubdivision to depth {precision.depth} (`{replay}`) did not prove \
      it either:{indentD cause}"
  return some message

/--
The bare route on the main goal `target`, an ordinary inequality on bounded variables that
`recognized` reads. The bound the goal states is checked first (`closeStatedMainGoal`); when the
kernel rejects it, the route refuses with the values the queries certify, read back without a
search (`rejectionMessage?`). Otherwise the box query runs and its certificate is transported.
Returns the explicit `cega` call that performs the same query, for suggestions. Fails, leaving the
goal untouched to the caller's state restoration, with a message that names the shape or
hypothesis the route wanted.

With `subdivide`, a query that does not prove the goal is followed by the query of the same mode
whose enclosure is computed after checked subdivision to `precision.depth`, under the same
admission budgets, for every shape. The first query, and so every proof the route found without
subdivision, is unchanged.
-/
private def closeRecognizedMainGoal (operation : String) (target : Expr)
    (recognized : Recognized) (precision : Continuum.RationalInterval.Precision)
    (subdivide : Bool) : TacticM (TSyntax `tactic) := do
  let ⟨_, reflected⟩ ← reflectOverBoundedVariables operation recognized.expression
  let mode := recognized.shape.mode
  let box ← queryBox operation reflected.bounds
  let endpoints := reflected.bounds.map fun found ↦ (found.lower.value, found.upper.value)
  let query ← querySyntax .plain reflected.atoms endpoints recognized.expression precision
  let subdivided :=
    querySyntax .subdivided reflected.atoms endpoints recognized.expression precision
  match ← closeStatedMainGoal operation target recognized reflected box precision subdivide query
      subdivided with
  | .closed replay => return replay
  | .rejected both =>
      if let some message ← rejectionMessage? operation target recognized reflected box
          precision both query subdivided then
        throwError message
  | .declined => pure ()
  let saved ← saveState
  let attempt : TacticM Unit := do
    let some result ← runBoxQuery mode .plain precision box.toList reflected.expression
      | refuse operation m!"the query `{query}` found no certificate: \
          {boxQueryFailureMessage .plain reflected.expression}"
    try
      closeRecognizedGoal operation recognized result reflected.atoms box
        reflected.bounds precision
    catch error =>
      throwError "{error.toMessageData}\nThe query run was `{query}`; its certified \
        {describeDisplay result.display} may be too weak for the stated bound. \
        {← refinementAdvice box.isEmpty precision}"
  let first : Except Exception Unit ←
    tryCatch (Except.ok <$> attempt) fun error ↦ pure (.error error)
  let .error firstError := first
    | return query
  -- A query over its admission budgets is refused again when subdivided.
  unless ← subdivisionAdmitted subdivide box reflected.expression precision do
    throw firstError
  saved.restore
  let subdividedQuery ← subdivided
  try
    let some result ←
        runBoxQuery mode .subdivided precision box.toList reflected.expression
      | refuse operation m!"the subdivided query found no certificate: \
          {boxQueryFailureMessage .subdivided reflected.expression}"
    closeRecognizedGoal operation recognized result reflected.atoms box
      reflected.bounds precision
    return subdividedQuery
  catch error =>
    saved.restore
    throwError "{firstError.toMessageData}\nSubdivision to depth {precision.depth} \
      (`{subdividedQuery}`) did not prove it either:{indentD error.toMessageData}"

/-! ## Conjunctions -/

/-- The conjunction `a ≤ v ∧ v ≤ b`, with `<` at an open endpoint, that the membership of a real
`v` in `Set.Icc a b`, `Set.Ico a b`, `Set.Ioc a b` or `Set.Ioo a b` unfolds to. -/
private def intervalConjunction? (target : Expr) : MetaM (Option Expr) := do
  let some (set, v) := membership? target | return none
  let some (strictLower, strictUpper) := intervalStrictness? set | return none
  unless ← isRealComparison (← inferType v) do return none
  let arguments := set.consumeMData.getAppArgs
  let relation (strict : Bool) (l r : Expr) : MetaM Expr :=
    mkAppM (if strict then ``LT.lt else ``LE.le) #[l, r]
  return some (mkAnd (← relation strictLower arguments[2]! v)
    (← relation strictUpper v arguments[3]!))

/-- The relations of `target` for the integral route: `target` itself when `statedBound?` reads
it, and otherwise the relations of the sides of a conjunction, or of the conjunction that an
interval membership unfolds to. -/
partial def relationLeaves (target : Expr) : MetaM (Array Expr) := do
  if (← statedBound? target).isSome then return #[target]
  if let some conjunction ← intervalConjunction? target then
    return ← relationLeaves conjunction
  let some (left, right) := target.consumeMData.and? | return #[target]
  return (← relationLeaves left) ++ (← relationLeaves right)

/-- Split `goal` along its conjunctions and interval memberships, into one goal for each
relation. -/
private partial def conjunctionLeaves (goal : MVarId) : MetaM (Array MVarId) :=
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    if let some conjunction ← intervalConjunction? target then
      return ← conjunctionLeaves (← goal.replaceTargetDefEq conjunction)
    let some (left, right) := target.consumeMData.and? | return #[goal]
    let l ← mkFreshExprSyntheticOpaqueMVar left
    let r ← mkFreshExprSyntheticOpaqueMVar right
    goal.assign (mkApp4 (mkConst ``And.intro) left right l r)
    return (← conjunctionLeaves l.mvarId!) ++ (← conjunctionLeaves r.mvarId!)

/-- One relation of a conjunction goal, with what the route reads from it. -/
private structure Conjunct where
  /-- The goal of the relation. -/
  goal : MVarId
  /-- Its statement. -/
  target : Expr
  /-- Its shape and expression. -/
  recognized : Recognized
  /-- The bound it states and the lemma that transports its checked form, when its constants are
  closed numeral expressions. -/
  stated? : Option (StatedBound × Name)

/-- Close the relations of `group`, which share their expression and state their bounds with
closed numerals, by one kernel check of the query of that expression that tests every stated
bound (`checkStatedBounds`): the plain query, and the subdivided query when the kernel rejects
that and `subdivide` admits it. Each checked bound is transported to its relation. Returns
`false`, with the state restored, when a check or a transport fails. -/
private def closeGroup (operation : String) (precision : Continuum.RationalInterval.Precision)
    (subdivide : Bool) (group : Array Conjunct) : TacticM Bool := do
  let some first := group[0]? | return false
  Tactic.ProofCarrier.restoringStateOnFalse <| falseOnFailure <| first.goal.withContext do
    let ⟨_, reflected⟩ ← reflectOverBoundedVariables operation first.recognized.expression
    let box ← queryBox operation reflected.bounds
    let stateds := group.filterMap fun conjunct ↦ conjunct.stated?.map (·.1)
    unless stateds.size == group.size do return false
    let check (method : EnclosureMethod) : TermElabM StatedCheck :=
      checkStatedBounds method precision box.toList reflected.expression stateds
    let mut outcome ← check .plain
    if outcome matches .rejected then
      if (← subdivisionAdmitted subdivide box reflected.expression precision) then
        outcome ← check .subdivided
    let .checked proofs := outcome | return false
    unless proofs.size == group.size do return false
    for (conjunct, proof) in group.zip proofs do
      let some (_, lemmaName) := conjunct.stated? | return false
      setGoals [conjunct.goal]
      closeRecognizedGoalWith operation lemmaName proof reflected.atoms box reflected.bounds
        (proveArithmeticComparison operation)
    return true

/--
Close the main goal, a conjunction of recognized relations on bounded variables, possibly with
interval memberships `v ∈ Set.Ioo a b` (also `Set.Icc`, `Set.Ico`, `Set.Ioc`) read as the
conjunctions they unfold to. The relations that share their expression and state their bounds
with closed numerals form a group; a group of two or more is closed by one kernel check of one
query (`closeGroup`), subdivided when `subdivide` allows. Every other relation, and every relation
of a group whose check fails, is closed in turn by the route for one relation, and a failure names
the relation. Native `cega [fast]` takes each relation in turn. Returns bare `cega` with the
policy, which reruns the route. Unless every relation is proved, the state is restored.
-/
private def closeConjunction (operation : String)
    (precision : Continuum.RationalInterval.Precision) (subdivide : Bool) :
    TacticM (TSyntax `tactic) := Tactic.ProofCarrier.preservingStateOnFailure do
  let goal ← getMainGoal
  let others := (← getGoals).filter (· != goal)
  let leaves ← conjunctionLeaves goal
  let mut conjuncts : Array Conjunct := #[]
  for leaf in leaves do
    let conjunct ← leaf.withContext do
      let target ← instantiateMVars (← leaf.getType)
      let some recognized ← recognize? target
        | refuse operation m!"the conjunct{indentExpr target}\nis not one of {relationShapes}"
      let stated? ← try statedTransport? recognized target catch _ => pure none
      return ({ goal := leaf, target, recognized, stated? } : Conjunct)
    conjuncts := conjuncts.push conjunct
  let mut groups : Array (Array Conjunct) := #[]
  for conjunct in conjuncts do
    if conjunct.stated?.isNone then continue
    match groups.findIdx? fun group ↦
        group[0]?.any (·.recognized.expression == conjunct.recognized.expression) with
    | some index => groups := groups.modify index (·.push conjunct)
    | none => groups := groups.push #[conjunct]
  let native ← nativeFastMode
  let mut closed : Array MVarId := #[]
  for group in groups do
    if !native && 2 ≤ group.size then
      if (← closeGroup operation precision subdivide group) then
        closed := closed ++ group.map (·.goal)
  for conjunct in conjuncts do
    if closed.contains conjunct.goal then continue
    setGoals [conjunct.goal]
    try
      discard <| withMainContext <|
        closeRecognizedMainGoal operation conjunct.target conjunct.recognized precision subdivide
    catch error =>
      throwError "{operation} box route: the conjunct{indentExpr conjunct.target}\nwas not \
        proved:{indentD error.toMessageData}"
  setGoals others
  if (← instantiateMVars (mkMVar goal)).hasExprMVar then
    refuse operation m!"internal error: a conjunct was left open"
  bareSyntax precision

/--
The bare route: read the main goal (after introducing leading binders) as an ordinary
inequality on bounded variables (`closeRecognizedMainGoal`) or, when it has variables, as a
conjunction of such inequalities (`closeConjunction`), and prove it from kernel-checked box
queries. Returns the call that reruns the same check, for suggestions: the explicit `cega` query
of one inequality, or bare `cega` with the policy for a conjunction. Fails, leaving the goal
untouched to the caller's state restoration, with a message that names the shape or hypothesis
the route wanted.

With `subdivide`, a query that does not prove the goal is followed by the query of the same mode
whose enclosure is computed after checked subdivision to `precision.depth`, under the same
admission budgets, for every shape. The first query, and so every proof the route found without
subdivision, is unchanged.
-/
def closeMainGoal (operation : String)
    (precision : Continuum.RationalInterval.Precision := {}) (subdivide : Bool := false) :
    TacticM (TSyntax `tactic) := do
  introduceBinders
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    if let some recognized ← recognize? target then
      return ← closeRecognizedMainGoal operation target recognized precision subdivide
    let conjunction := target.consumeMData.isAppOfArity ``And 2 ||
      (← intervalConjunction? target).isSome
    if target.hasFVar && conjunction then
      return ← closeConjunction operation precision subdivide
    refuse operation m!"the goal has {← describeHead target}; the route proves {supportedShapes}"

/-- The local real variables named by the bindings of an explicit query, with their rational
bounds from the local context. -/
private def explicitCoordinates (operation : String) (bindings : List BoxBinding) :
    MetaM (Array Expr × Array VariableBounds) := do
  let mut atoms : Array Expr := #[]
  let mut bounds : Array VariableBounds := #[]
  for binding in bindings do
    let some declaration := (← getLCtx).findFromUserName? binding.coordinate
      | refuse operation m!"the coordinate `{binding.coordinate}` of the box is not a local \
          variable of this goal"
    let atom := mkFVar declaration.fvarId
    unless ← Elaboration.RealExpression.hasType atom (mkConst ``Real) do
      refuse operation m!"the coordinate `{binding.coordinate}` is not a real variable"
    let sides ← variableBoundSides atom
    let (some lower, some upper) := sides | refuse operation (missingBoundsMessage atom sides)
    atoms := atoms.push atom
    bounds := bounds.push { atom, lower, upper }
  return (atoms, bounds)

/--
The explicit route: close the main goal, an ordinary inequality, from the result of a user's
`cega [enclose x in [a, b], …] expr` query. The binding names must be local real variables of the
goal, the hypotheses must place each variable inside its stated interval, and the expression
must evaluate to the stated term. The goal is read before the query is run, so the caller
introduces binders first through `introduceBinders`.
-/
def closeWithExplicitQuery
    (operation : String) (bindings : List BoxBinding)
    (result : BoxQueryResult)
    (precision : Continuum.RationalInterval.Precision := {}) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some recognized ← recognize? target
    | refuse operation m!"the goal has {← describeHead target}; an explicit box query proves a \
        certificate goal (`EnclosedOn`, `BoundOn`, `ApproxOn`) or {relationShapes}"
  let (atoms, bounds) ← explicitCoordinates operation bindings
  let box := (bindings.map BoxBinding.interval).toArray
  closeRecognizedGoal operation recognized result atoms box bounds precision

/-- The stated-bound route of `closeWithExplicitQuery`, tried before the user's query runs: the
bound the ordinary goal states is checked for the query of the goal's mode on `expression` over
the box of `bindings`, with its enclosure computed by `method`, in one kernel check, and
transported as there. Returns `false`, with the state restored, when it does not apply or the
kernel rejects it. -/
def closeWithStatedQuery
    (operation : String) (method : EnclosureMethod) (bindings : List BoxBinding) {n : Nat}
    (expression : Verified.Expr (Fin n))
    (precision : Continuum.RationalInterval.Precision := {}) : TacticM Bool :=
  Tactic.ProofCarrier.restoringStateOnFalse <| falseOnFailure <| withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some recognized ← recognize? target | return false
    let (atoms, bounds) ← explicitCoordinates operation bindings
    let box := (bindings.map BoxBinding.interval).toArray
    return (← closeStated operation recognized method expression atoms box bounds precision)
      matches .closed

/-! ## Certificate goals on coordinate boxes

A certificate goal states a bound at every point of its domain. When the domain is a coordinate
box, given by set-builder bounds on the coordinates, `Set.Icc`, `boxDomain`, or a definition that
unfolds to these, `prepareCertificateGoal` introduces the point and its membership, splits the
membership into one hypothesis for each coordinate bound, writes each coordinate `p i` with a
numeral index in one form, and writes `‖·‖` on `ℝ` as `|·|`. The goal that remains is an ordinary
goal for `closeMainGoal`. -/

/-- The certificate propositions whose domain `prepareCertificateGoal` reads. -/
private def certificateHeads : List Name :=
  [``CAS.Certificate.EnclosedOn, ``CAS.Certificate.BoundOn, ``CAS.Certificate.ApproxOn,
    ``CAS.Certificate.ResidualBound]

/-- The dimension `n` of a coordinate carrier `(i : Fin n) → _`. -/
private def carrierDimension? (carrier : Expr) : MetaM (Option Nat) := do
  let .forallE _ domain _ _ ← whnfR carrier | return none
  let domain ← whnfR domain
  unless domain.isAppOfArity ``Fin 1 do return none
  (evalNat domain.appArg!).run

/-- A fact `(box i).MemReal y` of a membership, whose endpoints are read in the kernel. -/
private structure MemRealFact where
  /-- The interval `box i`. -/
  interval : Expr
  /-- The element `y`. -/
  element : Expr
  /-- The proof of the fact. -/
  proof : Expr

/-- The facts that `proof`, a proof of the membership `type`, states, each with its proof:
conjunctions are split, a membership other than in an interval `Set.Icc a b` (also `Set.Ico`,
`Set.Ioc`, `Set.Ioo`) is unfolded, a quantifier over `Fin n` is specialized at each index, and the
facts `(box i).MemReal y` are collected in the state, for their endpoints. -/
private partial def splitFacts (proof type : Expr) :
    StateT (Array MemRealFact) MetaM (Array (Expr × Expr)) := do
  let type := (← instantiateMVars type).consumeMData
  if let some (left, right) := type.and? then
    let l ← splitFacts (← mkAppM ``And.left #[proof]) left
    let r ← splitFacts (← mkAppM ``And.right #[proof]) right
    return l ++ r
  if let some (set, element) := membership? type then
    if (intervalStrictness? set).isSome then
      return #[(proof, type)]
    let predicate ← withTransparency .all <| whnf set
    if let .lam _ _ body _ := predicate then
      let unfolded ← Core.betaReduce (body.instantiate1 element)
      return ← splitFacts (← mkExpectedTypeHint proof unfolded) unfolded
    return #[]
  if type.isAppOfArity ``RationalInterval.MemReal 2 then
    let arguments := type.getAppArgs
    modify (·.push { interval := arguments[0]!, element := arguments[1]!, proof })
    return #[]
  if let .forallE _ domain body _ := type then
    unless body.hasLooseBVars do return #[(proof, type)]
    let domain ← whnfR domain
    unless domain.isAppOfArity ``Fin 1 do return #[]
    let some n ← (evalNat domain.appArg!).run | return #[]
    let mut facts : Array (Expr × Expr) := #[]
    for k in [:n] do
      let index ← RealExpression.finLiteral k n
      let instantiated ← Core.betaReduce (body.instantiate1 index)
      facts := facts ++ (← splitFacts (mkApp proof index) instantiated)
    return facts
  if type.isConstOf ``True then return #[]
  return #[(proof, type)]

/-- The rationals `values`, closed terms of type `ℚ`, read in one kernel evaluation. -/
private def readRationals (values : Array Expr) : MetaM (Array ℚ) := do
  if values.isEmpty then return #[]
  let list ← mkListLit (mkConst ``Rat) values.toList
  let reduced ← CAS.Tactic.KernelReadBack.kernelWhnf
    (← mkAppM ``Verified.Expr.Serial.encodeRationals #[list]) "CEGA box endpoints"
  let some code := reduced.rawNatLit?
    | throwError "the endpoints of the box did not reduce to a literal"
  let some decoded := Verified.Expr.Serial.decodeRationals values.size code
    | throwError "the endpoints of the box did not decode"
  return decoded.toArray.map fun (num, den) ↦ mkRat num den

/-- `term` with every coordinate `WithLp.ofLp point i` of a numeral index `i` written in one form,
with the exponent and carrier of `template?` and the numeral `i : Fin n`. -/
private def canonicalizeCoordinates (point : Expr) (n : Nat)
    (template? : Option (Expr × Expr)) (term : Expr) : MetaM Expr := do
  let some (exponent, carrier) := template? | return term
  Meta.transform term (post := fun t ↦ do
    let t' := t.consumeMData
    if t'.isAppOfArity ``WithLp.ofLp 4 && t'.getAppArgs[2]!.consumeMData == point then
      if let some ⟨_, k⟩ ← getFinValue? t'.getAppArgs[3]! then
        return .done (mkApp4 t'.getAppFn exponent carrier point
          (← RealExpression.finLiteral k.val n))
    return .continue)

/-- The exponent and carrier of the first coordinate `WithLp.ofLp point i` in `term`. -/
private def coordinateTemplate? (point term : Expr) : Option (Expr × Expr) :=
  (term.find? fun t ↦
      t.isAppOfArity ``WithLp.ofLp 4 && t.getAppArgs[2]!.consumeMData == point).map
    fun t ↦ (t.getAppArgs[0]!, t.getAppArgs[1]!)

/-- `term` with the norm `‖a‖` of every real `a` written as `|a|`. -/
private def normToAbs (term : Expr) : MetaM Expr :=
  Meta.transform term (post := fun t ↦ do
    if t.isAppOfArity ``Norm.norm 3 then
      if ← isDefEq t.getAppArgs[0]! (mkConst ``Real) then
        return .done (← mkAppM ``abs #[t.getAppArgs[2]!])
    return .continue)

/-- The coordinates `WithLp.ofLp point i` that occur in `term`, each once, in the order found. -/
private partial def pointCoordinates (point term : Expr) (found : Array Expr := #[]) :
    Array Expr :=
  let term := term.consumeMData
  if term.isAppOfArity ``WithLp.ofLp 4 && term.getAppArgs[2]!.consumeMData == point &&
      !term.hasLooseBVars then
    if found.contains term then found else found.push term
  else
    match term with
    | .app f a => pointCoordinates point a (pointCoordinates point f found)
    | .lam _ type body _ | .forallE _ type body _ =>
        pointCoordinates point body (pointCoordinates point type found)
    | .letE _ type value body _ =>
        pointCoordinates point body
          (pointCoordinates point value (pointCoordinates point type found))
    | .proj _ _ inner => pointCoordinates point inner found
    | _ => found

/-- What `prepareCertificateGoal` made of the main goal. -/
inductive CertificatePreparation where
  /-- The goal is now an ordinary goal on the coordinates of the point, with their bounds as
  hypotheses. -/
  | prepared
  /-- The goal is not a certificate proposition; it is unchanged. -/
  | notCertificate
  /-- The domain `domain` of the certificate goal gives no rational bounds on the coordinate
  `coordinate`; the goal is unchanged. -/
  | notBox (domain : Expr) (coordinate : MessageData)

/--
Prepare a certificate goal `EnclosedOn f s lo hi`, `BoundOn f s c`, `ApproxOn f g s ε` or
`ResidualBound r s ε` for `closeMainGoal`: unfold it to `∀ p, p ∈ s → …`, introduce `p` and its
membership, and split the membership into hypotheses (`splitFacts`), each `(box i).MemReal y` of a
`boxDomain box` giving the two bounds `↑lo ≤ y` and `y ≤ ↑hi`, whose rationals the kernel reads in
one evaluation. The coordinates of `p` are written in one form and `‖·‖` on `ℝ` as `|·|`. The
goal and the hypotheses differ from what they replace only by definitional unfolding, which the
kernel checks with the proof. Returns `notBox` when a coordinate of `p` in the goal has no
rational bounds in the hypotheses, and `notCertificate` when the goal is not one of these
propositions; in both cases the goal is unchanged.
-/
def prepareCertificateGoal : TacticM CertificatePreparation := withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let some head := target.getAppFn.constName? | return .notCertificate
  unless certificateHeads.contains head do return .notCertificate
  let arguments := target.getAppArgs
  let position := if head == ``CAS.Certificate.EnclosedOn then 3 else 2
  let some domain := arguments[arguments.size - position]? | return .notCertificate
  let saved ← saveState
  let attempt : TacticM CertificatePreparation := do
    let mut unfolded := target
    for _ in [:4] do
      let some name := unfolded.getAppFn.constName? | break
      unless certificateHeads.contains name do break
      let some next ← unfoldDefinition? unfolded | break
      unfolded := next.headBeta
    let .forallE pointName _ (.forallE _ _ _ _) _ := unfolded | return .notCertificate
    let goal ← goal.replaceTargetDefEq unfolded
    let (point, goal) ← goal.intro pointName
    let (membership, goal) ← goal.intro `hmem
    let pointExpr := mkFVar point
    let goal ← goal.withContext do
      let (facts, memReals) ←
        (splitFacts (mkFVar membership) (← inferType (mkFVar membership))).run #[]
      let interval (fact : MemRealFact) : Expr :=
        mkApp (mkConst ``RationalInterval.toInterval) fact.interval
      let endpoints ← readRationals <| memReals.flatMap fun fact ↦
        #[mkApp2 (mkConst ``FloatLib.Numerics.Interval.lo [Level.zero]) (mkConst ``Rat)
            (interval fact),
          mkApp2 (mkConst ``FloatLib.Numerics.Interval.hi [Level.zero]) (mkConst ``Rat)
            (interval fact)]
      let realCast (q : ℚ) : MetaM Expr :=
        mkAppOptM ``Rat.cast #[some (mkConst ``Real), none, some (toExpr q)]
      let mut facts := facts
      for h : i in [:memReals.size] do
        let fact := memReals[i]
        let lower ← mkAppM ``LE.le #[← realCast endpoints[2 * i]!, fact.element]
        let upper ← mkAppM ``LE.le #[fact.element, ← realCast endpoints[2 * i + 1]!]
        let hinted ← mkExpectedTypeHint fact.proof (mkAnd lower upper)
        facts := facts.push (← mkAppM ``And.left #[hinted], lower)
        facts := facts.push (← mkAppM ``And.right #[hinted], upper)
      let body ← normToAbs (← Core.betaReduce (← instantiateMVars (← goal.getType)))
      let template := coordinateTemplate? pointExpr body <|>
        facts.findSome? fun (_, type) ↦ coordinateTemplate? pointExpr type
      let dimension ← match template with
        | some (_, carrier) => carrierDimension? carrier
        | none => pure none
      let canonical (term : Expr) : MetaM Expr := do
        let term ← Core.betaReduce term
        match dimension with
        | some n => canonicalizeCoordinates pointExpr n template term
        | none => pure term
      let body ← canonical body
      let mut hypotheses : Array Hypothesis := #[]
      for h : i in [:facts.size] do
        let (proof, type) := facts[i]
        let type ← canonical type
        hypotheses := hypotheses.push
          { userName := Name.mkSimple s!"hbox{i}", type, value := ← mkExpectedTypeHint proof type }
      let goal ← goal.change body
      let (_, goal) ← goal.assertHypotheses hypotheses
      pure goal
    replaceMainGoal [goal]
    goal.withContext do
      let body ← instantiateMVars (← goal.getType)
      let real ← isRealComparison (← inferType pointExpr)
      let coordinates :=
        if real then (if body.containsFVar point then #[pointExpr] else #[])
        else pointCoordinates pointExpr body
      for coordinate in coordinates do
        if (← variableBounds? coordinate).isNone then
          return .notBox domain (← addMessageContext m!"{coordinate}")
      return .prepared
  let outcome ← tryCatchRuntimeEx attempt fun error ↦ do
    saved.restore
    throw error
  unless outcome matches .prepared do
    saved.restore
  return outcome

end CAS.Tactic.BoxInequality

end

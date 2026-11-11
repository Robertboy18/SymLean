/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Elementary.Trig
public import CAS.Continuum.IntervalEval.Callbacks
public import CAS.Route.Step

/-!
# Certified interval evaluator

`evalWithLookups` is the backend-neutral expression traversal specialized to
exact rational intervals. It calls checked denominator and unary-range
providers, which finite lists of route entries compile from planner output.

The low-level lookup functions are computational only. Their results become
theorem-producing evidence only through the sound provider structures and the
certified contexts built in later modules.

## Main definitions

* `verifiedExprOps`: the exact rational interval operations for `Verified.Expr`.
* `evalWithLookups`, `evalRational`, `evalPolynomial`: the evaluators, ordered
  from most to least capable; all fail closed with `none`.
* `ExprAbsLowerProvider`, `UnaryRangeProvider` and their `fromRouteEntries`
  constructors: checked providers for denominator lower bounds and for ranges
  of unary operations, assembled from finite lists of planner entries.
* `UnaryRangeRouteEntry.ofIncreasingOnInterval`, `ofDecreasingOnInterval`: unary
  entries for a monotone operation from bounds on its values at the two endpoints.

## Main results

* `intervalExprBackend_verifiedExprOps`: each operation of `verifiedExprOps` has the inclusion
  property (if `x ∈ I` and `y ∈ J` then `x ∘ y ∈ I ∘ J`).

## Implementation notes

Endpoints are rationals. Addition, negation, multiplication and natural powers are FloatLib's exact
rational interval operations; `sin` and `cos` are FloatLib's enclosures rounded outward to a dyadic
grid and sharpened on monotone panels (`CAS.Continuum.Interval.Elementary.Trig`), and `π` and `e`
are fixed rational brackets. What interval arithmetic cannot decide alone is handled by callbacks
that see the expression as well as its interval. A quotient whose denominator interval excludes zero
is multiplied by a reciprocal range when the unary provider has one, and otherwise divided using the
interval's own bound on `|b|`. A denominator interval that contains zero needs a positive `δ ≤ |b|`
from the denominator provider, proved for the denominator expression on the whole chart. A real
power `a ^ b` is `exp (log a * b)` on a positive base interval.

A unary entry records the argument interval it was proved for, and the lookup applies it only
when the evaluator computes an interval with the same rational endpoints. The planner may
therefore propose entries freely: soundness rests on each entry's own proof. Ranges of monotone
operations come from the endpoint rule, the classical evaluation of a monotone function on an
interval.

## References

* Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud, *Introduction to Interval Analysis*,
  SIAM, Philadelphia, 2009, <https://doi.org/10.1137/1.9780898717716>. Chapter 5 for interval
  extensions of real functions and their fundamental properties.
* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>. We use its interval
  type `Interval ℚ`, its exact rational operations and its sine and cosine enclosures.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Certificate
open CAS.Verified

/-! ## Denominator lower bounds -/

/-- A positive rational proposed as an executable denominator lower bound.

Semantic validity for a particular expression and domain is supplied by
`ExprAbsLowerProvider.sound`; this payload is not a stand-alone certificate. -/
abbrev AbsLowerResult := {delta : ℚ // 0 < delta}

namespace AbsLowerResult

/-- Candidate rational bound later certified against a denominator's absolute value. -/
abbrev delta (result : AbsLowerResult) : ℚ :=
  result.1

/-- Positivity of the executable lower bound. -/
theorem pos (result : AbsLowerResult) : 0 < result.delta :=
  result.2

end AbsLowerResult

/-- A checked provider for denominator lower-bound certificates.

CEGA planners compile denominator facts into this callback object for
`evalRational`: `lookup` is executable, while `sound` proves every emitted
certificate is valid on the current chart. -/
structure ExprAbsLowerProvider {α : Type*} {ι : Type*} (s : Set α) (ρ : α → ι → ℝ) where
  /-- Executable lookup for denominator lower bounds. -/
  lookup : Verified.Expr ι → Option AbsLowerResult
  /-- Every emitted executable certificate is semantically sound. -/
  sound :
    ∀ x, x ∈ s → ∀ den cert, lookup den = some cert →
      (cert.delta : ℝ) ≤ |den.eval (ρ x)|

namespace ExprAbsLowerProvider

variable {α : Type*} {ι : Type*} {s : Set α} {ρ : α → ι → ℝ}

/-- A provider with no denominator side conditions. -/
def empty : ExprAbsLowerProvider s ρ where
  lookup := fun _ ↦ none
  sound := by
    intro _x _hx _den _cert hlookup
    simp at hlookup

end ExprAbsLowerProvider

/-! ## Finite denominator-provider entries -/

/--
One route-backed denominator side condition returned by a CEGA planner.

The entry stores the executable positive rational lower bound, its direct
semantic theorem for the indexed denominator, and the route provenance used
to obtain it.
-/
structure ExprAbsLowerRouteEntry {α : Type*} {ι : Type*} (s : Set α) (ρ : α → ι → ℝ) where
  /-- The denominator expression guarded by this entry. -/
  den : Verified.Expr ι
  /-- Positive rational lower bound used by interval division. -/
  bound : AbsLowerResult
  /-- The rational bound is valid for the denominator throughout the chart. -/
  sound : ∀ x, x ∈ s → (bound.delta : ℝ) ≤ |den.eval (ρ x)|
  /-- Route steps used to prove the side condition. -/
  steps : List RouteStep := []

namespace ExprAbsLowerProvider

variable {α : Type*} {ι : Type*} {s : Set α} {ρ : α → ι → ℝ}

/--
Build a denominator provider from a finite list of route-backed planner entries.

`List.findSome?` performs one tail-recursive first-match traversal. No
intermediate provider structures or fallback closures are allocated.
-/
def fromRouteEntries [DecidableEq ι]
    (entries : List (ExprAbsLowerRouteEntry s ρ)) :
    ExprAbsLowerProvider s ρ where
  lookup := fun den ↦
    entries.findSome? fun entry ↦
      if den = entry.den then some entry.bound else none
  sound := by
    intro x hx den cert hlookup
    obtain ⟨entry, _hentry, hentry⟩ :=
      List.exists_of_findSome?_eq_some hlookup
    by_cases hden : den = entry.den
    · simp only [ite_eq_left hden] at hentry
      have hcert := Option.some.inj hentry
      subst cert
      subst den
      exact entry.sound x hx
    · simp only [ite_eq_right hden] at hentry
      cases hentry

/-- Collect the route steps from a finite denominator-entry list. -/
def routeEntrySteps (entries : List (ExprAbsLowerRouteEntry s ρ)) : List RouteStep :=
  entries.flatMap fun entry ↦ entry.steps

end ExprAbsLowerProvider

/-! ## Executable interval evaluators -/

/--
The exact rational operations for the shared verified-expression evaluator.

The implemented arithmetic and trigonometric primitives return `some`. Raw
division returns `none`; `rationalCallbacks` supplies the checked denominator
handling. The interval operations use FloatLib, while the callbacks carry the
expression-specific side conditions needed by CEGA.
-/
def verifiedExprOps : IntervalExprOps RationalInterval where
  const? q := some (const q)
  pi? := some piInterval
  e? := some eInterval
  add? I J := some (I.add J)
  mul? I J := some (I.mul J)
  pow? I k := some (I.powNat k)
  div? _ _ := none
  neg? I := some I.neg
  sin? I := some I.sin
  cos? I := some I.cos

/-- Soundness witness for the exact rational expression operations. -/
theorem intervalExprBackend_verifiedExprOps : IntervalExprBackend verifiedExprOps where
  const_sound q _ h := Option.some.inj h ▸ memReal_const q
  pi_sound _ h := Option.some.inj h ▸ piInterval_sound
  e_sound _ h := Option.some.inj h ▸ eInterval_sound
  add_sound _ _ _ _ _ h hx hy := Option.some.inj h ▸ RationalInterval.add_sound hx hy
  mul_sound _ _ _ _ _ h hx hy := Option.some.inj h ▸ RationalInterval.mul_sound hx hy
  pow_sound _ k _ _ h hx := Option.some.inj h ▸ RationalInterval.powNat_sound hx k
  div_sound _ _ _ _ _ h := nomatch h
  neg_sound _ _ _ h hx := Option.some.inj h ▸ RationalInterval.neg_sound hx
  sin_sound _ _ _ h hx := Option.some.inj h ▸ RationalInterval.sin_sound hx
  cos_sound _ _ _ h hx := Option.some.inj h ▸ RationalInterval.cos_sound hx

/-- Conservative interval evaluation for the algebraic fragment of `Verified.Expr`.

Although `Verified.Expr.eval` is total, a rational literal with denominator zero is not a
mathematically valid rational constant.  The interval front end therefore rejects it rather than
turning Lean's totalized value into an analytic certificate. -/
def evalPolynomial {ι : Type*} (env : ι → RationalInterval)
    (expr : Verified.Expr ι) : Option RationalInterval :=
  verifiedExprOps.eval env expr

/-- Expression-aware callbacks for rational interval evaluation.

When the computed denominator interval excludes zero, division multiplies by
the reciprocal range of `unaryRange` if it has one, and otherwise divides using
the interval's own lower bound on `|b|`. When the interval contains zero,
division needs a positive lower bound on `|b|` from `divLower`. Logarithm and
square root follow Mathlib's total real semantics; their providers decide which
argument intervals admit a finite enclosure.

A real power `a ^ b` is enclosed only when the computed base interval is strictly
positive, by `Real.rpow_def_of_pos`: the logarithm range of the base is multiplied
by the exponent interval and passed to the exponential provider under the argument
expression `log a * b`, exactly as evaluating `exp (log a * b)` would. Any other base
interval fails closed.
-/
def rationalCallbacks {ι : Type*}
    (divLower : Verified.Expr ι → Option AbsLowerResult)
    (unaryRange : UnaryKind → Verified.Expr ι → RationalInterval → Option RationalInterval) :
    IntervalExprCallbacks RationalInterval ι where
  div? _a b IA IB :=
    if IB.hi < 0 ∨ 0 < IB.lo then
      match unaryRange .inv b IB with
      | some invInterval => some (IA.mul invInterval)
      | none =>
          if hneg : IB.hi < 0 then
            some (IA.divByAbsLower IB.negativeAbsLower (by
              simpa [RationalInterval.negativeAbsLower] using neg_pos.mpr hneg))
          else if hpos : 0 < IB.lo then
            some (IA.divByAbsLower IB.positiveAbsLower (by
              simpa [RationalInterval.positiveAbsLower] using hpos))
          else
            none
    else
      match divLower b with
      | some cert => some (IA.divByAbsLower cert.delta cert.pos)
      | none => none
  unary? op arg IA :=
    match op with
    | .log => unaryRange .log arg IA
    | .sqrt => unaryRange .sqrt arg IA
    | .atan => unaryRange .atan arg IA
    | .asin => unaryRange .asin arg IA
    | .acos => unaryRange .acos arg IA
    | .exp => unaryRange .exp arg IA
    | .inv => unaryRange .inv arg IA
  rpow? a b IA IB :=
    if 0 < IA.lo then
      match unaryRange .log a IA with
      | some logInterval => unaryRange .exp (.mul (.log a) b) (logInterval.mul IB)
      | none => none
    else
      none

/-- Low-level interval evaluation with caller-supplied lookup functions.

This evaluator combines the built-in algebraic/rational/trig rules with a callback for
unary transcendental and branch-sensitive operations.  The callback receives the operation,
the original argument expression, and the already-computed argument interval.

Reciprocal intervals must exclude zero before consulting their callback.
Logarithm and square root follow Mathlib's total real semantics, so their
providers decide whether a finite range can be certified. A reciprocal whose
coarse interval contains zero can still be certified through `divLower`,
which proves a semantic positive lower bound for the actual denominator.

This function only computes; passing arbitrary callbacks here proves nothing about them. The sound
interface is `CertifiedEvalContext.eval`, which bundles these lookups with their semantic proofs. -/
def evalWithLookups {ι : Type*} (env : ι → RationalInterval)
    (divLower : Verified.Expr ι → Option AbsLowerResult)
    (unaryRange : UnaryKind → Verified.Expr ι → RationalInterval → Option RationalInterval) :
    Verified.Expr ι → Option RationalInterval :=
  verifiedExprOps.evalWithCallbacks (rationalCallbacks divLower unaryRange) env

/-- Side-condition-aware interval evaluation for the algebraic/rational fragment.

The `divLower` callback supplies an explicit positive lower bound for
`|denominator|`. Advanced unary operations have no provider in this restricted
entry point and therefore return `none`.
-/
def evalRational {ι : Type*} (env : ι → RationalInterval)
    (divLower : Verified.Expr ι → Option AbsLowerResult)
    (expr : Verified.Expr ι) : Option RationalInterval :=
  evalWithLookups env divLower (fun _ _ _ ↦ none) expr

/-- A rational literal with denominator `0` is rejected by the polynomial evaluator. -/
@[simp] theorem evalPolynomial_rat_zero_den {ι : Type*} (env : ι → RationalInterval) (num : Int) :
    evalPolynomial env (.rat num 0) = none := rfl

/-- A rational literal with denominator `0` is rejected by the rational evaluator, whatever
denominator provider is supplied. -/
@[simp] theorem evalRational_rat_zero_den {ι : Type*} (env : ι → RationalInterval)
    (divLower : Verified.Expr ι → Option AbsLowerResult) (num : Int) :
    evalRational env divLower (.rat num 0) = none := rfl

/-- A rational literal with denominator `0` is rejected by the general evaluator, whatever
providers are supplied. -/
@[simp] theorem evalWithLookups_rat_zero_den {ι : Type*} (env : ι → RationalInterval)
    (divLower : Verified.Expr ι → Option AbsLowerResult)
    (unaryRange : UnaryKind → Verified.Expr ι → RationalInterval → Option RationalInterval)
    (num : Int) :
    evalWithLookups env divLower unaryRange (.rat num 0) = none := rfl

/-- A checked provider for certified unary-operation ranges.

Unlike denominator providers, unary range soundness depends on the interval that
`evalWithLookups` computed for the operation argument.  The `sound` field therefore
matches the exact callback obligation used by `evalWithLookups_sound`. -/
structure UnaryRangeProvider {ι : Type*} (env : ι → RationalInterval)
    (divLower : Verified.Expr ι → Option AbsLowerResult) where
  /-- Executable lookup for unary-operation output intervals. -/
  lookup : UnaryKind → Verified.Expr ι → RationalInterval → Option RationalInterval
  /-- Every emitted output interval is sound for the computed argument interval. -/
  sound :
    ∀ op arg IA result,
      evalWithLookups env divLower lookup arg = some IA →
      lookup op arg IA = some result →
      ∀ z, IA.MemReal z → result.MemReal (op.apply z)

namespace UnaryRangeProvider

variable {ι : Type*} {env : ι → RationalInterval}
    {divLower : Verified.Expr ι → Option AbsLowerResult}

/-- A provider with no certified unary ranges. -/
def empty : UnaryRangeProvider env divLower where
  lookup := fun _ _ _ ↦ none
  sound := by
    intro _op _arg _IA _cert _hArg hlookup
    simp at hlookup

end UnaryRangeProvider

/-- Endpoint equality is enough to transport interval membership.

`RationalInterval` contains proof fields, so planner entries compare the rational endpoints
rather than requiring full structure equality. -/
theorem memReal_of_same_endpoints {I J : RationalInterval} {z : ℝ}
    (hlo : I.lo = J.lo) (hhi : I.hi = J.hi) :
    I.MemReal z → J.MemReal z :=
  fun hz ↦ ⟨hlo ▸ hz.1, hhi ▸ hz.2⟩

/-- One unary range entry returned by a CEGA planner.

The entry is tied to the argument interval computed by the evaluator:
it only applies when the operation, argument expression, and rational endpoints of
the argument interval match.  This prevents a certificate for, say, `sqrt` on
`[0,1]` from being reused silently on a larger interval.
-/
structure UnaryRangeRouteEntry {ι : Type*} (env : ι → RationalInterval)
    (divLower : Verified.Expr ι → Option AbsLowerResult) where
  /-- Unary operation guarded by this entry. -/
  op : UnaryKind
  /-- Argument expression guarded by this entry. -/
  arg : Verified.Expr ι
  /-- Argument interval this entry was proved for. -/
  argInterval : RationalInterval
  /-- Interval enclosing the image of `argInterval` under `op`. -/
  range : RationalInterval
  /-- Route steps. -/
  steps : List RouteStep := []
  /-- The checked range proof for this exact argument interval. -/
  sound :
    ∀ z, argInterval.MemReal z → range.MemReal (op.apply z)

namespace UnaryRangeRouteEntry

variable {ι : Type*} {env : ι → RationalInterval}
    {divLower : Verified.Expr ι → Option AbsLowerResult}

/-- Build a unary range route from an increasing-operation endpoint certificate.

A caller supplies:

* the operation and its argument expression;
* the argument interval `IA` computed by the evaluator;
* an output interval `J`;
* a proof that the operation is increasing on `IA`;
* endpoint proofs showing `J.lo ≤ f(IA.lo)` and `f(IA.hi) ≤ J.hi`.

The resulting route entry proves `f(z) ∈ J` for every `z ∈ IA`.  Specific
solvers such as the nonpositive exponential route are small endpoint
instances of this rule.
-/
def ofIncreasingOnInterval
    (op : UnaryKind) (arg : Verified.Expr ι)
    (IA J : RationalInterval) (steps : List RouteStep)
    (mono :
      ∀ {u v : ℝ}, IA.MemReal u → IA.MemReal v → u ≤ v →
        op.apply u ≤ op.apply v)
    (lower : (J.lo : ℝ) ≤ op.apply (IA.lo : ℝ))
    (upper : op.apply (IA.hi : ℝ) ≤ (J.hi : ℝ)) :
    UnaryRangeRouteEntry env divLower where
  op := op
  arg := arg
  argInterval := IA
  range := J
  steps := steps
  sound := by
    intro z hz
    constructor
    · exact le_trans lower (mono IA.lo_memReal hz hz.1)
    · exact le_trans (mono hz IA.hi_memReal hz.2) upper

/-- Build a unary range route from a decreasing-operation endpoint certificate.

This is the decreasing analogue of `ofIncreasingOnInterval`. For a decreasing
operation on `IA`, the lower endpoint of the image is controlled by `f(IA.hi)`
and the upper endpoint by `f(IA.lo)`.
-/
def ofDecreasingOnInterval
    (op : UnaryKind) (arg : Verified.Expr ι)
    (IA J : RationalInterval) (steps : List RouteStep)
    (anti :
      ∀ {u v : ℝ}, IA.MemReal u → IA.MemReal v → u ≤ v →
        op.apply v ≤ op.apply u)
    (lower : (J.lo : ℝ) ≤ op.apply (IA.hi : ℝ))
    (upper : op.apply (IA.lo : ℝ) ≤ (J.hi : ℝ)) :
    UnaryRangeRouteEntry env divLower where
  op := op
  arg := arg
  argInterval := IA
  range := J
  steps := steps
  sound := by
    intro z hz
    constructor
    · exact le_trans lower (anti hz IA.hi_memReal hz.2)
    · exact le_trans (anti IA.lo_memReal hz hz.1) upper

/-- Executable lookup for one unary range entry. -/
def lookupOne [DecidableEq ι] (e : UnaryRangeRouteEntry env divLower)
    (op : UnaryKind) (arg : Verified.Expr ι) (IA : RationalInterval) :
    Option RationalInterval :=
  if op = e.op then
    if arg = e.arg then
      if IA.lo = e.argInterval.lo ∧ IA.hi = e.argInterval.hi then
        some e.range
      else
        none
    else
      none
  else
    none

/-- Soundness of one unary range entry. -/
private theorem lookupOne_sound [DecidableEq ι] (e : UnaryRangeRouteEntry env divLower)
    {op : UnaryKind} {arg : Verified.Expr ι} {IA result : RationalInterval}
    (hlookup : e.lookupOne op arg IA = some result) :
    ∀ z, IA.MemReal z → result.MemReal (op.apply z) := by
  intro z hz
  unfold lookupOne at hlookup
  split_ifs at hlookup with hop harg hI
  obtain rfl := Option.some.inj hlookup
  subst hop
  exact e.sound z (memReal_of_same_endpoints hI.1 hI.2 hz)

end UnaryRangeRouteEntry

/-- Executable lookup for a finite list of unary route entries. -/
def unaryRouteEntriesLookup {ι : Type*} [DecidableEq ι]
    {env : ι → RationalInterval} {divLower : Verified.Expr ι → Option AbsLowerResult} :
    List (UnaryRangeRouteEntry env divLower) →
      UnaryKind → Verified.Expr ι → RationalInterval → Option RationalInterval :=
  fun entries op arg IA ↦
    entries.findSome? fun entry ↦ entry.lookupOne op arg IA

/-- Soundness of a finite list of unary route entries. -/
theorem unaryRouteEntriesLookup_sound {ι : Type*} [DecidableEq ι]
    {env : ι → RationalInterval} {divLower : Verified.Expr ι → Option AbsLowerResult}
    (entries : List (UnaryRangeRouteEntry env divLower)) :
    ∀ op arg IA result,
      unaryRouteEntriesLookup entries op arg IA = some result →
      ∀ z, IA.MemReal z → result.MemReal (op.apply z) := by
  intro op arg IA result hlookup
  obtain ⟨entry, -, hentry⟩ := List.exists_of_findSome?_eq_some hlookup
  exact entry.lookupOne_sound hentry

namespace UnaryRangeProvider

variable {ι : Type*} {env : ι → RationalInterval}
    {divLower : Verified.Expr ι → Option AbsLowerResult}

/-- Build a checked unary range provider from finite route entries. -/
def fromRouteEntries [DecidableEq ι]
    (entries : List (UnaryRangeRouteEntry env divLower)) :
    UnaryRangeProvider env divLower where
  lookup := unaryRouteEntriesLookup entries
  sound := by
    intro op arg IA result _hArg hlookup z hz
    exact unaryRouteEntriesLookup_sound entries op arg IA result hlookup z hz

/-- Collect route steps from finite unary range entries. -/
def routeEntrySteps (entries : List (UnaryRangeRouteEntry env divLower)) :
    List RouteStep :=
  entries.flatMap fun entry ↦ entry.steps

end UnaryRangeProvider

end RationalInterval
end CAS.Continuum

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Registry.Core

/-!
# Denominator lower bounds for registries

Division by an expression `d` on a chart needs a positive rational `δ` with `δ ≤ |d|` at every
chart point. `denominatorRouteEntry?` produces such a route entry from a registered fact for
`d`, from a variable whose interval lies on one side of zero, or from products and positive
powers of solvable denominators (`productAbsLowerRouteEntry`, `powerAbsLowerRouteEntry`).
`intervalAbsLowerRouteEntry?` instead encloses all of `d` with the registry's evaluator and
requires the enclosure to exclude zero. It is noncomputable and serves
`autoSideRouteEnclosureAttempt?`, while the executable registry extension
`extendWithDenominatorFactsFor?` uses the structural solver.

## Implementation notes

Every entry carries its proof of `δ ≤ |d|` on the whole chart, so the solvers only propose
entries. The structural solver multiplies the bounds of the two factors of a product and raises
the bound of the base of a power. Because the factors may be registered facts, a product can
get a bound even when the interval of a factor contains zero. From an enclosure of `d` with
`0 < lo` the interval solver takes `δ = lo`, and from one with `hi < 0` it takes `δ = -hi`.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Certificate
open CAS.Verified

namespace CertifiedEvalRegistry

variable {α : Type*} {ι : Type*} [DecidableEq ι] {s : Set α} {ρ : α → ι → ℝ}

/-- Build a route entry proving a positive variable denominator is bounded away from zero. -/
def positiveVariableAbsLowerRouteEntry
    (r : CertifiedEvalRegistry s ρ) (i : ι)
    (hpos : 0 < (r.env i).lo) :
    ExprAbsLowerRouteEntry s ρ where
  den := .var i
  bound := by
    let deltaQ : ℚ := (r.env i).lo
    exact ⟨deltaQ, hpos⟩
  sound := by
    intro x hx
    have hmem := r.hvars x hx i
    exact le_trans hmem.1 (le_abs_self (ρ x i))
  steps := [.variableLowerBound]

/-- Build a route entry proving a negative variable denominator is bounded away from zero. -/
def negativeVariableAbsLowerRouteEntry
    (r : CertifiedEvalRegistry s ρ) (i : ι)
    (hneg : (r.env i).hi < 0) :
    ExprAbsLowerRouteEntry s ρ where
  den := .var i
  bound := by
    let deltaQ : ℚ := - (r.env i).hi
    have hpos : 0 < deltaQ := by
      dsimp [deltaQ]
      linarith
    exact ⟨deltaQ, hpos⟩
  sound := by
    intro x hx
    have hmem := r.hvars x hx i
    have hle : ((- (r.env i).hi : ℚ) : ℝ) ≤ -ρ x i := by
      simpa using neg_le_neg hmem.2
    exact le_trans hle (neg_le_abs (ρ x i))
  steps := [.variableLowerBound]

/-- Build a route entry proving a product denominator from factor denominator facts. -/
def productAbsLowerRouteEntry
    (_r : CertifiedEvalRegistry s ρ) (a b : Verified.Expr ι)
    (ea eb : ExprAbsLowerRouteEntry s ρ)
    (hea : ea.den = a) (heb : eb.den = b) :
    ExprAbsLowerRouteEntry s ρ where
  den := .mul a b
  bound := by
    let deltaQ : ℚ := ea.bound.delta * eb.bound.delta
    have hpos : 0 < deltaQ := by
      dsimp [deltaQ]
      exact mul_pos ea.bound.pos eb.bound.pos
    exact ⟨deltaQ, hpos⟩
  sound := by
    intro x hx
    have ha := ea.sound x hx
    have hb := eb.sound x hx
    rw [Rat.cast_mul]
    calc
      (ea.bound.delta : ℝ) * (eb.bound.delta : ℝ) ≤
          |ea.den.eval (ρ x)| * |eb.den.eval (ρ x)| :=
        mul_le_mul ha hb
          (le_of_lt (by exact_mod_cast eb.bound.pos))
          (abs_nonneg _)
      _ = |(Verified.Expr.mul a b).eval (ρ x)| := by
        simp [hea, heb, abs_mul]
  steps := ea.steps ++ eb.steps ++ [.productLowerBound]

/-- Build a route entry proving a positive-power denominator from a base denominator fact. -/
def powerAbsLowerRouteEntry
    (_r : CertifiedEvalRegistry s ρ) (a : Verified.Expr ι) (n : Nat)
    (ea : ExprAbsLowerRouteEntry s ρ)
    (hea : ea.den = a) :
    ExprAbsLowerRouteEntry s ρ where
  den := .pow a n
  bound := by
    let deltaQ : ℚ := ea.bound.delta ^ n
    have hpos : 0 < deltaQ := by
      dsimp [deltaQ]
      exact pow_pos ea.bound.pos n
    exact ⟨deltaQ, hpos⟩
  sound := by
    intro x hx
    have ha := ea.sound x hx
    rw [Rat.cast_pow]
    calc
      (ea.bound.delta : ℝ) ^ n ≤ |ea.den.eval (ρ x)| ^ n :=
        pow_le_pow_left₀
          (le_of_lt (by exact_mod_cast ea.bound.pos)) ha n
      _ = |(Verified.Expr.pow a n).eval (ρ x)| := by
        simp [hea, abs_pow]
  steps := ea.steps ++ [.powerLowerBound]

/-- Build a denominator lower-bound route from a strictly positive interval enclosure.

This is for proofs, not for commands: it uses the semantic evaluator
`Verified.Expr.eval`, which is noncomputable for the full expression language.
The executable exact-first planner instead uses the structural denominator solver.
-/
noncomputable def positiveIntervalAbsLowerRouteEntry
    (r : CertifiedEvalRegistry s ρ) (den : Verified.Expr ι) (I : RationalInterval)
    (hEval : r.toContext.eval den = some I)
    (hpos : 0 < I.lo) :
    ExprAbsLowerRouteEntry s ρ where
  den := den
  bound := by
    let deltaQ : ℚ := I.lo
    exact ⟨deltaQ, hpos⟩
  sound := by
    intro x hx
    have henc := r.toContext.enclosedOn den I hEval x hx
    exact le_trans henc.1 (le_abs_self (den.eval (ρ x)))
  steps := [.intervalLowerBound]

/-- Build a denominator lower-bound route from a strictly negative interval enclosure.

This is for proofs, not for commands, for the same reason as
`positiveIntervalAbsLowerRouteEntry`.
-/
noncomputable def negativeIntervalAbsLowerRouteEntry
    (r : CertifiedEvalRegistry s ρ) (den : Verified.Expr ι) (I : RationalInterval)
    (hEval : r.toContext.eval den = some I)
    (hneg : I.hi < 0) :
    ExprAbsLowerRouteEntry s ρ where
  den := den
  bound := by
    let deltaQ : ℚ := -I.hi
    have hpos : 0 < deltaQ := by
      dsimp [deltaQ]
      linarith
    exact ⟨deltaQ, hpos⟩
  sound := by
    intro x hx
    have henc := r.toContext.enclosedOn den I hEval x hx
    have hle : ((-I.hi : ℚ) : ℝ) ≤ -den.eval (ρ x) := by
      simpa using neg_le_neg henc.2
    exact le_trans hle (neg_le_abs (den.eval (ρ x)))
  steps := [.intervalLowerBound]

/-- Try to solve a denominator lower bound by enclosing the whole denominator expression,
keeping the proof that the returned entry is attached to the requested denominator.

This helper is noncomputable and meant for proofs; the executable registry extension
behind the exact-first planner does not use it.
-/
noncomputable def intervalAbsLowerRouteEntryWithProof?
    (r : CertifiedEvalRegistry s ρ) (den : Verified.Expr ι) :
    Option { e : ExprAbsLowerRouteEntry s ρ // e.den = den } :=
  match hEval : r.toContext.eval den with
  | some I =>
      if hpos : 0 < I.lo then
        some
          ⟨r.positiveIntervalAbsLowerRouteEntry den I hEval hpos,
            rfl⟩
      else if hneg : I.hi < 0 then
        some
          ⟨r.negativeIntervalAbsLowerRouteEntry den I hEval hneg,
            rfl⟩
      else
        none
  | none => none

/-- Try to solve a denominator lower bound by enclosing the whole denominator expression.

This helper is noncomputable and meant for proofs; use the structural denominator
solver when a computable route is required.
-/
noncomputable def intervalAbsLowerRouteEntry?
    (r : CertifiedEvalRegistry s ρ) (den : Verified.Expr ι) :
    Option (ExprAbsLowerRouteEntry s ρ) :=
  match r.intervalAbsLowerRouteEntryWithProof? den with
  | some ⟨entry, _hentry⟩ => some entry
  | none => none

/-- Try to solve a denominator target and keep the proof that the generated entry
is attached to the requested denominator expression. -/
def denominatorRouteEntryWithProof?
    (r : CertifiedEvalRegistry s ρ) (den : Verified.Expr ι) :
    Option { e : ExprAbsLowerRouteEntry s ρ // e.den = den } :=
  match r.divEntries.findSome? (fun entry ↦
      if h : entry.den = den then some ⟨entry, h⟩ else none) with
  | some entry => some entry
  | none => match den with
  | .var i =>
      if hpos : 0 < (r.env i).lo then
        some ⟨r.positiveVariableAbsLowerRouteEntry i hpos, rfl⟩
      else if hneg : (r.env i).hi < 0 then
        some ⟨r.negativeVariableAbsLowerRouteEntry i hneg, rfl⟩
      else
        none
  | .mul a b =>
      match r.denominatorRouteEntryWithProof? a,
        r.denominatorRouteEntryWithProof? b with
      | some ⟨ea, hea⟩, some ⟨eb, heb⟩ =>
          some
            ⟨r.productAbsLowerRouteEntry a b ea eb hea heb,
              rfl⟩
      | _, _ => none
  | .pow a (n + 1) =>
      match r.denominatorRouteEntryWithProof? a with
      | some ⟨ea, hea⟩ =>
          some
            ⟨r.powerAbsLowerRouteEntry a (n + 1) ea hea,
              rfl⟩
      | none => none
  | _ => none
termination_by structural den

/-- Try to prove a denominator is nonzero from the available range certificates.

The solver first reuses an exactly matching registered fact, preserving its
bound and route steps. Otherwise it handles variables whose chart intervals
stay away from zero, products of solvable denominators, and positive powers of
a solvable base. Recursive factor and base queries can also reuse registered
facts, even when their coarse intervals contain zero.
-/
def denominatorRouteEntry?
    (r : CertifiedEvalRegistry s ρ) (den : Verified.Expr ι) :
    Option (ExprAbsLowerRouteEntry s ρ) :=
  match r.denominatorRouteEntryWithProof? den with
  | some ⟨entry, _hentry⟩ => some entry
  | none => none

end CertifiedEvalRegistry
end RationalInterval
end CAS.Continuum

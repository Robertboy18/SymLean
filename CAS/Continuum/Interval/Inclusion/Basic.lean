/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
public import CAS.Continuum.Interval.Rational.Basic
public import Mathlib.Tactic.Inclusion.Core.Extensions
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# CEGA ranges on dyadic intervals

Mathlib's `dyadic_interval` tactic evaluates a real expression over `Inclusion.Interval Dyadic`
and checks the result in the kernel. To use CEGA's ranges, we register the `cega_real` family.
We read a bounded dyadic interval's endpoints as rationals and apply the CEGA range on
`RationalInterval`, then round the result outward to dyadic endpoints. The `prec` parameter
sets the rounding grid, as it does for rational literals in `dyadic_interval`.

An `inclusion` operation cannot carry side conditions, so every lifted range is total. An
unbounded argument, or an argument the CEGA range declines (a reciprocal across zero, say),
produces a fallback interval that holds for every real input.

## Implementation notes

The method is the inclusion principle of interval arithmetic: replacing every operation of an
expression by an interval operation with the inclusion property gives an interval that contains
the value of the expression (Rump, (5.17)). Mathlib's `inclusion` framework builds the interval
expression together with the membership proof, and the kernel decides the goal by evaluating it.
The family, the round trip through `RationalInterval` and the fallbacks are ours;
`mem_liftUnary` is the inclusion property of every lifted range. The round trip adds an outward
rounding per operation and lets each operation reuse its rational range and soundness proof
unchanged.

## References

* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Section 5.5 for the inclusion property (5.16) and the inclusion principle (5.17).
-/

@[expose] public section

open Inclusion

namespace CAS.Continuum.CEGAInclusion

/-- The `cega_real` inclusion family: CEGA's certified ranges on Mathlib's dyadic intervals. -/
meta initialize cegaRealFamily : InclusionFamily ← registerInclusionFamily `cega_real

/-- The rational interval with the endpoints of a bounded dyadic interval. -/
def toRational? (I : Interval Dyadic) : Option RationalInterval :=
  match (I.lb : Option Dyadic), (I.ub : Option Dyadic) with
  | some a, some b =>
      if h : a.toRat ≤ b.toRat then some (RationalInterval.ofBounds a.toRat b.toRat h) else none
  | _, _ => none

/-- If `x` lies in the dyadic interval `I` and `toRational? I = some J`, then `x` lies in the
rational interval `J`. -/
theorem memReal_of_toRational? {I : Interval Dyadic} {J : RationalInterval} {x : ℝ}
    (hx : x ∈ I) (hJ : toRational? I = some J) : J.MemReal x := by
  obtain ⟨_ | a, _ | b⟩ := I <;> simp only [toRational?, reduceCtorEq] at hJ
  rw [IntervalDyadicReal.mem_iff_mem_map, Interval.mem_map_iff] at hx
  split_ifs at hJ with h
  cases hJ
  exact RationalInterval.memReal_ofBounds h ⟨hx.1 a rfl, hx.2 b rfl⟩

/-- Round a rational interval outward to dyadic endpoints with precision `2 ^ (-prec)`. -/
def ofRational (J : RationalInterval) (prec : ℕ) : Interval Dyadic :=
  Interval.Icc (IntervalDyadicReal.rat J.lo prec).lb (IntervalDyadicReal.rat J.hi prec).ub

/-- Outward rounding keeps members: if `x` lies in the rational interval `J`, it lies in the dyadic
interval `ofRational J prec`, for every precision `prec`. -/
theorem mem_ofRational {J : RationalInterval} {x : ℝ} (hx : J.MemReal x) (prec : ℕ) :
    x ∈ ofRational J prec :=
  Interval.mem_Icc_of_le (IntervalDyadicReal.ratCast_mem J.lo prec) hx.1 hx.2
    (IntervalDyadicReal.ratCast_mem J.hi prec)

/--
Lift a CEGA range `f` to dyadic intervals.

A bounded argument goes through `f` and is rounded outward; an unbounded argument, or one on
which `f` returns `none`, gives `fallback`.
-/
def liftUnary (f : RationalInterval → Option RationalInterval) (fallback : Interval Dyadic)
    (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  match (toRational? I).bind f with
  | some K => ofRational K prec
  | none => fallback

/-- If `f` encloses `g` on rational intervals and `fallback` contains every value of `g`,
then the lifted range encloses `g` on dyadic intervals. -/
theorem mem_liftUnary {g : ℝ → ℝ} {f : RationalInterval → Option RationalInterval}
    (hf : ∀ {J K : RationalInterval} {x : ℝ}, f J = some K → J.MemReal x → K.MemReal (g x))
    {fallback : Interval Dyadic} (hfallback : ∀ x, g x ∈ fallback)
    {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    g x ∈ liftUnary f fallback I prec := by
  unfold liftUnary
  cases hI : toRational? I with
  | none => exact hfallback x
  | some J =>
    cases hK : f J with
    | none => simpa [hK] using hfallback x
    | some K => simpa [hK] using mem_ofRational (hf hK (memReal_of_toRational? hx hI)) prec

/-- The dyadic interval `[lo, hi]`. -/
def closed (lo hi : Dyadic) : Interval Dyadic := Interval.Icc lo hi

/-- A real `x` with `lo ≤ x ≤ hi` (endpoints read as reals) lies in the dyadic interval
`closed lo hi`. -/
theorem mem_closed {lo hi : Dyadic} {x : ℝ} (hlo : lo.toReal ≤ x) (hhi : x ≤ hi.toReal) :
    x ∈ closed lo hi :=
  Interval.mem_map_Icc Dyadic.toReal hlo hhi

/-- The dyadic interval `[lo, ∞)`. -/
def atLeast (lo : Dyadic) : Interval Dyadic := Interval.Ici lo

/-- A real `x` with `lo ≤ x` (`lo` read as a real) lies in the dyadic interval `atLeast lo`. -/
theorem mem_atLeast {lo : Dyadic} {x : ℝ} (hlo : lo.toReal ≤ x) : x ∈ atLeast lo :=
  ⟨WithBot.coe_le_coe.mpr hlo, le_top⟩

end CAS.Continuum.CEGAInclusion

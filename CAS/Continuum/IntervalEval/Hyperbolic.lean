/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Elementary.Hyperbolic
public import CAS.Continuum.Interval.Elementary.Exp
public import CAS.Continuum.IntervalEval.Context

/-!
# Correlated ranges for lowered hyperbolic expressions

The expression syntax lowers `sinh a`, `cosh a` and `tanh a` to `(exp a - exp (-a)) / 2`,
`(exp a + exp (-a)) / 2` and their quotient. Evaluating these forms operation by operation
treats the two exponentials as independent and overestimates the range.
`hyperbolicEnclosureAttempt?` recognizes exactly these forms, encloses `a` with
`evalNormalized`, and applies `sinhRange`, `coshRange` or `tanhRange` at the requested positive
Taylor order. `hyperbolicRange?` computes the same interval without the proof.

## Implementation notes

The ranges are FloatLib's enclosures of `sinh`, `cosh` and `tanh`; we only recognize the lowered
syntax, which must use one argument expression in every exponential, and rewrite the semantics
with `Real.sinh_eq`, `Real.cosh_eq` and `Real.tanh_eq`. Treating the two exponentials as one
function removes the dependency between them. The registry planner takes this route at once
when it applies.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>. We use its
  enclosures `Interval.sinhBounds`, `Interval.coshBounds` and `Interval.tanhBounds`.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval
namespace CertifiedEvalContext

open CAS.Certificate
open CAS.Verified

variable {α : Type*} {ι : Type*} [DecidableEq ι] {s : Set α} {ρ : α → ι → ℝ}

/-- Checked enclosure of the lowered `sinh arg`, written `(exp arg - exp (-arg)) / 2`. The
argument is enclosed by `evalNormalized`, and the result is `sinhRange` of that interval. -/
noncomputable def sinhAttempt?
    (p : CertifiedEvalContext s ρ) (arg : Verified.Expr ι)
    (order : ℕ+ := defaultExpTaylorOrder.toPNat') :
    Option
      (EnclosureAttempt α s
        (fun x ↦
          (Verified.Expr.div
            (.sub (.exp arg) (.exp (.neg arg))) (.nat 2)).eval (ρ x))) :=
  match harg : p.evalNormalized arg with
  | none => none
  | some input =>
      let output := sinhRange order input
      some
        { interval := output
          sound := by
            intro x hx
            have hinput := p.sound_normalized x hx arg input harg
            change (sinhRange order input).MemReal _
            simpa [Verified.Expr.eval, Real.sinh_eq] using
              sinhRange_sound order input hinput
          steps := [.hyperbolicRange] }

/-- Checked enclosure of the lowered `cosh arg`, written `(exp arg + exp (-arg)) / 2`. The
argument is enclosed by `evalNormalized`, and the result is `coshRange` of that interval. -/
noncomputable def coshAttempt?
    (p : CertifiedEvalContext s ρ) (arg : Verified.Expr ι)
    (order : ℕ+ := defaultExpTaylorOrder.toPNat') :
    Option
      (EnclosureAttempt α s
        (fun x ↦
          (Verified.Expr.div
            (.add (.exp arg) (.exp (.neg arg))) (.nat 2)).eval (ρ x))) :=
  match harg : p.evalNormalized arg with
  | none => none
  | some input =>
      let output := coshRange order input
      some
        { interval := output
          sound := by
            intro x hx
            have hinput := p.sound_normalized x hx arg input harg
            change (coshRange order input).MemReal _
            simpa [Verified.Expr.eval, Real.cosh_eq] using
              coshRange_sound order input hinput
          steps := [.hyperbolicRange] }

/-- Checked enclosure of the lowered `tanh left`, written as the quotient of the lowered `sinh`
and `cosh` forms. The equality hypotheses identify `right`, `denominatorLeft`, and
`denominatorRight` with `left`, whose `evalNormalized` interval is passed to `tanhRange`. -/
noncomputable def tanhAttempt?
    (p : CertifiedEvalContext s ρ)
    (left right denominatorLeft denominatorRight : Verified.Expr ι)
    (hright : left = right) (hleft : left = denominatorLeft)
    (hdenominatorRight : left = denominatorRight)
    (order : ℕ+ := defaultExpTaylorOrder.toPNat') :
    Option
      (EnclosureAttempt α s
        (fun x ↦
          (Verified.Expr.div
            (.div (.sub (.exp left) (.exp (.neg right))) (.nat 2))
            (.div
              (.add (.exp denominatorLeft) (.exp (.neg denominatorRight)))
              (.nat 2))).eval (ρ x))) :=
  match harg : p.evalNormalized left with
  | none => none
  | some input =>
      let output := tanhRange order input
      some
        { interval := output
          sound := by
            subst right
            subst denominatorLeft
            subst denominatorRight
            intro x hx
            have hinput := p.sound_normalized x hx left input harg
            have hrange := tanhRange_sound order input hinput
            change (tanhRange order input).MemReal
              (((Real.exp (left.eval (ρ x)) - Real.exp (-left.eval (ρ x))) / 2) /
                ((Real.exp (left.eval (ρ x)) + Real.exp (-left.eval (ρ x))) / 2))
            rw [show
                ((Real.exp (left.eval (ρ x)) - Real.exp (-left.eval (ρ x))) / 2) /
                    ((Real.exp (left.eval (ρ x)) + Real.exp (-left.eval (ρ x))) / 2) =
                  Real.tanh (left.eval (ρ x)) by
                  rw [Real.tanh_eq]
                  field_simp]
            exact hrange
          steps := [.hyperbolicRange] }

/-- Preview the correlated range of a lowered `sinh`, `cosh`, or `tanh` expression. -/
def hyperbolicRange?
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι)
    (order : ℕ+ := defaultExpTaylorOrder.toPNat') : Option RationalInterval :=
  match expr with
  | .div (.sub (.exp left) (.exp (.neg right))) (.nat 2) =>
      if left = right then
        (p.evalNormalized left).map (sinhRange order)
      else
        none
  | .div (.add (.exp left) (.exp (.neg right))) (.nat 2) =>
      if left = right then
        (p.evalNormalized left).map (coshRange order)
      else
        none
  | .div
      (.div (.sub (.exp left) (.exp (.neg right))) (.nat 2))
      (.div (.add (.exp denominatorLeft) (.exp (.neg denominatorRight))) (.nat 2)) =>
      if left = right ∧ left = denominatorLeft ∧ left = denominatorRight then
        (p.evalNormalized left).map (tanhRange order)
      else
        none
  | _ => none

/-- Build the checked correlated enclosure of a lowered hyperbolic expression. -/
noncomputable def hyperbolicEnclosureAttempt?
    (p : CertifiedEvalContext s ρ) (expr : Verified.Expr ι)
    (order : ℕ+ := defaultExpTaylorOrder.toPNat') :
    Option (EnclosureAttempt α s (fun x ↦ expr.eval (ρ x))) :=
  match expr with
  | .div (.sub (.exp left) (.exp (.neg right))) (.nat 2) =>
      if h : left = right then
        h ▸ p.sinhAttempt? left order
      else
        none
  | .div (.add (.exp left) (.exp (.neg right))) (.nat 2) =>
      if h : left = right then
        h ▸ p.coshAttempt? left order
      else
        none
  | .div
      (.div (.sub (.exp left) (.exp (.neg right))) (.nat 2))
      (.div (.add (.exp denominatorLeft) (.exp (.neg denominatorRight))) (.nat 2)) =>
      if h : left = right ∧ left = denominatorLeft ∧ left = denominatorRight then
        p.tanhAttempt? left right denominatorLeft denominatorRight h.1 h.2.1 h.2.2 order
      else
        none
  | _ => none

end CertifiedEvalContext
end RationalInterval
end CAS.Continuum

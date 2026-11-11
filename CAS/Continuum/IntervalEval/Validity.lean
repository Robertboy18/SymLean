/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.IteratedDifferentiation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import CAS.Continuum.IntervalEval.Registry.Refinement
public import CAS.Expr.Rendering -- shake: keep: `variable [Verified.Expr.VarNames ι]` in the public section needs the class even where no declaration uses it

/-!
# Automatic analytic-domain certificates

Symbolic differentiation is sound only where the expression is analytically valid: denominators
and logarithm arguments must be nonzero, the arguments of `asin` and `acos` must differ from `1`
and `-1`, and square-root arguments and the bases of real powers must be positive. These facts are
compiled from the same checked interval registry used for range analysis.

## Main definitions

* `CertifiedEvalRegistry.rationalIcc`: the registry of a closed interval with rational endpoints,
  holding only the exact enclosure of the variable.
* `lowerValidIterates`: forgets the derivative levels of a validity route beyond `m`.

## Main results

* `CertifiedEvalRegistry.nonzeroOn?`: a certificate route proving that every
  expression in a list is nonzero on the chart, from either a registered
  denominator lower bound or a sign-definite interval enclosure.
* `CertifiedEvalRegistry.validOn?`: a route proving `expr.ValidAt (ρ x)` for all
  chart points, by discharging the nonzero and positivity lists of
  `validityRequirements`.
* `CertifiedEvalRegistry.validIteratesOn?`, `validIteratesOnIcc?`: validity of
  the expression and its first `n - 1` symbolic derivatives on a rational
  interval (`ValidIteratesOn n`); `contDiffOn_of_validIterates` turns a route for
  `ValidIteratesOn (n + 1)` into `ContDiffOn ℝ n` for the univariate evaluation.

## Implementation notes

There is one source of domain semantics. `Verified.Expr.validityRequirements` extracts the
obligations of `Verified.Expr.ValidAt` as a list of expressions that must be nonzero and a list
that must be positive, `ValidityRequirements.validAt_of_holds` turns proofs of both lists into
`ValidAt`, and the code here only proves the lists. We fold all obligations into one sum with
`Verified.Expr.addList`, so a single `extendWithEasyFacts?` pass adds the denominator and
unary-range facts needed to evaluate every obligation. A nonzero obligation is proved from a
registered denominator bound `δ ≤ |d|` with `0 < δ` if there is one, and otherwise from an
enclosure of the simplified obligation lying strictly on one side of zero; a positivity
obligation needs an enclosure with a positive lower endpoint. Excluding zero by an enclosure is
the classical use of the inclusion property; the requirement lists and the two discharge rules
are ours.

The compiler fails closed. If a panel crosses a pole, touches a strict branch boundary, or
contains an unsupported operation needed to prove an obligation, it returns `none`, and adaptive
callers may subdivide and retry. `validIteratesOn? expr (n + 1)` combines `validOn? expr` with a
recursive call on `expr.diff 0`, and `Verified.Expr.diff_iteratedDiff` matches this chain with
the indexing of `ValidIteratesOn`. Bare `cega` integration and `findRoot` reduce
`validIteratesOnIcc?` with the kernel (`KernelReadBack.kernelWhnf`) and use the `cert` field of
the returned route as the proof.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS
open CAS.Verified

variable {α : Type*} {ι : Type*} [DecidableEq ι] [Verified.Expr.VarNames ι]
  {s : Set α} {ρ : α → ι → ℝ}

/-- Forget derivative levels beyond `m`. -/
def lowerValidIterates {expr : Verified.Expr (Fin 1)} {m n : ℕ} {u : Set ℝ}
    (route : CertificateRoute (expr.ValidIteratesOn n u)) (hmn : m ≤ n) :
    CertificateRoute (expr.ValidIteratesOn m u) :=
  route.map fun h ↦ h.mono hmn

/-- Derive ordinary `Cⁿ` regularity from a certificate route for analytic validity. -/
theorem contDiffOn_of_validIterates
    {expr : Verified.Expr (Fin 1)} {n : ℕ} {u : Set ℝ}
    (route : CertificateRoute (expr.ValidIteratesOn (n + 1) u))
    (hs : UniqueDiffOn ℝ u) :
    ContDiffOn ℝ n expr.univariateEval u :=
  Verified.Expr.contDiffOn_univariateEval expr n hs route.cert

namespace CertifiedEvalContext

/--
Prove a list of nonzero obligations from either a registered absolute lower
bound or a sign-definite interval enclosure.

The interval fallback covers compound expressions such as `x + 1`, which need no dedicated
denominator theorem when interval evaluation keeps them strictly away from zero.
-/
noncomputable def nonzeroListProof?
    (p : CertifiedEvalContext s ρ) :
    (exprs : List (Verified.Expr ι)) →
      Option (PLift (∀ x, x ∈ s → ∀ expr ∈ exprs, expr.eval (ρ x) ≠ 0))
  | [] =>
      some
        { down := by
            intro _x _hx _expr hexpr
            cases hexpr }
  | expr :: rest =>
      match hrest : nonzeroListProof? p rest with
      | none => none
      | some restProof =>
          match hprovider : p.divProvider.lookup expr with
          | some cert =>
              some
                { down := by
                    intro x hx target htarget
                    rcases List.mem_cons.mp htarget with rfl | hmem
                    · have hbound := p.divProvider.sound x hx target cert hprovider
                      have hdelta : (0 : ℝ) < cert.delta := by
                        exact_mod_cast cert.pos
                      exact abs_pos.mp (hdelta.trans_le hbound)
                    · exact restProof.down x hx target hmem }
          | none =>
              match heval : p.evalSimplified expr with
              | none => none
              | some I =>
                  if hlo : 0 < I.lo then
                    some
                      { down := by
                          intro x hx target htarget
                          rcases List.mem_cons.mp htarget with rfl | hmem
                          · have hmemI := p.sound_simplified x hx target I heval
                            have hloReal : (0 : ℝ) < (I.lo : ℝ) := by
                              exact_mod_cast hlo
                            exact ne_of_gt (hloReal.trans_le hmemI.1)
                          · exact restProof.down x hx target hmem }
                  else if hhi : I.hi < 0 then
                    some
                      { down := by
                          intro x hx target htarget
                          rcases List.mem_cons.mp htarget with rfl | hmem
                          · have hmemI := p.sound_simplified x hx target I heval
                            have hhiReal : (I.hi : ℝ) < 0 := by
                              exact_mod_cast hhi
                            exact ne_of_lt (hmemI.2.trans_lt hhiReal)
                          · exact restProof.down x hx target hmem }
                  else
                    none

/-- Prove a list of strict positivity obligations by certified interval evaluation. -/
noncomputable def positiveListProof?
    (p : CertifiedEvalContext s ρ) :
    (exprs : List (Verified.Expr ι)) →
      Option (PLift (∀ x, x ∈ s → ∀ expr ∈ exprs, 0 < expr.eval (ρ x)))
  | [] =>
      some
        { down := by
            intro _x _hx _expr hexpr
            cases hexpr }
  | expr :: rest =>
      match heval : p.evalSimplified expr, hrest : positiveListProof? p rest with
      | some I, some restProof =>
          if hlo : 0 < I.lo then
            some
              { down := by
                  intro x hx target htarget
                  rcases List.mem_cons.mp htarget with rfl | hmem
                  · have hmemI := p.sound_simplified x hx target I heval
                    have hloReal : (0 : ℝ) < (I.lo : ℝ) := by
                      exact_mod_cast hlo
                    exact hloReal.trans_le hmemI.1
                  · exact restProof.down x hx target hmem }
          else
            none
      | _, _ => none

end CertifiedEvalContext

namespace CertifiedEvalRegistry

/--
The empty checked registry for a closed interval with rational
endpoints.

All later denominator, unary-range, and validity facts are compiled from this
single exact variable enclosure at the requested precision.
-/
noncomputable def rationalIcc
    (a b : ℚ) (hab : a ≤ b) (precision : Precision := {}) :
    CertifiedEvalRegistry
      (Set.Icc (a : ℝ) (b : ℝ))
      (fun x : ℝ ↦ !₂[x]) := by
  let input := RationalInterval.ofBounds a b hab
  let env : Fin 1 → RationalInterval := fun _ ↦ input
  exact
    CertifiedEvalRegistry.ofEnvironment env (by
      intro x hx i
      fin_cases i
      simpa [env, input] using
        RationalInterval.memReal_ofBounds hab hx) precision

/--
Compile nonvanishing of an explicit list of expressions on this registry's
chart.

The compiler may derive denominator and unary-range facts needed to evaluate
compound obligations, then accepts only provider proofs or sign-definite
certified enclosures.
-/
noncomputable def nonzeroOn?
    (r : CertifiedEvalRegistry s ρ)
    (exprs : List (Verified.Expr ι)) :
    Option
      (CertificateRoute
        (∀ x, x ∈ s → ∀ expr ∈ exprs, expr.eval (ρ x) ≠ 0)) := by
  let obligations := Verified.Expr.addList exprs
  match hcompiled : r.extendWithEasyFacts? obligations with
  | none => exact none
  | some compiled =>
      match hproof :
          CertifiedEvalContext.nonzeroListProof?
            compiled.toContext exprs with
      | none => exact none
      | some proof =>
          exact some
            { steps := compiled.toRoute.steps
              cert := proof.down }

/--
Compile a proof that `expr` is analytically valid throughout this registry's
chart.

The expression's authoritative `validityRequirements` supplies all obligations. The registry
first compiles any interval facts needed to evaluate those
obligations, then discharges nonzero and positivity lists separately, and
finally invokes `ValidityRequirements.validAt_of_holds`.
-/
noncomputable def validOn?
    (r : CertifiedEvalRegistry s ρ) (expr : Verified.Expr ι) :
    Option (CertificateRoute (∀ x, x ∈ s → expr.ValidAt (ρ x))) := by
  let requirements := expr.validityRequirements
  let obligations := Verified.Expr.addList (requirements.nonzero ++ requirements.positive)
  match hcompiled : r.extendWithEasyFacts? obligations with
  | none => exact none
  | some compiled =>
      match hnonzero :
          CertifiedEvalContext.nonzeroListProof?
            compiled.toContext requirements.nonzero,
        hpositive :
          CertifiedEvalContext.positiveListProof?
            compiled.toContext requirements.positive with
      | some nonzeroProof, some positiveProof =>
          exact some
            { steps := compiled.toRoute.steps
              cert := by
                intro x hx
                exact
                  Verified.Expr.ValidityRequirements.validAt_of_holds (ρ x) expr
                    ⟨nonzeroProof.down x hx, positiveProof.down x hx⟩ }
      | _, _ => exact none

/--
Compile analytic validity for every derivative level needed by an iterated
one-variable derivative theorem.

The recursion follows the symbolic derivative chain directly. The theorem
`Verified.Expr.diff_iteratedDiff` identifies that chain with the public
`ValidIteratesOn` indexing convention.
-/
noncomputable def validIteratesOn?
    {t : Set ℝ}
    (r : CertifiedEvalRegistry t
      (fun x : ℝ ↦ !₂[x]))
    (expr : Verified.Expr (Fin 1)) :
    (n : ℕ) → Option (CertificateRoute (expr.ValidIteratesOn n t))
  | 0 =>
      some
        { cert := by
            intro k hk
            omega }
  | n + 1 =>
      match hhead : r.validOn? expr,
        htail : r.validIteratesOn? (expr.diff (0 : Fin 1)) n with
      | some head, some tail =>
          some
            { steps := head.steps ++ tail.steps
              cert := by
                intro k hk x hx
                cases k with
                | zero =>
                    simpa using head.cert x hx
                | succ k =>
                    have hk' : k < n := Nat.succ_lt_succ_iff.mp hk
                    rw [← Verified.Expr.diff_iteratedDiff]
                    exact tail.cert k hk' x hx }
      | _, _ => none

end CertifiedEvalRegistry

/--
Infer iterated analytic validity on a closed interval with exact rational
endpoints.

Callers that bound ranges with exact rational intervals (`compileDerivative?`) and callers
that use `DigitsEval` (bare `cega` integration, `findRoot`) share this exact proof of the
analytic domain conditions; each proves its range enclosures with its own backend.
-/
noncomputable def validIteratesOnIcc?
    (expr : Verified.Expr (Fin 1)) (n : ℕ) (a b : ℚ)
    (hab : (a : ℝ) < (b : ℝ)) :
    Option
      (CertificateRoute
        (expr.ValidIteratesOn n (Set.Icc (a : ℝ) (b : ℝ)))) := by
  have habQ : a ≤ b := by
    exact_mod_cast hab.le
  let base :
      CertifiedEvalRegistry
        (Set.Icc (a : ℝ) (b : ℝ))
        (fun x : ℝ ↦ !₂[x]) :=
    CertifiedEvalRegistry.rationalIcc a b habQ
  exact base.validIteratesOn? expr n

end RationalInterval
end CAS.Continuum

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Validity
public import CAS.Continuum.SymbolicDerivativeBounds

/-!
# Compiled symbolic derivatives

A `CompiledDerivative expr order a b` is the `order`-th symbolic derivative of a univariate
expression on the rational panel `[a, b]`, prepared for numerical range evaluation. It consists
of

* a route proving analytic validity of `expr` and its symbolic derivatives through order
  `order` on the panel (`ValidIteratesOn (order + 1)`);
* a rational canonical form `expression` of the derivative, with proofs of the nonzero
  conditions emitted by canonicalization;
* the pointwise equality of the symbolic derivative and `expression` on the panel.

A range provider for `expression`, over any `RealIntervalBackend`, therefore bounds the
derivative without repeating differentiation, canonicalization or branch reasoning.

## Main definitions

* `CanonicalDerivative`, `CompiledDerivative`, `CompiledTaylorJet`: one canonical derivative,
  the same with analytic validity, and the derivatives of orders `0, …, order + 1` under one
  validity proof.
* `RationalInterval.compileDerivative?`, `RationalInterval.compileTaylorJet?`: the compilers,
  which return `none` when a check fails.
* `CompiledDerivative.bounder`: an `IteratedDerivativeBounderOn` built from any range provider
  for `expression`.

## Main results

* `CompiledDerivative.contDiffOn`: the source function is `C^order` on `[a, b]`.

## Implementation notes

We separate the exact work from the numerical work. `RationalInterval.compileDerivative?`
differentiates symbolically (`Verified.Expr.symbolicDerivative`), canonicalizes the result with
`Verified.Expr.RationalCanonical.route`, discharges the nonzero side conditions by exact rational
interval evaluation on `[a, b]`, and proves analytic validity with `validIteratesOnIcc?`. The
proofs are stored in the structure, so the kernel checks them once per panel. `bounder` then
needs only an enclosure of `expression` and transports it to `iteratedDerivWithin` through
`IteratedDerivativeBounderOn.ofExprWithRewrite`.
-/

@[expose] public section

open Set

namespace CAS.Continuum

open CAS
open CAS.Certificate
open CAS.Verified

/--
A checked canonical form of one symbolic derivative on a rational panel.

This object holds only exact symbolic work: rational canonicalization, its
generated side conditions, and the resulting semantic equality. Analytic
validity is kept separate so a family of derivative orders can share one
maximal validity certificate.
-/
structure CanonicalDerivative
    (expr : Verified.Expr (Fin 1)) (order : ℕ) (a b : ℚ) where
  /-- Canonical expression to evaluate numerically. -/
  expression : Verified.Expr (Fin 1)
  /-- Metadata of the exact simplification passes for the canonical expression. -/
  casSteps : List Verified.Expr.PassInfo := []
  /-- Route steps used to prove canonicalization side conditions. -/
  intervalSteps : List RouteStep := []
  /-- The canonical expression equals the requested symbolic derivative on the panel. -/
  sound :
    ∀ x ∈ Icc (a : ℝ) (b : ℝ),
      (expr.symbolicDerivative order).eval (!₂[x]) =
        expression.eval (!₂[x])

/--
A checked, analytically valid symbolic derivative on one rational panel.

The canonical expression, route metadata, and semantic rewrite are inherited
from `CanonicalDerivative`; this structure adds only strict panel orientation
and the shared analytic-validity route. `expression` is the expression numerical
backends should evaluate, while `sound` transports any enclosure of it back to
the derivative requested by the caller.
-/
structure CompiledDerivative
    (expr : Verified.Expr (Fin 1)) (order : ℕ) (a b : ℚ)
    extends CanonicalDerivative expr order a b where
  /-- The real panel is nondegenerate and positively oriented. -/
  ordered : (a : ℝ) < (b : ℝ)
  /-- Analytic validity through the derivative level required by Taylor theory. -/
  validity :
    CertificateRoute
      (expr.ValidIteratesOn (order + 1) (Icc (a : ℝ) (b : ℝ)))

namespace CanonicalDerivative

/-- Add an analytic-validity certificate to a canonical derivative. -/
def withValidity
    {expr : Verified.Expr (Fin 1)} {order : ℕ} {a b : ℚ}
    (canonical : CanonicalDerivative expr order a b)
    (ordered : (a : ℝ) < (b : ℝ))
    (validity :
      CertificateRoute
        (expr.ValidIteratesOn (order + 1) (Icc (a : ℝ) (b : ℝ)))) :
    CompiledDerivative expr order a b where
  toCanonicalDerivative := canonical
  ordered := ordered
  validity := validity

end CanonicalDerivative

namespace CompiledDerivative

/-- The source function is `C^order` on the compiled panel. -/
theorem contDiffOn
    {expr : Verified.Expr (Fin 1)} {order : ℕ} {a b : ℚ}
    (compiled : CompiledDerivative expr order a b) :
    ContDiffOn ℝ order expr.univariateEval
      (Icc (a : ℝ) (b : ℝ)) :=
  RationalInterval.contDiffOn_of_validIterates compiled.validity (uniqueDiffOn_Icc compiled.ordered)

/--
Turn any proved range provider for the canonical expression into bounds on
Mathlib's `iteratedDerivWithin`.

Quadrature uses this route. Numerical backends provide only an
enclosure of `compiled.expression`; the symbolic equality and analytic validity
are reused from the compiled derivative.
-/
noncomputable def bounder
    {expr : Verified.Expr (Fin 1)} {order : ℕ} {a b : ℚ}
    {I : Type*} [RealIntervalBackend I]
    (compiled : CompiledDerivative expr order a b)
    (provider :
      ExprRangeProviderOn (I := I) compiled.expression
        (fun x ↦ !₂[x])
        (Icc (a : ℝ) (b : ℝ))) :
    IteratedDerivativeBounderOn order expr.univariateEval
      (Icc (a : ℝ) (b : ℝ)) :=
  IteratedDerivativeBounderOn.ofExprWithRewrite
    expr compiled.expression order (Icc (a : ℝ) (b : ℝ))
    (compiled.validity.cert.mono (Nat.le_succ order))
    (fun x hx ↦ (compiled.sound x hx).symm)
    provider

/-- On `[l, r]` the bound is `max |lo| |hi|` of the provider's interval on `[l, r]`. -/
@[simp]
theorem bounder_bound
    {expr : Verified.Expr (Fin 1)} {order : ℕ} {a b : ℚ}
    {I : Type*} [RealIntervalBackend I]
    (compiled : CompiledDerivative expr order a b)
    (provider :
      ExprRangeProviderOn (I := I) compiled.expression
        (fun x ↦ !₂[x])
        (Icc (a : ℝ) (b : ℝ)))
    {l r : ℝ} (hlr : l < r)
    (hsub : Icc l r ⊆ Icc (a : ℝ) (b : ℝ)) :
    (compiled.bounder provider).bound hlr hsub =
      max
        |RealIntervalBackend.lo (provider.result hlr hsub)|
        |RealIntervalBackend.hi (provider.result hlr hsub)| := by
  unfold bounder
  exact
    IteratedDerivativeBounderOn.ofExprWithRewrite_bound
      expr compiled.expression order (Icc (a : ℝ) (b : ℝ))
      (compiled.validity.cert.mono (Nat.le_succ order))
      (fun x hx ↦ (compiled.sound x hx).symm)
      provider hlr hsub

/--
Evaluate a compiled derivative with the exact-rational evaluation registry
`RationalInterval.CertifiedEvalRegistry`.

The evaluator compiles only the already canonical `expression`; derivative
rules and canonicalization are not repeated in the numerical backend.
-/
noncomputable def enclosureAttempt?
    {expr : Verified.Expr (Fin 1)} {order : ℕ} {a b : ℚ}
    (compiled : CompiledDerivative expr order a b) :
    Option
      (RationalInterval.EnclosureAttempt ℝ
        (Icc (a : ℝ) (b : ℝ))
        (fun x ↦ (expr.symbolicDerivative order).eval (!₂[x]))) := by
  have habQ : a ≤ b := by
    exact_mod_cast compiled.ordered.le
  let base :=
    RationalInterval.CertifiedEvalRegistry.rationalIcc a b habQ
  match hregistry :
      base.extendWithEasyFacts? compiled.expression with
  | none => exact none
  | some registry =>
      match heval :
          registry.toContext.evalSimplified compiled.expression with
      | none => exact none
      | some result =>
          exact some
            { interval := result
              sound := by
                intro x hx
                change
                  result.MemReal
                    ((expr.symbolicDerivative order).eval
                      (!₂[x]))
                rw [compiled.sound x hx]
                exact
                  registry.toContext.sound_simplified
                    x hx compiled.expression result heval
              steps := compiled.intervalSteps ++ registry.toRoute.steps }

end CompiledDerivative

/--
A checked family of Taylor derivatives under one analytic-validity proof.

Orders `0, ..., order + 1` are canonicalized once. The single validity
certificate covers exactly those levels, so coefficient and remainder
backends can project the derivative they need without rerunning branch or
singularity analysis.
-/
structure CompiledTaylorJet
    (expr : Verified.Expr (Fin 1)) (order : ℕ) (a b : ℚ) where
  /-- The real panel is nondegenerate and positively oriented. -/
  ordered : (a : ℝ) < (b : ℝ)
  /-- Analytic validity through the remainder derivative. -/
  validity :
    CertificateRoute
      (expr.ValidIteratesOn (order + 2) (Icc (a : ℝ) (b : ℝ)))
  /-- Canonical derivatives from order zero through `order + 1`. -/
  derivatives :
    (k : Fin (order + 2)) → CanonicalDerivative expr k.val a b

namespace CompiledTaylorJet

/-- Project one derivative without repeating validity or canonicalization. -/
def derivative
    {expr : Verified.Expr (Fin 1)} {order : ℕ} {a b : ℚ}
    (jet : CompiledTaylorJet expr order a b)
    (k : Fin (order + 2)) :
    CompiledDerivative expr k.val a b := by
  exact
    (jet.derivatives k).withValidity jet.ordered
      (RationalInterval.lowerValidIterates jet.validity (by omega))

end CompiledTaylorJet

namespace RationalInterval

/--
Canonicalize one derivative and discharge every generated nonzero condition.

This helper performs no analytic-validity search. Callers that compile several
orders can therefore share one proof route for maximal iterated validity.
-/
noncomputable def compileCanonicalDerivative?
    (expr : Verified.Expr (Fin 1)) (order : ℕ) (a b : ℚ)
    (hab : a ≤ b) :
    Option (CanonicalDerivative expr order a b) := by
  let base := CertifiedEvalRegistry.rationalIcc a b hab
  let source := expr.symbolicDerivative order
  let route := Verified.Expr.RationalCanonical.route source
  match hside : base.nonzeroOn? route.nonzero with
  | none => exact none
  | some side =>
      exact some
        { expression := route.rhs
          casSteps := route.steps
          intervalSteps := side.steps
          sound := by
            intro x hx
            exact
              (Verified.Expr.RationalCanonical.route_sound
                source (!₂[x])
                (side.cert x hx)).symm }

/--
Compile canonical derivatives from order zero through `maxOrder`.

The dependent result keeps each expression indexed by its actual derivative
order, preventing a backend from attaching a proof to the wrong Taylor
coefficient.
-/
noncomputable def compileCanonicalDerivativesUpTo?
    (expr : Verified.Expr (Fin 1)) (maxOrder : ℕ) (a b : ℚ)
    (hab : a ≤ b) :
    Option
      ((k : Fin (maxOrder + 1)) →
        CanonicalDerivative expr k.val a b) := by
  match maxOrder with
  | 0 =>
      match compileCanonicalDerivative? expr 0 a b hab with
      | none => exact none
      | some derivative =>
          exact some
            (fun k ↦
              Fin.cases derivative (fun impossible ↦ Fin.elim0 impossible) k)
  | maxOrder + 1 =>
      match compileCanonicalDerivativesUpTo? expr maxOrder a b hab,
          compileCanonicalDerivative? expr (maxOrder + 1) a b hab with
      | some previous, some last =>
          exact some (fun k ↦ Fin.lastCases last previous k)
      | _, _ => exact none
termination_by maxOrder

/--
Compile one derivative for all verified interval backends.

The function fails closed. It returns `none` when the panel
crosses an analytic singularity, touches a strict `log`/`sqrt` branch
boundary, or cannot prove a nonzero condition introduced by rational
canonicalization.
-/
noncomputable def compileDerivative?
    (expr : Verified.Expr (Fin 1)) (order : ℕ) (a b : ℚ)
    (hab : (a : ℝ) < (b : ℝ)) :
    Option (CompiledDerivative expr order a b) := by
  have habQ : a ≤ b := by
    exact_mod_cast hab.le
  match hvalid :
      validIteratesOnIcc? expr (order + 1) a b hab with
  | none => exact none
  | some validity =>
      match hcanonical :
          compileCanonicalDerivative? expr order a b habQ with
      | none => exact none
      | some canonical =>
          exact some (canonical.withValidity hab validity)

/--
Compile all Taylor coefficient derivatives and the remainder derivative under
one maximal validity certificate.

The compiler is fail-closed: any analytic-domain failure or unproved
canonicalization side condition rejects the complete jet.
-/
noncomputable def compileTaylorJet?
    (expr : Verified.Expr (Fin 1)) (order : ℕ) (a b : ℚ)
    (hab : (a : ℝ) < (b : ℝ)) :
    Option (CompiledTaylorJet expr order a b) := by
  have habQ : a ≤ b := by
    exact_mod_cast hab.le
  match hvalid :
      validIteratesOnIcc? expr (order + 2) a b hab with
  | none => exact none
  | some validity =>
      match hderivatives :
          compileCanonicalDerivativesUpTo? expr (order + 1) a b habQ with
      | none => exact none
      | some derivatives =>
          exact some
            { ordered := hab
              validity := validity
              derivatives := derivatives }

end RationalInterval
end CAS.Continuum

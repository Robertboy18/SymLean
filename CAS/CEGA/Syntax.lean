/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.CEGA.Elaboration
public meta import CAS.CEGA.Elaboration

/-!
# CEGA tactic syntax

The syntax of the `cega` tactic family. The arguments of `cega` form the syntax category
`cegaArgs`, which `cega?` of `CAS.Reporting` parses too. The forms are

* `cega`, which projects a checked carrier, proves a bound on an interval integral by a checked
  batch quadrature, or infers a rational box from local hypotheses or from the domain of a
  certificate goal, and `cega using t`, which uses the supplied carrier `t`;
  `cega (prec := n) (depth := n) (panels := n)` sets the precision and subdivision depth of the
  inferred box query and the panel count of an integral bound;
* `cega [fast]`, which tries closed finite and polynomial certificates according to
  the `cega.nativeCertificates` checking profile;
* `cega (cfg) [enclose x in [a, b], ...] e`, the explicit box query, which proves the
  projection the goal needs: an enclosure, an upper bound, an absolute bound or a midpoint
  approximation.

In the explicit query form each binding `x in [a, b]` (syntax category
`cegaIntervalBinding`) gives a coordinate and its closed interval with rational endpoints.
The optional configuration group sets the precision policy, as in `(prec := 40)`, and
`(depth := n)` subdivides the box. The goal may be a certificate proposition (`EnclosedOn`,
`BoundOn`, `ApproxOn`) on the box or an ordinary inequality in the box variables, and the proof
is built from a kernel-checked certificate theorem.

## Implementation notes

We keep the grammar apart from the elaborators of `CAS.CEGA` because `CAS.Tactic.BoxInequality`,
which `CAS.CEGA` imports, builds replay suggestions from it: the bare call or the explicit query
that reproduces a proof (`BoxInequality.bareSyntax`, `BoxInequality.querySyntax`).
`CAS.Numerics.Tactic` adds `cega [batch := n]` and `cega [fast, batch := n]` to `cegaArgs`. Every
form ends in a theorem that the kernel checks; only the `fast` forms with
`cega.nativeCertificates = true` also trust Lean's compiler and runtime, through `nativeEqTrue`.
-/

public meta section

namespace CAS.CEGA

open Lean Elab Tactic Parser.Tactic
open CAS.CEGA.Elaboration

/-- The arguments of `cega`, shared with `cega?`. -/
declare_syntax_cat cegaArgs

/-- `cega` proves real inequalities on boxes, closed numerical bounds and bounds on interval
integrals from certificates that the kernel checks.

## Theorem
`cega` closes goals of these shapes, with closed bounds `a`, `b` and `c`:

- `f x ≤ c`, `f x < c`, `c ≤ f x`, `c < f x`, `|f x| ≤ c` and `|f x| < c`;
- `a ≤ f x ∧ f x ≤ b`, also with `<`, and `f x ∈ Set.Icc a b`, also with `Set.Ioo`, `Set.Ico`
  and `Set.Ioc`;
- `f x ≤ g x`, and conjunctions of these goals;
- bounds on one interval integral, such as `(∫ x in a..b, f x) ≤ c` and
  `|(∫ x in a..b, f x) - c| ≤ ε`, with rational limits;
- the certificate propositions `EnclosedOn`, `BoundOn` and `ApproxOn` on a box.

Every real variable is bounded by hypotheses `a ≤ x` and `x ≤ b`, `x ∈ Set.Icc a b` or
`|x| ≤ r` with rational literals; a goal without variables needs none.

## Conditions and limits
The box route encloses the expressions of the goal on the box of the hypotheses and compares the
enclosure with the bound by exact rational arithmetic; when the first enclosure is too weak, it
subdivides the box to depth 2. An integral bound uses Simpson panels when the domain checker
certifies the first four derivatives of the integrand on `[a, b]`, and otherwise range panels,
which need only continuity; the panel count doubles from 1 up to `cega.maxIntegrationPanels`.
`cega` also projects a registered checked carrier of the goal. A closed goal that these routes
refuse is tried with `dyadic_interval [cega_real, prec := n]` at 32 bits unless `(prec := n)` or
`(digits := d)` sets them, and a closed decidable proposition with a kernel certificate. The
functions are those of the grammar of `#cas [N d]`, written as Mathlib terms such as `Real.sin x`
and `Real.sqrt x`, and a box has at most 8 variables (`cega.maxDimension`). A false bound, or a
true one that the enclosures do not reach, is refused with the next call to try; for an integral
the message gives the interval that the panel search proposes.

## Options
- `(prec := n)`, `(expOrder := n)`, `(logTerms := n)` and `(sqrtDigits := n)` set the precision
  of the box query as in `#cas [enclose]`; `(prec := n)` also sets the bits of a closed goal.
- `(depth := n)` sets the depth of the subdivision tried after the first query, default 2.
- `(panels := n)` fixes the panel count of an integral bound; `(digits := d)` fixes its working
  precision.
- `set_option cega.maxIntegrationPanels n` caps the doubling of the panels, default 256.
- `set_option cega.nativeCertificates true` lets `cega [fast]` check finite certificates with
  compiled code, which also trusts Lean's compiler; the default `false` keeps every check in the
  kernel.

## Examples
```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.85 := by
  cega
```
```lean
example : Real.exp 1 ≤ 2.72 := by
  cega
```
```lean
example : (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 3 / 4 := by
  cega
```

## In a proof
```lean
theorem cega_sin_lt_one (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x < 1 := by
  have h : Real.sin x ≤ 17 / 20 := by cega
  linarith
```

## See also
Mathematica `Interval` and `NIntegrate`, SymPy `AccumBounds`. The tactics `cega?` and `cas`,
which tries `cega` on ordinary inequalities, and the modes `enclose`, `nintegrate` and `N`.

## Possible issues
```lean
example (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.sin x ≤ 0.8 := by
  cega
```
```output
cega box route: comparison with the stated bound: the certified value does not give the stated
bound.
```
The bound is false, since `Real.sin 1 > 0.84`. For a true bound that the enclosure misses, the
message proposes `cega (depth := 4)` or `cega (prec := 24)`.
```lean
example (x : ℝ) : Real.sin x ≤ 1.5 := by
  cega
```
```output
cega box route: no rational bounds on `x` in the hypotheses; the route needs hypotheses `a ≤ x` and
`x ≤ b`, `x ∈ Set.Icc a b`, or `|x| ≤ r` with rational literal endpoints
```
Add bounds on `x` as hypotheses. A bound for every `x`, as here, follows from Mathlib's
`Real.sin_le_one`.
-/
syntax (name := tacticCega) "cega" (cegaArgs)? : tactic

/-- The argument of `cega using carrier`. -/
syntax (name := cegaUsing) " using " term : cegaArgs

/-- The argument of `cega [fast]`. -/
syntax (name := cegaFast) " [" &"fast" "]" : cegaArgs

/--
`cega [fast]`

Try closed finite and polynomial certificates under the `cega.nativeCertificates` checking
profile, then the kernel route of bare `cega`. A native certificate also trusts Lean's compiler
and runtime; with the default profile, `cega.nativeCertificates = false`, it is bare `cega`.
-/
tactic_extension tacticCega

/-- The configuration items of `cega (prec := n) (depth := n) (panels := n)`. -/
syntax (name := cegaConfigured) (colGt Lean.Parser.Term.configItem)+ : cegaArgs

/--
`cega (prec := n) (depth := n) (panels := n)`

Bare `cega` with a precision policy for its box route: `(prec := n)` and the other items of the
explicit form set the precision of the query, and `(depth := n)` the depth of the subdivision
that bare `cega` tries when the first query does not prove the bound (two by default). As in the
explicit form, depth zero still bisects the box once. On an interval integral, `(panels := n)`
fixes the number of quadrature panels, which otherwise doubles from one until the bound holds,
up to the option `cega.maxIntegrationPanels`.
-/
tactic_extension tacticCega

/-- The arguments of the explicit box query `cega (cfg) [enclose bindings] expr`. -/
syntax (name := cegaEnclose)
  Lean.Parser.Term.optConfig " [" &"enclose" cegaIntervalBinding,* "] " term : cegaArgs

/--
`cega [enclose ...] expr`

Synthesize a certificate for `expr` on an exact rational box and use it to close the current
goal. The goal selects the projection: an enclosure for `EnclosedOn f s lo hi`, an upper bound
for `BoundOn f s c`, an absolute bound for `BoundOn (fun x ↦ |f x|) s c`, a midpoint
approximation for `ApproxOn f (fun _ ↦ c) s ε`, and the bound an ordinary goal on the box's
variables states (`f x ≤ c`, `c ≤ f x`, `|f x| ≤ c`, `a ≤ f x ∧ f x ≤ b`, `f x ∈ Set.Icc a b`).
The optional configuration group, for example `(prec := 40)`, selects the numerical precision
policy, and `(depth := n)` encloses after `n` levels of checked box refinement. An empty
coordinate list, as in `cega [enclose] Real.sqrt 2`, queries a closed expression.
-/
tactic_extension tacticCega

end CAS.CEGA

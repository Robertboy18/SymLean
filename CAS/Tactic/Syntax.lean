/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public meta import Lean.Elab.Tactic.Doc

/-!
# Shared syntax for the computer algebra tactics

`cas` takes its arguments from the syntax category `casArgs`, and `cas?` parses the same
category, so every form of `cas` has a reporting twin. A frontend adds a form as a production of
`casArgs`, an elaborator for it and a `tactic_extension` entry that documents it. The tactic and
its core forms are declared here, apart from their routes, so that a frontend can refer to them
without loading the routes.
-/

public meta section

namespace CAS.ExactTactic

/-- The arguments of `cas` and `cas?`. -/
declare_syntax_cat casArgs

/-- `cas` proves the goal by computer algebra whose steps the kernel checks: identities, ideal
memberships, determinants, derivatives, integrals, the theorems of the `#cas` commands and
inequalities on bounded real variables.

## Theorem
`cas` closes the goal and proves no other statement. It closes goals of these shapes:

- an equality, disequality or order relation of ordinary terms that Mathlib's `field_simp`,
  `ring`, `norm_num`, `positivity`, `linarith` and `nlinarith` prove, and a real equality that the
  checked symbolic normalizer proves, such as `Real.sin x ^ 2 + Real.cos x ^ 2 = 1`;
- `Ideal.span {f₁, …, fₘ} = Ideal.span {g₁, …, gₖ}` and `f ∈ Ideal.span {g₁, …, gₘ}` in a
  commutative ring, with cofactors from a Gröbner basis that `ring` checks;
- the Gröbner property `∀ p ∈ Ideal.span S, p ≠ 0 → ∃ g ∈ S, MonomialOrder.lex.leadingTerm g ∣
  MonomialOrder.lex.leadingTerm p` of a set literal `S` in `MvPolynomial (Fin n) ℚ`, by
  Buchberger's criterion from divisions of its S-polynomials that the kernel checks;
- a goal with determinants `Matrix.det A` of matrix literals, which `cas` evaluates first;
- `deriv f x = e`, `HasDerivAt f e x`, `HasDerivWithinAt f e s x`, `DifferentiableAt ℝ f x`,
  and `iteratedDeriv n f x = e` and `iteratedDerivWithin n f s x = e` of a literal order `n`,
  nested derivatives such as `deriv (fun x ↦ deriv f x) x` included, by checked derivative rules;
- `Differentiable`, `DifferentiableOn`, `ContDiffAt`, `ContDiffOn`, `ContDiff`, `ContinuousAt`,
  `ContinuousOn`, `Continuous`, `AnalyticAt` and `AnalyticOnNhd` over `ℝ`, by checked derivative
  and smoothness theorems; continuity, differentiability on a set and analyticity are the
  smoothness theorem at the orders `0`, `1` and `ω`;
- `(∫ x in a..b, f x) = v` and improper integrals such as `(∫ t in Set.Ioi 0, f t) = v`, also
  with their convergence, `IntegrableOn f (Set.Ioi 0) ∧ ∫ t in Set.Ioi 0, f t = v`, by the
  checked integration planner, which applies an analytic theorem, one integration by parts or a
  checked primitive;
- `Set.EqOn f g s`, and `ApproxOn` and `ResidualBound` with zero error, pointwise on ordinary
  functions;
- the printed theorems of the `#cas` commands: algebra, matrix and number theory results, limits
  at a rational point and at `atTop` and `atBot`, polynomial sign conditions and counts of real
  roots;
- an inequality on real variables bounded by rational literal hypotheses, by the box route of
  `cega`.

## Conditions and limits
The routes run in the order that `CAS.ExactTactic.routeOrder` lists: determinants, ideals, the
theorems of the `#cas` commands, derivatives, integrals, the checked evaluator, the arithmetic
script, equation hints and polynomial consequences of equation hypotheses, the checked identity
route, the box route, the elementary rewrites (multiple-angle formulas, the exponential of a
multiple of a logarithm and sums of real exponents, under the hypotheses they need), `norm_num` on
a proposition without variables, and `grind` last, under the budget `cas.grindHeartbeats`. Other
modules add routes with `@[cas_route]`, and derivative backends for the Euclidean operators with
`@[cas_derivative_backend]`. Every route checks its proof against the original goal.
A derivative or an integral whose function needs a domain condition, such as `x ≠ 0` for
`Real.log x`, takes the evidence from `cas using h`; a nested derivative needs it only at the
point. When every route fails, the goal is unchanged and the message lists what each route
tried; the failure does not show that the goal is false.

## Options
- `set_option cas.grindHeartbeats n` sets the budget, in thousands of heartbeats, of the `grind`
  and `norm_num` fallbacks, default `20000`; `0` turns them off.
- `set_option cas.maxDerivativeSteps n` caps the recursive steps of the derivative rules, default
  `512`.
- `set_option trace.cas.fallback true` shows the diagnostics of the `grind` fallback.
- The forms `cas using h`, `cas using [h₁, h₂]`, `cas [l₁, l₂]` and
  `cas [integrate primitive := F]`, each documented in its own entry, pass domain evidence, local
  facts, simp lemmas and a primitive to the routes.

## Examples
```lean
example (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
  cas
```
```lean
example (x : ℝ) (hx : x ≠ 0) : deriv (fun t : ℝ ↦ t * Real.log t) x = Real.log x + 1 := by
  cas using hx
```
```lean
example : (∫ x in (0 : ℝ)..1, x * Real.exp x) = 1 := by
  cas
```
```lean
example : AnalyticAt ℝ (fun x ↦ Real.exp (Real.sin x) / (1 + x ^ 2)) 0 := by
  cas
```
```lean
open Filter Topology in
example : Tendsto (fun x : ℝ ↦ (x ^ 2 + 1) / (2 * x ^ 2 - 3)) atTop (𝓝 (1 / 2)) := by
  cas
```

## In a proof
```lean
theorem exp_lt_four (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : Real.exp x < 4 := by
  have h : Real.exp x ≤ 3 := by cas
  linarith
```
The box route proves the bound from the hypotheses on `x`, and `linarith` uses it.

## See also
Mathematica `FullSimplify` and `Reduce`, SymPy `simplify`. The tactics `cas?`, which suggests the
call to keep in a proof, `cas_nf` and `cega`, and the `#cas` modes, whose printed theorems `cas`
proves.

## Possible issues
```lean
example (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 2 := by
  cas
```
```output
cas could not prove this arithmetic relation. The statement may be false, or it may lie outside
the supported normalization and arithmetic fragment
```
Here the statement is false. The rest of the message lists what each route tried, such as the
difference `-1` of the two sides that the checked normalizer computed.
```lean
example (x : ℝ) : deriv (fun x ↦ x ^ 2) x = 3 * x := by
  cas
```
```output
cas computed a checked derivative, but it does not match the stated result.
```
`#cas [derive x] (x ^ 2)` prints the derivative that the route computed.
```lean
example (x : ℝ) : Real.exp x ≥ x + 1 := by
  cas
```
```output
Box enclosure route:
  cas box route: no rational bounds on `x` in the hypotheses
```
Hypotheses `a ≤ x` and `x ≤ b` with rational literals give the box route a box. For every real
`x`, Mathlib's `Real.add_one_le_exp x` proves this goal.
-/
syntax (name := tacticCas) "cas" (ppSpace casArgs)? : tactic

/-- `cas using h` passes side evidence to the routes. -/
syntax (name := casUsing) "using " term : casArgs

/-- `cas using [h₁, h₂]` adds complete proofs as local facts. -/
syntax (name := casUsingFacts) (priority := high) "using " "[" term,+ "]" : casArgs

/-- `cas [l₁, l₂]` passes local simp lemmas. -/
syntax (name := casLemmas) "[" Lean.Parser.Tactic.simpLemma,* "]" : casArgs

/-- `cas using h` proves the goal with the side evidence `h`. On a semantic target `h`
discharges the side conditions the route emits; on a derivative or integral goal it is the
analytic domain evidence (a nonzero, positivity or branch hypothesis, or a
`Verified.Expr.ValidAt` proof on the reflected route). Independently elaborated propositions are
noted as local facts for the arithmetic and domain solvers, including applied proofs such as
`h 0`. On an ordinary arithmetic goal the hint also enters the simp set and is evidence for the
conditions recorded by the checked identity route. Juxtaposed complete proof hints are conjoined
when they cannot elaborate as a single application; parentheses force a single term. -/
tactic_extension tacticCas

/-- `cas using [h₁, h₂]` proves the goal with a list of complete proposition proofs as local
facts. Inequalities and other propositions support arithmetic and domain discharge; only
matching equalities are passed as hints to polynomial consequence search. The list contains
proof terms, not simp directives, and incomplete evidence is rejected even when redundant. -/
tactic_extension tacticCas

/-- `cas [l₁, l₂]` proves the goal with the listed local simp lemmas, which the reflected
symbolic route and the arithmetic script of ordinary goals use. The arithmetic script also runs
on a reflected equality that the reflected route does not prove, so lemmas such as
`Verified.Expr.eval` can unfold its evaluations there. Before any route runs, the lemmas are
elaborated as `simp only [l₁, l₂]` elaborates them, so an unknown name fails at once. -/
tactic_extension tacticCas

end CAS.ExactTactic

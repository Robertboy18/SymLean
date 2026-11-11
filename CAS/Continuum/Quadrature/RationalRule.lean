/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.RationalEvaluation
public import CAS.Continuum.Quadrature.Rule

/-!
# Executable rational quadrature rules

`QuadratureRule` is the analytic semantics of a normalized rule and stores real
weights and nodes. `RationalQuadratureRule` is an exact executable
representation for the case in which all of those constants are rational.

`RationalQuadratureRule.toQuadratureRule` forgets the rational data to give the real rule, and
exact rational sampling casts to `QuadratureRule.termsOn` and `QuadratureRule.valueOn`.

## Main results

* `RationalQuadratureRule.cast_valueOn`: exact rational evaluation of a rule
  against a total callback casts to the real `valueOn`.
* `RationalQuadratureRule.termsOn?_sound`: for a partial (fail-closed) callback,
  every successfully sampled table casts to the real `termsOn`.
* `RationalQuadratureRule.symbolicTermsOn?_sound`: evaluating a `Verified.Expr`
  at rational nodes through `evalRat?` agrees with the real denotation of the
  expression, with the integration variable updated in the environment.

## Implementation notes

`QuadratureRule.termsOn` and `QuadratureRule.valueOn` are stated for real rules, so we define
the rational ones again over `ℚ`. They are ordinary computable functions: each node moves to
`a + ξ (b - a)`, each weight is scaled by `b - a`, and `weightedSum` adds the products in list
order. `cast_weightedSum` is an induction on the term list, and since `toQuadratureRule` casts
every pair, `map_termsOn_eq_termsOn` matches the rational table with the real one term by term.

`termsOn?` samples a callback `ℚ → Option ℚ` node by node through `compileTerms?` and returns
`none` as soon as one sample fails, so a table is complete or absent. `termsOn?_sound` turns an
equation `termsOn? f a b = some terms`, however it was established, into the real table.
`symbolicTermsOn?` takes the callback from `Verified.Expr.evalRat?`, which fails outside the
rational fragment: on `π`, `e`, the elementary functions, real powers, and division by zero,
including a literal with denominator zero. `evalExprAt?_sound` carries
`Verified.Expr.evalRat?_sound` along `Function.update`. Within SymLean no module samples a
rational rule, and only `CAS.Continuum.Quadrature.RationalComposite` imports these definitions.
-/

@[expose] public section

namespace CAS.Continuum

/-- Cast an exact rational weight-value or weight-node pair to real numbers. -/
def rationalPairToReal (term : ℚ × ℚ) : ℝ × ℝ :=
  ((term.1 : ℝ), (term.2 : ℝ))

/--
An ordered normalized quadrature rule whose weights and nodes are exact
rationals.
-/
abbrev RationalQuadratureRule :=
  NormalizedQuadratureRule ℚ

namespace RationalQuadratureRule

/-- Forget an executable rational rule to the exact-real rule. -/
noncomputable def toQuadratureRule (rule : RationalQuadratureRule) :
    QuadratureRule where
  terms := rule.terms.map rationalPairToReal
  nodes_mem_unit := by
    intro term hterm
    simp only [List.mem_map] at hterm
    obtain ⟨source, hsource, rfl⟩ := hterm
    have hnode := rule.nodes_mem_unit source hsource
    change (0 : ℝ) ≤ (source.2 : ℝ) ∧ (source.2 : ℝ) ≤ 1
    exact ⟨by exact_mod_cast hnode.1, by exact_mod_cast hnode.2⟩

/--
Exact rational terms obtained by transporting a normalized rule to `a..b`.

The callback is an ordinary exact rational function. The partial symbolic
front end `symbolicTermsOn?` supplies such values only after checked evaluation succeeds.
-/
def termsOn (rule : RationalQuadratureRule) (f : ℚ → ℚ) (a b : ℚ) :
    List (ℚ × ℚ) :=
  rule.terms.map fun term ↦
    ((b - a) * term.1, f (a + term.2 * (b - a)))

/-- Exact rational value of a transported rational rule. -/
def valueOn (rule : RationalQuadratureRule) (f : ℚ → ℚ) (a b : ℚ) : ℚ :=
  weightedSum (rule.termsOn f a b)

/-- Casting an exact rational weighted sum gives the real weighted sum. -/
theorem cast_weightedSum (terms : List (ℚ × ℚ)) :
    ((weightedSum terms : ℚ) : ℝ) =
      weightedSum (terms.map rationalPairToReal) := by
  induction terms with
  | nil => simp [weightedSum]
  | cons term terms ih =>
      rw [weightedSum_cons, Rat.cast_add, Rat.cast_mul, ih]
      rfl

/--
Transporting and sampling a rational rule agrees term-for-term with the
real `QuadratureRule` semantics.
-/
theorem map_termsOn_eq_termsOn
    (rule : RationalQuadratureRule) (f : ℚ → ℚ) (g : ℝ → ℝ)
    (a b : ℚ) (hf : ∀ x : ℚ, g (x : ℝ) = (f x : ℝ)) :
    (rule.termsOn f a b).map rationalPairToReal =
      rule.toQuadratureRule.termsOn g (a : ℝ) (b : ℝ) := by
  unfold termsOn toQuadratureRule QuadratureRule.termsOn
  simp only [List.map_map]
  refine List.map_congr_left fun term _ ↦ ?_
  simp [rationalPairToReal, ← hf]

/-- Exact rational rule evaluation casts to `QuadratureRule.valueOn`. -/
theorem cast_valueOn
    (rule : RationalQuadratureRule) (f : ℚ → ℚ) (g : ℝ → ℝ)
    (a b : ℚ) (hf : ∀ x : ℚ, g (x : ℝ) = (f x : ℝ)) :
    ((rule.valueOn f a b : ℚ) : ℝ) =
      rule.toQuadratureRule.valueOn g (a : ℝ) (b : ℝ) := by
  rw [valueOn, cast_weightedSum, map_termsOn_eq_termsOn rule f g a b hf]
  rfl

/--
Transport and sample an ordered rational term list with a partial exact
callback. This is the list-level worker used by `termsOn?`.
-/
def compileTerms? (f : ℚ → Option ℚ) (a b : ℚ) :
    List (ℚ × ℚ) → Option (List (ℚ × ℚ))
  | [] => some []
  | term :: terms => do
      let value ← f (a + term.2 * (b - a))
      let tail ← compileTerms? f a b terms
      pure (((b - a) * term.1, value) :: tail)

/--
Sample a partial exact-rational function at every transported rule node.

The order of the source rule is retained. If any sample fails, the whole
quadrature table fails closed.
-/
def termsOn? (rule : RationalQuadratureRule)
    (f : ℚ → Option ℚ) (a b : ℚ) : Option (List (ℚ × ℚ)) :=
  compileTerms? f a b rule.terms

private theorem compileTerms?_sound
    (f : ℚ → Option ℚ) (g : ℝ → ℝ) (a b : ℚ)
    (hf : ∀ x q, f x = some q → g (x : ℝ) = (q : ℝ))
    {source output : List (ℚ × ℚ)}
    (houtput : compileTerms? f a b source = some output) :
    output.map rationalPairToReal =
      (source.map rationalPairToReal).map fun term ↦
        (((b : ℝ) - a) * term.1,
          g ((a : ℝ) + term.2 * ((b : ℝ) - a))) := by
  induction source generalizing output with
  | nil =>
      cases houtput
      rfl
  | cons term terms ih =>
      simp only [compileTerms?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at houtput
      obtain ⟨value, hvalue, tail, htail, rfl⟩ := houtput
      rw [List.map_cons, ih htail]
      congr 1
      simp only [rationalPairToReal, Rat.cast_mul, Rat.cast_sub, Prod.mk.injEq, true_and]
      simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_sub] using (hf _ value hvalue).symm

/--
Every successfully sampled rational table is the real transported
quadrature table.
-/
theorem termsOn?_sound
    (rule : RationalQuadratureRule)
    (f : ℚ → Option ℚ) (g : ℝ → ℝ) (a b : ℚ)
    (hf : ∀ x q, f x = some q → g (x : ℝ) = (q : ℝ))
    {terms : List (ℚ × ℚ)}
    (hterms : rule.termsOn? f a b = some terms) :
    terms.map rationalPairToReal =
      rule.toQuadratureRule.termsOn g (a : ℝ) (b : ℝ) := by
  unfold termsOn? at hterms
  simpa [toQuadratureRule, QuadratureRule.termsOn, List.map_map] using
    compileTerms?_sound f g a b hf hterms

/-- Evaluate a symbolic expression at a rational value of one selected variable. -/
def evalExprAt? {ι : Type*} [DecidableEq ι]
    (expr : Verified.Expr ι) (coordinate : ι) (ρ : ι → ℚ) (x : ℚ) :
    Option ℚ :=
  expr.evalRat? (Function.update ρ coordinate x)

private theorem cast_update {ι : Type*} [DecidableEq ι]
    (ρ : ι → ℚ) (coordinate : ι) (x : ℚ) :
    (fun i ↦ ((Function.update ρ coordinate x i : ℚ) : ℝ)) =
      Function.update (fun i ↦ (ρ i : ℝ)) coordinate (x : ℝ) :=
  Function.comp_update (fun q : ℚ ↦ (q : ℝ)) ρ coordinate x

/-- Successful symbolic point evaluation agrees with the real expression semantics. -/
theorem evalExprAt?_sound {ι : Type*} [DecidableEq ι]
    (expr : Verified.Expr ι) (coordinate : ι) (ρ : ι → ℚ)
    {x q : ℚ} (h : evalExprAt? expr coordinate ρ x = some q) :
    expr.eval
        (Function.update (fun i ↦ (ρ i : ℝ)) coordinate (x : ℝ)) =
      (q : ℝ) := by
  unfold evalExprAt? at h
  rw [← cast_update ρ coordinate x]
  exact Verified.Expr.evalRat?_sound _ h

/--
Compile a univariate symbolic expression directly to exact rational
quadrature terms.

Variables other than `coordinate` retain their rational values from `ρ`.
-/
def symbolicTermsOn? {ι : Type*} [DecidableEq ι]
    (rule : RationalQuadratureRule) (expr : Verified.Expr ι)
    (coordinate : ι) (ρ : ι → ℚ) (a b : ℚ) :
    Option (List (ℚ × ℚ)) :=
  rule.termsOn? (evalExprAt? expr coordinate ρ) a b

/--
Successful symbolic compilation produces exactly the real
quadrature table for the expression's real denotation.
-/
theorem symbolicTermsOn?_sound {ι : Type*} [DecidableEq ι]
    (rule : RationalQuadratureRule) (expr : Verified.Expr ι)
    (coordinate : ι) (ρ : ι → ℚ) (a b : ℚ)
    {terms : List (ℚ × ℚ)}
    (hterms : rule.symbolicTermsOn? expr coordinate ρ a b = some terms) :
    terms.map rationalPairToReal =
      rule.toQuadratureRule.termsOn
        (fun x ↦ expr.eval
          (Function.update (fun i ↦ (ρ i : ℝ)) coordinate x))
        (a : ℝ) (b : ℝ) :=
  rule.termsOn?_sound
    (evalExprAt? expr coordinate ρ)
    (fun x ↦ expr.eval
      (Function.update (fun i ↦ (ρ i : ℝ)) coordinate x))
    a b
    (fun _ _ h ↦ evalExprAt?_sound expr coordinate ρ h)
    hterms

end RationalQuadratureRule
end CAS.Continuum

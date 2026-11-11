/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Simplify

/-!
# Structural decomposition of verified expressions

`productFactors`, `additiveTerms` and `signedAdditiveTerms` flatten associative expression
nodes into ordered term lists, and the rebuilding functions turn such lists back into
expressions.

The flattening functions preserve the original left-to-right order; they do
not sort factors or invoke commutativity. The rebuilding functions have
separate names because they produce different syntax:

* `mkMulList` and `mkAddList` use the basic smart constructors;
* `simplifyMulList` uses `simplifyMul`, which also moves negations and quotients out of each
  product;
* the raw `addList` and `mulList` folds in `CAS.Expr.Syntax` preserve
  constructors and are used where no local normalization is intended.

All three reconstruction policies have the same real-valued semantics. Search
procedures may inspect their syntax; proofs use the evaluation lemmas `eval_mkMulList`,
`eval_simplifyMulList`, `eval_mkAddList`, `eval_mkMulList_productFactors`, and
`eval_mkAddList_additiveTerms`.

`removeFactor?` deletes the first occurrence of a factor from a factor list, and
`eval_prod_removeFactor?` gives the corresponding factorization of the product of the values.
-/

@[expose] public section

namespace CAS

namespace Verified.Expr

/--
Flatten multiplication nodes into their factors in left-to-right order.

Only `.mul` nodes are traversed. In particular, powers and divisions remain
single factors because expanding either would change the decomposition used by
factor extraction and integration planning.
-/
def productFactors {ι : Type*} : Verified.Expr ι → List (Verified.Expr ι)
  | .mul left right => productFactors left ++ productFactors right
  | expr => [expr]

/-- Flatten addition nodes into their summands in left-to-right order. -/
def additiveTerms {ι : Type*} : Verified.Expr ι → List (Verified.Expr ι)
  | .add left right => additiveTerms left ++ additiveTerms right
  | expr => [expr]

/--
Flatten addition, subtraction, and negation into an ordered list of signed
summands.

This is the decomposition used by antiderivative search. `mkNeg` normalizes a
double negation while preserving the denotation of every emitted term.
-/
def signedAdditiveTerms {ι : Type*} : Verified.Expr ι → List (Verified.Expr ι)
  | .add left right => signedAdditiveTerms left ++ signedAdditiveTerms right
  | .sub left right =>
      signedAdditiveTerms left ++ (signedAdditiveTerms right).map mkNeg
  | .neg expr => (signedAdditiveTerms expr).map mkNeg
  | expr => [expr]

/-- Rebuild an ordered product with the basic smart multiplication constructor. -/
def mkMulList {ι : Type*} : List (Verified.Expr ι) → Verified.Expr ι
  | [] => .nat 1
  | factor :: rest => mkMul factor (mkMulList rest)

/--
Rebuild an ordered product while normalizing signs at each multiplication
node.
-/
def simplifyMulList {ι : Type*} : List (Verified.Expr ι) → Verified.Expr ι
  | [] => .nat 1
  | factor :: rest => simplifyMul factor (simplifyMulList rest)

/-- Rebuild an ordered sum with the basic smart addition constructor. -/
def mkAddList {ι : Type*} : List (Verified.Expr ι) → Verified.Expr ι
  | [] => .nat 0
  | term :: rest => mkAdd term (mkAddList rest)

/-- A product rebuilt with `mkMulList` evaluates to the product of the factor values. -/
@[simp] theorem eval_mkMulList {ι : Type*} (ρ : ι → ℝ)
    (factors : List (Verified.Expr ι)) :
    (mkMulList factors).eval ρ =
      (factors.map fun factor ↦ factor.eval ρ).prod := by
  induction factors with
  | nil => simp [mkMulList]
  | cons factor rest ih => simp [mkMulList, ih]

/-- Sign normalization in `simplifyMulList` does not change the value: the result still
evaluates to the product of the factor values. -/
@[simp] theorem eval_simplifyMulList {ι : Type*} (ρ : ι → ℝ)
    (factors : List (Verified.Expr ι)) :
    (simplifyMulList factors).eval ρ =
      (factors.map fun factor ↦ factor.eval ρ).prod := by
  induction factors with
  | nil => simp [simplifyMulList]
  | cons factor rest ih => simp [simplifyMulList, ih]

/-- Flattening an expression into its factors and rebuilding the product is a semantic
identity. Only `.mul` nodes are flattened, so this holds for every constructor. -/
theorem eval_mkMulList_productFactors {ι : Type*} (ρ : ι → ℝ)
    (expr : Verified.Expr ι) :
    (mkMulList (productFactors expr)).eval ρ = expr.eval ρ := by
  induction expr with
  | mul left right hleft hright => simp [productFactors, ← hleft, ← hright]
  | _ => simp [productFactors, mkMulList]

/-- A sum rebuilt with `mkAddList` evaluates to the sum of the term values. -/
@[simp] theorem eval_mkAddList {ι : Type*} (ρ : ι → ℝ)
    (terms : List (Verified.Expr ι)) :
    (mkAddList terms).eval ρ =
      (terms.map fun term ↦ term.eval ρ).sum := by
  induction terms with
  | nil => simp [mkAddList]
  | cons term rest ih => simp [mkAddList, ih]

/-- Flattening an expression into its summands and rebuilding the sum is a semantic identity.
Only `.add` nodes are flattened; subtraction and negation are left intact (compare
`signedAdditiveTerms`). -/
theorem eval_mkAddList_additiveTerms {ι : Type*} (ρ : ι → ℝ)
    (expr : Verified.Expr ι) :
    (mkAddList (additiveTerms expr)).eval ρ = expr.eval ρ := by
  induction expr with
  | add left right hleft hright => simp [additiveTerms, ← hleft, ← hright]
  | _ => simp [additiveTerms, mkAddList]

/-- Remove the first occurrence of `factor` from a list of factors, if it occurs. -/
def removeFactor? {ι : Type*} [DecidableEq ι] (factor : Verified.Expr ι) :
    List (Verified.Expr ι) → Option (List (Verified.Expr ι))
  | [] => none
  | head :: rest =>
      if head = factor then some rest
      else (removeFactor? factor rest).map (head :: ·)

/-- Removing a factor from a list splits the product of the values:
`factor * prod rest = prod factors`. -/
theorem eval_prod_removeFactor? {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (factor : Verified.Expr ι) :
    ∀ (factors rest : List (Verified.Expr ι)), removeFactor? factor factors = some rest →
      factor.eval ρ * (rest.map fun f ↦ f.eval ρ).prod = (factors.map fun f ↦ f.eval ρ).prod
  | [], _, h => by simp [removeFactor?] at h
  | head :: tail, rest, h => by
    simp only [removeFactor?] at h
    split_ifs at h with hhead
    · subst hhead
      cases Option.some.inj h
      simp
    · obtain ⟨rest', hrec, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [List.map_cons, List.prod_cons]
      linear_combination head.eval ρ * eval_prod_removeFactor? ρ factor tail rest' hrec

end Verified.Expr

end CAS

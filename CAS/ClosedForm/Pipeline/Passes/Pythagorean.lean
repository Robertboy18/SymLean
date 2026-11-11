/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.Decomposition
public import CAS.ClosedForm.Pipeline.Core

/-!
# Pythagorean normal form for cosine squares

The side pass that gives the checked normalizer the identity `sin u ^ 2 + cos u ^ 2 = 1` in
every arrangement of its terms within the polynomial part of an expression. The polynomial
normalizer treats `sin u` and `cos u` as unrelated atoms, and the `trig` pass of the base
pipeline recognizes the identity only when a sine square and a cosine square are the two
summands of one sum node. This pass eliminates cosine squares instead: pairs of factors `cos u`
in a product and powers `cos u ^ n` with `n ≥ 2` are replaced, one pair per node in each round
of the pipeline, through `cos u ^ 2 = 1 - sin u ^ 2` (`Real.cos_sq'`), after which the
polynomial normalizer sees an identity in the single atom `sin u`. Denominators, radicands,
logarithm arguments and real powers are left unchanged (`pythagoreanRewrite`).

## Main definitions

* `cosineSquareNormalForm`: `1 - sin u ^ 2`, the replacement of `cos u ^ 2`.
* `cosinePair?`: a pair of factors `cos u` in the factor list of a product.
* `pythagoreanTop`: the rewrite of one product or power node.
* `pythagoreanRewrite`: the positional traversal.
* `pythagoreanSidePass`: the pass, named `pythagorean`.

## Main results

* `eval_pythagoreanTop`, `eval_pythagoreanRewrite`: the rewrites preserve evaluation
  unconditionally.

## Implementation notes

We eliminate cosine and keep sine. The checked integrator runs this same pass on its
power-reduction residuals (`CAS.Integration.TrigNormalization`), so it makes the same choice.
Both orientations of a stated identity close, since the difference of the two sides is rewritten
as a whole.

At a product node the rewrite looks for the first factor `cos u` that occurs twice in the factor
list (`productFactors`) and returns the product of the remaining factors times `1 - sin u ^ 2`;
a power `cos u ^ (n + 2)` becomes `cos u ^ n * (1 - sin u ^ 2)`. One pair is replaced per node,
and the traversal and the iteration of the pipeline repeat the rewrite. The traversal descends
through sums, differences, negations, products, natural powers, the numerator of a quotient, and
the arguments of `sin`, `cos`, `atan`, `asin`, `acos`, and `exp`. It leaves denominators,
radicands, logarithm arguments, and real powers unchanged: the side passes record their
obligations from those subterms, and a recorded condition keeps the shape of the hypothesis that
discharges it (`cos x ≠ 0` for a quotient by `cos x ^ 2`, not `1 - sin x ^ 2 ≠ 0`).

The rewrite only removes cosine squares, and the `trig` pass only turns sums of a sine square and
a cosine square into numerals, so the two passes do not undo each other; the fuel of the pipeline
bounds the iteration in any case. The pass records no obligation.
-/

@[expose] public section

namespace CAS.Verified.Expr

/-- The replacement of a cosine square: `1 - sin u ^ 2`. -/
def cosineSquareNormalForm {ι : Type*} (phase : Verified.Expr ι) : Verified.Expr ι :=
  .sub (.nat 1) (.pow (.sin phase) 2)

/-- The replacement evaluates to the cosine square (`Real.cos_sq'`). -/
@[simp] theorem eval_cosineSquareNormalForm {ι : Type*} (ρ : ι → ℝ)
    (phase : Verified.Expr ι) :
    (cosineSquareNormalForm phase).eval ρ = Real.cos (phase.eval ρ) ^ 2 := by
  simp [cosineSquareNormalForm, Verified.Expr.eval, Real.cos_sq']

/-- The argument of a cosine node. -/
def cosineArgument? {ι : Type*} : Verified.Expr ι → Option (Verified.Expr ι)
  | .cos phase => some phase
  | _ => none

/-- Search the candidate factors of a product for a cosine `cos u` whose partner `cos u` also
occurs in `factors`, the complete factor list of the product. The result pairs the argument
`u` with the factors that remain after both occurrences are removed. -/
def cosinePair? {ι : Type*} [DecidableEq ι] (factors : List (Verified.Expr ι)) :
    List (Verified.Expr ι) → Option (Verified.Expr ι × List (Verified.Expr ι))
  | [] => none
  | candidate :: candidates =>
      match cosineArgument? candidate with
      | some phase =>
          match (removeFactor? (.cos phase) factors).bind (removeFactor? (.cos phase)) with
          | some rest => some (phase, rest)
          | none => cosinePair? factors candidates
      | none => cosinePair? factors candidates

/-- A found pair accounts for two factors `cos phase` of the product:
`cos phase * cos phase * prod rest = prod factors`. -/
theorem eval_prod_cosinePair? {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (factors : List (Verified.Expr ι)) :
    ∀ (candidates : List (Verified.Expr ι)) (phase : Verified.Expr ι)
      (rest : List (Verified.Expr ι)),
      cosinePair? factors candidates = some (phase, rest) →
        Real.cos (phase.eval ρ) * Real.cos (phase.eval ρ) * (rest.map fun f ↦ f.eval ρ).prod =
          (factors.map fun f ↦ f.eval ρ).prod
  | [], _, _, h => by simp [cosinePair?] at h
  | candidate :: candidates, phase, rest, h => by
      simp only [cosinePair?] at h
      split at h
      · split at h
        · rename_i found _ rest' hboth
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          obtain ⟨middle, hmiddle, hrest⟩ := Option.bind_eq_some_iff.mp hboth
          have hfirst := eval_prod_removeFactor? ρ _ factors middle hmiddle
          have hsecond := eval_prod_removeFactor? ρ _ middle _ hrest
          simp only [Verified.Expr.eval] at hfirst hsecond
          rw [← hfirst, ← hsecond]
          ring
        · exact eval_prod_cosinePair? ρ factors candidates phase rest h
      · exact eval_prod_cosinePair? ρ factors candidates phase rest h

/-- Rewrite one product or power node. A power `cos u ^ (n + 2)` becomes
`cos u ^ n * (1 - sin u ^ 2)`; a product containing two factors `cos u` anywhere in its factor
list (`productFactors`) becomes the product of the other factors times `1 - sin u ^ 2`. One
pair is replaced per node; the traversal and the fixed-point pipeline repeat the rewrite. Every
other node is left unchanged. -/
def pythagoreanTop {ι : Type*} [DecidableEq ι] : Verified.Expr ι → Verified.Expr ι
  | .pow (.cos phase) (n + 2) => mkMul (mkPow (.cos phase) n) (cosineSquareNormalForm phase)
  | .mul a b =>
      match cosinePair? (productFactors (.mul a b)) (productFactors (.mul a b)) with
      | some (phase, rest) => mkMul (mkMulList rest) (cosineSquareNormalForm phase)
      | none => .mul a b
  | expr => expr

/-- The node rewrite preserves evaluation. -/
theorem eval_pythagoreanTop {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) (expr : Verified.Expr ι) :
    (pythagoreanTop expr).eval ρ = expr.eval ρ := by
  unfold pythagoreanTop
  split
  · simp only [eval_mkMul, eval_mkPow, eval_cosineSquareNormalForm, Verified.Expr.eval,
      Nat.succ_eq_add_one]
    ring
  · rename_i a b
    split
    · rename_i phase rest hpair
      rw [eval_mkMul, eval_mkMulList, eval_cosineSquareNormalForm,
        ← eval_mkMulList_productFactors ρ (.mul a b), eval_mkMulList,
        ← eval_prod_cosinePair? ρ _ _ phase rest hpair]
      ring
    · rfl
  · rfl

/-- Apply `pythagoreanTop` throughout the polynomial part of an expression: through sums,
differences, negations, products, natural powers, numerators, and the arguments of `sin`,
`cos`, `atan`, `asin`, `acos`, and `exp`. Denominators, radicands, logarithm arguments, real
powers, and leaves are returned unchanged. -/
def pythagoreanRewrite {ι : Type*} [DecidableEq ι] : Verified.Expr ι → Verified.Expr ι
  | .add a b => .add (pythagoreanRewrite a) (pythagoreanRewrite b)
  | .sub a b => .sub (pythagoreanRewrite a) (pythagoreanRewrite b)
  | .neg a => .neg (pythagoreanRewrite a)
  | .mul a b => pythagoreanTop (.mul (pythagoreanRewrite a) (pythagoreanRewrite b))
  | .pow a n => pythagoreanTop (.pow (pythagoreanRewrite a) n)
  | .div a b => .div (pythagoreanRewrite a) b
  | .sin a => .sin (pythagoreanRewrite a)
  | .cos a => .cos (pythagoreanRewrite a)
  | .atan a => .atan (pythagoreanRewrite a)
  | .asin a => .asin (pythagoreanRewrite a)
  | .acos a => .acos (pythagoreanRewrite a)
  | .exp a => .exp (pythagoreanRewrite a)
  | expr => expr

/-- The traversal preserves evaluation. -/
theorem eval_pythagoreanRewrite {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) :
    ∀ expr : Verified.Expr ι, (pythagoreanRewrite expr).eval ρ = expr.eval ρ := by
  intro expr
  induction expr <;> simp [pythagoreanRewrite, eval_pythagoreanTop, *]

/-- Side pass for the Pythagorean normal form of cosine squares; it records no obligation. -/
def pythagoreanSidePass {ι : Type*} [DecidableEq ι] : SidePass ι where
  name := "pythagorean"
  run := fun expr ↦ { expr := pythagoreanRewrite expr, nonzero := [] }
  sound := by
    intro ρ expr _
    exact eval_pythagoreanRewrite ρ expr

end CAS.Verified.Expr

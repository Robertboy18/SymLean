/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
module

public import CAS.Expr.Simplify
public import CAS.Expr.Substitution

/-!
# Polynomial syntax and symbolic differentiation

`IsPolynomial` is the fragment of expressions built from literals, `π`, `e`, variables, sums,
differences, products, negations, and natural powers, with every rational literal having a
nonzero stored denominator. Such expressions have no variable-dependent domain restrictions
(`IsPolynomial.validAt`), and the fragment is preserved by symbolic differentiation
(`IsPolynomial.diff`), substitution (`IsPolynomial.mapVars`), simplification
(`IsPolynomial.simplify`), and finite sums (`isPolynomial_addList`).
-/

@[expose] public section

namespace CAS.Verified.Expr

/-- Polynomial syntax with well-formed rational coefficients. The constants `π` and `e`
are allowed coefficients; division and transcendental applications are excluded. -/
def IsPolynomial {ι : Type*} : Expr ι → Prop :=
  Expr.rec (fun _ ↦ True) (fun _ ↦ True) (fun _ den ↦ den ≠ 0)
    True True (fun _ ↦ True)
    (fun _ _ a b ↦ a ∧ b) (fun _ _ a b ↦ a ∧ b) (fun _ _ a b ↦ a ∧ b)
    (fun _ _ _ _ ↦ False) (fun _ a ↦ a) (fun _ _ a ↦ a)
    (fun _ _ ↦ False) (fun _ _ ↦ False) (fun _ _ ↦ False)
    (fun _ _ ↦ False) (fun _ _ ↦ False) (fun _ _ ↦ False)
    (fun _ _ ↦ False) (fun _ _ ↦ False) (fun _ _ _ _ ↦ False)

/-- Polynomial syntax satisfies the symbolic calculus domain conditions at every value. -/
theorem IsPolynomial.validAt {ι : Type*} {expr : Expr ι} (h : expr.IsPolynomial)
    (ρ : ι → ℝ) : expr.ValidAt ρ := by
  induction expr <;> simp_all [IsPolynomial]

/-- Symbolic partial differentiation preserves polynomial syntax. -/
theorem IsPolynomial.diff {ι : Type*} [DecidableEq ι] {expr : Expr ι}
    (h : expr.IsPolynomial) (v : ι) : (expr.diff v).IsPolynomial := by
  induction expr <;> simp_all only [Expr.diff, IsPolynomial, and_true]
  split <;> trivial

/-- Substituting polynomial expressions for variables preserves polynomial syntax. -/
theorem IsPolynomial.mapVars {ι : Type*} {κ : Type*} {expr : Expr ι} (h : expr.IsPolynomial)
    (f : ι → Expr κ) (hf : ∀ i, (f i).IsPolynomial) : (expr.mapVars f).IsPolynomial := by
  induction expr <;> simp_all [Expr.mapVars, IsPolynomial]

private theorem polynomial_mkIntConst {ι : Type*} (z : Int) :
    (mkIntConst (ι := ι) z).IsPolynomial := by
  unfold mkIntConst
  split <;> trivial

private theorem polynomial_mkRatConst {ι : Type*} (q : Rat) :
    (mkRatConst (ι := ι) q).IsPolynomial := by
  unfold mkRatConst
  split_ifs
  exacts [trivial, polynomial_mkIntConst _, q.den_nz]

private theorem polynomial_mkNatMul {ι : Type*} (n : Nat) {a : Expr ι}
    (ha : a.IsPolynomial) : (mkNatMul n a).IsPolynomial := by
  unfold mkNatMul
  split <;> simp_all [IsPolynomial]

private theorem polynomial_mkCoeffMul {ι : Type*} {a b : Expr ι}
    (ha : a.IsPolynomial) (hb : b.IsPolynomial) : (mkCoeffMul a b).IsPolynomial := by
  unfold mkCoeffMul
  split <;> simp_all [IsPolynomial]

private theorem polynomial_mkAdd {ι : Type*} {a b : Expr ι}
    (ha : a.IsPolynomial) (hb : b.IsPolynomial) : (mkAdd a b).IsPolynomial := by
  unfold mkAdd
  split <;> simp_all [IsPolynomial]

private theorem polynomial_mkMul {ι : Type*} {a b : Expr ι}
    (ha : a.IsPolynomial) (hb : b.IsPolynomial) : (mkMul a b).IsPolynomial := by
  unfold mkMul
  split
  all_goals simp only [IsPolynomial] at ha hb
  all_goals first
    | exact polynomial_mkIntConst _
    | exact polynomial_mkRatConst _
    | exact polynomial_mkCoeffMul (polynomial_mkRatConst _) (by tauto)
    | exact polynomial_mkNatMul _ (by tauto)
    | trivial

private theorem polynomial_mkSub {ι : Type*} [DecidableEq ι] {a b : Expr ι}
    (ha : a.IsPolynomial) (hb : b.IsPolynomial) : (mkSub a b).IsPolynomial := by
  unfold mkSub
  split
  · trivial
  split <;> first
    | exact polynomial_mkIntConst _
    | exact polynomial_mkRatConst _
    | exact ha
    | exact hb
    | exact ⟨ha, hb⟩

private theorem polynomial_mkNeg {ι : Type*} {a : Expr ι}
    (ha : a.IsPolynomial) : (mkNeg a).IsPolynomial := by
  unfold mkNeg
  split <;> first
    | exact polynomial_mkIntConst _
    | exact polynomial_mkRatConst _
    | exact ha

private theorem polynomial_mkPow {ι : Type*} {a : Expr ι} (ha : a.IsPolynomial) (n : Nat) :
    (mkPow a n).IsPolynomial := by
  unfold mkPow
  split <;> try trivial
  split <;> first
    | exact polynomial_mkRatConst _
    | exact ha

private theorem polynomial_simplifyAdd {ι : Type*} [DecidableEq ι] {a b : Expr ι}
    (ha : a.IsPolynomial) (hb : b.IsPolynomial) : (simplifyAdd a b).IsPolynomial := by
  unfold simplifyAdd
  split_ifs <;> (try split) <;> first
    | trivial
    | exact polynomial_mkAdd ha hb
    | exact polynomial_mkMul trivial ha
    | exact polynomial_mkRatConst _

private theorem polynomial_simplifyMul {ι : Type*} {a b : Expr ι}
    (ha : a.IsPolynomial) (hb : b.IsPolynomial) : (simplifyMul a b).IsPolynomial := by
  unfold simplifyMul
  split <;> simp_all only [IsPolynomial]
  all_goals first
    | exact polynomial_mkMul ha hb
    | exact polynomial_mkNeg (polynomial_mkMul ha hb)

private theorem polynomial_simplifySub {ι : Type*} [DecidableEq ι] {a b : Expr ι}
    (ha : a.IsPolynomial) (hb : b.IsPolynomial) : (simplifySub a b).IsPolynomial := by
  unfold simplifySub
  split
  exacts [polynomial_simplifyAdd ha hb, polynomial_mkSub ha hb]

private theorem polynomial_simplifyPow {ι : Type*} {a : Expr ι}
    (ha : a.IsPolynomial) (n : Nat) : (simplifyPow a n).IsPolynomial := by
  unfold simplifyPow
  split <;> apply polynomial_mkPow <;> exact ha

/-- Lightweight simplification does not introduce domain restrictions into polynomial syntax. -/
theorem IsPolynomial.simplify {ι : Type*} [DecidableEq ι] {expr : Expr ι}
    (h : expr.IsPolynomial) : expr.simplify.IsPolynomial := by
  induction expr <;> simp only [IsPolynomial] at h
  all_goals simp only [Expr.simplify]
  all_goals first
    | trivial
    | exact polynomial_simplifyAdd (by tauto) (by tauto)
    | exact polynomial_simplifyMul (by tauto) (by tauto)
    | exact polynomial_simplifySub (by tauto) (by tauto)
    | exact polynomial_mkNeg (by tauto)
    | exact polynomial_simplifyPow (by tauto) _

/-- A finite sum of polynomial expressions remains polynomial. -/
theorem isPolynomial_addList {ι : Type*} (xs : List (Expr ι))
    (h : ∀ term ∈ xs, term.IsPolynomial) : (addList xs).IsPolynomial := by
  have hfold (ys : List (Expr ι)) (acc : Expr ι) (ha : acc.IsPolynomial)
      (hy : ∀ term ∈ ys, term.IsPolynomial) : (ys.foldl Expr.add acc).IsPolynomial := by
    induction ys generalizing acc with
    | nil => exact ha
    | cons y ys ih => exact ih (.add acc y) ⟨ha, hy y (by simp)⟩ fun t ht ↦ hy t (by simp [ht])
  cases xs with
  | nil => trivial
  | cons x xs => exact hfold xs x (h x (by simp)) (fun term he ↦ h term (by simp [he]))

attribute [inherit_doc IsPolynomial] IsPolynomial.eq_1

end CAS.Verified.Expr

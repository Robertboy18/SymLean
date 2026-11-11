/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Notation
public import CAS.Expr.SmartConstructors
public import CAS.Polynomial.Sparse.Representation

/-!
# Real semantics of sparse rational polynomials

The real-valued meaning of the ordered representation of
`CAS.Polynomial.Sparse.Representation`, which itself contains no analysis.

## Main definitions

* `mvMonomialExpr`, `mvTermExpr`, `mvPolyExpr`: reification of monomials, terms, and
  polynomials back to `Verified.Expr (Fin n)`.
* `mvNormalizeExpr?`, `mvNormalizeExpr`: the polynomial normalizer for expressions over `Fin n`
  (reflect, normalize, reify), partial and with an identity fallback.
* `mvMonomialVal`, `mvTermVal`, `mvPolyVal`: evaluation at a point of `ℝ^n`.

## Main results

* `mvPolyVal_normalize`, `mvPolyVal_add`, `mvPolyVal_sub`, `mvPolyVal_mulPoly`,
  `mvPolyVal_powPoly`: normalization and arithmetic preserve evaluation.
* `mvPolyVal_eq_eval_of_mvPolyOf?`, `eval_mvPolyExpr`: reflection and reification preserve
  evaluation.
* `eval_mvNormalizeExpr`: soundness of the normalizer.
-/

@[expose] public section

namespace CAS

open scoped BigOperators

namespace Verified.Expr

namespace Alg

/-! ## Reification -/

/-- The symbolic power `x_i ^ k` that coordinate `i` contributes to a reified monomial. -/
def mvMonomialExprAux {n : Nat} (i : Fin n) (k : Nat) :
    Verified.Expr (Fin n) :=
  mkPow (.var i) k

/-- Reify an ordered monomial back to a symbolic expression. -/
def mvMonomialExpr {n : Nat} (mono : MvMonomial n) : Verified.Expr (Fin n) :=
  Verified.Expr.mulList ((List.finRange n).map fun i ↦ mvMonomialExprAux i (mono i))

/-- Reify a rational-coefficient ordered monomial term back to a symbolic expression. -/
def mvTermExpr {n : Nat} (term : Rat × MvMonomial n) : Verified.Expr (Fin n) :=
  mkMul (mkRatConst term.1) (mvMonomialExpr term.2)

/-- Reify an ordered multivariate polynomial back to a symbolic expression. -/
def mvPolyExpr {n : Nat} (poly : MvPoly n) : Verified.Expr (Fin n) :=
  Verified.Expr.addList ((mvNormalize poly).map mvTermExpr)

/--
Canonically simplify an ordered multivariate polynomial expression.

Expressions outside the polynomial fragment (quotients, transcendental functions, `π`, `e`)
return `none`. Polynomial inputs are reflected, coefficient-collected, ordered by graded
lexicographic order, and reified back to `Verified.Expr (Fin n)`.
-/
def mvNormalizeExpr? {n : Nat}
    (expr : Verified.Expr (Fin n)) : Option (Verified.Expr (Fin n)) := do
  let poly ← mvPolyOf? expr
  pure (mvPolyExpr poly)

/-- Total polynomial simplifier with conservative fallback for unsupported expressions. -/
def mvNormalizeExpr {n : Nat} (expr : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  (mvNormalizeExpr? expr).getD expr

/-! ## Real-valued evaluation -/

/-- Semantic value of an ordered exponent-vector monomial at a Euclidean point. -/
noncomputable def mvMonomialVal {n : Nat} (x : ℝ^n)
    (mono : MvMonomial n) : ℝ :=
  ((List.finRange n).map fun i ↦ x.ofLp i ^ mono i).prod

/-- Semantic value of a rational-coefficient ordered monomial term. -/
noncomputable def mvTermVal {n : Nat} (x : ℝ^n)
    (term : Rat × MvMonomial n) : ℝ :=
  (term.1 : ℝ) * mvMonomialVal x term.2

/-- Semantic value of a sparse ordered multivariate polynomial. -/
noncomputable def mvPolyVal {n : Nat} (x : ℝ^n) : MvPoly n → ℝ
  | [] => 0
  | term :: rest => mvTermVal x term + mvPolyVal x rest

private theorem mvPolyVal_append {n : Nat} (x : ℝ^n)
    (p q : MvPoly n) :
    mvPolyVal x (p ++ q) = mvPolyVal x p + mvPolyVal x q := by
  induction p with
  | nil => simp [mvPolyVal]
  | cons term rest ih =>
      simp only [List.cons_append, mvPolyVal, ih]
      ring

private theorem mvKey_injective {n : Nat} {a b : MvMonomial n} (h : mvKey a = mvKey b) :
    a = b := by
  simp only [mvKey, List.cons.injEq] at h
  funext i
  exact List.map_inj_left.mp h.2 i (List.mem_finRange i)

private theorem mvMergeKeyed_keys {n : Nat} :
    ∀ (fuel : Nat) (as bs : List (MvKeyedTerm n)),
      (∀ t ∈ as, t.1 = mvKey t.2.2) → (∀ t ∈ bs, t.1 = mvKey t.2.2) →
        ∀ t ∈ mvMergeKeyed fuel as bs, t.1 = mvKey t.2.2
  | 0, as, bs, ha, hb => by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      exacts [ha t ht, hb t ht]
  | _ + 1, [], _, _, hb => hb
  | _ + 1, _ :: _, [], ha, _ => ha
  | fuel + 1, a :: as, b :: bs, ha, hb => by
      have ha' : ∀ t ∈ as, t.1 = mvKey t.2.2 := fun t ht ↦ ha t (List.mem_cons_of_mem _ ht)
      have hb' : ∀ t ∈ bs, t.1 = mvKey t.2.2 := fun t ht ↦ hb t (List.mem_cons_of_mem _ ht)
      simp only [mvMergeKeyed]
      split
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        exacts [ha _ List.mem_cons_self, mvMergeKeyed_keys fuel as (b :: bs) ha' hb t ht]
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        exacts [hb _ List.mem_cons_self, mvMergeKeyed_keys fuel (a :: as) bs ha hb' t ht]
      · split
        · exact mvMergeKeyed_keys fuel as bs ha' hb'
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          exacts [ha a List.mem_cons_self, mvMergeKeyed_keys fuel as bs ha' hb' t ht]

private theorem mvPolyVal_mergeKeyed {n : Nat} (x : ℝ^n) :
    ∀ (fuel : Nat) (as bs : List (MvKeyedTerm n)),
      (∀ t ∈ as, t.1 = mvKey t.2.2) → (∀ t ∈ bs, t.1 = mvKey t.2.2) →
        mvPolyVal x ((mvMergeKeyed fuel as bs).map Prod.snd) =
          mvPolyVal x (as.map Prod.snd) + mvPolyVal x (bs.map Prod.snd)
  | 0, as, bs, _, _ => by simp [mvMergeKeyed, mvPolyVal_append]
  | _ + 1, [], bs, _, _ => by simp [mvMergeKeyed, mvPolyVal]
  | _ + 1, a :: as, [], _, _ => by simp [mvMergeKeyed, mvPolyVal]
  | fuel + 1, a :: as, b :: bs, ha, hb => by
      have ha' : ∀ t ∈ as, t.1 = mvKey t.2.2 := fun t ht ↦ ha t (List.mem_cons_of_mem _ ht)
      have hb' : ∀ t ∈ bs, t.1 = mvKey t.2.2 := fun t ht ↦ hb t (List.mem_cons_of_mem _ ht)
      simp only [mvMergeKeyed]
      split
      · simp only [List.map_cons, mvPolyVal, mvPolyVal_mergeKeyed x fuel as (b :: bs) ha' hb]
        ring
      · simp only [List.map_cons, mvPolyVal, mvPolyVal_mergeKeyed x fuel (a :: as) bs ha hb']
        ring
      · rename_i hcmp
        have hmono : a.2.2 = b.2.2 := mvKey_injective <|
          (ha a List.mem_cons_self).symm.trans
            ((Std.LawfulEqCmp.eq_of_compare hcmp).trans (hb b List.mem_cons_self))
        split
        · rename_i hc
          have hc' : (a.2.1 : ℝ) + b.2.1 = 0 := by exact_mod_cast hc
          simp only [List.map_cons, mvPolyVal, mvTermVal,
            mvPolyVal_mergeKeyed x fuel as bs ha' hb', hmono]
          linear_combination -mvMonomialVal x b.2.2 * hc'
        · simp only [List.map_cons, mvPolyVal, mvTermVal,
            mvPolyVal_mergeKeyed x fuel as bs ha' hb', hmono, Rat.cast_add]
          ring

private theorem mvRuns_flatten {n : Nat} :
    ∀ terms : List (MvKeyedTerm n), (mvRuns terms).flatten = terms
  | [] => rfl
  | t :: rest => by
      have ih := mvRuns_flatten rest
      simp only [mvRuns]
      split
      · rename_i u run runs h
        rw [h] at ih
        split <;> simp_all
      · simpa using ih

private theorem mvMergePairs_keys {n : Nat} (fuel : Nat) :
    ∀ runs : List (List (MvKeyedTerm n)), (∀ t ∈ runs.flatten, t.1 = mvKey t.2.2) →
      ∀ t ∈ (mvMergePairs fuel runs).flatten, t.1 = mvKey t.2.2
  | [], h => h
  | [_], h => h
  | a :: b :: rest, h => by
      simp only [List.flatten_cons, List.mem_append] at h
      simp only [mvMergePairs, List.flatten_cons, List.mem_append]
      intro t ht
      rcases ht with ht | ht
      · exact mvMergeKeyed_keys fuel a b (fun s hs ↦ h s (.inl hs))
          (fun s hs ↦ h s (.inr (.inl hs))) t ht
      · exact mvMergePairs_keys fuel rest (fun s hs ↦ h s (.inr (.inr hs))) t ht

private theorem mvPolyVal_mergePairs {n : Nat} (x : ℝ^n) (fuel : Nat) :
    ∀ runs : List (List (MvKeyedTerm n)), (∀ t ∈ runs.flatten, t.1 = mvKey t.2.2) →
      mvPolyVal x ((mvMergePairs fuel runs).flatten.map Prod.snd) =
        mvPolyVal x (runs.flatten.map Prod.snd)
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
      simp only [List.flatten_cons, List.mem_append] at h
      simp only [mvMergePairs, List.flatten_cons, List.map_append, mvPolyVal_append,
        mvPolyVal_mergeKeyed x fuel a b (fun s hs ↦ h s (.inl hs))
          (fun s hs ↦ h s (.inr (.inl hs))),
        mvPolyVal_mergePairs x fuel rest (fun s hs ↦ h s (.inr (.inr hs)))]
      ring

private theorem mvPolyVal_mergeRuns {n : Nat} (x : ℝ^n) (fuel : Nat) :
    ∀ (passes : Nat) (runs : List (List (MvKeyedTerm n))),
      (∀ t ∈ runs.flatten, t.1 = mvKey t.2.2) →
        mvPolyVal x ((mvMergeRuns fuel passes runs).map Prod.snd) =
          mvPolyVal x (runs.flatten.map Prod.snd)
  | _, [], _ => by simp [mvMergeRuns]
  | _, [_], _ => by simp [mvMergeRuns]
  | 0, _ :: _ :: _, _ => by simp only [mvMergeRuns]
  | passes + 1, a :: b :: rest, h => by
      simp only [mvMergeRuns]
      rw [mvPolyVal_mergeRuns x fuel passes _ (mvMergePairs_keys fuel _ h),
        mvPolyVal_mergePairs x fuel _ h]

private theorem mvPolyVal_filter {n : Nat} (x : ℝ^n) (keep : Rat × MvMonomial n → Bool)
    (hkeep : ∀ term, keep term = false → term.1 = 0) :
    ∀ poly : MvPoly n, mvPolyVal x (poly.filter keep) = mvPolyVal x poly
  | [] => rfl
  | term :: rest => by
      rw [List.filter_cons]
      cases hk : keep term
      · simp [mvPolyVal, mvTermVal, hkeep term hk, mvPolyVal_filter x keep hkeep rest]
      · simp [mvPolyVal, mvPolyVal_filter x keep hkeep rest]

/-- Canonicalizing an ordered sparse polynomial preserves its semantic value. -/
theorem mvPolyVal_normalize {n : Nat} (x : ℝ^n) (poly : MvPoly n) :
    mvPolyVal x (mvNormalize poly) = mvPolyVal x poly := by
  let keyed := (poly.filter fun term ↦ term.1 ≠ 0).map fun term ↦ (mvKey term.2, term)
  have hkeys : ∀ t ∈ (mvRuns keyed).flatten, t.1 = mvKey t.2.2 := by
    rw [mvRuns_flatten]
    intro t ht
    obtain ⟨term, -, rfl⟩ := List.mem_map.mp ht
    rfl
  have hvalue : mvPolyVal x (keyed.map Prod.snd) = mvPolyVal x poly := by
    simpa [keyed, List.map_map, Function.comp_def] using
      mvPolyVal_filter x (fun term ↦ term.1 ≠ 0) (fun term h ↦ by simpa using h) poly
  change mvPolyVal x ((mvMergeRuns keyed.length keyed.length (mvRuns keyed)).map Prod.snd) = _
  rw [mvPolyVal_mergeRuns x _ _ _ hkeys, mvRuns_flatten, hvalue]

/-- Sparse polynomial addition preserves real evaluation. -/
theorem mvPolyVal_add {n : Nat} (x : ℝ^n)
    (p q : MvPoly n) :
    mvPolyVal x (mvAdd p q) = mvPolyVal x p + mvPolyVal x q := by
  simp [mvAdd, mvPolyVal_normalize, mvPolyVal_append]

private theorem mvPolyVal_neg {n : Nat} (x : ℝ^n) :
    ∀ p : MvPoly n, mvPolyVal x (mvNeg p) = -mvPolyVal x p := by
  intro p
  induction p with
  | nil => simp [mvNeg, mvPolyVal]
  | cons term rest ih =>
      simp only [mvNeg, List.map_cons, mvPolyVal, mvTermVal, Rat.cast_neg, neg_mul] at ih ⊢
      rw [ih, neg_add]

/-- Sparse polynomial subtraction preserves real evaluation. -/
theorem mvPolyVal_sub {n : Nat} (x : ℝ^n)
    (p q : MvPoly n) :
    mvPolyVal x (mvSub p q) = mvPolyVal x p - mvPolyVal x q := by
  simp [mvSub, mvPolyVal_add, mvPolyVal_neg, sub_eq_add_neg]

private theorem mvMonomialVal_mul {n : Nat} (x : ℝ^n)
    (a b : MvMonomial n) :
    mvMonomialVal x (mvMul a b) = mvMonomialVal x a * mvMonomialVal x b := by
  simp only [mvMonomialVal, mvMul, pow_add, List.prod_map_mul]

/-- Monomial exponent-vector scaling preserves natural powers. -/
theorem mvMonomialVal_pow {n : Nat} (x : ℝ^n)
    (mono : MvMonomial n) (exponent : Nat) :
    mvMonomialVal x (mvPowMonomial mono exponent) =
      mvMonomialVal x mono ^ exponent := by
  unfold mvMonomialVal
  simp only [mvPowMonomial, pow_mul]
  generalize List.finRange n = indices
  induction indices with
  | nil => simp
  | cons i rest ih => simp [ih, mul_pow]

private theorem mvPolyVal_flatMap_mul {n : Nat} (x : ℝ^n)
    (tp : Rat × MvMonomial n) (q : MvPoly n) :
    mvPolyVal x (q.map fun tq ↦ (tp.1 * tq.1, mvMul tp.2 tq.2)) =
      mvTermVal x tp * mvPolyVal x q := by
  rcases tp with ⟨cp, mp⟩
  induction q with
  | nil => simp [mvPolyVal]
  | cons tq rest ih =>
      rcases tq with ⟨cq, mq⟩
      simp only [List.map_cons, mvPolyVal, mvTermVal, mvMonomialVal_mul, ih, Rat.cast_mul]
      ring

/-- Sparse polynomial multiplication preserves real evaluation. -/
theorem mvPolyVal_mulPoly {n : Nat} (x : ℝ^n)
    (p q : MvPoly n) :
    mvPolyVal x (mvMulPoly p q) = mvPolyVal x p * mvPolyVal x q := by
  simp only [mvMulPoly, mvPolyVal_normalize]
  induction p with
  | nil => simp [mvPolyVal]
  | cons tp rest ih =>
      simp only [List.flatMap_cons, mvPolyVal_append, mvPolyVal,
        mvPolyVal_flatMap_mul, ih]
      ring

/-- Sparse polynomial powers preserve real evaluation. -/
theorem mvPolyVal_powPoly {n : Nat} (x : ℝ^n)
    (p : MvPoly n) :
    ∀ k : Nat, mvPolyVal x (mvPowPoly p k) = mvPolyVal x p ^ k := by
  intro k
  induction k with
  | zero => simp [mvPowPoly, mvPolyVal, mvTermVal, mvMonomialVal, mvOne]
  | succ k ih => rw [mvPowPoly, mvPolyVal_mulPoly, ih, pow_succ']

private theorem mvMonomialVal_one {n : Nat} (x : ℝ^n) :
    mvMonomialVal x (mvOne n) = 1 := by
  simp [mvMonomialVal, mvOne]

private theorem mvMonomialVal_var {n : Nat} (x : ℝ^n) (i : Fin n) :
    mvMonomialVal x (mvVar i) = x.ofLp i := by
  unfold mvMonomialVal
  rw [← Fin.prod_univ_def (fun j : Fin n ↦ x.ofLp j ^ mvVar i j), Fintype.prod_eq_single i]
  · simp [mvVar]
  · intro j hj
    simp [mvVar, hj]

private theorem mvMonomialVal_mvMonomialOf? {n : Nat} (x : ℝ^n) :
    ∀ expr : Verified.Expr (Fin n), ∀ mono : MvMonomial n,
      mvMonomialOf? expr = some mono → mvMonomialVal x mono = expr.eval x := by
  intro expr
  induction expr with
  | nat v | int v =>
      intro mono h
      by_cases hv : v = 1
      · subst hv
        simp only [mvMonomialOf?, Option.some.injEq] at h
        simp [← h, mvMonomialVal_one]
      · simp [mvMonomialOf?, hv] at h
  | var i =>
      intro mono h
      simp only [mvMonomialOf?, Option.some.injEq] at h
      simp [← h, mvMonomialVal_var]
  | mul a b iha ihb =>
      intro mono h
      simp only [mvMonomialOf?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨ma, ha, mb, hb, rfl⟩ := h
      simp [mvMonomialVal_mul, iha ma ha, ihb mb hb]
  | pow a k ih =>
      intro mono h
      simp only [mvMonomialOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ma, ha, rfl⟩ := h
      simp [mvMonomialVal_pow, ih ma ha]
  | _ => simp [mvMonomialOf?]

/-- A single constant term evaluates to its coefficient. -/
theorem mvPolyVal_of_mvConstant? {n : Nat} (x : ℝ^n) {p : MvPoly n} {c : Rat}
    (h : mvConstant? p = some c) : mvPolyVal x p = c := by
  match p, h with
  | [(c', m)], h =>
      by_cases hm : m = mvOne n
      · simp only [mvConstant?, hm, ↓reduceIte, Option.some.injEq] at h
        subst h hm
        simp [mvPolyVal, mvTermVal, mvMonomialVal_one]
      · simp [mvConstant?, hm] at h

/-- Successful ordered-polynomial reflection preserves semantic evaluation. -/
theorem mvPolyVal_eq_eval_of_mvPolyOf? {n : Nat}
    (x : ℝ^n) (expr : Verified.Expr (Fin n)) (poly : MvPoly n)
    (h : mvPolyOf? expr = some poly) :
    mvPolyVal x poly = expr.eval x := by
  induction expr generalizing poly with
  | nat k =>
      by_cases hk : k = 0 <;> simp only [mvPolyOf?, hk, ↓reduceIte, Option.some.injEq] at h <;>
        simp [← h, hk, mvPolyVal, mvTermVal, mvMonomialVal_one]
  | int z =>
      by_cases hz : z = 0 <;> simp only [mvPolyOf?, hz, ↓reduceIte, Option.some.injEq] at h <;>
        simp [← h, hz, mvPolyVal, mvTermVal, mvMonomialVal_one]
  | rat num den =>
      have hqeval : ((mkRat num den : Rat) : ℝ) = (num : ℝ) / (den : ℝ) := rat_cast_mkRat_real ..
      by_cases hq : (mkRat num den : Rat) = 0
      · have hpoly : poly = [] := by simpa [mvPolyOf?, hq] using h.symm
        simp [hpoly, mvPolyVal, ← hqeval, hq]
      · have hpoly : poly = [(mkRat num den, mvOne n)] := by simpa [mvPolyOf?, hq] using h.symm
        simp [hpoly, mvPolyVal, mvTermVal, mvMonomialVal_one, hqeval]
  | var i =>
      simp only [mvPolyOf?, Option.some.injEq] at h
      simp [← h, mvPolyVal, mvTermVal, mvMonomialVal_var]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb =>
      simp only [mvPolyOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨pa, ha, pb, hb, rfl⟩ := h
      simp [mvPolyVal_add, mvPolyVal_sub, mvPolyVal_mulPoly, iha pa ha, ihb pb hb]
  | neg a ih =>
      simp only [mvPolyOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨pa, ha, rfl⟩ := h
      simp [mvPolyVal_neg, ih pa ha]
  | pow a k ih =>
      cases hmono : mvMonomialOf? a with
      | some mono =>
          simp only [mvPolyOf?, hmono, Option.some.injEq] at h
          simp [← h, mvPolyVal, mvTermVal, mvMonomialVal_pow,
            mvMonomialVal_mvMonomialOf? x a mono hmono]
      | none =>
          simp only [mvPolyOf?, hmono, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.some.injEq] at h
          obtain ⟨pa, ha, rfl⟩ := h
          simp [mvPolyVal_powPoly, ih pa ha]
  | div a b iha ihb =>
      simp only [mvPolyOf?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨pa, ha, pb, hb, c, hc, h⟩ := h
      by_cases hc0 : c = 0
      · simp [hc0] at h
      · simp only [hc0, ↓reduceIte, Option.some.injEq] at h
        subst h
        have hbval : b.eval x = c := by rw [← ihb pb hb, mvPolyVal_of_mvConstant? x hc]
        simp [mvPolyVal_mulPoly, iha pa ha, mvPolyVal, mvTermVal, mvMonomialVal_one, hbval,
          div_eq_mul_inv]
  | _ => simp [mvPolyOf?] at h

private theorem eval_mvMonomialExprAux {n : Nat} (x : ℝ^n) (i : Fin n) :
    ∀ k : Nat,
      Verified.Expr.eval (fun j : Fin n ↦ x.ofLp j) (mvMonomialExprAux i k) =
        x.ofLp i ^ k
  | k => by simp [mvMonomialExprAux, eval_mkPow]

/-- Reifying an ordered monomial preserves its semantic value. -/
theorem eval_mvMonomialExpr {n : Nat} (x : ℝ^n) (mono : MvMonomial n) :
    (mvMonomialExpr mono).eval x = mvMonomialVal x mono := by
  simp only [mvMonomialExpr, eval_mulList, List.map_map, mvMonomialVal]
  exact congrArg List.prod (List.map_congr_left fun i _ ↦ eval_mvMonomialExprAux x i (mono i))

/-- Reifying an ordered polynomial term preserves its semantic value. -/
theorem eval_mvTermExpr {n : Nat} (x : ℝ^n)
    (term : Rat × MvMonomial n) :
    (mvTermExpr term).eval x = mvTermVal x term := by
  simp [mvTermExpr, mvTermVal, eval_mvMonomialExpr]

/--
Reifying an ordered polynomial preserves the semantic value of its canonical
normalization.
-/
theorem eval_mvPolyExpr {n : Nat} (x : ℝ^n) :
    ∀ poly : MvPoly n, (mvPolyExpr poly).eval x = mvPolyVal x (mvNormalize poly)
  | poly => by
      simp only [mvPolyExpr, eval_addList, List.map_map]
      induction (mvNormalize poly) with
      | nil => simp [mvPolyVal]
      | cons term rest ih =>
          simp [mvPolyVal, eval_mvTermExpr, ih]

/-- When the partial ordered multivariate normalizer succeeds, its output evaluates to the same
real number as the input at every point. -/
theorem eval_mvNormalizeExpr?_eq {n : Nat} (x : ℝ^n)
    {expr out : Verified.Expr (Fin n)} (h : mvNormalizeExpr? expr = some out) :
    out.eval x = expr.eval x := by
  simp only [mvNormalizeExpr?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨poly, hpoly, rfl⟩ := h
  rw [eval_mvPolyExpr, mvPolyVal_normalize, mvPolyVal_eq_eval_of_mvPolyOf? x expr poly hpoly]

/--
The total ordered multivariate polynomial simplifier preserves expression
semantics.

Unsupported non-polynomial expressions are returned unchanged, so this theorem
covers both the successful polynomial branch and the conservative fallback.
-/
theorem eval_mvNormalizeExpr {n : Nat} (x : ℝ^n)
    (expr : Verified.Expr (Fin n)) :
    (mvNormalizeExpr expr).eval x = expr.eval x := by
  unfold mvNormalizeExpr
  cases h : mvNormalizeExpr? expr with
  | none => rfl
  | some out =>
      exact eval_mvNormalizeExpr?_eq x h

end Alg

end Verified.Expr
end CAS

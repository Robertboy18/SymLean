/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# Integer polynomials and pairs of natural numbers

A signed integer `p - q` is represented by the pair `(p, q)` of natural numbers, so that sums
and products use natural-number operations only: `(p, q) + (p', q') = (p + p', q + q')` and
`(p, q) (p', q') = (p p' + q q', p q' + q p')`. A polynomial with integer coefficients is a list
of monomials (`PairMonomial`: a sign, a magnitude and a list of variable indices), evaluated on
real numbers by `pairPolyValue`.

The error of a polynomial under perturbed variables is bounded by `pairPolyErr`, the sum over
the monomials of `|c| (∏ (X_v + e_v) - ∏ X_v)`, where `X_v` bounds the perturbed values and
`e_v` the perturbations (`abs_pairPolyValue_sub_le`).

## Implementation notes

We use pairs of natural numbers because the kernel evaluates natural-number operations on
literals but has no such extension for `Int` (see [PackedSlots](PackedSlots.lean)). `pairAdd`,
`pairMul` and `pairAbs` call `Nat.add`, `Nat.mul`, `Nat.sub`, `Nat.ble` and `cond` directly, so
kernel reduction unfolds no instance; a product costs four natural multiplications and two
additions, and `pairAbs` subtracts the smaller entry from the larger after one `Nat.ble`. Pairs
are never normalized: many pairs stand for one integer, and only `pairValue` matters, which
`pairValue_pairAdd`, `pairValue_pairMul` and `cast_pairAbs` compute once for all inputs.

The perturbation bound is proved over the reals, by induction over the variables of a monomial
(`abs_prod_sub_prod_le`, writing `y v P - y' v P'` as `y v (P - P') + (y v - y' v) P'`) and then
over the monomials; `pairPolyErr_mono` replaces `X` and `e` by larger bounds. Inside SymLean,
[PairForms](PairForms.lean) and [PairChecks](PairChecks.lean) build linear forms and sign tests
on these pairs, and [GridBall](GridBall.lean) returns its floor and ceiling shifts as pairs.
-/

@[expose] public section

namespace CAS.Numerics

/-- The signed value `p - q` of a pair. -/
def pairValue (a : ℕ × ℕ) : ℤ := (a.1 : ℤ) - a.2

/-- The sum of two pairs. -/
def pairAdd (a b : ℕ × ℕ) : ℕ × ℕ := (Nat.add a.1 b.1, Nat.add a.2 b.2)

/-- The product of two pairs. -/
def pairMul (a b : ℕ × ℕ) : ℕ × ℕ :=
  (Nat.add (Nat.mul a.1 b.1) (Nat.mul a.2 b.2), Nat.add (Nat.mul a.1 b.2) (Nat.mul a.2 b.1))

/-- The value of `pairAdd a b` is `pairValue a + pairValue b`. -/
@[simp] theorem pairValue_pairAdd (a b : ℕ × ℕ) :
    pairValue (pairAdd a b) = pairValue a + pairValue b := by
  simp only [pairValue, pairAdd, Nat.add_eq]
  push_cast
  ring

/-- The value of `pairMul a b` is `pairValue a * pairValue b`. -/
@[simp] theorem pairValue_pairMul (a b : ℕ × ℕ) :
    pairValue (pairMul a b) = pairValue a * pairValue b := by
  simp only [pairValue, pairMul, Nat.add_eq, Nat.mul_eq]
  push_cast
  ring

/-- The absolute value of a pair as a natural number. -/
def pairAbs (a : ℕ × ℕ) : ℕ := cond (Nat.ble a.2 a.1) (Nat.sub a.1 a.2) (Nat.sub a.2 a.1)

/-- `pairAbs a` is `|pairValue a|` in the integers. -/
theorem cast_pairAbs (a : ℕ × ℕ) : (pairAbs a : ℤ) = |pairValue a| := by
  unfold pairAbs pairValue
  by_cases h : a.2 ≤ a.1
  · simp [Nat.ble_eq.mpr h, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.2 (Int.ofNat_le.2 h))]
  · rw [show Nat.ble a.2 a.1 = false from Bool.eq_false_iff.mpr fun e ↦ h (Nat.ble_eq.mp e)]
    simp [Nat.cast_sub (by omega : a.1 ≤ a.2), abs_of_neg (by omega : (a.1 : ℤ) - a.2 < 0)]

/-- A monomial with integer coefficient `±coeff` in the variables `vars`. -/
structure PairMonomial where
  /-- Whether the coefficient is negative. -/
  neg : Bool
  /-- The magnitude of the coefficient. -/
  coeff : ℕ
  /-- The variable indices, with repetition. -/
  vars : List ℕ

/-- The signed coefficient of a monomial. -/
def PairMonomial.sign (μ : PairMonomial) : ℤ := cond μ.neg (-(μ.coeff : ℤ)) μ.coeff

/-- The real value of a polynomial. -/
def pairPolyValue (P : List PairMonomial) (y : ℕ → ℝ) : ℝ :=
  (P.map fun μ ↦ (μ.sign : ℝ) * (μ.vars.map y).prod).sum

/-! ### Perturbation bounds -/

/-- The perturbation bound of a product: `∏ (X + e) - ∏ X`. -/
def prodErr (X e : ℕ → ℝ) (vs : List ℕ) : ℝ :=
  (vs.map fun v ↦ X v + e v).prod - (vs.map X).prod

/-- If `|y v| ≤ X v` for every `v ∈ vs`, then `|(vs.map y).prod| ≤ (vs.map X).prod`. -/
theorem abs_list_prod_le (y X : ℕ → ℝ) (vs : List ℕ) (hX : ∀ v ∈ vs, |y v| ≤ X v) :
    |(vs.map y).prod| ≤ (vs.map X).prod := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, abs_mul]
    exact mul_le_mul (hX v List.mem_cons_self)
      (ih fun w hw ↦ hX w (List.mem_cons_of_mem v hw)) (abs_nonneg _)
      ((abs_nonneg _).trans (hX v List.mem_cons_self))

/-- If `|y' v| ≤ X v` and `|y v - y' v| ≤ e v` for every `v ∈ vs`, the products of `y` and `y'`
over `vs` differ by at most `prodErr X e vs`. -/
theorem abs_prod_sub_prod_le (y y' X e : ℕ → ℝ) (vs : List ℕ)
    (hX : ∀ v ∈ vs, |y' v| ≤ X v) (he : ∀ v ∈ vs, |y v - y' v| ≤ e v) :
    |(vs.map y).prod - (vs.map y').prod| ≤ prodErr X e vs := by
  induction vs with
  | nil => simp [prodErr]
  | cons v vs ih =>
    obtain ⟨hXv, hX⟩ := List.forall_mem_cons.1 hX
    obtain ⟨hev, he⟩ := List.forall_mem_cons.1 he
    have ih' := ih hX he
    have hyv : |y v| ≤ X v + e v := by linarith [abs_sub_abs_le_abs_sub (y v) (y' v)]
    simp only [prodErr, List.map_cons, List.prod_cons] at ih' ⊢
    set P := (vs.map y).prod
    set P' := (vs.map y').prod
    rw [show y v * P - y' v * P' = y v * (P - P') + (y v - y' v) * P' by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    linarith [mul_le_mul hyv ih' (abs_nonneg _) ((abs_nonneg _).trans hyv),
      mul_le_mul hev (abs_list_prod_le y' X vs hX) (abs_nonneg _) ((abs_nonneg _).trans hev)]

/-- The perturbation bound of a polynomial: `∑ |c| (∏ (X + e) - ∏ X)` over its monomials. -/
def pairPolyErr (P : List PairMonomial) (X e : ℕ → ℝ) : ℝ :=
  (P.map fun μ ↦ (μ.coeff : ℝ) * prodErr X e μ.vars).sum

/-- Perturbing the variables of a polynomial by at most `e`, at values bounded by `X`, changes
its value by at most `pairPolyErr`. -/
theorem abs_pairPolyValue_sub_le (P : List PairMonomial) (y y' X e : ℕ → ℝ)
    (hX : ∀ v, |y' v| ≤ X v) (he : ∀ v, |y v - y' v| ≤ e v) :
    |pairPolyValue P y - pairPolyValue P y'| ≤ pairPolyErr P X e := by
  induction P with
  | nil => simp [pairPolyValue, pairPolyErr]
  | cons μ P ih =>
    simp only [pairPolyValue, pairPolyErr, List.map_cons, List.sum_cons] at ih ⊢
    have hs : |(μ.sign : ℝ)| = μ.coeff := by
      unfold PairMonomial.sign
      cases μ.neg <;> simp
    have hμ : |(μ.sign : ℝ) * ((μ.vars.map y).prod - (μ.vars.map y').prod)| ≤
        μ.coeff * prodErr X e μ.vars := by
      rw [abs_mul, hs]
      exact mul_le_mul_of_nonneg_left (abs_prod_sub_prod_le y y' X e μ.vars (fun v _ ↦ hX v)
        (fun v _ ↦ he v)) (Nat.cast_nonneg _)
    rw [abs_le] at hμ ih ⊢
    constructor <;> linarith

/-- `abs_pairPolyValue_sub_le` with the hypotheses only on the variables below `K`, when every
monomial uses only such variables. -/
theorem abs_pairPolyValue_sub_le_of_lt (P : List PairMonomial) (y y' X e : ℕ → ℝ) {K : ℕ}
    (hK : ∀ μ ∈ P, ∀ v ∈ μ.vars, v < K)
    (hX : ∀ v < K, |y' v| ≤ X v) (he : ∀ v < K, |y v - y' v| ≤ e v) :
    |pairPolyValue P y - pairPolyValue P y'| ≤ pairPolyErr P X e := by
  induction P with
  | nil => simp [pairPolyValue, pairPolyErr]
  | cons μ P ih =>
    obtain ⟨hμK, hK⟩ := List.forall_mem_cons.1 hK
    have ih' := ih hK
    simp only [pairPolyValue, pairPolyErr, List.map_cons, List.sum_cons] at ih' ⊢
    have hs : |(μ.sign : ℝ)| = μ.coeff := by
      unfold PairMonomial.sign
      cases μ.neg <;> simp
    have hμ : |(μ.sign : ℝ) * ((μ.vars.map y).prod - (μ.vars.map y').prod)| ≤
        μ.coeff * prodErr X e μ.vars := by
      rw [abs_mul, hs]
      exact mul_le_mul_of_nonneg_left (abs_prod_sub_prod_le y y' X e μ.vars
        (fun v hv ↦ hX v (hμK v hv)) (fun v hv ↦ he v (hμK v hv))) (Nat.cast_nonneg _)
    rw [abs_le] at hμ ih' ⊢
    constructor <;> linarith

/-- The product bounds grow with the bounds: for `0 ≤ X ≤ X'` and `0 ≤ e ≤ e'` on the variables,
`∏ X ≤ ∏ X'` and `0 ≤ prodErr X e ≤ prodErr X' e'`. -/
theorem prodErr_mono {X X' e e' : ℕ → ℝ} (vs : List ℕ) (hX0 : ∀ v ∈ vs, 0 ≤ X v)
    (he0 : ∀ v ∈ vs, 0 ≤ e v) (hX : ∀ v ∈ vs, X v ≤ X' v) (he : ∀ v ∈ vs, e v ≤ e' v) :
    0 ≤ (vs.map X).prod ∧ (vs.map X).prod ≤ (vs.map X').prod ∧ 0 ≤ prodErr X e vs ∧
      prodErr X e vs ≤ prodErr X' e' vs := by
  induction vs with
  | nil => simp [prodErr]
  | cons v vs ih =>
    obtain ⟨hXv, hX0⟩ := List.forall_mem_cons.1 hX0
    obtain ⟨hev, he0⟩ := List.forall_mem_cons.1 he0
    obtain ⟨hXv', hX⟩ := List.forall_mem_cons.1 hX
    obtain ⟨hev', he⟩ := List.forall_mem_cons.1 he
    obtain ⟨h1, h2, h3, h4⟩ := ih hX0 he0 hX he
    simp only [prodErr, List.map_cons, List.prod_cons] at h3 h4 ⊢
    set A := (vs.map fun v ↦ X v + e v).prod
    set B := (vs.map X).prod
    set A' := (vs.map fun v ↦ X' v + e' v).prod
    set B' := (vs.map X').prod
    refine ⟨mul_nonneg hXv h1, mul_le_mul hXv' h2 h1 (hXv.trans hXv'), ?_, ?_⟩
    · nlinarith
    · nlinarith [mul_le_mul hXv' h4 h3 (hXv.trans hXv'), mul_le_mul hev' (show A ≤ A' by linarith)
        (by linarith) (hev.trans hev')]

/-- The perturbation bound of a polynomial grows with the bounds on its variables. -/
theorem pairPolyErr_mono (P : List PairMonomial) {X X' e e' : ℕ → ℝ}
    (hX0 : ∀ μ ∈ P, ∀ v ∈ μ.vars, 0 ≤ X v) (he0 : ∀ μ ∈ P, ∀ v ∈ μ.vars, 0 ≤ e v)
    (hX : ∀ μ ∈ P, ∀ v ∈ μ.vars, X v ≤ X' v) (he : ∀ μ ∈ P, ∀ v ∈ μ.vars, e v ≤ e' v) :
    pairPolyErr P X e ≤ pairPolyErr P X' e' := by
  unfold pairPolyErr
  induction P with
  | nil => simp
  | cons μ P ih =>
    simp only [List.forall_mem_cons] at hX0 he0 hX he
    simp only [List.map_cons, List.sum_cons]
    have := ih hX0.2 he0.2 hX.2 he.2
    have := (prodErr_mono μ.vars hX0.1 he0.1 hX.1 he.1).2.2.2
    gcongr

end CAS.Numerics

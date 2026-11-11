/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.CoefficientList
public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.List.GetD

/-!
# Rational coefficient lists as Mathlib polynomials

Mathlib's `Polynomial.ofCoeffList l` is the polynomial with the coefficients `l`, lowest degree
first, the convention of `CAS.Polynomial.coeffEval`. The list operations of
`CAS.Polynomial.CoefficientList` compute the polynomial operations under `ofCoeffList`: sums
(`ofCoeffList_coeffAdd`), scalar multiples (`ofCoeffList_coeffScale`), products
(`ofCoeffList_coeffMul`), powers (`ofCoeffList_coeffPow`) and derivatives
(`ofCoeffList_coeffDeriv`), and the Boolean `coeffEq` implies equality of the polynomials
(`ofCoeffList_eq_of_coeffEq`). With the degree bound `degree_ofCoeffList_lt` and the value at a
real point (`eval_map_ofCoeffList`), these move an identity between coefficient lists, which the
kernel decides, to an identity between polynomials over any ring that `ℚ` maps to, as for the
complex polynomials `CAS.AlgRoot.polyC`.
-/

@[expose] public section

namespace CAS.Polynomial

open _root_.Polynomial

/-- `coeffScale c l` is the polynomial `C c * ofCoeffList l`. -/
theorem ofCoeffList_coeffScale (c : ℚ) (l : List ℚ) :
    ofCoeffList (coeffScale c l) = C c * ofCoeffList l :=
  ofCoeffList_map_mul c l

/-- `coeffAdd l m` is the polynomial `ofCoeffList l + ofCoeffList m`, for lists of any lengths. -/
theorem ofCoeffList_coeffAdd (l m : List ℚ) :
    ofCoeffList (coeffAdd l m) = ofCoeffList l + ofCoeffList m := by
  fun_induction coeffAdd l m with
  | case1 | case2 => simp
  | case3 a l b m ih =>
    simp only [ofCoeffList_cons, ih, C_add]
    ring

/-- `coeffMul l m` is the polynomial `ofCoeffList l * ofCoeffList m`. -/
theorem ofCoeffList_coeffMul (l m : List ℚ) :
    ofCoeffList (coeffMul l m) = ofCoeffList l * ofCoeffList m := by
  induction l with
  | nil => simp [coeffMul]
  | cons a l ih =>
    rw [coeffMul, ofCoeffList_coeffAdd, ofCoeffList_coeffScale, ofCoeffList_zero_cons, ih,
      ofCoeffList_cons]
    ring

/-- `coeffPow l k` is the polynomial `ofCoeffList l ^ k`. -/
theorem ofCoeffList_coeffPow (l : List ℚ) (k : ℕ) :
    ofCoeffList (coeffPow l k) = ofCoeffList l ^ k := by
  induction k with
  | zero => simp [coeffPow, ofCoeffList_cons]
  | succ k ih => rw [coeffPow, ofCoeffList_coeffMul, ih, pow_succ, mul_comm]

/-- `coeffDeriv l` is the derivative of the polynomial `ofCoeffList l`. -/
theorem ofCoeffList_coeffDeriv (l : List ℚ) :
    ofCoeffList (coeffDeriv l) = derivative (ofCoeffList l) := by
  induction l with
  | nil => simp [coeffDeriv]
  | cons a l ih =>
    rw [coeffDeriv, ofCoeffList_coeffAdd, ofCoeffList_zero_cons, ih, ofCoeffList_cons,
      derivative_add, derivative_C, derivative_mul, derivative_X, zero_add, one_mul]

/-- A list on which `coeffAllZero` holds, all of whose entries are zero, is the zero polynomial. -/
theorem ofCoeffList_eq_zero_of_coeffAllZero :
    ∀ {l : List ℚ}, coeffAllZero l = true → ofCoeffList l = 0
  | [], _ => ofCoeffList_nil
  | a :: l, h => by
    simp only [coeffAllZero, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [ofCoeffList_cons, ofCoeffList_eq_zero_of_coeffAllZero h.2, h.1]
    simp

/-- Two lists that `coeffEq` accepts, equal up to trailing zeros, are the same polynomial. -/
theorem ofCoeffList_eq_of_coeffEq :
    ∀ {l m : List ℚ}, coeffEq l m = true → ofCoeffList l = ofCoeffList m
  | [], m, h => by
    simp only [coeffEq] at h
    rw [ofCoeffList_nil, ofCoeffList_eq_zero_of_coeffAllZero h]
  | a :: l, [], h => by
    simp only [coeffEq] at h
    rw [ofCoeffList_nil, ofCoeffList_eq_zero_of_coeffAllZero h]
  | a :: l, b :: m, h => by
    simp only [coeffEq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [ofCoeffList_cons, ofCoeffList_cons, ofCoeffList_eq_of_coeffEq h.2, h.1]

/-- Over any semiring, the polynomial of a list of `n` coefficients has degree less than `n`. -/
theorem degree_ofCoeffList_lt {R : Type*} [Semiring R] (l : List R) :
    (ofCoeffList l).degree < l.length := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_ofCoeffList, List.getD_eq_default _ _ hm]

/-- For any ring homomorphism `f : ℚ →+* ℝ`, the polynomial `ofCoeffList a` mapped by `f` takes
the value `coeffEval a x` at every real `x`. -/
theorem eval_map_ofCoeffList (f : ℚ →+* ℝ) (a : List ℚ) (x : ℝ) :
    ((ofCoeffList a).map f).eval x = coeffEval a x := by
  induction a with
  | nil => simp
  | cons c cs ih =>
    rw [ofCoeffList_cons, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, ih]
    simp

end CAS.Polynomial

/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
module

public import CAS.Continuum.TaylorJet
public import Mathlib.Data.List.GetD

/-!
# Horner evaluation of coefficient lists

`listHornerEval x cs` evaluates the polynomial with ascending coefficient list `cs` at `x` by
the finite Horner recurrence `finiteHornerEval`, reading coefficients past the end of the list
as `0`. The empty list is the zero polynomial (`listHornerEval_nil`), prepending a coefficient is
one Horner step (`listHornerEval_cons`), and over a commutative semiring the value is the power
sum `∑ k < cs.length, cs[k] * x ^ k` (`listHornerEval_eq_sum`).
-/

@[expose] public section

namespace CAS.Polynomial

open CAS.Continuum
open scoped BigOperators

/-- Evaluate an ascending coefficient list by the finite Horner recurrence. -/
def listHornerEval {R : Type*} [Semiring R] (x : R) (coefficients : List R) : R :=
  finiteHornerEval coefficients.length x (fun k ↦ coefficients.getD k 0)

/-- An empty coefficient list represents the zero polynomial. -/
@[simp]
theorem listHornerEval_nil {R : Type*} [Semiring R] (x : R) :
    listHornerEval x [] = 0 := rfl

/-- Prepending the constant coefficient is one step of Horner evaluation. -/
@[simp]
theorem listHornerEval_cons {R : Type*} [Semiring R] (x c : R) (coefficients : List R) :
    listHornerEval x (c :: coefficients) = listHornerEval x coefficients * x + c := by
  simp [listHornerEval, finiteHornerEval]

/-- List Horner evaluation equals the finite ascending power-basis sum. -/
theorem listHornerEval_eq_sum {R : Type*} [CommSemiring R]
    (x : R) (coefficients : List R) :
    listHornerEval x coefficients =
      ∑ k ∈ Finset.range coefficients.length, coefficients.getD k 0 * x ^ k := by
  rw [listHornerEval, finiteHornerEval_eq_sum, Finset.sum_range_succ]
  simp

end CAS.Polynomial

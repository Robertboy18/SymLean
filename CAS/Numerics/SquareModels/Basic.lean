/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CAS.Numerics.BinaryGridNatural

/-!
# Polynomial models on the unit square

A `SquareModel` is a polynomial `m(s, t) = ∑ c s^a t^b`, given as a list of terms `(a, b, c)`
with integer coefficients in units of `2 ^ -P`, together with a radius `rad` in the same units.
It encloses a function `f` on the unit square when `|f(s, t) - m(s, t)| ≤ rad 2 ^ -P` for all
`s, t ∈ [0, 1]` (`SquareModel.Encloses`).

## Main definitions

* `SquareModel`: a midpoint polynomial on the unit square with a radius, in units of `2 ^ -P`.
* `SquareModel.Encloses`: `|f(s, t) - m(s, t)| ≤ rad 2 ^ -P` on the unit square.
-/

@[expose] public section

namespace CAS.Numerics

open Finset Set

/-- A polynomial model on the unit square: terms `(a, b, c)` of the midpoint `∑ c s^a t^b` and a
radius, in units of `2 ^ -P`. -/
structure SquareModel where
  /-- The terms `(a, b, c)` of the midpoint. -/
  terms : List (ℕ × ℕ × ℤ)
  /-- The radius. -/
  rad : ℕ

namespace SquareModel

/-- The value `c s^a t^b` of a term. -/
def termEval (s t : ℝ) (τ : ℕ × ℕ × ℤ) : ℝ := (τ.2.2 : ℝ) * s ^ τ.1 * t ^ τ.2.1

/-- The value of a list of terms. -/
def listEval (s t : ℝ) (l : List (ℕ × ℕ × ℤ)) : ℝ := (l.map (termEval s t)).sum

variable (M : SquareModel) (P : ℕ)

/-- The midpoint polynomial at a point, in units of `2 ^ -P`. -/
def midEval (s t : ℝ) : ℝ := listEval s t M.terms

/-- `M` encloses `f` on the unit square at precision `P`. -/
def Encloses (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |f s t - M.midEval s t / 2 ^ P| ≤ M.rad / 2 ^ P

/-! ### Values of term lists -/

/-- The empty term list has the value `0`. -/
@[simp] theorem listEval_nil (s t : ℝ) : listEval s t [] = 0 := rfl

/-- The value of `τ :: l` is the value of the term `τ` plus the value of `l`. -/
@[simp] theorem listEval_cons (s t : ℝ) (τ : ℕ × ℕ × ℤ) (l : List (ℕ × ℕ × ℤ)) :
    listEval s t (τ :: l) = termEval s t τ + listEval s t l := by
  simp [listEval]

/-- The value of a concatenation of term lists is the sum of their values. -/
@[simp] theorem listEval_append (s t : ℝ) (l l' : List (ℕ × ℕ × ℤ)) :
    listEval s t (l ++ l') = listEval s t l + listEval s t l' := by
  simp [listEval]

/-! ### Negation -/

/-- Negating every coefficient negates the value of a term list. -/
@[simp] theorem listEval_neg (s t : ℝ) (l : List (ℕ × ℕ × ℤ)) :
    listEval s t (l.map fun τ ↦ (τ.1, τ.2.1, -τ.2.2)) = -listEval s t l := by
  induction l with
  | nil => simp
  | cons τ l ih =>
    simp only [List.map_cons, listEval_cons, ih, termEval, Int.cast_neg]
    ring

/-! ### Sums over ranges -/

/-- A list sum over `List.range n` is the finite sum over `range n`. -/
theorem list_sum_range (n : ℕ) (f : ℕ → ℝ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

end SquareModel

end CAS.Numerics
